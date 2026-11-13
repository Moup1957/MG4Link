package fr.alexandre.mg4link

import android.Manifest
import android.annotation.SuppressLint
import android.app.Activity
import android.app.AlertDialog
import android.bluetooth.BluetoothDevice
import android.bluetooth.BluetoothGatt
import android.bluetooth.BluetoothGattCallback
import android.bluetooth.BluetoothGattCharacteristic
import android.bluetooth.BluetoothGattDescriptor
import android.bluetooth.BluetoothManager
import android.bluetooth.BluetoothProfile
import android.bluetooth.le.ScanCallback
import android.bluetooth.le.ScanResult
import android.content.ClipData
import android.content.ClipboardManager
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.graphics.Color
import android.graphics.PixelFormat
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.LayerDrawable
import android.location.Location
import android.location.LocationListener
import android.location.LocationManager
import android.media.AudioManager
import android.media.ToneGenerator
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.Looper
import android.provider.Settings
import android.text.InputType
import android.view.Gravity
import android.webkit.JavascriptInterface
import android.webkit.WebView
import android.webkit.WebViewClient
import android.webkit.WebChromeClient
import android.webkit.ConsoleMessage
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.Window
import android.view.WindowManager
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.Switch
import android.widget.TextView
import java.io.BufferedReader
import java.io.File
import java.io.InputStreamReader
import java.net.HttpURLConnection
import java.net.URLEncoder
import java.net.URL
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.UUID
import java.util.concurrent.LinkedBlockingQueue
import java.util.concurrent.TimeUnit
import kotlin.concurrent.thread

private val CCCD_UUID: UUID = UUID.fromString("00002902-0000-1000-8000-00805f9b34fb")

private fun has(props: Int, flag: Int): Boolean = (props and flag) != 0

private fun propsText(p: Int): String {
    val l = ArrayList<String>()
    if (has(p, BluetoothGattCharacteristic.PROPERTY_READ)) l.add("read")
    if (has(p, BluetoothGattCharacteristic.PROPERTY_WRITE)) l.add("write")
    if (has(p, BluetoothGattCharacteristic.PROPERTY_WRITE_NO_RESPONSE)) l.add("write-nr")
    if (has(p, BluetoothGattCharacteristic.PROPERTY_NOTIFY)) l.add("notify")
    if (has(p, BluetoothGattCharacteristic.PROPERTY_INDICATE)) l.add("indicate")
    return l.joinToString(",")
}

/** Appareil Bluetooth LE vu pendant le scan. */
class Found(val dev: BluetoothDevice, var name: String, var rssi: Int)

/** Étape d'un itinéraire : nom, distance prévue, et position GPS si géocodée (v0.8). */
class Stage(val name: String, val km: Double, val lat: Double = 0.0, val lon: Double = 0.0) {
    val hasPos: Boolean get() = lat != 0.0 || lon != 0.0
}

/** Position retournée par le géocodage d'une adresse. */
class Geo(val lat: Double, val lon: Double)

/** Borne de recharge issue de la base IRVE. */
class Borne(val lat: Double, val lon: Double, val kw: Double, val enseigne: String, val nom: String, val adresse: String)

/** v0.41 : radar / zone de danger (fichier « Zones de danger Europe CSV »
 * de lufop.net, placé dans Download/MG4Link/radars.csv). */
class Radar(val lat: Double, val lon: Double, val name: String, val speed: Int)

/**
 * Lien série ELM327 au-dessus d'une caractéristique BLE :
 * on écrit une commande, on attend la réponse jusqu'au prompt '>'.
 */
@SuppressLint("MissingPermission")
class ElmLink {
    @Volatile
    var gatt: BluetoothGatt? = null

    @Volatile
    var writeChar: BluetoothGattCharacteristic? = null

    private val rx = LinkedBlockingQueue<String>()

    fun onData(bytes: ByteArray) {
        rx.offer(String(bytes, Charsets.US_ASCII))
    }

    @Synchronized
    fun request(cmd: String, timeoutMs: Long = 4000): String {
        val g = gatt ?: return "ERREUR : non connecté"
        val c = writeChar ?: return "ERREUR : pas de caractéristique d'écriture"
        rx.clear()

        val noResp = has(c.properties, BluetoothGattCharacteristic.PROPERTY_WRITE_NO_RESPONSE) &&
            !has(c.properties, BluetoothGattCharacteristic.PROPERTY_WRITE)
        val data = (cmd + "\r").toByteArray(Charsets.US_ASCII)
        var off = 0
        while (off < data.size) {
            val end = minOf(off + 20, data.size)
            c.value = data.copyOfRange(off, end)
            c.writeType = if (noResp) {
                BluetoothGattCharacteristic.WRITE_TYPE_NO_RESPONSE
            } else {
                BluetoothGattCharacteristic.WRITE_TYPE_DEFAULT
            }
            // v0.29 : Android refuse une écriture quand la précédente n'est
            // pas encore terminée (GATT « busy », fréquent juste après une
            // reconnexion). On retente jusqu'à 3 fois avec 250 ms d'écart
            // avant d'abandonner.
            var written = false
            for (tryIdx in 1..3) {
                if (g.writeCharacteristic(c)) { written = true; break }
                Thread.sleep(250)
            }
            if (!written) return "ERREUR : écriture refusée"
            off = end
            Thread.sleep(30)
        }

        val sb = StringBuilder()
        var gotPrompt = false
        val deadline = System.currentTimeMillis() + timeoutMs
        while (System.currentTimeMillis() < deadline) {
            val part = rx.poll(100, TimeUnit.MILLISECONDS) ?: continue
            sb.append(part)
            if (sb.indexOf(">") >= 0) {
                gotPrompt = true
                break
            }
        }
        val raw = sb.toString().replace(">", "")
        val lines = raw.split('\r', '\n').map { it.trim() }.filter { it.isNotEmpty() && it != cmd }
        val res = lines.joinToString("\n")
        return if (gotPrompt) res else "$res [délai dépassé]"
    }
}

@SuppressLint("MissingPermission")
class MainActivity : Activity() {

    private val handler = Handler(Looper.getMainLooper())
    private val clock = SimpleDateFormat("HH:mm:ss", Locale.FRANCE)
    private val logBuf = StringBuilder()

    private lateinit var statusTv: TextView
    private lateinit var liveTv: TextView
    private lateinit var routeTv: TextView
    private lateinit var logTv: TextView
    private lateinit var logScroll: ScrollView
    private lateinit var cmdEt: EditText

    private val elm = ElmLink()
    private var gatt: BluetoothGatt? = null
    private val found = LinkedHashMap<String, Found>()
    private var scanning = false

    @Volatile
    private var ready = false

    @Volatile
    private var liveOn = false
    private var liveThread: Thread? = null
    private var liveGen = 0

    @Volatile
    private var needElmReinit = false
    private lateinit var liveSwitch: Switch

    @Volatile
    private var obdSpeed = "-"

    @Volatile
    private var volt = "-"

    @Volatile
    private var soc = "-"

    @Volatile
    private var odo = "-"

    @Volatile
    private var v42 = "-"

    @Volatile
    private var gpsInfo = "GPS : en attente de signal"

    @Volatile
    private var tripKm = 0.0
    private var lastLoc: Location? = null
    private var gpsStarted = false

    @Volatile
    private var gpsFixed = false

    // ------------------------------------------------------- Itinéraire
    @Volatile
    private var socPct = -1.0

    @Volatile
    private var consoPctPerKm = 0.22

    private val stages = ArrayList<Stage>()
    private var tripActive = false
    private var stageIdx = 0
    private var stageStartKm = 0.0
    private var stageStartSoc = -1.0
    private var lowWarned = false

    // v0.13 : reste à parcourir recalculé par la route depuis la position
    // actuelle (comme un GPS). -1 = pas encore calculé.
    @Volatile
    private var remainKm = -1.0

    // v0.38 : SOH mesuré (bouton « SOH batterie… »), affiché dans la
    // fenêtre flottante tant qu'il est connu.
    @Volatile
    private var sohPct = -1.0

    // Apprentissage continu (v0.7.2)
    @Volatile
    private var learnKm = 0.0

    @Volatile
    private var learnSoc = -1.0

    // Watchdog + correction de charge (v0.9)
    @Volatile
    private var lastLiveTick = 0L

    @Volatile
    private var socFactor = 1.0

    @Volatile
    private var last5bPct = -1.0

    @Volatile
    private var lastLoggedSoc = -1.0

    // -------------------------------------------- Fenêtre flottante
    private var overlayLayout: LinearLayout? = null
    private var overlayTv: TextView? = null
    private val wm: WindowManager
        get() = getSystemService(Context.WINDOW_SERVICE) as WindowManager

    // --------------------------------------------------- Bornes IRVE v0.7
    private val bornes = ArrayList<Borne>()

    @Volatile
    private var bornesLoading = false

    // v0.41 : radars / zones de danger (lufop.net, Download/MG4Link/radars.csv)
    private val radars = ArrayList<Radar>()
    @Volatile
    private var radarInfo = "" // ligne « ⚠ RADAR … » affichée dans la fenêtre flottante
    @Volatile
    private var lastRadarKey = ""
    @Volatile
    private var lastRadarLevel = 0
    @Volatile
    private var lastRadarCheck = 0L
    @Volatile
    private var lastRadarBeep = 0L
    // v0.46 : compteur de recharges DC (détection : SOC qui monte vite).
    @Volatile
    private var dcCount = 0
    @Volatile
    private var dcSoc0 = -1.0
    @Volatile
    private var dcT0 = 0L
    @Volatile
    private var dcRate = 0.0
    @Volatile
    private var dcLastUp = 0L
    @Volatile
    private var dcLastSoc = -1.0
    @Volatile
    private var dcLastT = 0L

    // ------------------------------------------------------------------ UI

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).toInt()

    /** v0.21 : fond de bouton avec cadre double trait (effet de relief
     * sur l'écran noir) : liseré extérieur + fond en retrait avec son
     * propre liseré clair. */
    private fun framedBg(fill: Int): LayerDrawable {
        val fond = GradientDrawable()
        fond.setColor(fill)
        fond.cornerRadius = dp(4).toFloat()
        fond.setStroke(dp(1), 0xFF90A4AE.toInt())
        val cadre = GradientDrawable()
        cadre.setColor(0xFF455A64.toInt())
        cadre.cornerRadius = dp(4).toFloat()
        cadre.setStroke(dp(1), 0xFF546E7A.toInt())
        val layers = LayerDrawable(arrayOf(cadre, fond))
        layers.setLayerInset(1, dp(2), dp(2), dp(2), dp(2))
        return layers
    }

    private fun makeButton(label: String, onClick: () -> Unit): Button {
        val b = Button(this)
        b.text = label
        b.isAllCaps = false
        // v0.19 : boutons compacts pour agrandir les zones d'affichage.
        b.textSize = 12f
        b.minHeight = 0
        b.minWidth = 0
        b.setPadding(dp(8), dp(5), dp(8), dp(5))
        // v0.20 : thème sombre - texte blanc sur fond gris foncé.
        b.setTextColor(Color.WHITE)
        // v0.21 : cadre double trait pour donner du volume au bouton.
        b.background = framedBg(0xFF37474F.toInt())
        b.setOnClickListener { onClick() }
        return b
    }

    private fun row(vararg views: View): LinearLayout {
        val r = LinearLayout(this)
        r.orientation = LinearLayout.HORIZONTAL
        for (v in views) {
            val lp = LinearLayout.LayoutParams(
                0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
            // v0.21 : espace entre les boutons (séparation).
            lp.setMargins(dp(2), dp(2), dp(2), dp(2))
            r.addView(v, lp)
        }
        return r
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)

        val root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        // v0.20 : retour au thème sombre - fond noir, textes blancs,
        // boutons gris foncé, onglet actif vert.
        root.setBackgroundColor(Color.BLACK)
        root.setPadding(dp(8), dp(28), dp(8), dp(8))

        statusTv = TextView(this)
        statusTv.textSize = 17f
        statusTv.typeface = Typeface.DEFAULT_BOLD
        statusTv.setTextColor(Color.WHITE)
        statusTv.text = "MG4 Link v0.49 - non connecté"
        root.addView(statusTv)

        // v0.18 : l'app est organisée en 4 onglets — Connexion, Itinéraire,
        // Bornes, Code (commande + journal). Un seul onglet visible à la fois.
        fun newSection(): LinearLayout {
            val s = LinearLayout(this)
            s.orientation = LinearLayout.VERTICAL
            return s
        }
        val secConn = newSection()
        val secRoute = newSection()
        val secBornes = newSection()
        val secCode = newSection()
        val tabTitles = listOf("Connexion", "Itinéraire", "Bornes", "Code")
        val contents = listOf(secConn, secRoute, secBornes, secCode)

        val tabBtns = ArrayList<Button>()
        // v0.20 : thème sombre - gris foncé, texte blanc ; l'onglet actif
        // passe au vert dans showTab().
        for (t in tabTitles) {
            val b = Button(this)
            b.text = t
            b.isAllCaps = false
            b.textSize = 13f
            b.minHeight = 0
            b.setPadding(dp(4), dp(6), dp(4), dp(6))
            b.setTextColor(Color.WHITE)
            // v0.21 : cadre double trait aussi sur les onglets.
            b.background = framedBg(0xFF424242.toInt())
            tabBtns.add(b)
        }
        val tabRow = LinearLayout(this)
        tabRow.orientation = LinearLayout.HORIZONTAL
        for (b in tabBtns) {
            tabRow.addView(b, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))
        }
        root.addView(tabRow)
        // v0.21 : on masque le VRAI conteneur ajouté à root (section ou
        // ScrollView). Avant, on ne masquait que la section INTÉRIEURE :
        // les ScrollView vides des onglets Itinéraire/Bornes restaient
        // visibles et occupaient chacune un tiers de l'écran, ce qui
        // poussait le contenu des autres onglets vers le bas.
        val containers = ArrayList<View>()
        for (i in contents.indices) {
            if (i == 0 || i == 3) {
                // v0.20 : Connexion et Code ne défilent pas - leur zone
                // d'affichage (données voiture, journal) occupe toute la
                // hauteur restante (weight 1).
                root.addView(contents[i], LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))
                containers.add(contents[i])
            } else {
                val sc = ScrollView(this)
                sc.addView(contents[i])
                root.addView(sc, LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))
                containers.add(sc)
            }
        }
        fun showTab(i: Int) {
            for (j in containers.indices) {
                containers[j].visibility = if (j == i) View.VISIBLE else View.GONE
                // v0.20 : onglet actif vert, les autres gris foncé.
                tabBtns[j].background = framedBg(
                    if (j == i) 0xFF2E7D32.toInt() else 0xFF424242.toInt())
                tabBtns[j].setTextColor(Color.WHITE)
                tabBtns[j].setTypeface(null, if (j == i) Typeface.BOLD else Typeface.NORMAL)
            }
            // v0.18 : à l'ouverture de l'onglet Code, le journal défile en bas.
            if (i == 3) logScroll.post { logScroll.fullScroll(View.FOCUS_DOWN) }
        }
        for (i in tabBtns.indices) tabBtns[i].setOnClickListener { showTab(i) }

        // ----- Onglet CONNEXION -----
        secConn.addView(
            row(
                makeButton("Scanner et connecter") { startScan() },
                makeButton("Déconnecter") {
                    disconnect()
                    status("Déconnecté")
                    log("Déconnexion demandée")
                }
            )
        )

        liveSwitch = Switch(this)
        liveSwitch.text = "Lecture live"
        // v0.20 : texte blanc et taille compacte.
        liveSwitch.textSize = 12f
        liveSwitch.setTextColor(Color.WHITE)
        liveSwitch.setOnCheckedChangeListener { _, on -> setLive(on) }
        secConn.addView(
            row(
                makeButton("Tests de base") { testsBase() },
                makeButton("Tests batterie") { testsBatterie() }
            )
        )
        // v0.37 : santé de la batterie (SOH) lue dans le BMS.
        secConn.addView(row(makeButton("SOH batterie…") { readSoh() }))
        secConn.addView(liveSwitch)

        secConn.addView(row(makeButton("Charge affichée…") { askSoc() }))

        liveTv = TextView(this)
        liveTv.typeface = Typeface.MONOSPACE
        liveTv.textSize = 12f
        liveTv.setTextColor(Color.WHITE)
        liveTv.setPadding(0, dp(3), 0, dp(3))
        // v0.20 : zone de données pleine hauteur - les 8 lignes de
        // la voiture s'affichent sans faire défiler.
        secConn.addView(liveTv, LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))
        refreshLive()

        // ----- Onglet ITINÉRAIRE -----
        secRoute.addView(
            row(
                makeButton("Itinéraire…") { editStages() },
                makeButton("Démarrer le trajet") { startTrip() },
                makeButton("Étape suivante") { nextStage() }
            )
        )

        secRoute.addView(
            row(
                makeButton("Itinéraire dans Maps") { openInMaps() },
                makeButton("Fenêtre flottante") { toggleOverlay() }
            )
        )

        secRoute.addView(
            row(
                makeButton("Sauver itinéraire") { saveItinerary() },
                makeButton("Charger itinéraire") { loadItinerary() },
                makeButton("Calibrage…") { calibrate() }
            )
        )

        // v0.18 : « Supprimer étape » déplacé dans l'onglet Itinéraire.
        secRoute.addView(
            row(
                makeButton("Supprimer étape…") { removeStage() }
            )
        )

        routeTv = TextView(this)
        routeTv.typeface = Typeface.MONOSPACE
        routeTv.textSize = 12f
        routeTv.setTextColor(Color.WHITE)
        routeTv.setPadding(0, dp(2), 0, dp(2))
        secRoute.addView(routeTv)
        refreshRoute()

        // ----- Onglet BORNES -----
        secBornes.addView(
            row(
                makeButton("Bornes recharge") { showBornes() },
                makeButton("Mettre à jour bornes") { updateBornes(true) }
            )
        )

        secBornes.addView(
            row(
                makeButton("Carte bornes…") { showBornesMap() }
            )
        )

        // ----- Onglet CODE (commande + journal) -----
        cmdEt = EditText(this)
        cmdEt.hint = "Commande, ex. 010D (lecture seule !)"
        cmdEt.setSingleLine(true)
        // v0.20 : texte blanc, ligne de commande compacte.
        cmdEt.setTextColor(Color.WHITE)
        cmdEt.setHintTextColor(0xFFB0BEC5.toInt())
        cmdEt.minHeight = 0
        cmdEt.setPadding(dp(8), dp(4), dp(8), dp(4))
        val cmdRow = LinearLayout(this)
        cmdRow.orientation = LinearLayout.HORIZONTAL
        cmdRow.addView(cmdEt, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 3f))
        cmdRow.addView(
            makeButton("Envoyer") { sendManual() },
            LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1.4f)
        )
        secCode.addView(cmdRow)

        // v0.18 : confirmation avant d'effacer le journal (effacements
        // accidentels en touchant le bouton pendant un défilement).
        secCode.addView(
            row(
                makeButton("Copier") { copyLog() },
                makeButton("Partager") { shareLog() },
                makeButton("Effacer") {
                    AlertDialog.Builder(this)
                        .setTitle("Effacer le journal ?")
                        .setMessage("Tout l'historique affiché sera vidé.")
                        .setPositiveButton("Effacer") { _, _ ->
                            synchronized(logBuf) { logBuf.setLength(0) }
                            logTv.text = ""
                        }
                        .setNegativeButton("Annuler", null)
                        .show()
                }
            )
        )

        logTv = TextView(this)
        logTv.typeface = Typeface.MONOSPACE
        logTv.textSize = 11f
        logTv.setTextColor(Color.WHITE)
        logTv.setTextIsSelectable(true)
        logScroll = ScrollView(this)
        logScroll.addView(logTv)
        secCode.addView(logScroll, LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))

        showTab(0)
        setContentView(root)

        log("MG4 Link v0.49 démarré (Android ${Build.VERSION.RELEASE}, SDK ${Build.VERSION.SDK_INT})")
        val prefs = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
        val savedConso = prefs.getFloat("conso", 0f)
        if (savedConso > 0f) {
            consoPctPerKm = savedConso.toDouble()
            log("Calibrage mémorisé : " + "%.3f".format(consoPctPerKm) + " %/km (autonomie à 100 % : " +
                "%.0f".format(100.0 / consoPctPerKm) + " km)")
        }
        socFactor = prefs.getFloat("socFactor", 1f).toDouble()
        if (Math.abs(socFactor - 1.0) > 0.01) {
            log("Correction de charge OBD mémorisée : ×" + "%.3f".format(socFactor))
        }
        lastLiveTick = System.currentTimeMillis()
        // Watchdog (v0.9) : si le fil de lecture live se bloque (accroc Bluetooth),
        // il est relancé automatiquement — sinon les valeurs restent figées.
        thread(name = "watchdog") {
            while (true) {
                Thread.sleep(5000)
                if (liveOn && ready && System.currentTimeMillis() - lastLiveTick > 15000) {
                    if (liveThread?.isAlive == true) {
                        // v0.12 : le fil vit mais la voiture ne répond plus → on demande
                        // au fil de réinitialiser le dongle ELM327 (une seule fois, pas de spam).
                        if (!needElmReinit) {
                            log("Lecture live sans réponse OBD depuis 15 s - réinitialisation du dongle demandée.")
                            needElmReinit = true
                        }
                    } else {
                        log("Fil de lecture live arrêté - redémarrage automatique.")
                        startLiveThread()
                    }
                }
            }
        }
        // v0.13 : recalcul routier périodique du reste à parcourir (comme un GPS).
        // Si vous empruntez un autre itinéraire que celui estimé au départ, la
        // distance restante et la charge prévue à l'arrivée se recalent toutes seules.
        thread(name = "reste-gps") {
            var lastStage = -1
            var lastKm = -999.0
            while (true) {
                Thread.sleep(30000)
                val idx = if (tripActive) stageIdx else -1
                val st = stages.getOrNull(idx)
                val loc = lastLoc
                if (tripActive && st != null && st.hasPos && loc != null) {
                    if (idx != lastStage) {
                        lastStage = idx
                        lastKm = -999.0
                    }
                    // v0.28 : seule une distance routière RÉELLE met à jour
                    // le reste (les estimations à vol d'oiseau faisaient
                    // sauter le compteur : 1,7 -> 4,8 -> 0,9 km).
                    val km = tryRoadKm(Geo(loc.latitude, loc.longitude), Geo(st.lat, st.lon))
                    if (km != null && km > 0 && Math.abs(km - lastKm) >= 1.0) {
                        remainKm = km
                        lastKm = km
                        log("Reste " + fmtKm(km) + " km par la route jusqu'à « " +
                            st.name.take(30) + " » (recalculé).")
                        if (km <= 1.0) {
                            handler.post { finishStage(false) }
                        } else {
                            handler.post {
                                refreshRoute()
                                refreshOverlay()
                            }
                        }
                    } else if (km == null) {
                        // v0.28 : OSRM en panne - l'arrivée est quand même
                        // détectée si on est physiquement proche de l'étape.
                        if (distKm(loc.latitude, loc.longitude, st.lat, st.lon) <= 0.35) {
                            handler.post { finishStage(false) }
                        }
                    }
                }
            }
        }
        if (hasAll()) startGps()
        ensureStorageAccess()
        thread(name = "bornes-cache") {
            restoreConsoPublic()
            restoreDc()
            loadBornesCache()
            loadRadars()
        }
    }

    /** v0.49 : confirme dans le journal quand « Tous les fichiers » est
     * accordée (au retour des réglages). Avant, la ligne « non accordée »
     * écrite au démarrage restait la dernière parole et donnait l'impression
     * d'un bug, alors que la permission était accordée juste après. */
    private var storageLogged = false

    override fun onResume() {
        super.onResume()
        if (Build.VERSION.SDK_INT >= 30 && !storageLogged &&
            android.os.Environment.isExternalStorageManager()) {
            storageLogged = true
            log("Autorisation « Tous les fichiers » accordée : les caches " +
                "survivront à une réinstallation.")
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        disconnect()
        hideOverlay()
        try {
            val lm = getSystemService(Context.LOCATION_SERVICE) as LocationManager
            lm.removeUpdates(locListener)
        } catch (e: Exception) {
            // rien
        }
    }

    private fun status(s: String) {
        handler.post { statusTv.text = s }
    }

    private fun log(msg: String) {
        val line = clock.format(Date()) + "  " + msg
        synchronized(logBuf) {
            logBuf.append(line).append('\n')
            if (logBuf.length > 300_000) logBuf.delete(0, 100_000)
        }
        handler.post {
            logTv.append(line + "\n")
            if (logTv.length() > 40_000) {
                val t = logTv.text.toString()
                logTv.text = t.substring(t.length - 25_000)
            }
            logScroll.post { logScroll.fullScroll(View.FOCUS_DOWN) }
        }
    }

    /** Petite boîte de dialogue d'information. */
    private fun alert(titre: String, msg: String) {
        handler.post {
            AlertDialog.Builder(this)
                .setTitle(titre)
                .setMessage(msg)
                .setPositiveButton("OK", null)
                .show()
        }
    }

    private fun refreshLive() {
        val autonomie = if (socPct >= 0) "%.0f".format(socPct / consoPctPerKm) + " km" else "?"
        val txt = "Charge : $soc\n" +
            "Autonomie estimée : $autonomie\n" +
            "Odomètre (PID A6) : $odo\n" +
            "Vitesse (OBD 010D) : $obdSpeed\n" +
            "Tension 12 V (ATRV) : $volt\n" +
            "Tension module (PID 42) : $v42\n" +
            "$gpsInfo\n" +
            "Distance GPS : " + "%.2f".format(tripKm) + " km\n" +
            // v0.47 : compteur de recharges DC (persistant).
            "Recharges DC : $dcCount"
        handler.post { liveTv.text = txt }
    }

    private fun logText(): String = synchronized(logBuf) { logBuf.toString() }

    private fun copyLog() {
        val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
        cm.setPrimaryClip(ClipData.newPlainText("journal", logText()))
        status("Journal copié")
    }

    private fun shareLog() {
        val i = Intent(Intent.ACTION_SEND)
        i.type = "text/plain"
        i.putExtra(Intent.EXTRA_SUBJECT, "Journal MG4 Link")
        i.putExtra(Intent.EXTRA_TEXT, logText().takeLast(150_000))
        startActivity(Intent.createChooser(i, "Partager le journal"))
    }

    // --------------------------------------------------------- Permissions

    private fun neededPermissions(): Array<String> {
        val l = ArrayList<String>()
        l.add(Manifest.permission.ACCESS_FINE_LOCATION)
        if (Build.VERSION.SDK_INT >= 31) {
            l.add(Manifest.permission.BLUETOOTH_SCAN)
            l.add(Manifest.permission.BLUETOOTH_CONNECT)
        }
        return l.toTypedArray()
    }

    private fun hasAll(): Boolean =
        neededPermissions().all { checkSelfPermission(it) == PackageManager.PERMISSION_GRANTED }

    override fun onRequestPermissionsResult(
        requestCode: Int,
        permissions: Array<out String>,
        grantResults: IntArray
    ) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (hasAll()) {
            startGps()
            log("Autorisations accordées. Touchez de nouveau « Scanner et connecter ».")
        } else {
            log("Autorisations refusées : Bluetooth et position sont nécessaires.")
            status("Autorisations manquantes")
        }
    }

    // ----------------------------------------------------------------- GPS

    private val locListener = object : LocationListener {
        override fun onLocationChanged(loc: Location) {
            // v0.35 : le premier point reçu est journalisé - indispensable
            // pour distinguer « GPS pas encore fixé » d'un vrai problème.
            if (!gpsFixed) {
                gpsFixed = true
                log("Position GPS reçue (±" + loc.accuracy.toInt() + " m, " +
                    loc.provider + ") : calcul des distances possible.")
            }
            val prev = lastLoc
            if (prev != null && loc.speed > 1f) {
                val d = prev.distanceTo(loc)
                if (d < 500f) tripKm += d / 1000.0
            }
            lastLoc = loc
            gpsInfo = "GPS : " + "%.1f".format(loc.speed * 3.6f) + " km/h  " +
                "%.5f".format(loc.latitude) + ", " + "%.5f".format(loc.longitude) +
                " (±" + loc.accuracy.toInt() + " m)"
            refreshLive()
            // Suivi du trajet par GPS (v0.9) : fonctionne même si la lecture
            // OBD live est bloquée ou désactivée.
            if (stageReached()) finishStage(false)
            refreshRoute()
            refreshOverlay()
            // v0.41 : alertes radars / zones de danger (5 km puis 2 km).
            checkRadars(loc)
        }

        override fun onProviderEnabled(provider: String) {}
        override fun onProviderDisabled(provider: String) {}
        override fun onStatusChanged(provider: String?, status: Int, extras: Bundle) {}
    }

    /** Dernière position connue, même sans fixation GPS active (v0.7.1). */
    private fun bestLoc(): Location? {
        return try {
            val lm = getSystemService(Context.LOCATION_SERVICE) as LocationManager
            listOf(
                LocationManager.GPS_PROVIDER,
                LocationManager.NETWORK_PROVIDER,
                LocationManager.PASSIVE_PROVIDER
            ).filter { lm.allProviders.contains(it) }
                .mapNotNull { lm.getLastKnownLocation(it) }
                .maxByOrNull { it.time }
        } catch (e: Exception) {
            null
        }
    }

    private fun startGps() {
        if (gpsStarted) return
        try {
            val lm = getSystemService(Context.LOCATION_SERVICE) as LocationManager
            // v0.35 : le GPS satellite seul peut mettre plusieurs minutes à
            // fixer à froid. Le positionnement réseau (antennes mobiles /
            // Wi-Fi, ± 20 à 100 m) donne une position en quelques secondes :
            // largement suffisant pour calculer les distances d'itinéraire,
            // et le GPS finit par prendre le relais avec la précision.
            var started = false
            for (p in listOf(LocationManager.GPS_PROVIDER, LocationManager.FUSED_PROVIDER,
                             LocationManager.NETWORK_PROVIDER, LocationManager.PASSIVE_PROVIDER)) {
                if (lm.allProviders.contains(p)) {
                    try {
                        lm.requestLocationUpdates(p, 1000L, 0f, locListener)
                        started = true
                    } catch (e: Exception) { }
                }
            }
            gpsStarted = started
            if (!started) log("GPS indisponible : aucun fournisseur de position.")
        } catch (e: Exception) {
            log("GPS indisponible : ${e.message}")
        }
    }

    // ---------------------------------------------------------------- Scan

    private val scanCb = object : ScanCallback() {
        override fun onScanResult(callbackType: Int, result: ScanResult) {
            val d = result.device
            val n = result.scanRecord?.deviceName ?: d.name ?: ""
            val f = found[d.address]
            if (f == null) {
                found[d.address] = Found(d, n, result.rssi)
            } else {
                if (n.isNotEmpty()) f.name = n
                f.rssi = result.rssi
            }
        }

        override fun onScanFailed(errorCode: Int) {
            log("Échec du scan : code $errorCode")
        }
    }

    private fun looksLikeObd(name: String): Boolean {
        val n = name.lowercase(Locale.ROOT)
        return n.contains("vlinker") || n.contains("vgate") || n.contains("obd") ||
            n.contains("elm") || n.contains("mc")
    }

    private fun startScan() {
        if (!hasAll()) {
            requestPermissions(neededPermissions(), 1)
            return
        }
        if (scanning) return
        val bm = getSystemService(Context.BLUETOOTH_SERVICE) as BluetoothManager
        val adapter = bm.adapter
        if (adapter == null || !adapter.isEnabled) {
            status("Bluetooth désactivé")
            log("Activez le Bluetooth du téléphone.")
            return
        }
        val scanner = adapter.bluetoothLeScanner
        if (scanner == null) {
            status("Scanner Bluetooth indisponible")
            return
        }
        found.clear()
        scanning = true
        scanner.startScan(scanCb)
        status("Recherche du dongle (8 s)...")
        log("Scan Bluetooth LE démarré")
        handler.postDelayed({
            try {
                scanner.stopScan(scanCb)
            } catch (e: Exception) {
                // rien
            }
            scanning = false
            showPicker()
        }, 8000)
    }

    private fun showPicker() {
        val list = found.values.sortedWith(
            compareByDescending<Found> { looksLikeObd(it.name) }.thenByDescending { it.rssi }
        )
        if (list.isEmpty()) {
            status("Aucun appareil trouvé")
            log("Aucun appareil trouvé. Dongle branché, voiture en contact ? Fermez les autres applications OBD.")
            return
        }
        val labels = list.map {
            (if (it.name.isEmpty()) "(sans nom)" else it.name) + "\n" + it.dev.address + "   " + it.rssi + " dBm"
        }.toTypedArray()
        AlertDialog.Builder(this)
            .setTitle("Choisissez le dongle")
            .setItems(labels) { _, i -> connect(list[i].dev) }
            .setNegativeButton("Annuler", null)
            .show()
    }

    // ------------------------------------------------------------- Gatt/BLE

    private fun connect(dev: BluetoothDevice) {
        disconnect()
        log("Connexion à ${dev.name ?: "?"} (${dev.address})...")
        status("Connexion...")
        gatt = dev.connectGatt(this, false, gattCb, BluetoothDevice.TRANSPORT_LE)
    }

    private fun disconnect() {
        liveOn = false
        ready = false
        liveGen++          // v0.12 : fait sortir l'ancien fil de lecture de sa boucle
        needElmReinit = false
        try {
            gatt?.disconnect()
            gatt?.close()
        } catch (e: Exception) {
            // rien
        }
        gatt = null
        elm.gatt = null
        elm.writeChar = null
    }

    private val gattCb = object : BluetoothGattCallback() {
        override fun onConnectionStateChange(g: BluetoothGatt, st: Int, newState: Int) {
            if (newState == BluetoothProfile.STATE_CONNECTED) {
                log("Bluetooth connecté (code $st). Découverte des services...")
                handler.postDelayed({ g.discoverServices() }, 400)
            } else if (newState == BluetoothProfile.STATE_DISCONNECTED) {
                log("Déconnecté (code $st)")
                status("Déconnecté")
                ready = false
                elm.writeChar = null
            }
        }

        override fun onServicesDiscovered(g: BluetoothGatt, st: Int) {
            log("Services découverts (code $st) :")
            for (s in g.services) {
                log("  service ${s.uuid}")
                for (c in s.characteristics) {
                    log("    caractéristique ${c.uuid}  [${propsText(c.properties)}]")
                }
            }

            // On préfère les services série connus des dongles ELM327 BLE.
            val preferred = listOf("18f0", "fff0", "ffe0")
            val services = g.services.filter { s ->
                val id = s.uuid.toString().substring(4, 8).lowercase(Locale.ROOT)
                id != "1800" && id != "1801" && id != "180a"
            }.sortedBy { s ->
                val idx = preferred.indexOf(s.uuid.toString().substring(4, 8).lowercase(Locale.ROOT))
                if (idx < 0) 99 else idx
            }

            var notifyC: BluetoothGattCharacteristic? = null
            var writeC: BluetoothGattCharacteristic? = null
            for (s in services) {
                val n = s.characteristics.firstOrNull {
                    has(it.properties, BluetoothGattCharacteristic.PROPERTY_NOTIFY) ||
                        has(it.properties, BluetoothGattCharacteristic.PROPERTY_INDICATE)
                }
                val w = s.characteristics.firstOrNull {
                    has(it.properties, BluetoothGattCharacteristic.PROPERTY_WRITE) ||
                        has(it.properties, BluetoothGattCharacteristic.PROPERTY_WRITE_NO_RESPONSE)
                }
                if (n != null && w != null) {
                    notifyC = n
                    writeC = w
                    break
                }
            }
            if (notifyC == null || writeC == null) {
                log("ERREUR : aucun service série (notification + écriture) trouvé.")
                status("Service série introuvable")
                return
            }
            log("Choisi : écriture ${writeC.uuid}, notification ${notifyC.uuid}")
            elm.gatt = g
            elm.writeChar = writeC
            g.setCharacteristicNotification(notifyC, true)
            val cccd = notifyC.getDescriptor(CCCD_UUID)
            if (cccd == null) {
                log("Pas de descripteur de notification, on continue quand même.")
                thread(name = "init") { initElm() }
                return
            }
            cccd.value = if (has(notifyC.properties, BluetoothGattCharacteristic.PROPERTY_NOTIFY)) {
                BluetoothGattDescriptor.ENABLE_NOTIFICATION_VALUE
            } else {
                BluetoothGattDescriptor.ENABLE_INDICATION_VALUE
            }
            g.writeDescriptor(cccd)
        }

        override fun onDescriptorWrite(g: BluetoothGatt, descriptor: BluetoothGattDescriptor, st: Int) {
            log("Notifications activées (code $st)")
            thread(name = "init") { initElm() }
        }

        // Android 13 et plus
        override fun onCharacteristicChanged(
            g: BluetoothGatt,
            characteristic: BluetoothGattCharacteristic,
            value: ByteArray
        ) {
            elm.onData(value)
        }

        // Android 12 et moins
        @Deprecated("Deprecated in Java")
        override fun onCharacteristicChanged(g: BluetoothGatt, characteristic: BluetoothGattCharacteristic) {
            if (Build.VERSION.SDK_INT < 33) {
                val v = characteristic.value
                if (v != null) elm.onData(v)
            }
        }
    }

    // --------------------------------------------------------------- ELM327

    /** v0.29 : une réponse est-elle en échec (écriture refusée ou délai
     * dépassé) ? Avant, ces échecs passaient inaperçus et l'app affichait
     * « Initialisation terminée » alors que le dongle était muet. */
    private fun elmFailed(r: String): Boolean =
        r.startsWith("ERREUR") || r.contains("[délai dépassé]")

    private fun initElm(retried: Boolean = false) {
        try {
            status("Initialisation du dongle...")
            var failed = 0
            for (cmd in listOf("ATZ", "ATE0", "ATL0", "ATS0", "ATH0", "ATSP0")) {
                val r = elm.request(cmd, if (cmd == "ATZ") 5000L else 3000L)
                log("> $cmd\n$r")
                if (elmFailed(r)) failed++
            }
            var r = elm.request("ATRV", 3000)
            log("> ATRV\n$r")
            if (elmFailed(r)) failed++
            r = elm.request("0100", 12000)
            log("> 0100 (détection du protocole, peut durer quelques secondes)\n$r")
            if (elmFailed(r)) failed++
            r = elm.request("ATDP", 3000)
            log("> ATDP\n$r")
            if (elmFailed(r)) failed++
            if (failed > 0 && !retried) {
                // v0.29 : une seule seconde tentative complète - le refus
                // d'écriture du vLinker arrive souvent juste après le branchement
                // ou une reconnexion, puis disparaît.
                log("Initialisation : $failed commande(s) en échec, nouvelle tentative dans 1 s...")
                Thread.sleep(1000)
                initElm(true)
                return
            }
            ready = true
            // v0.12 : la lecture live démarre ou REdémarre dès que le dongle est prêt,
            // même si l'interrupteur était déjà sur ON (cas de la reconnexion après
            // une déconnexion : avant, rien ne relançait la lecture).
            if (liveSwitch.isChecked) setLive(true)
            else handler.post { liveSwitch.isChecked = true }
            if (failed == 0) {
                status("Prêt - dongle connecté")
                log("Initialisation terminée.")
                // v0.46 : SOH lu AUTOMATIQUEMENT à la connexion (le bouton
                // « SOH batterie… » reste disponible pour relire à la main).
                if (sohPct < 0) readSoh()
            } else {
                // v0.29 : plus de faux « Initialisation terminée » si des
                // commandes ont échoué même après la seconde tentative.
                ready = false
                status("Initialisation en échec")
                log("Initialisation en échec ($failed commande(s) sans réponse) : touchez à nouveau « Scanner et connecter ».")
            }
        } catch (e: Exception) {
            log("Erreur d'initialisation : ${e.message}")
        }
    }

    private fun hexAfter(resp: String, prefix: String, bytes: Int): List<Int>? {
        val s = resp.replace(" ", "").replace("\n", "").uppercase(Locale.ROOT)
        val i = s.indexOf(prefix)
        if (i < 0) return null
        val start = i + prefix.length
        if (s.length < start + 2 * bytes) return null
        return try {
            (0 until bytes).map { s.substring(start + 2 * it, start + 2 * it + 2).toInt(16) }
        } catch (e: NumberFormatException) {
            null
        }
    }

    private fun setLive(on: Boolean) {
        liveOn = on
        if (!on) return
        if (liveThread?.isAlive == true) return
        log("Lecture live démarrée.")
        startLiveThread()
    }

    /** Lance le fil de lecture live (relançable par le watchdog). */
    private fun startLiveThread() {
        // v0.11 : numéro de génération - un redémarrage par le watchdog fait
        // sortir proprement l'ancien fil de sa boucle (plus de fils en double).
        val myGen = ++liveGen
        liveThread = thread(name = "live") {
            var noData = 0
            while (liveOn && myGen == liveGen) {
                try {
                    if (ready && needElmReinit) {
                        // v0.12 : auto-réparation - si la voiture ne répond plus, on
                        // réinitialise le dongle (ATZ...) puis on relance la détection.
                        needElmReinit = false
                        log("Réinitialisation du dongle ELM327...")
                        for (cmd in listOf("ATZ", "ATE0", "ATL0", "ATS0", "ATH0", "ATSP0")) {
                            elm.request(cmd, if (cmd == "ATZ") 5000L else 3000L)
                        }
                        elm.request("0100", 12000)
                        lastLiveTick = System.currentTimeMillis()
                    }
                    if (ready) {
                        val s = elm.request("010D", 2500)
                        val b = hexAfter(s, "410D", 1)
                        // v0.11 : le "tick" du watchdog n'est rafraîchi QUE si la
                        // voiture répond vraiment (avant, il l'était à chaque tour,
                        // même sans réponse, donc le watchdog ne se déclenchait jamais).
                        if (s.contains("41")) {
                            lastLiveTick = System.currentTimeMillis()
                            noData = 0
                        } else if (++noData == 10) {
                            log("OBD sans réponse : 010D → \"$s\"")
                        }
                        obdSpeed = if (b != null) "${b[0]} km/h" else "pas de réponse ($s)"
                        volt = elm.request("ATRV", 2500)
                        val s5 = hexAfter(elm.request("015B", 2500), "415B", 1)
                        if (s5 != null) {
                            last5bPct = s5[0] * 100.0 / 255.0
                            socPct = last5bPct * socFactor
                            soc = "%.1f".format(socPct) + " %" +
                                (if (Math.abs(socFactor - 1.0) > 0.01)
                                    " (brut " + "%.1f".format(last5bPct) + " %)" else "")
                            if (Math.abs(socPct - lastLoggedSoc) >= 1.0) {
                                lastLoggedSoc = socPct
                                log("Charge : " + "%.1f".format(socPct) + " % (5B brut " +
                                    "%.1f".format(last5bPct) + " %)")
                            }
                            // v0.46 : détection des recharges DC - le SOC monte
                            // vite (> 0,8 %/min ; une AC 7 kW reste sous
                            // ~0,2 %/min sur 61 kWh).
                            trackDcCharge(socPct)
                        } else {
                            soc = "pas de réponse"
                        }
                        val so = hexAfter(elm.request("01A6", 2500), "41A6", 4)
                        odo = if (so != null) {
                            val raw = (so[0].toLong() shl 24) or (so[1].toLong() shl 16) or
                                (so[2].toLong() shl 8) or so[3].toLong()
                            "%.1f".format(raw / 10.0) + " km"
                        } else {
                            "pas de réponse"
                        }
                        val s42 = hexAfter(elm.request("0142", 2500), "4142", 2)
                        v42 = if (s42 != null) {
                            "%.2f".format((s42[0] * 256 + s42[1]) / 1000.0) + " V"
                        } else {
                            "pas de réponse"
                        }
                        // Apprentissage continu (v0.7.2) : réapprend la consommation tous les 2 km.
                        if (socPct >= 0.0) {
                            if (learnSoc < 0.0) {
                                learnSoc = socPct
                                learnKm = tripKm
                            } else {
                                val dKm = tripKm - learnKm
                                if (dKm >= 2.0) {
                                    val sample = (learnSoc - socPct) / dKm
                                    if (sample > 0.02 && sample < 2.0) {
                                        val old = consoPctPerKm
                                        consoPctPerKm = 0.75 * consoPctPerKm + 0.25 * sample
                                        log("Conso réappris en roulant : " + "%.3f".format(old) + " → " +
                                            "%.3f".format(consoPctPerKm) + " %/km (sur " +
                                            "%.1f".format(dKm) + " km)")
                                        persistConso()
                                    }
                                    learnSoc = socPct
                                    learnKm = tripKm
                                }
                            }
                        }
                        refreshLive()
                        if (stageReached()) finishStage(false)
                        if (socPct >= 0.0 && socPct <= 15.0 && !lowWarned) {
                            lowWarned = true
                            warnLow()
                        }
                        if (socPct > 16.0) lowWarned = false
                        refreshRoute()
                        refreshOverlay()
                    }
                    Thread.sleep(700)
                } catch (e: Exception) {
                    log("Lecture live : ${e.message}")
                    Thread.sleep(1500)
                }
            }
        }
    }

    private fun testsBase() {
        if (!ready) {
            log("Dongle pas prêt : connectez-vous d'abord.")
            return
        }
        thread(name = "tests") {
            val cmds = listOf(
                "ATI", "AT@1", "ATRV", "ATDP",
                "0100", "0120", "0140", "0160", "0180", "01A0", "01C0",
                "0101", "0902", "015C"
            )
            for (c in cmds) {
                log("> $c\n" + elm.request(c, 8000))
            }
            log("Tests de base terminés.")
        }
    }

    /** v0.37 : SOH (santé) de la batterie via le PID UDS 22B061 - celui
     * qu'utilise ABRP sur MG4 (identifié sur MG ZS/MG5 puis confirmé par la
     * communauté MG4). On interroge le calculateur batterie en adressage
     * physique (7E4, réponse 7EC - repli 7E6/7EE), puis on RESTAURE
     * l'adressage fonctionnel normal (7DF) pour ne pas casser la lecture
     * live. Valeur = 2 octets / 100 (ex : 0x2710 = 10000 -> 100,0 %). */
    private fun readSoh() {
        if (!ready) {
            log("Dongle pas prêt : connectez-vous d'abord.")
            return
        }
        thread(name = "soh") {
            var found = false
            // v0.39 : la vraie combinaison MG4 (dépôt officiel OBDb/MG-MG4) :
            // la requête 22B061 part sur l'adressage FONCTIONNEL 7DF et le
            // BMS répond sur 7ED (pas 7E4 comme sur les ZS/MG5 - c'est ce qui
            // donnait « NO DATA »). On garde 7E4/7E6 en repli au cas où.
            for ((req, resp) in listOf("7DF" to "7ED", "7E4" to "7EC", "7E6" to "7EE")) {
                log("SOH : interrogation du calculateur batterie (" + req + ")...")
                elm.request("ATSH " + req, 3000)
                elm.request("ATCRA " + resp, 3000)
                val r = elm.request("22B061", 6000)
                log("> 22B061 (" + req + ")\n" + r)
                // Restauration de l'adressage normal AVANT d'analyser,
                // même si la réponse est illisible.
                elm.request("ATCRA", 3000)
                elm.request("ATSH 7DF", 3000)
                val m = Regex("62B061([0-9A-Fa-f]{4})")
                    .find(r.replace(" ", "").uppercase(Locale.ROOT))
                if (m != null) {
                    val v = Integer.parseInt(m.groupValues[1], 16) / 100.0
                    if (v > 40.0 && v <= 105.0) {
                        val degr = 100.0 - v
                        log("SOH batterie : " + String.format(Locale.US, "%.1f", v) +
                            " % (dégradation estimée : " +
                            String.format(Locale.US, "%.1f", degr) + " %).")
                        // v0.38 : mémorisé pour la fenêtre flottante.
                        sohPct = v
                        refreshOverlay()
                        alert("Santé de la batterie (SOH)",
                            "SOH : " + String.format(Locale.US, "%.1f", v) + " %\n" +
                                "Dégradation estimée : " +
                                String.format(Locale.US, "%.1f", degr) + " %\n\n" +
                                "(PID 22B061, même valeur qu'ABRP : estimation du BMS, " +
                                "pas un test de capacité en laboratoire.)")
                        found = true
                        break
                    }
                }
            }
            if (!found) {
                log("SOH : aucune réponse exploitable du calculateur batterie (22B061).")
                alert("SOH introuvable",
                    "Le calculateur batterie n'a pas répondu au PID 22B061.\n\n" +
                        "Réessayez contact mis (bouton Start sans appuyer sur la pédale), " +
                        "voiture non branchée.")
            }
        }
    }

    private fun testsBatterie() {
        if (!ready) {
            log("Dongle pas prêt : connectez-vous d'abord.")
            return
        }
        thread(name = "tests2") {
            log("> ATH1 (affiche l'adresse de chaque calculateur)\n" + elm.request("ATH1", 3000))
            val cmds = listOf(
                "0100", "015B", "015C", "01A6", "0142", "0146", "0149",
                "0105", "0104", "010C", "010D"
            )
            for (c in cmds) {
                log("> $c\n" + elm.request(c, 8000))
            }
            log("> ATH0\n" + elm.request("ATH0", 3000))
            log("Tests batterie terminés.")
        }
    }

    private fun sendManual() {
        val c = cmdEt.text.toString().trim().uppercase(Locale.ROOT)
        if (c.isEmpty()) return
        cmdEt.setText("")
        thread(name = "cmd") {
            log("> $c\n" + elm.request(c, 8000))
        }
    }

    // ------------------------------------------------------- Itinéraire

    /**
     * Analyse une ligne d'itinéraire (v0.7.2) :
     * - "Nom;km" ou "Nom : km" (recommandé, le nom peut être une adresse complète) ;
     * - "Nom 145 km" accepté seulement si le nom ne contient aucun chiffre
     *   (pour éviter de confondre un numéro de rue ou un code postal avec une distance).
     */
    private fun parseStage(line: String): Stage? {
        val t = line.trim()
        if (t.isEmpty()) return null
        val sep = Regex("^(.+?)[;:]\\s*([0-9]+(?:[.,][0-9]+)?)\\s*(km)?\\s*$").find(t)
        if (sep != null) {
            val n = sep.groupValues[1].trim().trimEnd(';', ':', ',')
            val k = sep.groupValues[2].replace(',', '.').toDoubleOrNull() ?: return null
            if (n.isNotEmpty() && k > 0) return Stage(n, k)
        }
        val m = Regex("^(\\D*?)\\s+([0-9]+(?:[.,][0-9]+)?)\\s*(km)\\s*$").find(t)
        if (m != null) {
            val n = m.groupValues[1].trim().trimEnd(';', ':', ',')
            val k = m.groupValues[2].replace(',', '.').toDoubleOrNull() ?: return null
            if (n.isNotEmpty() && k > 0) return Stage(n, k)
        }
        return null
    }

    private fun editStages() {
        val input = EditText(this)
        input.hint = "Une étape par ligne.\nAvec distance : Reims;145\nSans distance (Internet) :\n3 le haut fief 44190 Gorges\n(ville, adresse complète... l'app calcule les km)"
        input.setSingleLine(false)
        input.minLines = 6
        input.gravity = Gravity.TOP
        input.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE
        input.setText(stages.joinToString("\n") { it.name + ";" + fmtKm(it.km) })
        AlertDialog.Builder(this)
            .setTitle("Définir l'itinéraire")
            .setView(input)
            .setPositiveButton("OK") { _, _ -> buildStages(input.text.toString()) }
            .setNegativeButton("Annuler", null)
            .show()
    }

    private fun fmtKm(km: Double): String =
        if (km % 1.0 == 0.0) "%.0f".format(km) else "%.1f".format(km)

    /**
     * Construit l'itinéraire depuis le texte saisi (v0.8).
     * Lignes avec distance (« Nom;km ») : utilisées telles quelles.
     * Lignes sans distance : géocodées via OpenStreetMap (Nominatim),
     * distance = vol d'oiseau depuis l'étape précédente (ou la position actuelle) × 1,2.
     */
    private fun buildStages(raw: String) {
        val lines = raw.lines().map { it.trim() }.filter { it.isNotEmpty() }
        if (lines.isEmpty()) return
        val explicit = lines.map { parseStage(it) }
        if (explicit.all { it != null }) {
            applyStages(explicit.filterNotNull(), emptyList())
            return
        }
        status("Géocodage des adresses (Internet)...")
        log("Géocodage de " + lines.size + " ligne(s) via OpenStreetMap...")
        thread(name = "geocode") {
            class Pending(val line: String, val explicit: Stage?, val geo: Geo?)
            val pend = ArrayList<Pending>()
            val fails = ArrayList<String>()
            for (line in lines) {
                val st = parseStage(line)
                if (st != null) {
                    pend.add(Pending(line, st, null))
                    continue
                }
                val gf = geocodeFull(line)
                if (gf == null) {
                    fails.add(line)
                    log("Adresse introuvable : " + line)
                } else {
                    pend.add(Pending(line, null, gf.first))
                    log("« " + line + " » localisé → " +
                        String.format(Locale.US, "%.3f, %.3f", gf.first.lat, gf.first.lon) +
                        " (" + gf.second + ")")
                }
                Thread.sleep(1100) // règle Nominatim : 1 requête/seconde maximum
            }
            // Distances routières réelles (v0.9), depuis la position actuelle
            // pour la première étape, sinon depuis l'étape géocodée précédente.
            // v0.15 : la position n'est utilisée que si elle est récente (moins de
            // 10 min) - une ancienne position pouvait donner une distance de 0 km.
            val here = lastLoc ?: bestLoc()
            val fresh = here != null && here.time > 0L &&
                System.currentTimeMillis() - here.time < 10L * 60 * 1000
            val start = if (fresh) Geo(here!!.latitude, here!!.longitude) else null
            val result = ArrayList<Stage>()
            var prev: Geo? = null
            for (p in pend) {
                if (p.explicit != null) {
                    result.add(p.explicit)
                    continue
                }
                val g = p.geo ?: continue
                val origin = prev ?: start
                val km = if (origin == null) 0.0 else roadKm(origin, g)
                result.add(Stage(p.line, km, g.lat, g.lon))
                // v0.35 : plus de faux « distance routière réelle » à 0 km -
                // sans position, la distance sera recalculée au départ du
                // trajet dès que le GPS accroche (v0.15/v0.28).
                if (origin == null) {
                    log("« " + p.line + " » : distance inconnue pour l'instant " +
                        "(position pas encore fixée : recalcul au départ du trajet).")
                } else {
                    log("« " + p.line + " » : " + fmtKm(km) + " km (distance routière réelle)")
                }
                prev = g
            }
            handler.post { applyStages(result, fails) }
        }
    }

    /**
     * Distance routière réelle entre deux points via OSRM (OpenStreetMap,
     * gratuit, sans clé). Repli : vol d'oiseau × 1,25 si le service ne répond pas.
     */
    /**
     * v0.28 : distance routière OSRM « réelle » - null si le service ne
     * répond pas après 2 tentatives. Les appels critiques (recalcul au
     * départ, reste à parcourir) n'écrasent jamais une valeur réelle par
     * une estimation à vol d'oiseau.
     */
    private fun tryRoadKm(a: Geo, b: Geo): Double? {
        var lastErr = "pas de réponse"
        for (essai in 1..2) {
            try {
                val url = "https://router.project-osrm.org/route/v1/driving/" +
                    fmtD(a.lon) + "," + fmtD(a.lat) + ";" + fmtD(b.lon) + "," + fmtD(b.lat) +
                    "?overview=false"
                val json = httpGet(url, 12000)
                val m = Regex("\"distance\"\\s*:\\s*([0-9]+(?:\\.[0-9]+)?)").find(json)
                if (m != null) return m.groupValues[1].toDouble() / 1000.0
                lastErr = "réponse illisible"
            } catch (e: Exception) {
                lastErr = e.message ?: "erreur"
            }
            if (essai == 1) Thread.sleep(1000)
        }
        log("OSRM indisponible (" + lastErr + ") : estimation à vol d'oiseau.")
        return null
    }

    /** Distance routière (OSRM) ; repli : vol d'oiseau × 1,35 si le service
     * ne répond pas (les routes réelles font 20 à 50 % de plus que la
     * ligne droite). */
    private fun roadKm(a: Geo, b: Geo): Double =
        tryRoadKm(a, b) ?: distKm(a.lat, a.lon, b.lat, b.lon) * 1.35

    private fun applyStages(list: List<Stage>, fails: List<String>) {
        stages.clear()
        stages.addAll(list)
        tripActive = false
        stageIdx = 0
        // v0.36 : le reste-à-parcourir du TRAJET PRÉCÉDENT ne doit pas
        // survivre au nouvel itinéraire - sinon (reste 0,7 km d'un ancien
        // trajet) la nouvelle étape était validée instantanément (« atteinte :
        // 0,0 km parcourus »).
        remainKm = -1.0
        log("Itinéraire : " + stages.size + " étape(s), total " +
            fmtKm(stages.sumOf { it.km }) + " km" +
            (if (fails.isNotEmpty()) " (" + fails.size + " adresse(s) ignorée(s))" else ""))
        refreshRoute()
        status("Itinéraire : " + stages.size + " étape(s)")
        if (fails.isNotEmpty()) {
            alert(
                "Adresses introuvables (" + fails.size + ")",
                "Ces lignes n'ont pas été localisées et sont ignorées :\n\n" +
                    fails.joinToString("\n") +
                    "\n\nVérifie l'orthographe, ou ajoute la ville / le code postal."
            )
        }
    }

    /** Géocodage d'une adresse via Nominatim (OpenStreetMap, gratuit). */
    /**
     * Géocodage Nominatim (v0.16) : limité à France/Espagne/Portugal - une
     * recherche libre pouvait renvoyer un homonyme au mauvais endroit
     * (« gorges » -> Gorges en Somme, près d'Amiens, au lieu de la
     * Loire-Atlantique). Renvoie le lieu ET son nom complet Nominatim
     * pour confirmation visuelle avant d'ouvrir la carte.
     */
    private fun geocodeFull(addr: String): Pair<Geo, String>? {
        return try {
            val url = "https://nominatim.openstreetmap.org/search?format=json&limit=1" +
                "&countrycodes=fr,es,pt&addressdetails=0&q=" + URLEncoder.encode(addr, "UTF-8")
            val json = httpGet(url, 15000)
            val lat = Regex("\"lat\"\\s*:\\s*\"(-?[0-9.]+)\"").find(json)?.groupValues?.get(1)
                ?: return null
            val lon = Regex("\"lon\"\\s*:\\s*\"(-?[0-9.]+)\"").find(json)?.groupValues?.get(1)
                ?: return null
            val nom = Regex("\"display_name\"\\s*:\\s*\"([^\"]*)\"")
                .find(json)?.groupValues?.get(1) ?: addr
            Pair(Geo(lat.toDouble(), lon.toDouble()), nom)
        } catch (e: Exception) {
            log("Géocodage de « " + addr + " » : " + e.message)
            null
        }
    }

    private fun geocode(addr: String): Geo? = geocodeFull(addr)?.first

    /** Distance à vol d'oiseau en km. */
    private fun distKm(lat1: Double, lon1: Double, lat2: Double, lon2: Double): Double {
        val r = 6371.0
        val dLat = Math.toRadians(lat2 - lat1)
        val dLon = Math.toRadians(lon2 - lon1)
        val a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
            Math.cos(Math.toRadians(lat1)) * Math.cos(Math.toRadians(lat2)) *
            Math.sin(dLon / 2) * Math.sin(dLon / 2)
        return 2 * r * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a))
    }

    /** Relecture d'un itinéraire sauvegardé : « nom;km;lat;lon ». */
    private fun parseSaved(line: String): Stage? {
        val p = line.split(';')
        if (p.size < 2) return null
        val km = p[1].replace(',', '.').toDoubleOrNull() ?: return null
        val lat = if (p.size >= 3) p[2].replace(',', '.').toDoubleOrNull() ?: 0.0 else 0.0
        val lon = if (p.size >= 4) p[3].replace(',', '.').toDoubleOrNull() ?: 0.0 else 0.0
        return Stage(p[0], km, lat, lon)
    }

    // ------------------------------------------------- Itinéraires favoris

    private fun saveItinerary() {
        if (stages.isEmpty()) {
            log("Aucun itinéraire à sauvegarder : définissez-le d'abord.")
            return
        }
        val input = EditText(this)
        input.hint = "Nom de l'itinéraire"
        AlertDialog.Builder(this)
            .setTitle("Sauvegarder l'itinéraire")
            .setView(input)
            .setPositiveButton("Sauver") { _, _ ->
                val name = input.text.toString().trim()
                if (name.isEmpty()) {
                    log("Nom vide : itinéraire non sauvegardé.")
                    return@setPositiveButton
                }
                val prefs = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
                val data = stages.joinToString("\n") { it.name + ";" + it.km + ";" + it.lat + ";" + it.lon }
                val names = (prefs.getStringSet("names", null) ?: mutableSetOf()).toMutableSet()
                names.add(name)
                prefs.edit()
                    .putString("it:" + name.lowercase(Locale.ROOT), data)
                    .putStringSet("names", names)
                    .apply()
                log("Itinéraire « " + name + " » sauvegardé (" + stages.size + " étapes).")
            }
            .setNegativeButton("Annuler", null)
            .show()
    }

    private fun loadItinerary() {
        val prefs = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
        val names = ((prefs.getStringSet("names", null) ?: mutableSetOf())).sorted()
        if (names.isEmpty()) {
            log("Aucun itinéraire sauvegardé pour l'instant.")
            return
        }
        AlertDialog.Builder(this)
            .setTitle("Charger un itinéraire")
            .setItems(names.toTypedArray()) { _, i ->
                val data = prefs.getString("it:" + names[i].lowercase(Locale.ROOT), null)
                if (data != null) {
                    stages.clear()
                    for (line in data.lines()) {
                        val st = parseSaved(line)
                        if (st != null) stages.add(st)
                    }
                    tripActive = false
                    stageIdx = 0
                    remainKm = -1.0 // v0.36 : reste obsolète de l'ancien trajet
                    log("Itinéraire « " + names[i] + " » chargé (" + stages.size + " étapes, total " +
                        "%.0f".format(stages.sumOf { it.km }) + " km).")
                    refreshRoute()
                } else {
                    log("Itinéraire « " + names[i] + " illisible.")
                }
            }
            .setNegativeButton("Annuler", null)
            .show()
    }

    /** Mémorise la consommation apprise/calibrée. */
    private fun persistConso() {
        getSharedPreferences("mg4link", Context.MODE_PRIVATE).edit()
            .putFloat("conso", consoPctPerKm.toFloat())
            .apply()
        // v0.36 : copie silencieuse dans Download/MG4Link - les préférences
        // internes sont EFFACÉES à chaque désinstallation (APK non signé =
        // désinstallation obligatoire), l'expérience acquise était donc
        // perdue à chaque mise à jour. Ce fichier, lui, survit.
        try {
            if (android.os.Environment.isExternalStorageManager()) {
                val dir = publicDir()
                dir.mkdirs()
                File(dir, "conso.txt").writeText("%.4f".format(consoPctPerKm))
            }
        } catch (e: Exception) { }
    }

    /** v0.46 : suit la montée du SOC pour compter les recharges DC.
     * Une AC 7 kW fait monter le SOC d'au maximum ~0,2 %/min ; au-delà de
     * 0,8 %/min, c'est de la DC. La session est considérée terminée quand
     * le SOC n'a plus bougé depuis 5 minutes. Le compteur est affiché dans
     * le journal et survit aux désinstallations (Download/MG4Link). */
    private fun trackDcCharge(soc: Double) {
        val now = System.currentTimeMillis()
        if (dcLastT > 0L && soc > dcLastSoc + 0.05) {
            val mins = (now - dcLastT) / 60000.0
            if (mins > 0.05) {
                val rate = (soc - dcLastSoc) / mins
                dcRate = 0.7 * dcRate + 0.3 * rate
                if (dcSoc0 < 0.0 && dcRate > 0.8) {
                    dcSoc0 = dcLastSoc
                    dcT0 = dcLastT
                    dcLastUp = now
                    log("Recharge DC détectée (montée " + "%.1f".format(dcRate) + " %/min)…")
                }
            }
        }
        if (dcSoc0 >= 0.0) {
            if (soc > dcLastSoc + 0.05) dcLastUp = now
            if (now - dcLastUp > 5L * 60000L) {
                dcCount++
                val mins = (dcLastUp - dcT0) / 60000.0
                log("Recharge DC n°" + dcCount + " terminée : +" +
                    "%.0f".format(soc - dcSoc0) + " % en " +
                    "%.0f".format(mins) + " min.")
                persistDc()
                dcSoc0 = -1.0
                dcRate = 0.0
            }
        }
        dcLastSoc = soc
        dcLastT = now
    }

    /** v0.46 : le compteur DC survit aux désinstallations (comme conso.txt). */
    private fun persistDc() {
        getSharedPreferences("mg4link", Context.MODE_PRIVATE).edit()
            .putInt("dccount", dcCount).apply()
        try {
            if (android.os.Environment.isExternalStorageManager()) {
                val dir = publicDir()
                dir.mkdirs()
                File(dir, "dccount.txt").writeText(dcCount.toString())
            }
        } catch (e: Exception) { }
    }

    /** v0.46 : relit le compteur DC (préférences, puis Download/MG4Link). */
    private fun restoreDc() {
        val sp = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
        dcCount = sp.getInt("dccount", 0)
        if (dcCount > 0) {
            log("Compteur de recharges DC : " + dcCount + ".")
            return
        }
        val v = loadPublicCache("dccount.txt")?.trim()?.toIntOrNull() ?: return
        if (v in 1..9999) {
            dcCount = v
            log("Compteur de recharges DC récupéré depuis Download/MG4Link : " + v + ".")
            persistDc()
        }
    }

    /** v0.36 : après une réinstallation, relit la conso sauvegardée dans
     * Download/MG4Link (préférences internes vides). */
    private fun restoreConsoPublic() {
        try {
            val sp = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
            if (sp.getFloat("conso", 0f) > 0f) return
            val v = loadPublicCache("conso.txt")?.trim()
                ?.replace(',', '.')?.toDoubleOrNull() ?: return
            if (v > 0.05 && v < 2.0) {
                consoPctPerKm = v
                log("Calibrage récupéré depuis Download/MG4Link : " +
                    "%.3f".format(v) + " %/km (autonomie à 100 % : " +
                    "%.0f".format(100.0 / v) + " km)")
                persistConso()
            }
        } catch (e: Exception) { }
    }

    /** Calibrage manuel : autonomie réelle à 100 % → consommation %/km (v0.7.2). */
    private fun calibrate() {
        val input = EditText(this)
        input.hint = "Autonomie réelle à 100 % (km), ex. 380"
        input.inputType = InputType.TYPE_CLASS_NUMBER or InputType.TYPE_NUMBER_FLAG_DECIMAL
        input.setText("%.0f".format(100.0 / consoPctPerKm))
        AlertDialog.Builder(this)
            .setTitle("Calibrage de l'autonomie")
            .setMessage(
                "Indique l'autonomie que la voiture affiche batterie pleine (100 %).\n" +
                    "L'app en déduit la consommation en %/km, la mémorise et repartira dessus au démarrage."
            )
            .setView(input)
            .setPositiveButton("OK") { _, _ ->
                val km = input.text.toString().replace(',', '.').toDoubleOrNull()
                if (km == null || km < 150.0 || km > 800.0) {
                    alert("Calibrage", "Valeur invalide : entrez un nombre entre 150 et 800 km.")
                    return@setPositiveButton
                }
                consoPctPerKm = 100.0 / km
                learnSoc = -1.0
                persistConso()
                log("Calibrage : autonomie 100 % = " + "%.0f".format(km) + " km → " +
                    "%.3f".format(consoPctPerKm) + " %/km (mémorisé).")
                refreshRoute()
                refreshLive()
            }
            .setNegativeButton("Annuler", null)
            .show()
    }

    /**
     * Charge affichée par le tableau de bord (v0.9). Le PID 5B n'est pas
     * toujours fiable sur MG4 : cette saisie corrige la charge utilisée pour
     * les prédictions et apprend le facteur de correction 5B → affiché.
     */
    private fun askSoc() {
        val input = EditText(this)
        input.hint = "Pourcentage affiché par la voiture, ex. 58"
        input.inputType = InputType.TYPE_CLASS_NUMBER or InputType.TYPE_NUMBER_FLAG_DECIMAL
        AlertDialog.Builder(this)
            .setTitle("Charge tableau de bord")
            .setMessage(
                "Entre le pourcentage de batterie affiché par la voiture maintenant.\n" +
                    "L'app s'en sert pour les prédictions (la lecture OBD 5B est parfois " +
                    "fausse sur MG4) et apprend la correction à appliquer au 5B."
            )
            .setView(input)
            .setPositiveButton("OK") { _, _ ->
                val pct = input.text.toString().replace(',', '.').toDoubleOrNull()
                if (pct == null || pct < 1.0 || pct > 100.0) {
                    alert("Charge", "Valeur invalide : entre 1 et 100.")
                    return@setPositiveButton
                }
                socPct = pct
                soc = "%.1f".format(pct) + " % (tableau de bord)"
                lastLoggedSoc = pct
                learnSoc = pct
                learnKm = tripKm
                if (last5bPct > 0.0) {
                    val f = pct / last5bPct
                    if (f in 0.5..1.5) {
                        socFactor = 0.7 * socFactor + 0.3 * f
                        getSharedPreferences("mg4link", Context.MODE_PRIVATE).edit()
                            .putFloat("socFactor", socFactor.toFloat())
                            .apply()
                        log("Charge tableau de bord : " + "%.1f".format(pct) +
                            " % (5B brut " + "%.1f".format(last5bPct) +
                            " %) → facteur de correction ×" + "%.3f".format(socFactor) + " (mémorisé).")
                    } else {
                        log("Charge tableau de bord : " + "%.1f".format(pct) +
                            " % (5B brut " + "%.1f".format(last5bPct) +
                            " %) : écart trop grand pour corriger automatiquement.")
                    }
                } else {
                    log("Charge tableau de bord : " + "%.1f".format(pct) + " % (pas de lecture 5B).")
                }
                refreshLive()
                refreshRoute()
                refreshOverlay()
            }
            .setNegativeButton("Annuler", null)
            .show()
    }

    private fun startTrip() {
        if (stages.isEmpty()) {
            log("Définissez d'abord un itinéraire avec le bouton « Itinéraire… ».")
            return
        }
        if (tripActive) {
            tripActive = false
            log("Trajet interrompu.")
            refreshRoute()
            return
        }
        tripActive = true
        stageIdx = 0
        stageStartKm = tripKm
        stageStartSoc = socPct
        lowWarned = false
        // v0.15 : recalcul de la distance de la première étape au départ du
        // trajet, si la position n'était pas encore connue (km à 0) au moment
        // de la construction de l'itinéraire.
        val st0 = stages[stageIdx]
        if (st0.hasPos) {
            val here = lastLoc ?: bestLoc()
            val fresh = here != null && here.time > 0L &&
                System.currentTimeMillis() - here.time < 10L * 60 * 1000
            if (fresh) {
                // v0.28 : on ne remplace la distance que par une valeur
                // routière RÉELLE - avant, une estimation à vol d'oiseau
                // (4,5 km) écrasait la vraie distance routière (6,8 km)
                // et l'étape se terminait trop tôt.
                val d = tryRoadKm(Geo(here!!.latitude, here!!.longitude), Geo(st0.lat, st0.lon))
                if (d != null && d > 0.1 &&
                    (st0.km <= 0.1 || Math.abs(d - st0.km) > 1.0)) {
                    stages[stageIdx] = Stage(st0.name, d, st0.lat, st0.lon)
                    log("Distance routière recalculée : « " + st0.name + " » à " +
                        fmtKm(d) + " km.")
                } else if (d == null && st0.km <= 0.1) {
                    log("OSRM indisponible : distance conservée, arrivée détectée par le GPS.")
                }
            } else if (st0.km <= 0.1) {
                log("Position GPS pas encore fixée : distance recalculée en roulant.")
            }
        }
        log("Trajet démarré : prochaine étape « " + stages[0].name + " » à " +
            "%.0f".format(stages[0].km) + " km.")
        refreshRoute()
    }

    private fun nextStage() {
        if (!tripActive) {
            log("Aucun trajet en cours : touchez « Démarrer le trajet ».")
            return
        }
        if (stageIdx < stages.size) finishStage(true)
    }

    /**
     * v0.28 : l'étape est-elle atteinte ? Pour une étape localisée, on est
     * arrivé quand on est physiquement PROCHE de la destination (à 350 m à
     * vol d'oiseau) ou que le reste routier réel est ≤ 1 km - pas seulement
     * quand les km parcourus dépassent la distance planifiée (sous-estimée
     * si OSRM était en panne au départ). Étape sans position : odomètre GPS.
     */
    private fun stageReached(): Boolean {
        if (!tripActive || stageIdx >= stages.size) return false
        val s = stages[stageIdx]
        val loc = lastLoc
        return if (s.hasPos && loc != null) {
            val d = FloatArray(1)
            Location.distanceBetween(loc.latitude, loc.longitude, s.lat, s.lon, d)
            d[0] <= 350.0 || (remainKm >= 0.0 && remainKm <= 1.0)
        } else {
            (tripKm - stageStartKm) >= s.km
        }
    }

    @Synchronized
    private fun finishStage(manual: Boolean) {
        if (!tripActive || stageIdx >= stages.size) return
        val s = stages[stageIdx]
        val driven = tripKm - stageStartKm
        val sc = socPct
        if (sc >= 0 && stageStartSoc >= 0 && driven > 0.5) {
            val sample = (stageStartSoc - sc) / driven
            if (sample > 0.02 && sample < 2.0) {
                consoPctPerKm = 0.7 * consoPctPerKm + 0.3 * sample
                log("Consommation mesurée : " + "%.3f".format(consoPctPerKm) +
                    " %/km (sur " + "%.1f".format(driven) + " km)")
            }
        }
        log("Étape « " + s.name + " » " + (if (manual) "validée" else "atteinte") +
            " : " + "%.1f".format(driven) + " km parcourus, charge " +
            (if (sc >= 0) "%.1f".format(sc) + " %" else "inconnue"))
        stageIdx++
        stageStartKm = tripKm
        stageStartSoc = sc
        remainKm = -1.0 // v0.36 : sera recalculé pour la prochaine étape
        if (stageIdx >= stages.size) {
            tripActive = false
            log("Itinéraire terminé !")
            status("Itinéraire terminé")
        }
        refreshRoute()
    }

    private fun warnLow() {
        log("ATTENTION : charge à 15 % ou moins - prévoyez une recharge !")
        status("Charge basse (15 %)")
        handler.post {
            AlertDialog.Builder(this)
                .setTitle("Charge basse")
                .setMessage("La batterie est à " + soc + ". Prévoyez une recharge.")
                .setPositiveButton("Compris", null)
                .show()
        }
    }

    private fun refreshRoute() {
        if (!this::routeTv.isInitialized) return
        val sb = StringBuilder()
        if (stages.isEmpty()) {
            sb.append("Itinéraire non défini - touchez « Itinéraire… »")
        } else {
            sb.append("Conso estimée : ").append("%.2f".format(consoPctPerKm)).append(" %/km\n")
            val sc = socPct
            var cum = 0.0
            for (i in stages.indices) {
                val s = stages[i]
                cum += s.km
                var state = "  "
                if (i < stageIdx) state = "✓"
                if (tripActive && i == stageIdx) state = "→"
                var pred = "?"
                if (sc >= 0) {
                    val p = sc - cum * consoPctPerKm
                    pred = "%.0f".format(p) + " %" + (if (p < 15.0) " !" else "")
                }
                sb.append(state).append(' ').append(i + 1).append(". ").append(s.name)
                    .append(" (").append("%.0f".format(s.km)).append(" km) → ").append(pred).append('\n')
            }
            if (tripActive && stageIdx < stages.size) {
                // v0.13 : priorité au reste recalculé par la route depuis la position
                // actuelle ; repli sur l'estimation initiale si pas encore calculée.
                val remain =
                    if (stages[stageIdx].hasPos && remainKm >= 0.0) remainKm
                    else (stages[stageIdx].km - (tripKm - stageStartKm)).coerceAtLeast(0.0)
                sb.append("Reste " + "%.1f".format(remain) +
                    " km avant " + stages[stageIdx].name)
            }
        }
        val txt = sb.toString()
        handler.post { routeTv.text = txt }
    }

    // ------------------------------------------- Google Maps + fenêtre flottante

    private fun openInMaps() {
        if (stages.isEmpty()) {
            log("Définissez d'abord un itinéraire avec le bouton « Itinéraire… ».")
            return
        }
        try {
            // Une étape géocodée est envoyée par ses coordonnées (plus fiable que le texte).
            fun wp(s: Stage): String =
                if (s.hasPos) "${s.lat},${s.lon}" else URLEncoder.encode(s.name, "UTF-8")
            val dest = wp(stages.last())
            val wps = stages.dropLast(1).take(9).joinToString("%7C") { wp(it) }
            val url = "https://www.google.com/maps/dir/?api=1&destination=" + dest +
                (if (wps.isNotEmpty()) "&waypoints=" + wps else "")
            startActivity(Intent(Intent.ACTION_VIEW, Uri.parse(url)))
            log("Itinéraire envoyé à Google Maps (" + stages.size + " étape(s)).")
        } catch (e: Exception) {
            log("Impossible d'ouvrir Maps : " + e.message)
        }
    }

    private fun toggleOverlay() {
        if (overlayLayout != null) {
            hideOverlay()
            return
        }
        if (!Settings.canDrawOverlays(this)) {
            log("Autorisation manquante : dans les réglages Android, autorisez MG4 Link à " +
                "« s'afficher par-dessus d'autres applications », puis retouchez le bouton.")
            try {
                startActivity(
                    Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION, Uri.parse("package:" + packageName))
                )
            } catch (e: Exception) {
                log("Impossible d'ouvrir les réglages : " + e.message)
            }
            return
        }
        showOverlay()
    }

    private fun showOverlay() {
        val layout = LinearLayout(this)
        layout.orientation = LinearLayout.HORIZONTAL
        layout.setBackgroundColor(Color.argb(215, 15, 60, 25))
        val tv = TextView(this)
        tv.typeface = Typeface.MONOSPACE
        tv.textSize = 16f
        tv.setTextColor(Color.WHITE)
        tv.setPadding(dp(16), dp(12), dp(8), dp(12))
        val close = Button(this)
        close.text = "×"
        close.textSize = 18f
        close.setPadding(dp(8), 0, dp(8), 0)
        close.setOnClickListener { hideOverlay() }
        layout.addView(tv, LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))
        layout.addView(close, LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.MATCH_PARENT))

        val params = WindowManager.LayoutParams(
            WindowManager.LayoutParams.WRAP_CONTENT,
            WindowManager.LayoutParams.WRAP_CONTENT,
            WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE,
            PixelFormat.TRANSLUCENT
        )
        params.gravity = Gravity.TOP or Gravity.START
        params.x = dp(10)
        params.y = dp(120)

        var downX = 0f
        var downY = 0f
        var startX = 0
        var startY = 0
        layout.setOnTouchListener { _, ev ->
            when (ev.action) {
                MotionEvent.ACTION_DOWN -> {
                    downX = ev.rawX
                    downY = ev.rawY
                    startX = params.x
                    startY = params.y
                    false
                }
                MotionEvent.ACTION_MOVE -> {
                    val nx = startX + (ev.rawX - downX).toInt()
                    val ny = startY + (ev.rawY - downY).toInt()
                    if (Math.abs(nx - params.x) > 4 || Math.abs(ny - params.y) > 4) {
                        params.x = nx
                        params.y = ny
                        wm.updateViewLayout(layout, params)
                    }
                    true
                }
                else -> false
            }
        }

        try {
            wm.addView(layout, params)
            overlayLayout = layout
            overlayTv = tv
            log("Fenêtre flottante affichée - glissez-la pour la déplacer, × pour la fermer.")
            refreshOverlay()
        } catch (e: Exception) {
            log("Fenêtre flottante impossible : " + e.message)
        }
    }

    private fun hideOverlay() {
        val l = overlayLayout
        if (l != null) {
            try {
                wm.removeView(l)
            } catch (e: Exception) {
                // rien
            }
            overlayLayout = null
            overlayTv = null
        }
    }

    private fun refreshOverlay() {
        val tv = overlayTv ?: return
        val sc = socPct
        val sb = StringBuilder()
        sb.append("⚡ ").append(if (sc >= 0) "%.1f".format(sc) + " %" else "-- %")
        if (sc >= 0) {
            sb.append('\n').append("autonomie ").append("%.0f".format(sc / consoPctPerKm)).append(" km")
        }
        if (tripActive && stageIdx < stages.size) {
            val s = stages[stageIdx]
            // v0.13 : reste recalculé par la route (comme un GPS) en priorité.
            val remain =
                if (s.hasPos && remainKm >= 0.0) remainKm
                else (s.km - (tripKm - stageStartKm)).coerceAtLeast(0.0)
            sb.append('\n').append(s.name)
            sb.append('\n').append("reste ").append("%.1f".format(remain)).append(" km")
            if (sc >= 0) {
                val p = sc - remain * consoPctPerKm
                sb.append('\n').append("arrivée : ").append("%.0f".format(p)).append(" %")
            }
        } else {
            if (stages.isNotEmpty()) sb.append('\n').append("trajet non démarré")
        }
        sb.append('\n').append("%.2f".format(consoPctPerKm)).append(" %/km")
        // v0.38 : santé de la batterie, affichée dès qu'elle a été lue
        // une fois avec le bouton « SOH batterie… ».
        // v0.46 : recharge DC en cours (compteur + gain depuis le début).
        if (dcSoc0 >= 0.0 && socPct >= 0.0) {
            sb.append('\n').append("⚡ DC +").append("%.0f".format(socPct - dcSoc0))
                .append(" %")
        }
        // v0.41 : alerte radar en cours (⚠ + distance), au-dessus du SOH.
        if (radarInfo.isNotEmpty()) {
            sb.append('\n').append(radarInfo)
        }
        if (sohPct > 0) {
            sb.append('\n').append("SOH ").append(String.format(Locale.US, "%.1f", sohPct))
                .append(" %")
        }
        val txt = sb.toString()
        handler.post { tv.text = txt }
    }

    // ------------------------------------------------------ Bornes IRVE v0.7.1

    private fun bornesFile(): File = File(filesDir, "bornes_cache.txt")

    // v0.14 : copie publique des caches dans Téléchargements/MG4Link - ce dossier
    // n'est PAS supprimé à la désinstallation (Android 9 et plus récent).
    /** Dossier public Download/MG4Link (accessible avec « Tous les fichiers »). */
    private fun publicDir(): File = File(
        android.os.Environment.getExternalStoragePublicDirectory(
            android.os.Environment.DIRECTORY_DOWNLOADS), "MG4Link")

    /**
     * v0.17 : demande (une seule fois) l'autorisation « Tous les fichiers ».
     * Sans elle, Android cache à la nouvelle installation les fichiers du
     * dossier Download créés par l'installation précédente (« 0 fichiers
     * visibles ») : le cache des bornes ne pouvait jamais être relu après
     * une réinstallation. App personnelle hors Play Store : autorisée.
     */
    private fun ensureStorageAccess() {
        try {
            if (Build.VERSION.SDK_INT < 30) return
            if (android.os.Environment.isExternalStorageManager()) return
            val sp = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
            if (sp.getBoolean("storageAsked", false)) return
            sp.edit().putBoolean("storageAsked", true).apply()
            log("Autorisation « Tous les fichiers » non accordée : les caches " +
                "du dossier Téléchargements ne survivront pas à une réinstallation.")
            AlertDialog.Builder(this)
                .setTitle("Autorisation « Tous les fichiers »")
                .setMessage("Pour retrouver les caches de bornes (123 000 bornes) " +
                    "après une réinstallation, l'app doit lire le dossier " +
                    "Téléchargements.\n\nDans l'écran qui s'ouvre : active « " +
                    "Autoriser la gestion de tous les fichiers ».\n" +
                    "(une seule fois, pour toujours)")
                .setPositiveButton("Ouvrir les réglages") { _, _ ->
                    try {
                        startActivity(android.content.Intent(
                            android.provider.Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION,
                            Uri.parse("package:" + packageName)))
                    } catch (e: Exception) {
                        try {
                            startActivity(android.content.Intent(
                                android.provider.Settings.ACTION_MANAGE_ALL_FILES_ACCESS_PERMISSION))
                        } catch (e2: Exception) {
                            log("Ouverture des réglages impossible : " + e2.message)
                        }
                    }
                }
                .setNegativeButton("Plus tard", null)
                .show()
        } catch (e: Exception) {
            log("ensureStorageAccess : " + e.message)
        }
    }

    private fun savePublicCache(name: String, text: String) {
        // v0.17 : avec « Tous les fichiers », écriture directe - MediaStore
        // renomme les copies « (12).txt » et les fichiers restent invisibles
        // à la prochaine installation.
        try {
            if (android.os.Environment.isExternalStorageManager()) {
                val dir = publicDir()
                dir.mkdirs()
                val base = name.removeSuffix(".txt")
                dir.listFiles()?.forEach {
                    if (it.isFile && (it.name == name ||
                        (it.name.startsWith(base + " (") && it.name.endsWith(".txt")))) {
                        it.delete()
                    }
                }
                val f = File(dir, name)
                f.writeText(text)
                log("Cache public écrit directement : " + f.name + " (" +
                    (f.length() / 1024) + " Ko).")
                return
            }
        } catch (e: Exception) {
            log("Écriture directe du cache public : " + e.message)
        }
        try {
            if (Build.VERSION.SDK_INT < 29) return
            val uri = android.provider.MediaStore.Downloads.EXTERNAL_CONTENT_URI
            // v0.15.8 : Android renomme parfois les fichiers (« (6).txt ») quand
            // le nom existe déjà - on supprime donc aussi les copies renommées.
            val base = name.removeSuffix(".txt")
            contentResolver.delete(uri,
                android.provider.MediaStore.MediaColumns.DISPLAY_NAME + " = ? OR " +
                    android.provider.MediaStore.MediaColumns.DISPLAY_NAME + " LIKE ?",
                arrayOf(name, base + " (%"))
            val values = android.content.ContentValues()
            values.put(android.provider.MediaStore.MediaColumns.DISPLAY_NAME, name)
            values.put(android.provider.MediaStore.MediaColumns.MIME_TYPE, "text/plain")
            values.put(android.provider.MediaStore.MediaColumns.RELATIVE_PATH, "Download/MG4Link")
            val u = contentResolver.insert(uri, values) ?: return
            contentResolver.openOutputStream(u)?.use { it.write(text.toByteArray(Charsets.UTF_8)) }
        } catch (e: Exception) {
            log("Sauvegarde publique impossible : " + e.message)
        }
    }

    private fun loadPublicCache(name: String): String? {
        // v0.17 : en priorité, lecture directe du dossier Download/MG4Link
        // (possible avec « Tous les fichiers ») - c'est le seul moyen de
        // retrouver les fichiers créés par une installation précédente :
        // la médiathèque (MediaStore) les cache à la nouvelle installation
        // (« 0 fichiers visibles » dans les journaux).
        try {
            if (android.os.Environment.isExternalStorageManager()) {
                val dir = publicDir()
                val base = name.removeSuffix(".txt")
                var best: File? = null
                val direct = File(dir, name)
                if (direct.isFile && direct.canRead()) {
                    best = direct
                } else {
                    best = dir.listFiles()
                        ?.filter { it.isFile && it.name.startsWith(base + " (") &&
                            it.name.endsWith(".txt") }
                        ?.maxByOrNull { it.lastModified() }
                }
                if (best != null && best.canRead()) {
                    log("Cache public « " + best.name + " » lu directement dans " +
                        "Download/MG4Link (" + (best.length() / 1024) + " Ko).")
                    return best.readText()
                }
                log("Lecture directe : « " + name + " » absent de Download/MG4Link.")
                return null
            }
        } catch (e: Exception) {
            log("Lecture directe du cache public : " + e.message)
        }
        // Repli (sans l'autorisation) : la médiathèque Android.
        var seen = 0
        val names = StringBuilder()
        try {
            if (Build.VERSION.SDK_INT < 29) return null
            val uri = android.provider.MediaStore.Downloads.EXTERNAL_CONTENT_URI
            contentResolver.query(uri, arrayOf(
                android.provider.MediaStore.MediaColumns._ID,
                android.provider.MediaStore.MediaColumns.DISPLAY_NAME), null, null,
                android.provider.MediaStore.MediaColumns.DATE_ADDED + " DESC")?.use { c ->
                // v0.15.8 : Android renomme les copies « nom (N).txt » - on
                // accepte aussi ces noms, la plus récente d'abord.
                val base = name.removeSuffix(".txt")
                while (c.moveToNext()) {
                    seen++
                    val dn = c.getString(1)
                    if (names.length < 150) names.append(dn).append(" | ")
                    if (dn == name || (dn.startsWith(base + " (") && dn.endsWith(".txt"))) {
                        val u = android.content.ContentUris.withAppendedId(uri, c.getLong(0))
                        return contentResolver.openInputStream(u)
                            ?.bufferedReader()?.readText()
                    }
                }
            }
        } catch (e: Exception) {
            // v0.15.3 : plus de silence - chaque échec de lecture du cache
            // public est journalisé pour diagnostic.
            log("Lecture du cache public " + name + " impossible : " + e.message)
        }
        // v0.15.6 : diagnostic - ce que l'app voit réellement dans Download.
        log("Cache public : « " + name + " » invisible (" + seen +
            " fichiers visibles dans Download). Aperçu : " + names)
        return null
    }

    private fun bornesAgeMs(): Long {
        val d = getSharedPreferences("mg4link", Context.MODE_PRIVATE).getLong("bornesDate", 0L)
        return if (d == 0L) Long.MAX_VALUE else System.currentTimeMillis() - d
    }

    /** v0.41 : charge les radars depuis Download/MG4Link.
     * Sources acceptées : soit un fichier unique radars.csv (ou .txt),
     * soit un dossier Download/MG4Link/radars/ contenant TOUS les fichiers
     * CSV lufop tels quels (un par pays et par type, ex : ESFixeES90,
     * FRMobile…) - pas besoin de les fusionner.
     * Format lufop « Zones de danger Europe CSV » : lignes du type
     * « longitude;latitude;nom;type;vitesse » (ordre lon/lat détecté
     * automatiquement, séparateur ; ou , accepté). Les fichiers doivent
     * être de vrais fichiers .csv (ouverts dans le Bloc-notes, on doit y
     * voir des chiffres séparés par des points-virgules), PAS des .ods. */
    private fun loadRadars() {
        val dir = publicDir()
        val files = ArrayList<File>()
        val sub = File(dir, "radars")
        if (sub.isDirectory) {
            sub.listFiles()?.filter { it.isFile && it.canRead() }?.let { files.addAll(it) }
        }
        for (n in listOf("radars.csv", "radars.txt", "radars_lufop.csv")) {
            val c = File(dir, n)
            if (c.isFile && c.canRead()) files.add(c)
        }
        if (files.isEmpty()) {
            log("Radars : aucun fichier trouvé. Créez un dossier « radars » " +
                "dans Download/MG4Link et copiez-y les fichiers CSV de " +
                "lufop.net (« Zones de danger Europe CSV », inscription " +
                "gratuite), ou un fichier unique radars.csv.")
            return
        }
        try {
            class Row(val a: Double, val b: Double, val name: String, val speed: Int)
            val rows = ArrayList<Row>()
            var lonFirst = 0
            var latFirst = 0
            var koTotal = 0L
            val vides = ArrayList<String>()
            for (f in files) {
                koTotal += f.length() / 1024
                var nLus = 0
                f.forEachLine { line ->
                    val p = line.split(';', ',').map { it.trim() }
                    if (p.size < 2) return@forEachLine
                    val a = p[0].replace(',', '.').toDoubleOrNull() ?: return@forEachLine
                    val b = p[1].replace(',', '.').toDoubleOrNull() ?: return@forEachLine
                    // Vote sur l'ordre des colonnes : en FR/ES/PT, la latitude
                    // est entre 35 et 55 et la longitude entre -10 et 10 environ.
                    if (a in 35.0..55.0 && b in -10.0..10.0) latFirst++
                    if (b in 35.0..55.0 && a in -10.0..10.0) lonFirst++
                    val name = p.firstOrNull {
                        it.toDoubleOrNull() == null && it.isNotEmpty()
                    } ?: "Radar"
                    // v0.48 : vitesse = dernier nombre APRÈS les coordonnées
                    // (avant, la latitude tronquée, ex 47,72 -> 47, était
                    // prise pour la limite !) et multiple de 10 (30, 50, 70,
                    // 80, 90, 110, 130). Repli : le nom, qui contient souvent
                    // la limite (« FR Radar Fixe FR 80 »).
                    var speed = p.drop(2).mapNotNull { s -> s.toDoubleOrNull()?.toInt() }
                        .lastOrNull { it in 20..160 && it % 10 == 0 } ?: 0
                    if (speed == 0) {
                        speed = Regex("(\\d{2,3})").findAll(name)
                            .mapNotNull { it.value.toIntOrNull() }
                            .lastOrNull { it in 20..160 && it % 10 == 0 } ?: 0
                    }
                    rows.add(Row(a, b, name, speed))
                    nLus++
                }
                if (nLus == 0) vides.add(f.name)
            }
            if (rows.isEmpty()) {
                log("Radars : " + files.size + " fichier(s) mais aucune ligne " +
                    "exploitable. Vérifiez que ce sont bien des fichiers CSV " +
                    "(chiffres séparés par des points-virgules), pas des .ods.")
                return
            }
            val lonEnPremier = lonFirst >= latFirst
            val lst = ArrayList<Radar>()
            for (r in rows) {
                val lat = if (lonEnPremier) r.b else r.a
                val lon = if (lonEnPremier) r.a else r.b
                // Filtre de sécurité : on ne garde que des coordonnées
                // plausibles (France, Espagne, Portugal et environs).
                if (lat in 34.0..56.0 && lon in -11.0..17.0) {
                    lst.add(Radar(lat, lon, r.name, r.speed))
                }
            }
            synchronized(radars) {
                radars.clear()
                radars.addAll(lst)
            }
            log("Radars chargés : " + lst.size + " points depuis " + files.size +
                " fichier(s) (" + koTotal + " Ko). Alertes à 5 km puis 2 km.")
            if (vides.isNotEmpty()) {
                log("Radars : fichiers ignorés (aucune ligne exploitable) : " +
                    vides.take(5).joinToString(", ") +
                    (if (vides.size > 5) "… (" + vides.size + " au total)" else ""))
            }
        } catch (e: Exception) {
            log("Radars : erreur de lecture (" + e.message + ").")
        }
    }


    /** v0.41 : alerte radar - bip + ligne « ⚠ » dans la fenêtre flottante,
     * à 5 km puis 2 km avant le radar / zone le plus proche. */
    private fun checkRadars(loc: Location) {
        val now = System.currentTimeMillis()
        if (now - lastRadarCheck < 2000L) return
        lastRadarCheck = now
        val lst = synchronized(radars) { radars }
        if (lst.isEmpty()) { radarInfo = ""; return }
        var best: Radar? = null
        var bestD = Double.MAX_VALUE
        for (r in lst) {
            val d = distKm(loc.latitude, loc.longitude, r.lat, r.lon)
            if (d < bestD) { bestD = d; best = r }
        }
        val r = best ?: return
        val key = r.lat.toString() + "," + r.lon.toString()
        if (key != lastRadarKey || bestD > 5.5) {
            lastRadarKey = key
            lastRadarLevel = 0
        }
        val level = when {
            bestD <= 2.0 -> 2
            bestD <= 5.0 -> 1
            else -> 0
        }
        if (level == 0) {
            radarInfo = ""
            return
        }
        val limite = if (r.speed > 0) " (limite " + r.speed + " km/h)" else ""
        val dist = if (level == 2) "%.1f".format(bestD) + " km" else "%.0f".format(bestD) + " km"
        radarInfo = "⚠ RADAR " + r.name + limite + " - " + dist
        // v0.46 : bip insistant RÉPÉTÉ toutes les 15 s tant qu'on reste à
        // moins de 2 km (avant : un seul bip, facile à rater).
        if (level > lastRadarLevel) {
            lastRadarLevel = level
            lastRadarBeep = now
            log(radarInfo)
            beep(level == 2)
            refreshOverlay()
        } else if (level == 2 && now - lastRadarBeep > 15000L) {
            lastRadarBeep = now
            beep(true)
        }
    }

    /** v0.48 : bip sur le flux ALARME + vibration. Avant (STREAM_MUSIC),
     * le bip était inaudible quand le téléphone était branché au port USB
     * de la voiture : le mode conduite / Android Auto coupait ou détournait
     * le flux média. Le flux alarme n'est pas affecté, et la vibration
     * fonctionne dans tous les cas. */
    private fun beep(insistant: Boolean) {
        thread(name = "bip-radar") {
            try {
                val tg = ToneGenerator(AudioManager.STREAM_ALARM, 100)
                if (insistant) {
                    for (i in 1..3) {
                        tg.startTone(ToneGenerator.TONE_PROP_BEEP2, 400)
                        Thread.sleep(750)
                    }
                } else {
                    tg.startTone(ToneGenerator.TONE_PROP_BEEP, 300)
                    Thread.sleep(250)
                    tg.startTone(ToneGenerator.TONE_PROP_BEEP, 300)
                }
                Thread.sleep(500)
                tg.release()
            } catch (e: Exception) { }
            // Vibration de secours : 3 pulsations (insistant) ou 1 simple.
            try {
                val vib = getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
                    ?: return@thread
                val motif = if (insistant)
                    longArrayOf(0, 300, 150, 300, 150, 300)
                else
                    longArrayOf(0, 300)
                if (Build.VERSION.SDK_INT >= 26) {
                    vib.vibrate(VibrationEffect.createWaveform(motif, -1))
                } else {
                    // v0.48b : vibrate(LongArray) supprimé du SDK 36 - on
                    // garde une vibration simple pour les vieux Android.
                    vib.vibrate(300L)
                }
            } catch (e: Exception) { }
        }
    }

    /** v0.42 : site officiel de l'opérateur de la borne (occupation des
     * bornes visible dans son app/son site). L'accès direct aux données
     * temps réel (OCPI) est un service B2B payant - impossible pour une
     * app personnelle - on renvoie donc vers la source fiable gratuite :
     * l'opérateur lui-même. Null si l'opérateur est inconnu. */
    private fun operatorLiveUrl(enseigne: String): String? {
        val e = enseigne.uppercase(Locale.ROOT)
        return when {
            e.contains("ZUNDER") -> "https://zunder.com"
            e.contains("IONITY") -> "https://ionity.eu"
            e.contains("ELECTRA") -> "https://go-electra.com"
            e.contains("FASTNED") -> "https://fastnedcharging.com"
            e.contains("MOEVE") || e.contains("CEPSA") -> "https://moeve.com"
            e.contains("TESLA") -> "https://www.tesla.com/fr_FR/findus"
            e.contains("MOBI.E") -> "https://www.mobie.pt"
            e.contains("POWERDOT") -> "https://powerdot.com"
            e.contains("REPSOL") -> "https://www.repsol.es"
            e.contains("EDP") -> "https://www.edp.pt"
            e.contains("GALP") -> "https://www.galp.com"
            // v0.43 : opérateurs supplémentaires (retours de test).
            e.contains("IZIVIA") -> "https://www.izivia.com"
            e.contains("VIRTY") || e.contains("SODETREL") -> "https://www.virty.fr"
            e.contains("WENEA") -> "https://wenea.com"
            e.contains("IBIL") -> "https://ibil.es"
            e.contains("E-RED") || e.contains("ERED") -> "https://e-red.es"
            e.contains("FRESHMILE") -> "https://freshmile.com"
            e.contains("SHELL") -> "https://shellrecharge.com"
            e.contains("IECHARGE") || e.contains("IE CHARGE") -> "https://iecharge.io"
            e.contains("VIANEO") || e.contains("ENGIE") -> "https://www.engie-vianeo.com"
            e.contains("ATLANTE") -> "https://atlante.energy"
            else -> null
        }
    }

    /** v0.44 : paquet Android de l'appli de l'opérateur (null si inconnu).
     * Si l'appli est installée, « occupation en direct » l'ouvre
     * directement ; sinon on retombe sur le site web. */
    private fun operatorPkg(enseigne: String): String? {
        val e = enseigne.uppercase(Locale.ROOT)
        return when {
            e.contains("ZUNDER") -> "es.easycharger.app"
            e.contains("IONITY") -> "com.cleevio.ionity.android.app"
            e.contains("ELECTRA") -> "com.electra.app"
            e.contains("TESLA") -> "com.teslamotors.tesla"
            e.contains("IZIVIA") -> "com.izivia.izivia"
            // v0.45 : Engie Vianeo et Atlante (retours de test).
            e.contains("VIANEO") || e.contains("ENGIE") -> "com.engie.vianeo"
            e.contains("ATLANTE") -> "com.atlante.charging"
            // v0.44b : IECharge (reseau HPC, applis FR/ES/PT).
            e.contains("IECHARGE") || e.contains("IE CHARGE") -> "com.iecharge"
            else -> null
        }
    }

    /** v0.44 : ouvre l'appli de l'opérateur si installée, sinon son site. */
    private fun openLive(enseigne: String) {
        var ok = false
        val pkg = operatorPkg(enseigne)
        if (pkg != null) {
            try {
                startActivity(packageManager.getLaunchIntentForPackage(pkg))
                ok = true
            } catch (e: Exception) { }
        }
        if (!ok) {
            val u = operatorLiveUrl(enseigne)
            if (u != null) {
                try {
                    startActivity(Intent(Intent.ACTION_VIEW, Uri.parse(u)))
                    ok = true
                } catch (e: Exception) {
                    log("Site opérateur indisponible : " + e.message)
                }
            }
        }
        if (!ok) log("Pas d'appli ni de site connu pour « " + enseigne + " ».")
    }

    private fun loadBornesCache() {
        var f = bornesFile()
        if (!f.exists()) {
            // v0.14 : repli sur la copie publique (Téléchargements/MG4Link) qui
            // survit à la désinstallation de l'app.
            var public = loadPublicCache("bornes_cache.txt")
            // v0.16 : Android (MediaStore) met parfois plusieurs dizaines de
            // secondes à « voir » les fichiers du dossier Download après le
            // démarrage du téléphone - le premier essai échouait et l'app
            // retéléchargeait 92 000 bornes pour rien. On réessaie pendant
            // ~20 s avant d'abandonner.
            var essai = 1
            while (public == null && essai < 5) {
                try { Thread.sleep(5000L) } catch (e: InterruptedException) { return }
                log("Cache des bornes : nouvel essai (" + (essai + 1) + "/5)...")
                public = loadPublicCache("bornes_cache.txt")
                essai++
            }
            if (public != null) try { f.writeText(public) } catch (e: Exception) { }
        }
        if (!f.exists()) return
        try {
            val lst = ArrayList<Borne>()
            f.forEachLine { line -> parseBorneCache(line)?.let { lst.add(it) } }
            if (lst.isNotEmpty()) {
                synchronized(bornes) {
                    bornes.clear()
                    bornes.addAll(lst)
                }
                val ageH = bornesAgeMs() / 3600000L
                // v0.17.1 : après restauration d'un vieux cache, la date de mise
                // à jour est inconnue (préférence absente) - ne pas afficher un
                // âge absurde (« 2562047788015 h »).
                log("Base IRVE France en cache : " + lst.size + " bornes" +
                    (if (ageH > 100000L) " (date de mise à jour inconnue)." else
                        " (maj il y a " + ageH + " h)."))
            }
            loadBornesIberia()
        } catch (e: Exception) {
            log("Cache IRVE illisible : " + e.message)
        }
    }

    /** Une ligne de cache : « lat;lon;kw;enseigne;adresse ». */
    private fun parseBorneCache(line: String): Borne? {
        val p = line.split(';')
        if (p.size < 5) return null
        val lat = p[0].toDoubleOrNull() ?: return null
        val lon = p[1].toDoubleOrNull() ?: return null
        val kw = p[2].toDoubleOrNull() ?: return null
        return Borne(lat, lon, kw, p[3], p[3], p[4])
    }

    /**
     * Bornes Espagne/Portugal en cache. v0.16 : nouveau nom de fichier -
     * l'ancien cache, rempli avec la bbox qui couvrait aussi la France du
     * sud-ouest, contenait ~28 000 bornes françaises en double. Il est
     * ignoré ; le nouveau sera écrit à la prochaine mise à jour réussie.
     */
    private fun bornesIberiaFile(): File = File(filesDir, "bornes_iberia2.txt")

    private fun loadBornesIberia() {
        var f = bornesIberiaFile()
        if (!f.exists()) {
            val public = loadPublicCache("bornes_iberia2.txt")
            if (public != null) try { f.writeText(public) } catch (e: Exception) { }
        }
        if (!f.exists()) {
            log("Cache Espagne/Portugal introuvable (interne et dossier Download).")
            return
        }
        try {
            val lst = ArrayList<Borne>()
            f.forEachLine { line -> parseBorneCache(line)?.let { lst.add(it) } }
            if (lst.isNotEmpty()) {
                synchronized(bornes) { bornes.addAll(lst) }
                log("Bornes Espagne/Portugal en cache : " + lst.size)
            }
        } catch (e: Exception) {
            log("Cache Espagne/Portugal illisible : " + e.message)
        }
    }

    /** Découpe une ligne CSV en respectant les guillemets ; séparateur ';' ou ',' (v0.7.1). */
    private fun splitCsvLine(line: String, sep: Char): List<String> {
        val out = ArrayList<String>()
        val cur = StringBuilder()
        var inQ = false
        var i = 0
        while (i < line.length) {
            val ch = line[i]
            if (inQ) {
                if (ch == '"') {
                    if (i + 1 < line.length && line[i + 1] == '"') {
                        cur.append('"')
                        i++
                    } else {
                        inQ = false
                    }
                } else {
                    cur.append(ch)
                }
            } else {
                when (ch) {
                    '"' -> inQ = true
                    sep -> {
                        out.add(cur.toString())
                        cur.setLength(0)
                    }
                    else -> cur.append(ch)
                }
            }
            i++
        }
        out.add(cur.toString())
        return out
    }

    /** "lon,lat" (éventuellement entre crochets) -> [lat, lon]. */
    private fun parseCoord(s: String): DoubleArray? {
        val t = s.replace("[", "").replace("]", "").trim()
        val parts = t.split(',')
        if (parts.size < 2) return null
        val lon = parts[0].trim().toDoubleOrNull() ?: return null
        val lat = parts[1].trim().toDoubleOrNull() ?: return null
        return doubleArrayOf(lat, lon)
    }

    private fun httpGet(urlStr: String, timeoutMs: Int): String {
        val conn = URL(urlStr).openConnection() as HttpURLConnection
        conn.connectTimeout = timeoutMs
        conn.readTimeout = timeoutMs
        conn.instanceFollowRedirects = true
        conn.setRequestProperty("User-Agent", "MG4Link/0.49 (Android; https://github.com/Moup1957/MG4Link)")
        try {
            val reader = BufferedReader(InputStreamReader(conn.inputStream, Charsets.UTF_8))
            val sb = StringBuilder()
            var line = reader.readLine()
            while (line != null) {
                sb.append(line)
                line = reader.readLine()
            }
            reader.close()
            return sb.toString()
        } finally {
            conn.disconnect()
        }
    }

    private fun downloadCsv(urlStr: String, onLine: (String) -> Unit): Int {
        val conn = URL(urlStr).openConnection() as HttpURLConnection
        conn.connectTimeout = 30000
        conn.readTimeout = 300000
        conn.instanceFollowRedirects = true
        conn.setRequestProperty("User-Agent", "MG4Link/0.49 (Android; https://github.com/Moup1957/MG4Link)")
        var count = 0
        try {
            val reader = BufferedReader(InputStreamReader(conn.inputStream, Charsets.UTF_8))
            var line = reader.readLine()
            while (line != null) {
                onLine(line)
                count++
                line = reader.readLine()
            }
            reader.close()
        } finally {
            conn.disconnect()
        }
        return count
    }

    private fun updateBornes(force: Boolean) {
        if (bornesLoading) {
            log("Téléchargement des bornes déjà en cours, patientez...")
            return
        }
        if (!force && bornes.isNotEmpty() && bornesAgeMs() < 7L * 24L * 3600L * 1000L) {
            log("Base des bornes déjà à jour.")
            return
        }
        bornesLoading = true
        log("Mise à jour de la base IRVE France (Wi-Fi conseillé, 1 à 2 min)...")
        thread(name = "bornes-dl") {
            try {
                // v0.23 : si la base France en cache est récente (moins de
                // 7 jours) et qu'un fichier officiel espagnol plus récent que
                // le dernier import est présent, on importe l'Espagne et le
                // Portugal directement, sans retélécharger les ~125 000
                // bornes françaises (1 à 2 minutes économisées).
                val prefsX = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
                val frRecent = bornesFile().exists() &&
                    System.currentTimeMillis() - prefsX.getLong("bornesDate", 0L) <
                    7L * 24L * 3600L * 1000L
                val esF = findEsXmlFile()
                if (frRecent && esF != null &&
                    esF.lastModified() > prefsX.getLong("iberiaDate", 0L)) {
                    log("Fichier espagnol officiel détecté - import direct " +
                        "(base France conservée depuis le cache).")
                    synchronized(bornes) { bornes.clear() }
                    bornesFile().forEachLine { line ->
                        parseBorneCache(line)?.let { b ->
                            synchronized(bornes) { bornes.add(b) }
                        }
                    }
                    log("France : " + bornes.size + " bornes rechargées depuis le cache.")
                    updateBornesIberia()
                    log("Base complète chargée : " + bornes.size +
                        " bornes (France en cache + Espagne + Portugal).")
                    return@thread
                }
                val api = "https://www.data.gouv.fr/api/1/datasets/" +
                    "base-nationale-des-irve-data-gouv-infrastructures-de-recharge-pour-vehicules-electriques-donnees-statiques/"
                val json = httpGet(api, 30000)
                val urls = Regex("https:[^\"\\\\]+?\\.csv")
                    .findAll(json).map { it.value }.toList()
                    .filter { it.contains("consolidation-etalab-schema-irve-statique") }
                if (urls.isEmpty()) {
                    log("ERREUR : URL de la base IRVE introuvable - réessayez plus tard.")
                    alert("Bornes", "URL de la base IRVE introuvable. Réessayez plus tard.")
                    return@thread
                }
                val best = urls.maxByOrNull { Regex("(\\d{8})").find(it)?.groupValues?.get(1) ?: "0" }!!
                log("Fichier source : " + best.substringAfterLast('/'))

                val parsed = ArrayList<Borne>()
                var header: List<String>? = null
                var sep = ';'
                var iCoord = -1
                var iKw = -1
                var iOper = -1
                var iEnseigne = -1
                var iNom = -1
                var iAdr = -1
                val out = StringBuilder()
                var n = 0
                downloadCsv(best) { line ->
                    if (header == null) {
                        // Le CSV v2.3.1 utilise la virgule ; les anciens le point-virgule.
                        sep = if (line.count { it == ';' } >= line.count { it == ',' }) ';' else ','
                        header = splitCsvLine(line, sep)
                        iCoord = header!!.indexOf("coordonneesXY")
                        iKw = header!!.indexOf("puissance_nominale")
                        if (iKw < 0) iKw = header!!.indexOf("puissance_max")
                        iOper = header!!.indexOf("nom_operateur")
                        iEnseigne = header!!.indexOf("nom_enseigne")
                        iNom = header!!.indexOf("nom_station")
                        iAdr = header!!.indexOf("adresse_station")
                        if (iCoord < 0 || iKw < 0) {
                            log("Colonnes IRVE introuvables ! En-tête reçu (300 premiers caractères) : " +
                                line.take(300))
                        } else {
                            log("Colonnes IRVE : coordonnees=$iCoord puissance=$iKw (" +
                                header!![iKw] + ") opérateur=$iOper enseigne=$iEnseigne")
                        }
                    } else if (iCoord >= 0 && iKw >= 0) {
                        val f = splitCsvLine(line, sep)
                        if (f.size > iCoord && f.size > iKw) {
                            val ll = parseCoord(f[iCoord])
                            val kw = f[iKw].replace(',', '.').toDoubleOrNull() ?: 0.0
                            if (ll != null && kw >= 22.0) {
                                val enseigne = when {
                                    iOper >= 0 && f.size > iOper && f[iOper].isNotEmpty() -> f[iOper]
                                    iEnseigne >= 0 && f.size > iEnseigne && f[iEnseigne].isNotEmpty() -> f[iEnseigne]
                                    else -> "Opérateur ?"
                                }
                                val nom = if (iNom >= 0 && f.size > iNom) f[iNom] else ""
                                val adr = if (iAdr >= 0 && f.size > iAdr && f[iAdr].isNotEmpty()) f[iAdr] else nom
                                parsed.add(Borne(ll[0], ll[1], kw, enseigne, nom, adr))
                                out.append(ll[0]).append(';').append(ll[1]).append(';')
                                    .append(kw).append(';')
                                    .append(enseigne.replace(';', ' ')).append(';')
                                    .append(adr.replace(';', ' ')).append('\n')
                            }
                        }
                    }
                    n++
                    if (n % 50000 == 0) log("Téléchargement IRVE : " + n + " lignes lues...")
                }
                synchronized(bornes) {
                    bornes.clear()
                    bornes.addAll(parsed)
                }
                bornesFile().writeText(out.toString())
                savePublicCache("bornes_cache.txt", out.toString())
                getSharedPreferences("mg4link", Context.MODE_PRIVATE).edit()
                    .putLong("bornesDate", System.currentTimeMillis())
                    .apply()
                log("Base IRVE France chargée : " + bornes.size + " bornes ≥ 22 kW (" + n + " lignes).")
                // Espagne + Portugal : retéléchargés seulement si le cache a plus de
                // 7 jours (v0.15) - le serveur Overpass bloque les requêtes répétées.
                val prefsB = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
                val iAge = System.currentTimeMillis() - prefsB.getLong("iberiaDate", 0L)
                // v0.22 : un nouveau fichier officiel espagnol déposé dans
                // Download/MG4Link est pris en compte immédiatement, même si
                // le cache a moins de 7 jours.
                val esXmlF = findEsXmlFile()
                val xmlNouveau = esXmlF != null &&
                    esXmlF.lastModified() > prefsB.getLong("iberiaDate", 0L)
                if (iAge in 1 until 7L * 24 * 3600 * 1000 && !xmlNouveau) {
                    log("Bornes Espagne/Portugal : cache de moins de 7 jours, pas de retéléchargement.")
                } else {
                    updateBornesIberia()
                }
                log("Base complète chargée : " + bornes.size + " bornes (France + Espagne + Portugal).")
                if (bornes.isEmpty()) {
                    alert("Bornes", "La base a été téléchargée mais aucune borne ≥ 22 kW n'a été trouvée. " +
                        "Copiez le journal et envoyez-le pour diagnostic.")
                }
            } catch (e: Exception) {
                log("Erreur base IRVE : " + e.message)
                alert("Bornes", "Erreur pendant le téléchargement : " + e.message)
            } finally {
                bornesLoading = false
            }
        }
    }

    /**
     * v0.22 : import du fichier XML officiel espagnol (MITECO,
     * « Instalaciones públicas de recarga ») posé par l'utilisateur
     * dans Download/MG4Link. Chaque bloc <INSTALACION> décrit un
     * CONNECTEUR ; on regroupe par point de recharge
     * (IDPUNTODERECARGA) en gardant la puissance maximale.
     */
    private fun findEsXmlFile(): File? {
        try {
            val files = publicDir().listFiles()?.filter {
                it.isFile && it.name.endsWith(".xml", ignoreCase = true) &&
                    it.name.contains("nstalaciones", ignoreCase = true)
            } ?: return null
            return files.maxByOrNull { it.lastModified() }
        } catch (e: Exception) {
            return null
        }
    }

    private fun importEsXml(out: StringBuilder): Int {
        val f = findEsXmlFile() ?: return 0
        try {
            log("Espagne : lecture en flux du fichier officiel MITECO " + f.name +
                " (" + (f.length() / 1048576L) + " Mo)...")
            // Regroupement par point de recharge : plusieurs connecteurs
            // (50 kW CCS + 22 kW T2...) partagent le même IDPUNTODERECARGA.
            val byPoint = LinkedHashMap<String, Borne>()
            // v0.23 : le fichier fait ~55 Mo - le charger en mémoire d'un coup
            // (readText) faisait planter l'application par manque de mémoire.
            // On lit maintenant ligne par ligne : un seul bloc <INSTALACION>
            // (quelques ko) est en mémoire à la fois.
            // v0.26 : le fichier MITECO met des milliers de blocs SUR LA MÊME
            // LIGNE (lignes de ~1 Mo) - la lecture ne détectait qu'un bloc par
            // ligne (62 blocs au lieu de ~100 000). On découpe maintenant
            // chaque ligne sur le délimiteur <INSTALACION>.
            val delim = "<INSTALACION>"
            val block = StringBuilder()
            var inBlock = false
            var nBlocks = 0
            fun parseAndClear() {
                if (block.isNotEmpty()) {
                    nBlocks++
                    parseEsBlock(block.toString(), byPoint)
                    block.setLength(0)
                }
            }
            java.io.BufferedReader(java.io.InputStreamReader(
                java.io.FileInputStream(f), Charsets.UTF_8)).use { br ->
                var line = br.readLine()
                while (line != null) {
                    if (!line.contains(delim)) {
                        // Fichier « aéré » : la ligne complète la suite du bloc.
                        if (inBlock) block.append('\n').append(line)
                    } else {
                        // Ligne dense : elle contient 1+ blocs complets.
                        val parts = line.split(delim)
                        if (inBlock) {
                            block.append(parts[0])
                            parseAndClear()
                            inBlock = false
                        }
                        for (i in 1 until parts.size - 1) {
                            block.setLength(0)
                            block.append(parts[i])
                            parseAndClear()
                        }
                        if (parts.size > 1) {
                            // Dernier fragment : début d'un nouveau bloc qui
                            // continue sur la ligne suivante.
                            block.setLength(0)
                            block.append(parts.last())
                            inBlock = true
                        }
                    }
                    line = br.readLine()
                }
            }
            parseAndClear()
            log("Espagne : " + nBlocks + " blocs INSTALACION lus dans le fichier.")
            if (byPoint.isEmpty()) {
                log("Fichier espagnol lu mais aucun point ≥ 22 kW trouvé.")
                return 0
            }
            val lst = byPoint.values.toList()
            synchronized(bornes) { bornes.addAll(lst) }
            lst.forEach { out.append(cacheLine(it)) }
            log("Bornes Espagne (base officielle MITECO) : " + lst.size +
                " points de recharge ≥ 22 kW.")
            return lst.size
        } catch (e: Exception) {
            log("Erreur lecture fichier espagnol : " + e.message)
            return 0
        }
    }

    /**
     * v0.23 : analyse d'un bloc <INSTALACION> (1 connecteur) du fichier
     * MITECO, extrait de importEsXml pour la lecture en flux. Le connecteur
     * est regroupé par point de recharge (IDPUNTODERECARGA) dans byPoint,
     * en gardant la puissance maximale du point.
     */
    private fun parseEsBlock(block: String, byPoint: LinkedHashMap<String, Borne>) {
        fun tag(n: String): String {
            val m = Regex("<" + n + ">(.*?)</" + n + ">").find(block)
            return m?.groupValues?.get(1)?.trim() ?: ""
        }
        // v0.25 : tolère aussi bien « 41.6523 » que « 41,6523 » (virgule
        // décimale espagnole) pour les coordonnées.
        val lat = tag("LATITUD").replace(',', '.').toDoubleOrNull() ?: return
        val lon = tag("LONGITUD").replace(',', '.').toDoubleOrNull() ?: return
        // « 350,00 kW » (virgule décimale espagnole).
        val kw = kwFromTag(tag("POTENCIAMAXIMA"))
        if (kw < 22.0) return
        val id = tag("IDPUNTODERECARGA")
        val key = if (id.isNotEmpty()) id else (tag("NOMBREINSTALACION") + lat + lon)
        val old = byPoint[key]
        if (old != null) {
            if (kw > old.kw) byPoint[key] = Borne(lat, lon, kw, old.enseigne, old.nom, old.adresse)
            return
        }
        // v0.26 : l'opérateur peut s'écrire <NOMBREOPERADOR>,
        // <NOMBRE_OPERADOR> ou <NOMBRE OPERADOR> selon les exports - on
        // essaie les trois formes.
        val operador = listOf("NOMBREOPERADOR", "NOMBRE_OPERADOR", "NOMBRE OPERADOR")
            .map { tag(it) }.firstOrNull { it.isNotEmpty() } ?: ""
        val nom = tag("NOMBREINSTALACION")
        val dir = tag("DIRECCION")
        val muni = tag("MUNICIPIO")
        val enseigne = "Espagne - " + (if (operador.isNotEmpty()) operador else nom)
        val adresse = dir + (if (dir.isNotEmpty() && muni.isNotEmpty()) ", " else "") + muni
        byPoint[key] = Borne(lat, lon, kw, enseigne,
            nom.ifEmpty { "Point de recharge" }, adresse)
    }

    /**
     * Bornes Espagne + Portugal (v0.8) via l'API Overpass (OpenStreetMap).
     * Les registres officiels RIPREE / MOBI.E n'ont pas de téléchargement CSV
     * direct et stable : OpenStreetMap est gratuit, sans clé et mis à jour
     * par la communauté. Puissance lue depuis les tags « maxpower » ou
     * « socket:type2_combo:output ».
     */
    private fun updateBornesIberia(): Int {
        // v0.16 : zones par frontières réelles du pays (area ISO3166).
        val zones = listOf("Espagne" to "ES", "Portugal" to "PT")
        val out = StringBuilder()
        var total = 0
        for ((pays, code) in zones) {
            try {
                // v0.22 : pour l'Espagne, la base officielle MITECO (fichier
                // XML posé dans Download/MG4Link) est bien plus complète
                // qu'OpenStreetMap - on l'utilise dès qu'elle est présente.
                if (pays == "Espagne") {
                    val nXml = importEsXml(out)
                    if (nXml > 0) {
                        log("Bornes " + pays + " : " + nXml +
                            " bornes ajoutées (base officielle, Overpass ignoré).")
                        total += nXml
                        continue
                    }
                }
                val csv = "[out:csv(::lat,::lon,\"maxpower\",\"socket:type2_combo:output\"," +
                    "\"operator\",\"name\",\"addr:street\",\"addr:housenumber\",\"addr:city\";true;\",\")]"
                val bbox = if (code == "ES") "35.0,-9.9,43.9,4.5" else "36.5,-9.9,42.3,-6.0"
                // Télécharge une requête Overpass sur les 3 serveurs en cascade.
                fun dl(query: String): Int {
                    val enc = URLEncoder.encode(query, "UTF-8")
                    var header: List<String>? = null
                    var count = 0
                    var lignes = 0
                    val parsed = ArrayList<Borne>()
                    var lastErr: Exception? = null
                    val bases = listOf(
                        "https://overpass-api.de/api/interpreter?data=",
                        "https://overpass.kumi.systems/api/interpreter?data=",
                        "https://overpass.private.coffee/api/interpreter?data=")
                    for ((bi, base) in bases.withIndex()) {
                        try {
                            header = null
                            parsed.clear()
                            count = 0
                            lignes = 0
                            downloadCsv(base + enc) { line ->
                                lignes++
                                if (header == null) {
                                    header = splitCsvLine(line, ',')
                                    log("Overpass " + pays + " - en-tête reçu : " + line.take(200))
                                } else {
                                    val b = overpassToBorne(splitCsvLine(line, ','), header!!, pays)
                                    if (b != null) {
                                        parsed.add(b)
                                        count++
                                        out.append(cacheLine(b))
                                    }
                                }
                            }
                            if (lignes <= 1) {
                                log("Overpass " + pays + " : " + lignes + " ligne(s) reçue(s) au total.")
                            }
                            lastErr = null
                            break
                        } catch (e: Exception) {
                            lastErr = e
                            log("Overpass " + pays + " : serveur " + (bi + 1) + "/" +
                                bases.size + " en échec (" + e.message + ")...")
                        }
                    }
                    if (lastErr != null) throw lastErr
                    synchronized(bornes) { bornes.addAll(parsed) }
                    return count
                }
                // v0.16/v0.17 : frontières réelles du pays d'abord ; si le
                // serveur ne renvoie rien (certains gèrent mal « area »),
                // repli sur la bbox classique.
                log("Téléchargement des bornes " + pays + " (OpenStreetMap, frontières du pays)...")
                var count = dl(csv + "[timeout:300];area[\"ISO3166\"=\"" + code + "\"]->.pays;" +
                    "node[\"amenity\"=\"charging_station\"](area.pays);out;")
                if (count == 0) {
                    log("Frontières " + pays + " : 0 borne - nouvel essai avec zone classique...")
                    count = dl(csv + "[timeout:300];node[\"amenity\"=\"charging_station\"](" +
                        bbox + ");out;")
                }
                log("Bornes " + pays + " : " + count + " bornes ≥ 22 kW ajoutées.")
                total += count
            } catch (e: Exception) {
                log("Erreur bornes " + pays + " : " + e.message)
            }
        }
        if (out.isNotEmpty()) {
            bornesIberiaFile().writeText(out.toString())
            savePublicCache("bornes_iberia2.txt", out.toString())
            getSharedPreferences("mg4link", Context.MODE_PRIVATE).edit()
                .putLong("iberiaDate", System.currentTimeMillis())
                .apply()
        }
        if (total == 0) {
            // v0.15.2 : on tente TOUJOURS le rechargement du cache (interne ou
            // dossier Download public) - après une réinstallation, le fichier
            // interne n'existe plus mais le cache public, lui, a survécu.
            loadBornesIberia()
            if (bornesIberiaFile().exists()) {
                log("Échec Espagne/Portugal : cache précédent rechargé.")
            } else {
                alert("Bornes Espagne/Portugal",
                    "Aucune borne n'a été trouvée dans OpenStreetMap pour ces pays.\n" +
                        "Copie le journal et envoie-le pour diagnostic.")
            }
        }
        return total
    }

    private fun fmtD(v: Double): String = String.format(Locale.US, "%.4f", v)

    private fun cacheLine(b: Borne): String =
        b.lat.toString() + ";" + b.lon + ";" + b.kw + ";" +
            b.enseigne.replace(';', ' ') + ";" + b.adresse.replace(';', ' ') + "\n"

    /** Extrait une puissance en kW d'un tag OSM (« 50 kW », « 22000 W », « 150 »...). */
    private fun kwFromTag(s: String): Double {
        val m = Regex("([0-9]+(?:[.,][0-9]+)?)\\s*(kW|W)?").find(s.trim()) ?: return 0.0
        var v = m.groupValues[1].replace(',', '.').toDoubleOrNull() ?: return 0.0
        if (m.groupValues[2] == "W") v /= 1000.0
        return v
    }

    /** Convertit une ligne CSV Overpass en borne ; null si puissance < 22 kW. */
    private fun overpassToBorne(f: List<String>, h: List<String>, pays: String): Borne? {
        // Recherche de colonne tolérante : « ::lat » ou « lat » ou « _lat... »
        fun colOf(pattern: String): Int {
            h.forEachIndexed { i, name ->
                val n = name.trim().lowercase(Locale.ROOT)
                val p = pattern.lowercase(Locale.ROOT)
                if (n == p || n == "::" + p || n.endsWith(p) && (p == "lat" || p == "lon")) return i
            }
            return -1
        }
        val iLat = colOf("lat")
        val iLon = colOf("lon")
        if (iLat < 0 || iLon < 0 || f.size <= iLat || f.size <= iLon) return null
        val lat = f[iLat].toDoubleOrNull() ?: return null
        val lon = f[iLon].toDoubleOrNull() ?: return null
        fun tag(name: String): String {
            val i = h.indexOf(name)
            return if (i >= 0 && f.size > i) f[i] else ""
        }
        var kw = kwFromTag(tag("maxpower"))
        if (kw < 22.0) kw = kwFromTag(tag("socket:type2_combo:output"))
        if (kw < 22.0) return null
        val operator = tag("operator")
        val name = tag("name")
        val enseigne = pays + " - " + when {
            operator.isNotEmpty() -> operator
            name.isNotEmpty() -> name
            else -> "Opérateur ?"
        }
        val adr = listOf(tag("addr:housenumber"), tag("addr:street"), tag("addr:city"))
            .filter { it.isNotEmpty() }.joinToString(", ")
        return Borne(lat, lon, kw, enseigne, name, if (adr.isNotEmpty()) adr else name)
    }

    /** v0.30 : saisie libre d'un lieu (ville, adresse, code postal)
     * puis géocodage OpenStreetMap avec confirmation (homonymes possibles,
     * ex : Gorges 44 vs Gorges dans l'Oise). Retrouve la recherche de bornes
     * autour d'une VILLE, perdue depuis que l'étape courante est proposée. */
    private fun choosePlace(then: (Location, String) -> Unit) {
        val et = EditText(this)
        et.hint = "Ex : Gorges 44, Valladolid, Super U 44190 Gétigné…"
        et.setSingleLine()
        AlertDialog.Builder(this)
            .setTitle("Autour de quel lieu ?")
            .setMessage("Saisissez un lieu, idéalement avec son code postal ou " +
                "son département (ex : Gorges 44) :")
            .setView(et)
            .setPositiveButton("Rechercher") { _, _ ->
                val q = et.text.toString().trim()
                if (q.isEmpty()) return@setPositiveButton
                status("Recherche du lieu…")
                thread(name = "geocode-borne") {
                    val gf = geocodeFull(q)
                    handler.post {
                        status("")
                        if (gf == null) {
                            log("Lieu introuvable : « " + q + " ».")
                            alert("Lieu introuvable",
                                "OpenStreetMap n'a pas trouvé « " + q + " ».")
                        } else {
                            val g = gf.first
                            val nom = gf.second
                            log("« " + q + " » localisé → " +
                                String.format(Locale.US, "%.3f, %.3f", g.lat, g.lon) +
                                " (" + nom + ")")
                            val c = Location("lieu")
                            c.latitude = g.lat
                            c.longitude = g.lon
                            AlertDialog.Builder(this)
                                .setTitle("C'est bien ce lieu ?")
                                .setMessage(nom + "\n\n" +
                                    String.format(Locale.US, "%.3f, %.3f", g.lat, g.lon) +
                                    "\n\nContinuer avec ce lieu ?")
                                .setPositiveButton("Continuer") { _, _ ->
                                    then(c, "autour de « " + q.take(30) + " »")
                                }
                                .setNegativeButton("Annuler", null)
                                .show()
                        }
                    }
                }
            }
            .setNegativeButton("Annuler", null)
            .show()
    }

    private fun showBornes() {
        if (bornes.isEmpty()) {
            if (!bornesLoading) {
                log("Base des bornes vide : lancement du téléchargement initial.")
                alert("Bornes", "La base des bornes est vide : téléchargement lancé (1 à 2 min, Wi-Fi conseillé). " +
                    "Retouchez « Bornes recharge » une fois le téléchargement terminé.")
                updateBornes(true)
            } else {
                log("Téléchargement en cours, retouchez « Bornes recharge » dans un instant.")
                alert("Bornes", "Téléchargement en cours... retouchez « Bornes recharge » dans un instant.")
            }
            return
        }
        // Zone de recherche (v0.10) : autour de ma position ou autour de la prochaine étape.
        val nextStage = stages.getOrNull(if (tripActive) stageIdx else 0)
        fun pickOperator(center: Location, zoneLabel: String, radiusKm: Double,
                         minKw: Double) {
            // v0.24 : filtre par opérateur - les réseaux proposés sont
            // ceux réellement présents dans la zone (les plus fréquents).
            val ops = topOperateurs(center, radiusKm, minKw)
            val labels = ArrayList<String>()
            labels.add("Tous les opérateurs (" + ops.size + " réseaux)")
            labels.addAll(ops)
            AlertDialog.Builder(this)
                .setTitle("Réseau / opérateur ?")
                .setItems(labels.toTypedArray()) { _, i ->
                    listBornes(minKw, center, radiusKm, zoneLabel,
                        if (i == 0) null else labels[i])
                }
                .setNegativeButton("Annuler", null)
                .show()
        }
        fun choosePower(center: Location, zoneLabel: String, radiusKm: Double) {
            val filtres = arrayOf("Toutes (≥ 22 kW)", "≥ 50 kW", "≥ 100 kW", "≥ 150 kW")
            AlertDialog.Builder(this)
                .setTitle("Puissance minimale ?")
                .setItems(filtres) { _, i ->
                    val minKw = when (i) {
                        1 -> 50.0
                        2 -> 100.0
                        3 -> 150.0
                        else -> 22.0
                    }
                    pickOperator(center, zoneLabel, radiusKm, minKw)
                }
                .setNegativeButton("Annuler", null)
                .show()
        }
        fun chooseRadius(center: Location, zoneLabel: String) {
            val rayons = arrayOf("5 km", "10 km", "25 km", "50 km")
            AlertDialog.Builder(this)
                .setTitle("Rayon de recherche (" + zoneLabel + ")")
                .setItems(rayons) { _, i ->
                    val r = when (i) {
                        1 -> 10.0
                        2 -> 25.0
                        3 -> 50.0
                        else -> 5.0
                    }
                    choosePower(center, zoneLabel, r)
                }
                .setNegativeButton("Annuler", null)
                .show()
        }
        if (nextStage != null && nextStage.hasPos) {
            val opts = ArrayList<String>()
            val here = lastLoc ?: bestLoc()
            if (here != null) opts.add("Autour de ma position")
            opts.add("Autour de « " + nextStage.name.take(30) + " » (étape " +
                ((if (tripActive) stageIdx else 0) + 1) + ")")
            // v0.30 : retour de la recherche autour d'une ville saisie.
            opts.add("Autour d'un lieu (ville, code postal…)")
            AlertDialog.Builder(this)
                .setTitle("Bornes autour de quoi ?")
                .setItems(opts.toTypedArray()) { _, i ->
                    if (i == 0 && here != null) {
                        chooseRadius(here, "autour de moi")
                    } else if (i == opts.size - 1) {
                        choosePlace { c, l -> chooseRadius(c, l) }
                    } else {
                        val c = Location("stage")
                        c.latitude = nextStage.lat
                        c.longitude = nextStage.lon
                        chooseRadius(c, "autour de « " + nextStage.name.take(30) + " »")
                    }
                }
                .setNegativeButton("Annuler", null)
                .show()
        } else {
            // Dernière position connue même sans GPS actif (utile en garage) - v0.7.1
            val loc = lastLoc ?: bestLoc()
            if (loc == null) {
                // v0.32 : sans position GPS (à l'intérieur, en garage), on
                // propose directement la recherche autour d'un lieu, comme le
                // bouton « Carte bornes... » - avant, le bouton restait bloqué
                // sur un message d'erreur.
                log("Pas encore de position GPS : recherche autour d'un lieu proposée.")
                choosePlace { c, l -> chooseRadius(c, l) }
                return
            }
            // v0.30 : même sans étape, on peut chercher autour d'une ville.
            AlertDialog.Builder(this)
                .setTitle("Bornes autour de quoi ?")
                .setItems(arrayOf("Autour de ma position",
                    "Autour d'un lieu (ville, code postal…)")) { _, i ->
                    if (i == 0) chooseRadius(loc, "autour de moi")
                    else choosePlace { c, l -> chooseRadius(c, l) }
                }
                .setNegativeButton("Annuler", null)
                .show()
        }
    }

    private fun listBornes(minKw: Double, loc: Location, radiusKm: Double, zoneLabel: String,
                           operateur: String? = null) {
        class NearB(val b: Borne, val km: Double)
        val arr: List<NearB> = synchronized(bornes) {
            bornes.filter { it.kw >= minKw &&
                (operateur == null ||
                    (it.enseigne + " " + it.nom).contains(operateur, true)) }
                .map { b ->
                    val d = FloatArray(1)
                    Location.distanceBetween(loc.latitude, loc.longitude, b.lat, b.lon, d)
                    NearB(b, d[0] / 1000.0)
                }
                .filter { it.km <= radiusKm }
                .sortedBy { it.km }
                // v0.31 : les bases IRVE/MITECO contiennent une fiche par
                // CONNECTEUR - une station de 10 connecteurs apparaissait donc
                // 10 fois dans la liste. On ne garde que la plus proche par
                // station (même enseigne + même adresse).
                .distinctBy { it.b.enseigne.trim().lowercase() + "|" +
                    it.b.adresse.trim().lowercase() }
                .take(50)
        }
        if (arr.isEmpty()) {
            log("Aucune borne ≥ " + "%.0f".format(minKw) + " kW à moins de " +
                "%.0f".format(radiusKm) + " km " + zoneLabel + ".")
            alert("Bornes", "Aucune borne ≥ " + "%.0f".format(minKw) + " kW à moins de " +
                "%.0f".format(radiusKm) + " km " + zoneLabel + ".")
            return
        }
        val labels = arr.map {
            val b = it.b
            reseauOf(b) + "\n" +
                "%.1f".format(it.km) + " km - " + "%.0f".format(b.kw) + " kW - " +
                b.adresse.take(38)
        }.toTypedArray()
        AlertDialog.Builder(this)
            .setTitle("Bornes ≥ " + "%.0f".format(minKw) + " kW, " +
                "%.0f".format(radiusKm) + " km max, " + zoneLabel +
                (operateur?.let { " - " + it } ?: ""))
            .setItems(labels) { _, i -> borneAction(arr[i].b, arr[i].km) }
            .setNegativeButton("Fermer", null)
            .show()
    }

    private fun borneAction(b: Borne, km: Double) {
        // v0.33 : les deux actions étaient de simples lignes de texte sous
        // l'adresse (setItems) et passaient inaperçues - elles sont
        // maintenant de vrais boutons bien visibles.
        var dlgRef: android.app.Dialog? = null
        val box = LinearLayout(this)
        box.orientation = LinearLayout.VERTICAL
        val tv = TextView(this)
        tv.text = "Adresse : " + b.adresse + "\n" +
            "Puissance max : " + "%.0f".format(b.kw) + " kW\n" +
            "Distance : " + "%.1f".format(km) + " km (à vol d'oiseau)"
        tv.setPadding(dp(18), dp(14), dp(18), dp(6))
        box.addView(tv)
        val ins = Button(this)
        ins.text = "Insérer dans l'itinéraire"
        ins.isAllCaps = false
        ins.setOnClickListener {
            insertBorne(b, km)
            dlgRef?.dismiss()
        }
        box.addView(ins)
        val gmaps = Button(this)
        gmaps.text = "Ouvrir dans Google Maps"
        gmaps.isAllCaps = false
        gmaps.setOnClickListener {
            try {
                startActivity(
                    Intent(
                        Intent.ACTION_VIEW,
                        Uri.parse("https://www.google.com/maps/search/?api=1&query=" + b.lat + "," + b.lon)
                    )
                )
            } catch (e: Exception) {
                log("Maps indisponible : " + e.message)
            }
            dlgRef?.dismiss()
        }
        box.addView(gmaps)
        // v0.42 : lien vers le site/app de l'opérateur (occupation des
        // bornes en temps réel - les données OCPI sont B2B payantes, la
        // source gratuite fiable reste l'opérateur lui-même).
        val liveUrl = operatorLiveUrl(b.enseigne)
        if (liveUrl != null) {
            val live = Button(this)
            live.text = "Voir l'occupation en direct"
            live.isAllCaps = false
            live.setOnClickListener {
                openLive(b.enseigne)
                dlgRef?.dismiss()
            }
            box.addView(live)
        }
        val dlg = AlertDialog.Builder(this)
            .setTitle(b.enseigne)
            .setView(box)
            .setNegativeButton("Fermer", null)
            .create()
        dlgRef = dlg
        dlg.show()
    }

    private fun insertBorne(b: Borne, km: Double) {
        val name = ("Borne " + b.enseigne + " - " + b.adresse).replace(';', ' ').replace('\n', ' ')
        // Distance routière réelle depuis la position actuelle si possible (v0.10),
        // sinon estimation depuis l'étape en cours.
        val here = lastLoc ?: bestLoc()
        val stageKm = when {
            here != null -> roadKm(Geo(here.latitude, here.longitude), Geo(b.lat, b.lon))
            tripActive && stageIdx < stages.size ->
                (stages[stageIdx].km - (tripKm - stageStartKm)) + km
            else -> km
        }
        // v0.34 : pendant un trajet, la borne devient la prochaine étape
        // (comme avant). HORS trajet, elle s'ajoute à la FIN de l'itinéraire :
        // avant elle était toujours insérée en tête (étape 1), donc deux
        // bornes choisies Valladolid puis Bragança se retrouvaient dans
        // l'ordre inverse (Bragança avant Valladolid) et Google Maps
        // construisait un itinéraire aberrant.
        // v0.40 : HORS trajet, on insère la borne à la position qui MINIMISE
        // LE DÉTOUR le long de l'itinéraire (à vol d'oiseau, calcul local
        // instantané). Avant (v0.34) elle allait toujours à la FIN, même si
        // elle se trouvait sur la route bien avant les dernières étapes.
        val pos = if (tripActive) {
            stageIdx.coerceAtMost(stages.size)
        } else {
            val origin = here?.let { Geo(it.latitude, it.longitude) }
            var best = stages.size
            var bestCost = Double.MAX_VALUE
            for (i in 0..stages.size) {
                val prev: Geo? = when {
                    i > 0 -> stages[i - 1].let { if (it.hasPos) Geo(it.lat, it.lon) else null }
                    else -> origin
                }
                val next: Geo? = stages.getOrNull(i)
                    ?.let { if (it.hasPos) Geo(it.lat, it.lon) else null }
                val cost = when {
                    prev != null && next != null ->
                        distKm(prev.lat, prev.lon, b.lat, b.lon) +
                            distKm(b.lat, b.lon, next.lat, next.lon) -
                            distKm(prev.lat, prev.lon, next.lat, next.lon)
                    prev != null -> distKm(prev.lat, prev.lon, b.lat, b.lon)
                    next != null -> distKm(b.lat, b.lon, next.lat, next.lon)
                    else -> 0.0
                }
                if (cost < bestCost) { bestCost = cost; best = i }
            }
            best
        }
        stages.add(pos, Stage(name, stageKm, b.lat, b.lon))
        log("Borne insérée comme étape " + (pos + 1) + " sur " + stages.size + " : " + name +
            " (" + fmtKm(stageKm) + " km, distance routière).")
        refreshRoute()
    }

    // ------------------------------------------- Carte des bornes (v0.13)

    /** Supprime une étape de l'itinéraire (v0.14), ex. une borne insérée. */
    private fun removeStage() {
        if (stages.isEmpty()) {
            alert("Itinéraire", "Aucune étape à supprimer.")
            return
        }
        val labels = stages.mapIndexed { i, s ->
            (i + 1).toString() + ". " + s.name.take(45)
        }.toTypedArray()
        var sel = -1
        AlertDialog.Builder(this)
            .setTitle("Supprimer quelle étape ?")
            .setSingleChoiceItems(labels, -1) { _, w -> sel = w }
            .setPositiveButton("Supprimer") { _, _ ->
                if (sel >= 0 && sel < stages.size) {
                    val s = stages.removeAt(sel)
                    if (stageIdx > sel) stageIdx--
                    if (stageIdx >= stages.size) tripActive = false
                    log("Étape supprimée : " + s.name)
                    refreshRoute()
                    refreshOverlay()
                }
            }
            .setNegativeButton("Annuler", null)
            .show()
    }

    /**
     * Badge / carte de recharge correspondant à une borne (null si aucun des
     * réseaux de l'utilisateur). Le rapprochement se fait sur le nom de
     * l'enseigne/enseigne de la base IRVE.
     */
    /** v0.27 : nom de réseau COURT d'une borne (Tesla, Ionity, Zunder...),
     * reconnu à partir de l'enseigne/nom brut des bases (qui contiennent des
     * noms juridiques : « IONITY SAS », « Espagne - IBERDROLA CLIENTES »...).
     * Utilisé pour le filtre par opérateur et l'affichage, France/Espagne/
     * Portugal confondus. */
    private fun reseauOf(b: Borne): String {
        val t = (b.enseigne + " " + b.nom).lowercase(Locale.ROOT)
        val reseaux = listOf(
            "ionity" to "Ionity", "tesla" to "Tesla", "zunder" to "Zunder",
            "electra" to "Electra", "iberdrola" to "Iberdrola", "endesa" to "Endesa",
            "repsol" to "Repsol", "wenea" to "Wenea", "atlante" to "Atlante",
            "totalenergies" to "TotalEnergies", "shell" to "Shell Recharge",
            "fastned" to "Fastned", "allego" to "Allego", "izivia" to "Izivia",
            "freshmile" to "Freshmile", "engie" to "Engie", "edf" to "EDF",
            "edp" to "EDP", "galp" to "Galp", "mobie" to "Mobi.E",
            "chargepoint" to "ChargePoint", "interparking" to "Interparking",
            "carrefour" to "Carrefour", "leclerc" to "Leclerc", "lidl" to "Lidl",
            "porsche" to "Porsche", "audi" to "Audi", "stellantis" to "Stellantis",
            "renault" to "Renault", "mobilize" to "Mobilize", "bouygues" to "Bouygues",
            "evy1" to "Evy1", "gireve" to "Gireve")
        for ((mot, nom) in reseaux) if (t.contains(mot)) return nom
        // Repli : l'enseigne brute, débarrassée du préfixe pays.
        var s = b.enseigne.removePrefix("Espagne - ").trim()
        if (s.isEmpty()) s = b.nom.trim()
        if (s.isEmpty()) return "Réseau ?"
        return s.take(24)
    }

    /** Réseau court d'une borne, pour le filtre et l'affichage (v0.27). */
    private fun operateurOf(b: Borne): String = reseauOf(b)

    /**
     * v0.24 : réseaux les plus fréquents dans la zone (puissance et rayon
     * déjà choisis), pour proposer le filtre par opérateur. Le plus fréquent
     * en premier, 12 maximum. Remplace l'ancien système de « cartes de
     * recharge » qui ne colorait que les points sans filtrer.
     */
    private fun topOperateurs(loc: Location, radiusKm: Double, minKw: Double): List<String> {
        val counts = LinkedHashMap<String, Int>()
        synchronized(bornes) {
            for (b in bornes) {
                if (b.kw < minKw) continue
                val d = FloatArray(1)
                Location.distanceBetween(loc.latitude, loc.longitude, b.lat, b.lon, d)
                if (d[0] / 1000.0 > radiusKm) continue
                val op = operateurOf(b)
                counts[op] = (counts[op] ?: 0) + 1
            }
        }
        return counts.entries.sortedByDescending { it.value }.take(12).map { it.key }
    }

    /** Échappe une chaîne pour l'insérer dans le JavaScript de la carte. */
    private fun escapeJs(s: String): String =
        s.replace("\\", "\\\\").replace("\"", "\\\"").replace("'", "\\'")
            .replace("\n", " ").replace("\r", " ").replace("<", "‹")

    /** Carte des bornes : choix zone → rayon → puissance, puis carte interactive. */
    private fun showBornesMap() {
        if (bornes.isEmpty()) {
            alert("Bornes", "La base des bornes est vide : touchez d'abord « Mettre à jour bornes ».")
            return
        }
        val nextStage = stages.getOrNull(if (tripActive) stageIdx else 0)
        val here = lastLoc ?: bestLoc()
        fun pickOperator(center: Location, zoneLabel: String, radiusKm: Double,
                         minKw: Double) {
            // v0.24 : filtre par opérateur - réseaux réellement présents
            // dans la zone (les plus fréquents d'abord).
            val ops = topOperateurs(center, radiusKm, minKw)
            val labels = ArrayList<String>()
            labels.add("Tous les opérateurs (" + ops.size + " réseaux)")
            labels.addAll(ops)
            AlertDialog.Builder(this)
                .setTitle("Réseau / opérateur ?")
                .setItems(labels.toTypedArray()) { _, i ->
                    openBornesMap(minKw, center, radiusKm, zoneLabel,
                        if (i == 0) null else labels[i])
                }
                .setNegativeButton("Annuler", null)
                .show()
        }
        fun pickPower(center: Location, zoneLabel: String, radiusKm: Double) {
            val filtres = arrayOf("Toutes (≥ 22 kW)", "≥ 50 kW", "≥ 100 kW", "≥ 150 kW")
            AlertDialog.Builder(this)
                .setTitle("Puissance minimale ?")
                .setItems(filtres) { _, i ->
                    val minKw = when (i) {
                        1 -> 50.0
                        2 -> 100.0
                        3 -> 150.0
                        else -> 22.0
                    }
                    pickOperator(center, zoneLabel, radiusKm, minKw)
                }
                .setNegativeButton("Annuler", null)
                .show()
        }
        fun pickRadius(center: Location, zoneLabel: String) {
            AlertDialog.Builder(this)
                .setTitle("Rayon de recherche (" + zoneLabel + ")")
                .setItems(arrayOf("5 km", "10 km", "25 km", "50 km")) { _, i ->
                    val r = when (i) {
                        1 -> 10.0
                        2 -> 25.0
                        3 -> 50.0
                        else -> 5.0
                    }
                    pickPower(center, zoneLabel, r)
                }
                .setNegativeButton("Annuler", null)
                .show()
        }
        if (nextStage != null && nextStage.hasPos) {
            // v0.15.1 : l'étape est proposée même sans position GPS (utile
            // à l'intérieur, sans fixation GPS).
            val opts = ArrayList<String>()
            if (here != null) opts.add("Autour de ma position")
            opts.add("Autour de « " + nextStage.name.take(30) + " »")
            // v0.30 : retour de la recherche autour d'une ville saisie.
            opts.add("Autour d'un lieu (ville, code postal…)")
            AlertDialog.Builder(this)
                .setTitle("Bornes autour de quoi ?")
                .setItems(opts.toTypedArray()) { _, i ->
                    if (i == 0 && here != null) {
                        pickRadius(here, "autour de moi")
                    } else if (i == opts.size - 1) {
                        choosePlace { c, l -> pickRadius(c, l) }
                    } else {
                        val c = Location("stage")
                        c.latitude = nextStage.lat
                        c.longitude = nextStage.lon
                        pickRadius(c, "autour de « " + nextStage.name.take(30) + " »")
                    }
                }
                .setNegativeButton("Annuler", null)
                .show()
        } else if (here != null) {
            // v0.30 : même sans étape, on peut chercher autour d'une ville.
            AlertDialog.Builder(this)
                .setTitle("Bornes autour de quoi ?")
                .setItems(arrayOf("Autour de ma position",
                    "Autour d'un lieu (ville, code postal…)")) { _, i ->
                    if (i == 0) pickRadius(here, "autour de moi")
                    else choosePlace { c, l -> pickRadius(c, l) }
                }
                .setNegativeButton("Annuler", null)
                .show()
        } else {
            // v0.15.1 : sans position et sans étape localisée, on propose de
            // saisir un lieu (ville, adresse) recherché sur OpenStreetMap.
            val et = EditText(this)
            et.hint = "Ex : Gorges 44, Super U 44190 Gétigné…"
            et.setSingleLine()
            AlertDialog.Builder(this)
                .setTitle("Autour de quel lieu ?")
                .setMessage("Aucune position GPS disponible pour l'instant " +
                    "(normal à l'intérieur). Saisissez un lieu, idéalement avec son " +
                    "code postal ou son département (ex : Gorges 44) :")
                .setView(et)
                .setPositiveButton("Rechercher") { _, _ ->
                    val q = et.text.toString().trim()
                    if (q.isEmpty()) return@setPositiveButton
                    status("Recherche du lieu…")
                    thread(name = "geocode-borne") {
                        val gf = geocodeFull(q)
                        handler.post {
                            status("")
                            if (gf == null) {
                                log("Lieu introuvable : « " + q + " ».")
                                alert("Lieu introuvable",
                                    "OpenStreetMap n'a pas trouvé « " + q + " ».")
                            } else {
                                val g = gf.first
                                val nom = gf.second
                                log("« " + q + " » localisé → " +
                                    String.format(Locale.US, "%.3f, %.3f", g.lat, g.lon) +
                                    " (" + nom + ")")
                                // v0.16 : confirmation - le lieu géocodé peut être un
                                // homonyme au mauvais endroit (cf. Gorges/Amiens).
                                val c = Location("lieu")
                                c.latitude = g.lat
                                c.longitude = g.lon
                                AlertDialog.Builder(this)
                                    .setTitle("C'est bien ce lieu ?")
                                    .setMessage(nom + "\n\n" +
                                        String.format(Locale.US, "%.3f, %.3f", g.lat, g.lon) +
                                        "\n\nContinuer avec ce lieu ?")
                                    .setPositiveButton("Continuer") { _, _ ->
                                        pickRadius(c, "autour de « " + q.take(30) + " »")
                                    }
                                    .setNegativeButton("Annuler", null)
                                    .show()
                            }
                        }
                    }
                }
                .setNegativeButton("Annuler", null)
                .show()
        }
    }

    /** Ouvre la carte interactive des bornes (OpenStreetMap + Leaflet). */
    private fun openBornesMap(minKw: Double, loc: Location, radiusKm: Double, zoneLabel: String,
                              operateur: String? = null) {
        class NearB(val b: Borne, val km: Double)
        val arr: List<NearB> = synchronized(bornes) {
            bornes.filter { it.kw >= minKw &&
                (operateur == null ||
                    (it.enseigne + " " + it.nom).contains(operateur, true)) }
                .map { b ->
                    val d = FloatArray(1)
                    Location.distanceBetween(loc.latitude, loc.longitude, b.lat, b.lon, d)
                    NearB(b, d[0] / 1000.0)
                }
                .filter { it.km <= radiusKm }
                .sortedBy { it.km }
                // v0.31 : idem listBornes - une seule pastille par station
                // sur la carte (un marqueur par connecteur superposait 10
                // points au même endroit).
                .distinctBy { it.b.enseigne.trim().lowercase() + "|" +
                    it.b.adresse.trim().lowercase() }
                .take(150)
        }
        if (arr.isEmpty()) {
            log("Carte : aucune borne ≥ " + "%.0f".format(minKw) + " kW à moins de " +
                "%.0f".format(radiusKm) + " km " + zoneLabel + ".")
            alert("Bornes", "Aucune borne ≥ " + "%.0f".format(minKw) +
                " kW à moins de " + "%.0f".format(radiusKm) + " km " + zoneLabel + ".")
            return
        }
        val data = StringBuilder("[")
        for (i in arr.indices) {
            val n = arr[i]
            if (i > 0) data.append(",")
            data.append("{lat:").append(fmtD(n.b.lat))
                .append(",lon:").append(fmtD(n.b.lon))
                // v0.15.2 : Locale.US obligatoire - en français, "%.1f" donne
                // "4,5" (virgule) et cassait le JavaScript de la carte
                // (Uncaught SyntaxError: Unexpected number).
                .append(",km:").append(String.format(Locale.US, "%.1f", n.km))
                .append(",kw:").append(String.format(Locale.US, "%.0f", n.b.kw))
                .append(",nom:\"").append(escapeJs(reseauOf(n.b))).append("\"")
                .append(",adresse:\"").append(escapeJs(n.b.adresse)).append("\"")
                // v0.42 : site de l'opérateur (occupation en direct), vide si inconnu.
                .append(",site:\"").append(escapeJs(operatorLiveUrl(n.b.enseigne) ?: "")).append("\"}")
        }
        data.append("]")
        // v0.14 : l'itinéraire et la position actuelle sont dessinés sur la carte.
        val route = StringBuilder("[")
        var firstPt = true
        for (s in stages) {
            if (s.hasPos) {
                if (!firstPt) route.append(",")
                firstPt = false
                route.append("[").append(fmtD(s.lat)).append(",").append(fmtD(s.lon)).append("]")
            }
        }
        route.append("]")
        val me = lastLoc
        val meJs = if (me != null) "[" + fmtD(me.latitude) + "," + fmtD(me.longitude) + "]" else "null"
        val html = MAP_HTML
            .replace("__DATA__", data.toString())
            .replace("__ROUTE__", route.toString())
            .replace("__ME__", meJs)
            .replace("__LAT__", fmtD(loc.latitude))
            .replace("__LON__", fmtD(loc.longitude))
        var dlgRef: android.app.Dialog? = null
        val wv = WebView(this)
        wv.settings.javaScriptEnabled = true
        wv.settings.domStorageEnabled = true
        // v0.15.5 : identité de l'app pour le serveur de tuiles OpenStreetMap
        // - sans User-Agent identifiable, il répond « 418 Blocked ».
        wv.settings.userAgentString =
            "MG4Link/0.49 (Android; https://github.com/Moup1957/MG4Link)"
        // v0.15.4 : la page HTML n'apparaissait JAMAIS dans la boîte (écran
        // vide, même le texte « Chargement de la carte… » était absent) ->
        // suivi du chargement dans le journal pour distinguer un échec de
        // rendu d'un échec réseau.
        wv.webViewClient = object : WebViewClient() {
            override fun onPageStarted(
                view: WebView?,
                url: String?,
                favicon: android.graphics.Bitmap?
            ) {
                log("Carte : page en cours de chargement (" + (url ?: "?") + ").")
            }

            override fun onPageFinished(
                view: WebView?,
                url: String?
            ) {
                log("Carte : page chargée, rendu en cours.")
            }

            override fun onReceivedError(
                view: WebView?,
                request: android.webkit.WebResourceRequest?,
                error: android.webkit.WebResourceError?
            ) {
                try {
                    log("Carte : ressource en échec : " + error?.description +
                        " (" + request?.url + ")")
                } catch (e: Exception) { }
            }
        }
        wv.webChromeClient = object : WebChromeClient() {
            override fun onConsoleMessage(cm: ConsoleMessage): Boolean {
                log("Carte JS : " + cm.message() + " (" + cm.sourceId() + ":" +
                    cm.lineNumber() + ")")
                return true
            }
        }
        wv.addJavascriptInterface(object {
            @JavascriptInterface
            fun insertAt(i: Int) {
                val n = arr.getOrNull(i) ?: return
                handler.post {
                    insertBorne(n.b, n.km)
                    dlgRef?.dismiss()
                }
            }

            @JavascriptInterface
            fun openUrl(i: Int) {
                val n = arr.getOrNull(i) ?: return
                // v0.44 : appli de l'opérateur si installée, sinon son site.
                handler.post { openLive(n.b.enseigne) }
            }

            @JavascriptInterface
            fun jsErr(msg: String) {
                log("Erreur carte JS : " + msg)
            }
        }, "Android")
        // v0.15.4 : vrai Dialog (plein écran) construit manuellement - la
        // boîte AlertDialog laissait la WebView invisible/à 0 pixel malgré
        // ses paramètres de taille (écran gris vide constaté en test).
        val dlg = android.app.Dialog(this)
        dlg.requestWindowFeature(Window.FEATURE_NO_TITLE)
        val box = LinearLayout(this)
        box.orientation = LinearLayout.VERTICAL
        val title = TextView(this)
        title.text = "Bornes ≥ " + "%.0f".format(minKw) + " kW" +
            (operateur?.let { " - " + it } ?: "") + ", " + arr.size + " affichées"
        title.textSize = 17f
        title.typeface = Typeface.DEFAULT_BOLD
        title.setPadding(dp(14), dp(12), dp(14), dp(6))
        box.addView(title)
        box.addView(wv, LinearLayout.LayoutParams(
            ViewGroup.LayoutParams.MATCH_PARENT, dp(440)))
        val close = Button(this)
        close.text = "Fermer"
        close.setOnClickListener { dlg.dismiss() }
        box.addView(close)
        dlgRef = dlg
        dlg.setContentView(box)
        dlg.show()
        try {
            dlg.window?.setLayout(
                WindowManager.LayoutParams.MATCH_PARENT,
                WindowManager.LayoutParams.WRAP_CONTENT)
        } catch (e: Exception) { }
        log("Carte : envoi de la page (" + html.length + " caractères)...")
        wv.loadDataWithBaseURL("https://openstreetmap.org/", html, "text/html", "utf-8", null)
        log("Carte des bornes ouverte : " + arr.size + " bornes ≥ " +
            "%.0f".format(minKw) + " kW à moins de " + "%.0f".format(radiusKm) +
            " km " + zoneLabel + ".")
    }

    /** Modèle HTML de la carte (OpenStreetMap + Leaflet, badge par couleur). */
    private val MAP_HTML = """<!DOCTYPE html>
<html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/leaflet@1.9.4/dist/leaflet.css"/>
<script src="https://cdn.jsdelivr.net/npm/leaflet@1.9.4/dist/leaflet.js"></script>
<style>html,body{margin:0;padding:0;height:100%;font-family:sans-serif}
#map{height:100%}.lg{position:absolute;right:8px;bottom:8px;z-index:1000;background:#fff;
padding:6px 8px;border:1px solid #888;border-radius:6px;font-size:11px;line-height:1.6}
.dot{display:inline-block;width:10px;height:10px;border-radius:5px;margin-right:4px}
#err{position:absolute;left:8px;top:8px;z-index:1000;background:#fff;
padding:6px 8px;border:1px solid #888;border-radius:6px;font-size:12px}</style>
</head><body><div id="map"></div>
<div id="err">Chargement de la carte…</div>
<div class="lg" id="lg"></div>
<script>
// v0.15 : toute erreur JavaScript est remontée dans le journal de l'app.
window.onerror = function(m) { Android.jsErr('' + m); return true; };
var DATA = __DATA__;
// v0.24 : la couleur du point dépend de sa puissance (les anciennes
// « cartes de recharge » ne coloraient que les points, sans filtrer).
var TIERS = [["≥ 150 kW","#e01a1a"],["50 à 149 kW","#f5a623"],["22 à 49 kW","#7b1fa2"]];
function colFor(kw) { return kw >= 150 ? TIERS[0][1] : (kw >= 50 ? TIERS[1][1] : TIERS[2][1]); }
var map = L.map('map');
// v0.15.9 : tuiles Esri World Street (sans clé) - CARTO affichait
// « API KEY REQUIRED » (clé obligatoire) et le serveur OSM bloquait.
var base = L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Street_Map/MapServer/tile/{z}/{y}/{x}',
 {maxZoom:19, attribution:'&copy; Esri, OpenStreetMap'});
base.addTo(map);
var pts = [];
DATA.forEach(function(d, i) {
  var col = colFor(d.kw);
  var m = L.circleMarker([d.lat, d.lon],
    {radius:9, color:'#000', weight:1, fillColor:col, fillOpacity:0.95}).addTo(map);
  m.bindPopup(
    '<b>' + d.nom + '</b><br>' + d.kw + ' kW - à ' + d.km + ' km<br>' +
    '<small>' + d.adresse + '</small>' +
    '<br><button style="margin-top:6px" onclick="Android.insertAt(' + i + ')">' +
    'Insérer comme étape</button>' +
    (d.site ? '<br><button style="margin-top:6px" onclick="Android.openUrl(' + i + ')">' +
    'Occupation en direct</button>' : ''));
  pts.push([d.lat, d.lon]);
});
// v0.14 : itinéraire (trait bleu) + position actuelle (point bleu)
var ROUTE = __ROUTE__;
if (ROUTE.length > 1) {
  L.polyline(ROUTE, {color: '#0b57d0', weight: 4, opacity: 0.75}).addTo(map);
  ROUTE.forEach(function(p) { pts.push(p); });
}
var ME = __ME__;
if (ME) {
  L.circleMarker(ME, {radius: 11, color: '#fff', weight: 3,
    fillColor: '#1a73e8', fillOpacity: 1}).addTo(map).bindPopup('Vous êtes ici');
  pts.push(ME);
}
var lg = document.getElementById('lg');
var h = '';
for (var t = 0; t < TIERS.length; t++) { h += '<div><span class="dot" style="background:' +
  TIERS[t][1] + '"></span>' + TIERS[t][0] + '</div>'; }
lg.innerHTML = h;
if (pts.length) { map.fitBounds(pts, {padding: [25, 25]}); }
else { map.setView([__LAT__, __LON__], 11); }
document.getElementById('err').style.display = 'none';
</script></body></html>"""
}
