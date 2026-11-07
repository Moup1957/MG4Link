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
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
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
        statusTv.text = "MG4 Link v0.32 - non connecté"
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

        log("MG4 Link v0.32 démarré (Android ${Build.VERSION.RELEASE}, SDK ${Build.VERSION.SDK_INT})")
        val prefs = getSharedPreferences("mg4link", Context.MODE_PRIVATE)
        val savedConso = pref
