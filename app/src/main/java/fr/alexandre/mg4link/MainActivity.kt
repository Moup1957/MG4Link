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

/** Statut de disponibilité temps réel d'une borne / station (v0.50). */
enum class DispoStatus(val code: Int, val label: String, val dot: String, val hex: String) {
    LIBRE(1, "Libre", "\uD83D\uDFE2", "#2e7d32"),
    OCCUPE(2, "Occupé", "\uD83D\uDFE0", "#f57c00"),
    HORS_SERVICE(3, "Hors service", "\uD83D\uDD34", "#d32f2f"),
    INCONNU(0, "Inconnu", "\u26AA", "#9e9e9e")
}

/** Borne de recharge issue de la base IRVE (avec idStation / idPdc pour rapprochement dynamique v0.50). */
class Borne(
    val lat: Double,
    val lon: Double,
    val kw: Double,
    val enseigne: String,
    val nom: String,
    val adresse: String,
    val idStation: String = "",
    val idPdc: String = ""
)

/** Point de charge dynamique issu du flux IRVE temps réel (v0.50). */
class DynPdc(
    val idPdc: String,
    val idStation: String,
    val lat: Double,
    val lon: Double,
    val status: DispoStatus
)

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

    @Volatile
    private var remainKm = -1.0

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

    // --------------------------------------------------- Bornes IRVE v0.7 + Dispo v0.50
    private val bornes = ArrayList<Borne>()

    @Volatile
    private var bornesLoading = false

    @Volatile
    private var dispoLoading = false

    // Index temps réel IRVE dynamique (v0.50)
    private val dynByPdcId = HashMap<String, DispoStatus>()
    private val dynByStationId = HashMap<String, MutableList<DispoStatus>>()
    private val dynGeoList = ArrayList<DynPdc>()

    @Volatile
    private var dynTotalPdc = 0

    @Volatile
    private var dynLastUpdateMs = 0L

    // v0.41 : radars / zones de danger
    private val radars = ArrayList<Radar>()
    @Volatile
    private var radarInfo = ""
    @Volatile
    private var lastRadarKey = ""
    @Volatile
    private var lastRadarLevel = 0
    @Volatile
    private var lastRadarCheck = 0L
    @Volatile
    private var lastRadarBeep = 0L

    // v0.46 : compteur de recharges DC
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
        b.textSize = 12f
        b.minHeight = 0
        b.minWidth = 0
        b.setPadding(dp(8), dp(5), dp(8), dp(5))
        b.setTextColor(Color.WHITE)
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
        root.setBackgroundColor(Color.BLACK)
        root.setPadding(dp(8), dp(28), dp(8), dp(8))

        statusTv = TextView(this)
        statusTv.textSize = 17f
        statusTv.typeface = Typeface.DEFAULT_BOLD
        statusTv.setTextColor(Color.WHITE)
        statusTv.text = "MG4 Link v0.51 - non connecté"
        root.addView(statusTv)

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
        for (t in tabTitles) {
            val b = Button(this)
            b.text = t
            b.isAllCaps = false
            b.textSize = 13f
            b.minHeight = 0
            b.setPadding(dp(4), dp(6), dp(4), dp(6))
            b.setTextColor(Color.WHITE)
            b.background = framedBg(0xFF424242.toInt())
            tabBtns.add(b)
        }
        val tabRow = LinearLayout(this)
        tabRow.orientation = LinearLayout.HORIZONTAL
        for (b in tabBtns) {
            tabRow.addView(b, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))
        }
        root.addView(tabRow)

        val containers = ArrayList<View>()
        for (i in contents.indices) {
            if (i == 0 || i == 3) {
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
                tabBtns[j].background = framedBg(
                    if (j == i) 0xFF2E7D32.toInt() else 0xFF424242.toInt())
                tabBtns[j].setTextColor(Color.WHITE)
                tabBtns[j].setTypeface(null, if (j == i) Typeface.BOLD else Typeface.NORMAL)
            }
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
        liveSwitch.textSize = 12f
        liveSwitch.setTextColor(Color.WHITE)
        liveSwitch.setOnCheckedChangeListener { _, on -> setLive(on) }
        secConn.addView(
            row(
                makeButton("Tests de base") { testsBase() },
                makeButton("Tests batterie") { testsBatterie() }
            )
        )
        secConn.addView(row(makeButton("SOH batterie…") { readSoh() }))
        secConn.addView(liveSwitch)

        secConn.addView(row(makeButton("Charge affichée…") { askSoc() }))

        liveTv = TextView(this)
        liveTv.typeface = Typeface.MONOSPACE
        liveTv.textSize = 12f
        liveTv.setTextColor(Color.WHITE)
        liveTv.setPadding(0, dp(3), 0, dp(3))
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

        // ----- Onglet BORNES (v0.51) -----
        secBornes.addView(
            row(
                makeButton("Bornes recharge") { showBornes() },
                makeButton("Mettre à jour bornes") { updateBornes(true) }
            )
        )

        secBornes.addView(
            row(
                makeButton("Dispo bornes") { updateDispoBornes(true, null) }
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

        log("MG4 Link v0.51 démarré (Android ${Build.VERSION.RELEASE}, SDK ${Build.VERSION.SDK_INT})")
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
        thread(name = "watchdog") {
            while (true) {
                Thread.sleep(5000)
                if (liveOn && ready && System.currentTimeMillis() - lastLiveTick > 15000) {
                    if (liveThread?.isAlive == true) {
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
            if (stageReached()) finishStage(false)
            refreshRoute()
            refreshOverlay()
            checkRadars(loc)
        }

        override fun onProviderEnabled(provider: String) {}
        override fun onProviderDisabled(provider: String) {}
        override fun onStatusChanged(provider: String?, status: Int, extras: Bundle) {}
    }

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
        liveGen++
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

        override fun onCharacteristicChanged(
            g: BluetoothGatt,
            characteristic: BluetoothGattCharacteristic,
            value: ByteArray
        ) {
            elm.onData(value)
        }

        @Deprecated("Deprecated in Java")
        override fun onCharacteristicChanged(g: BluetoothGatt, characteristic: BluetoothGattCharacteristic) {
            if (Build.VERSION.SDK_INT < 33) {
                val v = characteristic.value
                if (v != null) elm.onData(v)
            }
        }
    }

    // --------------------------------------------------------------- ELM327

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
                log("Initialisation : $failed commande(s) en échec, nouvelle tentative dans 1 s...")
                Thread.sleep(1000)
                initElm(true)
                return
            }
            ready = true
            if (liveSwitch.isChecked) setLive(true)
            else handler.post { liveSwitch.isChecked = true }
            if (failed == 0) {
                status("Prêt - dongle connecté")
                log("Initialisation terminée.")
                if (sohPct < 0) readSoh()
            } else {
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

    private fun startLiveThread() {
        val myGen = ++liveGen
        liveThread = thread(name = "live") {
            var noData = 0
            while (liveOn && myGen == liveGen) {
                try {
                    if (ready && needElmReinit) {
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

    private fun readSoh() {
        if (!ready) {
            log("Dongle pas prêt : connectez-vous d'abord.")
            return
        }
        thread(name = "soh") {
            var found = false
            for ((req, resp) in listOf("7DF" to "7ED", "7E4" to "7EC", "7E6" to "7EE")) {
                log("SOH : interrogation du calculateur batterie (" + req + ")...")
                elm.request("ATSH " + req, 3000)
                elm.request("ATCRA " + resp, 3000)
                val r = elm.request("22B061", 6000)
                log("> 22B061 (" + req + ")\n" + r)
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
                Thread.sleep(1100)
            }
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

    private fun roadKm(a: Geo, b: Geo): Double =
        tryRoadKm(a, b) ?: distKm(a.lat, a.lon, b.lat, b.lon) * 1.35

    private fun applyStages(list: List<Stage>, fails: List<String>) {
        stages.clear()
        stages.addAll(list)
        tripActive = false
        stageIdx = 0
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

    private fun distKm(lat1: Double, lon1: Double, lat2: Double, lon2: Double): Double {
        val r = 6371.0
        val dLat = Math.toRadians(lat2 - lat1)
        val dLon = Math.toRadians(lon2 - lon1)
        val a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
            Math.cos(Math.toRadians(lat1)) * Math.cos(Math.toRadians(lat2)) *
            Math.sin(dLon / 2) * Math.sin(dLon / 2)
        return 2 * r * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a))
    }

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
