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
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
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
            if (!g.writeCharacteristic(c)) return "ERREUR : écriture refusée"
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

    private fun makeButton(label: String, onClick: () -> Unit): Button {
        val b = Button(this)
        b.text = label
        b.isAllCaps = false
        b.setOnClickListener { onClick() }
        return b
    }

    private fun row(vararg views: View): LinearLayout {
        val r = LinearLayout(this)
        r.orientation = LinearLayout.HORIZONTAL
        for (v in views) {
            r.addView(v, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))
        }
        return r
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)

        val root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        root.setPadding(dp(10), dp(28), dp(10), dp(10))

        statusTv = TextView(this)
        statusTv.textSize = 17f
        statusTv.typeface = Typeface.DEFAULT_BOLD
        statusTv.text = "MG4 Link v0.9 - non connecté"
        root.addView(statusTv)

        root.addView(
            row(
                makeButton("Scanner et connecter") { startScan() },
                makeButton("Déconnecter") {
                    disconnect()
                    status("Déconnecté")
                    log("Déconnexion demandée")
                }
            )
        )

        val liveSwitch = Switch(this)
        liveSwitch.text = "Lecture live"
        liveSwitch.setOnCheckedChangeListener { _, on -> setLive(on) }
        root.addView(
            row(
                makeButton("Tests de base") { testsBase() },
                makeButton("Tests batterie") { testsBatterie() }
            )
        )
        root.addView(liveSwitch)

        root.addView(row(makeButton("Charge affichée…") { askSoc() }))

        liveTv = TextView(this)
        liveTv.typeface = Typeface.MONOSPACE
        liveTv.textSize = 13f
        liveTv.setPadding(0, dp(8), 0, dp(8))
        root.addView(liveTv)
        refreshLive()

        root.addView(
            row(
                makeButton("Itinéraire…") { editStages() },
                makeButton("Démarrer le trajet") { startTrip() },
                makeButton("Étape suivante") { nextStage() }
            )
        )

        root.addView(
            row(
                makeButton("Itinéraire dans Maps") { openInMaps() },
                makeButton("Fenêtre flottante") { toggleOverlay() }
            )
        )

        root.addView(
            row(
                makeButton("Sauver itinéraire") { saveItinerary() },
                makeButton("Charger itinéraire") { loadItinerary() },
                makeButton("Calibrage…") { calibrate() }
            )
        )

        root.addView(
            row(
                makeButton("Bornes recharge") { showBornes() },
                makeButton("Mettre à jour bornes") { updateBornes(true) }
            )
        )

        routeTv = TextView(this)
        routeTv.typeface = Typeface.MONOSPACE
        routeTv.textSize = 12f
        routeTv.setPadding(0, dp(4), 0, dp(4))
        root.addView(routeTv)
        refreshRoute()

        cmdEt = EditText(this)
        cmdEt.hint = "Commande, ex. 010D (lecture seule !)"
        cmdEt.setSingleLine(true)
        val cmdRow = LinearLayout(this)
        cmdRow.orientation = LinearLayout.HORIZONTAL
        cmdRow.addView(cmdEt, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 3f))
        cmdRow.addView(
            makeButton("Envoyer") { sendManual() },
            LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1.4f)
        )
        root.addView(cmdRow)

        root.addView(
            row(
                makeButton("Copier") { copyLog() },
                makeButton("Partager") { shareLog() },
                makeButton("Effacer") {
                    synchronized(logBuf) { logBuf.setLength(0) }
                    logTv.text = ""
                }
            )
        )

        logTv = TextView(this)
        logTv.typeface = Typeface.MONOSPACE
        logTv.textSize = 11f
        logTv.setTextIsSelectable(true)
        logScroll = ScrollView(this)
        logScroll.addView(logTv)
        root.addView(logScroll, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))

        setContentView(root)

        log("MG4 Link v0.9 démarré (Android ${Build.VERSION.RELEASE}, SDK ${Build.VERSION.SDK_INT})")
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
                    log("Lecture live bloquée (plus de réponse depuis 15 s) - redémarrage automatique.")
                    startLiveThread()
                }
            }
        }
        if (hasAll()) startGps()
        thread(name = "bornes-cache") { loadBornesCache() }
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
            "Distance GPS : " + "%.2f".format(tripKm) + " km"
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
            if (tripActive && stageIdx < stages.size &&
                (tripKm - stageStartKm) >= stages[stageIdx].km) finishStage(false)
            refreshRoute()
            refreshOverlay()
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
            if (lm.allProviders.contains(LocationManager.GPS_PROVIDER)) {
                lm.requestLocationUpdates(LocationManager.GPS_PROVIDER, 1000L, 0f, locListener)
                gpsStarted = true
            }
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

    private fun initElm() {
        try {
            status("Initialisation du dongle...")
            for (cmd in listOf("ATZ", "ATE0", "ATL0", "ATS0", "ATH0", "ATSP0")) {
                val r = elm.request(cmd, if (cmd == "ATZ") 5000L else 3000L)
                log("> $cmd\n$r")
            }
            log("> ATRV\n" + elm.request("ATRV", 3000))
            log("> 0100 (détection du protocole, peut durer quelques secondes)\n" + elm.request("0100", 12000))
            log("> ATDP\n" + elm.request("ATDP", 3000))
            ready = true
            status("Prêt - dongle connecté")
            log("Initialisation terminée.")
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
        startLiveThread()
    }

    /** Lance le fil de lecture live (relançable par le watchdog). */
    private fun startLiveThread() {
        liveThread = thread(name = "live") {
            while (liveOn) {
                lastLiveTick = System.currentTimeMillis()
                try {
                    if (ready) {
                        val s = elm.request("010D", 2500)
                        val b = hexAfter(s, "410D", 1)
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
                        if (tripActive && stageIdx < stages.size &&
                            (tripKm - stageStartKm) >= stages[stageIdx].km) finishStage(false)
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
                val g = geocode(line)
                if (g == null) {
                    fails.add(line)
                    log("Adresse introuvable : " + line)
                } else {
                    pend.add(Pending(line, null, g))
                    log("« " + line + " » localisé → " + "%.3f".format(g.lat) + ", " +
                        "%.3f".format(g.lon))
                }
                Thread.sleep(1100) // règle Nominatim : 1 requête/seconde maximum
            }
            // Distances routières réelles (v0.9), depuis la position actuelle
            // pour la première étape, sinon depuis l'étape géocodée précédente.
            val here = lastLoc ?: bestLoc()
            val start = if (here != null) Geo(here.latitude, here.longitude) else null
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
                log("« " + p.line + " » : " + fmtKm(km) + " km (distance routière réelle)")
                prev = g
            }
            handler.post { applyStages(result, fails) }
        }
    }

    /**
     * Distance routière réelle entre deux points via OSRM (OpenStreetMap,
     * gratuit, sans clé). Repli : vol d'oiseau × 1,25 si le service ne répond pas.
     */
    private fun roadKm(a: Geo, b: Geo): Double {
        return try {
            val url = "https://router.project-osrm.org/route/v1/driving/" +
                fmtD(a.lon) + "," + fmtD(a.lat) + ";" + fmtD(b.lon) + "," + fmtD(b.lat) +
                "?overview=false"
            val json = httpGet(url, 15000)
            val m = Regex("\"distance\"\\s*:\\s*([0-9]+(?:\\.[0-9]+)?)").find(json)
            if (m != null) {
                m.groupValues[1].toDouble() / 1000.0
            } else {
                distKm(a.lat, a.lon, b.lat, b.lon) * 1.25
            }
        } catch (e: Exception) {
            log("OSRM indisponible (" + e.message + ") : estimation vol d'oiseau.")
            distKm(a.lat, a.lon, b.lat, b.lon) * 1.25
        }
    }

    private fun applyStages(list: List<Stage>, fails: List<String>) {
        stages.clear()
        stages.addAll(list)
        tripActive = false
        stageIdx = 0
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
    private fun geocode(addr: String): Geo? {
        return try {
            val url = "https://nominatim.openstreetmap.org/search?format=json&limit=1&addressdetails=0&q=" +
                URLEncoder.encode(addr, "UTF-8")
            val json = httpGet(url, 15000)
            val lat = Regex("\"lat\"\\s*:\\s*\"(-?[0-9.]+)\"").find(json)?.groupValues?.get(1)
                ?: return null
            val lon = Regex("\"lon\"\\s*:\\s*\"(-?[0-9.]+)\"").find(json)?.groupValues?.get(1)
                ?: return null
            Geo(lat.toDouble(), lon.toDouble())
        } catch (e: Exception) {
            log("Géocodage de « " + addr + " » : " + e.message)
            null
        }
    }

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
                sb.append("Reste " + "%.1f".format(stages[stageIdx].km - (tripKm - stageStartKm)) +
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
            val remain = (s.km - (tripKm - stageStartKm)).coerceAtLeast(0.0)
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
        val txt = sb.toString()
        handler.post { tv.text = txt }
    }

    // ------------------------------------------------------ Bornes IRVE v0.7.1

    private fun bornesFile(): File = File(filesDir, "bornes_cache.txt")

    private fun bornesAgeMs(): Long {
        val d = getSharedPreferences("mg4link", Context.MODE_PRIVATE).getLong("bornesDate", 0L)
        return if (d == 0L) Long.MAX_VALUE else System.currentTimeMillis() - d
    }

    private fun loadBornesCache() {
        val f = bornesFile()
        if (!f.exists()) return
        try {
            val lst = ArrayList<Borne>()
            f.forEachLine { line -> parseBorneCache(line)?.let { lst.add(it) } }
            if (lst.isNotEmpty()) {
                synchronized(bornes) {
                    bornes.clear()
                    bornes.addAll(lst)
                }
                log("Base IRVE France en cache : " + lst.size + " bornes (maj il y a " +
                    (bornesAgeMs() / 3600000L) + " h).")
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

    /** Bornes Espagne/Portugal en cache (v0.8). */
    private fun bornesIberiaFile(): File = File(filesDir, "bornes_iberia.txt")

    private fun loadBornesIberia() {
        val f = bornesIberiaFile()
        if (!f.exists()) return
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
        conn.setRequestProperty("User-Agent", "MG4Link/0.9 (Android; https://github.com/Moup1957/MG4Link)")
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
        conn.setRequestProperty("User-Agent", "MG4Link/0.9 (Android; https://github.com/Moup1957/MG4Link)")
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
                getSharedPreferences("mg4link", Context.MODE_PRIVATE).edit()
                    .putLong("bornesDate", System.currentTimeMillis())
                    .apply()
                log("Base IRVE France chargée : " + bornes.size + " bornes ≥ 22 kW (" + n + " lignes).")
                // Espagne + Portugal (v0.8) via OpenStreetMap
                updateBornesIberia()
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
     * Bornes Espagne + Portugal (v0.8) via l'API Overpass (OpenStreetMap).
     * Les registres officiels RIPREE / MOBI.E n'ont pas de téléchargement CSV
     * direct et stable : OpenStreetMap est gratuit, sans clé et mis à jour
     * par la communauté. Puissance lue depuis les tags « maxpower » ou
     * « socket:type2_combo:output ».
     */
    private fun updateBornesIberia(): Int {
        val zones = listOf(
            "Espagne" to doubleArrayOf(35.0, -9.9, 43.9, 4.5),
            "Portugal" to doubleArrayOf(36.5, -9.9, 42.3, -6.0)
        )
        val out = StringBuilder()
        var total = 0
        for ((pays, bb) in zones) {
            try {
                val bbox = fmtD(bb[0]) + "," + fmtD(bb[1]) + "," + fmtD(bb[2]) + "," + fmtD(bb[3])
                val q = "[out:csv(::lat,::lon,\"maxpower\",\"socket:type2_combo:output\"," +
                    "\"operator\",\"name\",\"addr:street\",\"addr:housenumber\",\"addr:city\";true;\",\")]" +
                    "[timeout:180];node[\"amenity\"=\"charging_station\"](" + bbox + ");out;"
                val url = "https://overpass-api.de/api/interpreter?data=" + URLEncoder.encode(q, "UTF-8")
                log("Téléchargement des bornes " + pays + " (OpenStreetMap)...")
                var header: List<String>? = null
                var count = 0
                val parsed = ArrayList<Borne>()
                downloadCsv(url) { line ->
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
                synchronized(bornes) { bornes.addAll(parsed) }
                log("Bornes " + pays + " : " + count + " bornes ≥ 22 kW ajoutées.")
                total += count
            } catch (e: Exception) {
                log("Erreur bornes " + pays + " : " + e.message)
            }
        }
        if (out.isNotEmpty()) {
            bornesIberiaFile().writeText(out.toString())
            getSharedPreferences("mg4link", Context.MODE_PRIVATE).edit()
                .putLong("iberiaDate", System.currentTimeMillis())
                .apply()
        }
        if (total == 0) {
            alert("Bornes Espagne/Portugal",
                "Aucune borne n'a été trouvée dans OpenStreetMap pour ces pays.\n" +
                    "Copie le journal et envoie-le pour diagnostic.")
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
        // Dernière position connue même sans GPS actif (utile en garage) - v0.7.1
        val loc = lastLoc ?: bestLoc()
        if (loc == null) {
            log("Pas encore de position GPS : sortez ou attendez la fixation GPS.")
            alert("Position inconnue", "Aucune position disponible pour l'instant (normal en garage). " +
                "Sortez dehors ou attendez la fixation GPS, puis retouchez « Bornes recharge ».")
            return
        }
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
                listBornes(minKw, loc)
            }
            .setNegativeButton("Annuler", null)
            .show()
    }

    private fun listBornes(minKw: Double, loc: Location) {
        class NearB(val b: Borne, val km: Double)
        val arr: List<NearB>
        synchronized(bornes) {
            arr = bornes.filter { it.kw >= minKw }
                .map { b ->
                    val d = FloatArray(1)
                    Location.distanceBetween(loc.latitude, loc.longitude, b.lat, b.lon, d)
                    NearB(b, d[0] / 1000.0)
                }
                .sortedBy { it.km }
                .take(50)
        }
        if (arr.isEmpty()) {
            log("Aucune borne ≥ " + "%.0f".format(minKw) + " kW dans la base.")
            alert("Bornes", "Aucune borne ≥ " + "%.0f".format(minKw) + " kW dans la base.")
            return
        }
        val labels = arr.map {
            val b = it.b
            (if (b.enseigne.isNotEmpty()) b.enseigne else b.nom) + "\n" +
                "%.1f".format(it.km) + " km - " + "%.0f".format(b.kw) + " kW - " +
                b.adresse.take(38)
        }.toTypedArray()
        AlertDialog.Builder(this)
            .setTitle("Bornes ≥ " + "%.0f".format(minKw) + " kW (50 plus proches)")
            .setItems(labels) { _, i -> borneAction(arr[i].b, arr[i].km) }
            .setNegativeButton("Fermer", null)
            .show()
    }

    private fun borneAction(b: Borne, km: Double) {
        val opts = arrayOf("Insérer comme prochaine étape", "Ouvrir dans Google Maps")
        AlertDialog.Builder(this)
            .setTitle(b.enseigne)
            .setMessage(
                "Adresse : " + b.adresse + "\n" +
                    "Puissance max : " + "%.0f".format(b.kw) + " kW\n" +
                    "Distance : " + "%.1f".format(km) + " km (à vol d'oiseau)"
            )
            .setItems(opts) { _, which ->
                when (which) {
                    0 -> insertBorne(b, km)
                    1 -> try {
                        startActivity(
                            Intent(
                                Intent.ACTION_VIEW,
                                Uri.parse("https://www.google.com/maps/search/?api=1&query=" + b.lat + "," + b.lon)
                            )
                        )
                    } catch (e: Exception) {
                        log("Maps indisponible : " + e.message)
                    }
                }
            }
            .setNegativeButton("Annuler", null)
            .show()
    }

    private fun insertBorne(b: Borne, km: Double) {
        val name = ("Borne " + b.enseigne + " - " + b.adresse).replace(';', ' ').replace('\n', ' ')
        val stageKm = if (tripActive && stageIdx < stages.size) {
            (stages[stageIdx].km - (tripKm - stageStartKm)) + km
        } else {
            km
        }
        stages.add(stageIdx.coerceAtMost(stages.size), Stage(name, stageKm, b.lat, b.lon))
        log("Borne insérée comme étape " + (stageIdx + 1) + " : " + name +
            " (" + "%.0f".format(stageKm) + " km, distance à vol d'oiseau - ajustez si besoin).")
        refreshRoute()
    }
}
