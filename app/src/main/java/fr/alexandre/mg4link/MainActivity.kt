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
import java.net.URLEncoder
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

/** Étape d'un itinéraire : nom et distance prévue depuis l'étape précédente. */
class Stage(val name: String, val km: Double)

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

    // -------------------------------------------- Fenêtre flottante
    private var overlayLayout: LinearLayout? = null
    private var overlayTv: TextView? = null
    private val wm: WindowManager
        get() = getSystemService(Context.WINDOW_SERVICE) as WindowManager

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
        statusTv.text = "MG4 Link v0.5 - non connecté"
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

        log("MG4 Link v0.5 démarré (Android ${Build.VERSION.RELEASE}, SDK ${Build.VERSION.SDK_INT})")
        if (hasAll()) startGps()
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

    private fun refreshLive() {
        val txt = "Charge (PID 5B, à valider) : $soc\n" +
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
        }

        override fun onProviderEnabled(provider: String) {}
        override fun onProviderDisabled(provider: String) {}
        override fun onStatusChanged(provider: String?, status: Int, extras: Bundle?) {}
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
        liveThread = thread(name = "live") {
            while (liveOn) {
                try {
                    if (ready) {
                        val s = elm.request("010D", 2500)
                        val b = hexAfter(s, "410D", 1)
                        obdSpeed = if (b != null) "${b[0]} km/h" else "pas de réponse ($s)"
                        volt = elm.request("ATRV", 2500)
                        val s5 = hexAfter(elm.request("015B", 2500), "415B", 1)
                        soc = if (s5 != null) "%.1f".format(s5[0] * 100.0 / 255.0) + " %" else "pas de réponse"
                        socPct = if (s5 != null) s5[0] * 100.0 / 255.0 else socPct
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
                "0101", "0902"
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
                "0100", "015B", "01A6", "0142", "0146", "0149",
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

    /** Analyse une ligne : accepte "Nom;km", "Nom : km", "Nom, km" ou "Nom 145 km". */
    private fun parseStage(line: String): Stage? {
        val t = line.trim()
        if (t.isEmpty()) return null
        val sep = Regex("^(.+?)[;:\\u0009]\\s*([0-9]+(?:[.,][0-9]+)?)\\s*(km)?\\s*$").find(t)
        if (sep != null) {
            val n = sep.groupValues[1].trim().trimEnd(';', ':', ',')
            val k = sep.groupValues[2].replace(',', '.').toDoubleOrNull() ?: return null
            if (n.isNotEmpty() && k > 0) return Stage(n, k)
        }
        val m = Regex("^(.+?)[,;:]?\\s+([0-9]+(?:[.,][0-9]+)?)\\s*(km)?\\s*$").find(t)
        if (m != null) {
            val n = m.groupValues[1].trim().trimEnd(';', ':', ',')
            val k = m.groupValues[2].replace(',', '.').toDoubleOrNull() ?: return null
            if (n.isNotEmpty() && k > 0) return Stage(n, k)
        }
        return null
    }

    private fun editStages() {
        val input = EditText(this)
        input.hint = "Une étape par ligne.\nFormats acceptés :\nReims;145\nReims : 145\nReims 145"
        input.setSingleLine(false)
        input.minLines = 6
        input.gravity = Gravity.TOP
        input.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE
        input.setText(stages.joinToString("\n") { it.name + ";" + it.km })
        AlertDialog.Builder(this)
            .setTitle("Définir l'itinéraire")
            .setView(input)
            .setPositiveButton("OK") { _, _ ->
                stages.clear()
                var rejets = 0
                for (line in input.text.toString().lines()) {
                    if (line.isBlank()) continue
                    val st = parseStage(line)
                    if (st != null) {
                        stages.add(st)
                    } else {
                        rejets++
                        log("Ligne d'itinéraire non comprise : " + line.trim())
                    }
                }
                log("Itinéraire : " + stages.size + " étape(s), total " +
                    "%.0f".format(stages.sumOf { it.km }) + " km" +
                    (if (rejets > 0) " (" + rejets + " ligne(s) ignorée(s))" else ""))
                refreshRoute()
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

    private fun finishStage(manual: Boolean) {
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
            val dest = URLEncoder.encode(stages.last().name, "UTF-8")
            val wps = stages.dropLast(1).take(9).joinToString("%7C") { URLEncoder.encode(it.name, "UTF-8") }
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
}
