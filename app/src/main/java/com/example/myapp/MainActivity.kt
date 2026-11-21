package com.example.myapp

import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.ClipData
import android.content.ClipDescription
import android.content.ClipboardManager
import android.content.ContentProvider
import android.content.ContentValues
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.content.pm.ServiceInfo
import android.database.Cursor
import android.database.MatrixCursor
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.PixelFormat
import android.graphics.drawable.GradientDrawable
import android.net.Uri
import android.net.wifi.WifiManager
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.IBinder
import android.os.Looper
import android.os.ParcelFileDescriptor
import android.os.PowerManager
import android.provider.DocumentsContract
import android.provider.OpenableColumns
import android.provider.Settings
import android.text.InputType
import android.text.TextUtils
import android.view.Gravity
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.WindowManager
import android.view.inputmethod.EditorInfo
import android.view.inputmethod.InputMethodManager
import android.webkit.MimeTypeMap
import android.widget.Button
import android.widget.CheckBox
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import org.json.JSONArray
import org.json.JSONObject
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileNotFoundException
import java.io.FileOutputStream
import java.io.IOException
import java.io.InputStream
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.Inet4Address
import java.net.InetAddress
import java.net.InetSocketAddress
import java.net.NetworkInterface
import java.net.ServerSocket
import java.net.Socket
import java.net.SocketAddress
import java.util.Locale
import java.util.UUID
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger

// Light item: only two strings. The document Uri is built later, only for the few files in use.
class FileItem(val name: String, val docId: String)

class ListRes(val items: ArrayList<FileItem>, val error: String)

// A text file chosen by the user to travel with every batch.
class TxtItem(val uri: String, val name: String)

// Natural order: 1, 2, 3 ... 10, 11 (not 1, 10, 11, 2). Works for "5.pdf", "file7.txt", "IMG_0012.jpg" and so on.
fun natCompare(a: String, b: String): Int {
    var i = 0
    var j = 0
    val la = a.length
    val lb = b.length
    while (i < la && j < lb) {
        val ca = a[i]
        val cb = b[j]
        if (ca in '0'..'9' && cb in '0'..'9') {
            var si = i
            while (si < la && a[si] == '0') si++
            var sj = j
            while (sj < lb && b[sj] == '0') sj++
            var ei = si
            while (ei < la && a[ei] in '0'..'9') ei++
            var ej = sj
            while (ej < lb && b[ej] in '0'..'9') ej++
            val lenA = ei - si
            val lenB = ej - sj
            if (lenA != lenB) return if (lenA < lenB) -1 else 1
            var k = 0
            while (k < lenA) {
                val x = a[si + k]
                val y = b[sj + k]
                if (x != y) return if (x < y) -1 else 1
                k++
            }
            i = ei
            j = ej
        } else {
            val x = ca.lowercaseChar()
            val y = cb.lowercaseChar()
            if (x != y) return if (x < y) -1 else 1
            i++
            j++
        }
    }
    val ra = la - i
    val rb = lb - j
    return if (ra == rb) 0 else if (ra < rb) -1 else 1
}

fun mimeOfName(name: String): String {
    val ext = name.substringAfterLast('.', "").lowercase()
    if (ext.isEmpty()) return "application/octet-stream"
    val m = MimeTypeMap.getSingleton().getMimeTypeFromExtension(ext)
    if (m != null) return m
    return when (ext) {
        "heic" -> "image/heic"
        "heif" -> "image/heif"
        "avif" -> "image/avif"
        "txt", "log", "md" -> "text/plain"
        "pdf" -> "application/pdf"
        else -> "application/octet-stream"
    }
}

// Serves the picked files (any type) to other apps when they paste from the clipboard.
class ClipProvider : ContentProvider() {

    override fun onCreate(): Boolean = true

    private fun docOf(uri: Uri): Uri? {
        val segs = uri.pathSegments
        if (segs.size < 1) return null
        return Uri.parse(segs[0])
    }

    override fun getType(uri: Uri): String? {
        val nm = uri.lastPathSegment ?: ""
        val m = mimeOfName(nm)
        if (m != "application/octet-stream") return m
        val d = docOf(uri) ?: return m
        val ctx = context ?: return m
        val t: String? = try {
            ctx.contentResolver.getType(d)
        } catch (e: Exception) {
            null
        }
        return t ?: m
    }

    override fun query(
        uri: Uri,
        projection: Array<String>?,
        selection: String?,
        selectionArgs: Array<String>?,
        sortOrder: String?
    ): Cursor? {
        val d = docOf(uri) ?: return null
        val ctx = context ?: return null
        val name = uri.lastPathSegment ?: "file"
        var size = -1L
        try {
            ctx.contentResolver.query(d, arrayOf(OpenableColumns.SIZE), null, null, null)?.use { c ->
                if (c.moveToFirst() && !c.isNull(0)) {
                    size = c.getLong(0)
                }
            }
        } catch (e: Exception) {
        }
        val want: Array<String> = projection ?: arrayOf(OpenableColumns.DISPLAY_NAME, OpenableColumns.SIZE)
        val row = arrayOfNulls<Any>(want.size)
        for (i in want.indices) {
            if (want[i] == OpenableColumns.DISPLAY_NAME) {
                row[i] = name
            } else if (want[i] == OpenableColumns.SIZE) {
                if (size >= 0L) row[i] = size
            }
        }
        val mc = MatrixCursor(want)
        mc.addRow(row)
        return mc
    }

    override fun openFile(uri: Uri, mode: String): ParcelFileDescriptor? {
        val d = docOf(uri) ?: return null
        val ctx = context ?: return null
        return ctx.contentResolver.openFileDescriptor(d, "r")
    }

    override fun insert(uri: Uri, values: ContentValues?): Uri? = null

    override fun delete(uri: Uri, selection: String?, selectionArgs: Array<String>?): Int = 0

    override fun update(
        uri: Uri,
        values: ContentValues?,
        selection: String?,
        selectionArgs: Array<String>?
    ): Int = 0
}

// ═════════════════════════ LAN engine (send / receive files between phones) ═════════════════════════

const val TCP_PORT = 45455
const val UDP_PORT = 45454
const val MAGIC = 0x4C434232
const val RECV_AUTH = "com.example.myapp.recv"

fun mimeForName(n: String): String {
    val dot = n.lastIndexOf('.')
    if (dot < 0 || dot >= n.length - 1) return "application/octet-stream"
    val m = MimeTypeMap.getSingleton().getMimeTypeFromExtension(n.substring(dot + 1).lowercase())
    return m ?: "application/octet-stream"
}

// ───────────────────────── data classes ─────────────────────────

class OutItem(
    val id: String,
    val isText: Boolean,
    val name: String,
    val uriStr: String,
    val text: String,
    val size: Long
)

class InItem(val isText: Boolean, val name: String, val path: String, val size: Long)

class Batch(val id: String, val from: String, val time: Long, val items: List<InItem>)

class Peer(val id: String, nameInit: String, ipInit: String) {
    @Volatile var name: String = nameInit
    @Volatile var ip: String = ipInit
    @Volatile var lastSeen: Long = 0L
    @Volatile var everSeen: Long = 0L
    @Volatile var selected: Boolean = true
    @Volatile var wasOnline: Boolean = false
    val sending = AtomicBoolean(false)

    fun online(): Boolean = System.currentTimeMillis() - lastSeen < 10000L
}

class Delivery(val batchId: String, val items: List<OutItem>, val created: Long)


class Src(val stream: InputStream, val size: Long, val tmp: File?) {
    fun close() {
        try {
            stream.close()
        } catch (e: Exception) {
        }
        if (tmp != null) {
            try {
                tmp.delete()
            } catch (e: Exception) {
            }
        }
    }
}

fun fmtSize(n: Long): String {
    if (n < 1024L) return n.toString() + " B"
    val kb = n / 1024.0
    if (kb < 1024.0) return String.format(Locale.US, "%.1f KB", kb)
    val mb = kb / 1024.0
    if (mb < 1024.0) return String.format(Locale.US, "%.1f MB", mb)
    return String.format(Locale.US, "%.2f GB", mb / 1024.0)
}

// Asks Android (once) to let this app run in the background without being put to sleep.
fun askBatteryExemption(a: Activity, prefs: SharedPreferences) {
    try {
        if (prefs.getBoolean("battery_asked", false)) return
        prefs.edit().putBoolean("battery_asked", true).apply()
        val pm = a.getSystemService(Context.POWER_SERVICE) as PowerManager
        if (!pm.isIgnoringBatteryOptimizations(a.packageName)) {
            val i = Intent(Settings.ACTION_REQUEST_IGNORE_BATTERY_OPTIMIZATIONS)
            i.data = Uri.parse("package:" + a.packageName)
            a.startActivity(i)
        }
    } catch (e: Exception) {
    }
}

// ───────────────────────── core engine ─────────────────────────

class Lan(val ctx: Context) {
    val handler = Handler(Looper.getMainLooper())
    val prefs: SharedPreferences = ctx.getSharedPreferences("lanclip", Context.MODE_PRIVATE)
    val pool: ExecutorService = Executors.newCachedThreadPool()
    val peers = ConcurrentHashMap<String, Peer>()
    val staged = ArrayList<OutItem>()
    val inbox = ArrayList<Batch>()
    val inboxDir: File = File(ctx.filesDir, "inbox")
    val myId: String = loadId()
    @Volatile var myName: String = prefs.getString("name", null) ?: (Build.MODEL ?: "Android")
    @Volatile var onChange: (() -> Unit)? = null
    @Volatile var statusListener: ((String) -> Unit)? = null
    @Volatile var lastStatus: String = "Starting..."
    @Volatile var running: Boolean = false
    @Volatile var gen: Int = 0
    @Volatile private var serverSock: ServerSocket? = null
    @Volatile private var udpSock: DatagramSocket? = null
    private val statusScheduled = AtomicBoolean(false)
    private val counter = AtomicInteger(0)
    val pending = ConcurrentHashMap<String, ArrayList<Delivery>>()
    private val seenIds = LinkedHashSet<String>()
    @Volatile private var annSock: DatagramSocket? = null
    private var cpuLock: PowerManager.WakeLock? = null
    @Volatile var lastErr: String = ""
    private var multicastLock: WifiManager.MulticastLock? = null
    private var wifiLock: WifiManager.WifiLock? = null

    init {
        inboxDir.mkdirs()
        loadState()
        loadPeers()
    }

    private fun loadId(): String {
        val s = prefs.getString("id", null)
        if (s != null) return s
        val n = UUID.randomUUID().toString()
        prefs.edit().putString("id", n).apply()
        return n
    }

    fun newId(): String = UUID.randomUUID().toString()

    fun folderUri(): String? = prefs.getString("folder", null)

    fun setFolder(s: String) {
        prefs.edit().putString("folder", s).apply()
    }

    fun setName(n: String) {
        myName = n
        prefs.edit().putString("name", n).apply()
        changed()
    }

    // ---- UI notifications (throttled, never blocks) ----

    fun status(msg: String) {
        lastStatus = msg
        if (statusScheduled.compareAndSet(false, true)) {
            handler.postDelayed({
                statusScheduled.set(false)
                statusListener?.invoke(lastStatus)
            }, 120)
        }
    }

    fun changed() {
        handler.post { onChange?.invoke() }
    }

    // ---- start networking ----

    fun start() {
        if (running) return
        running = true
        gen += 1
        val g = gen
        try {
            val wm = ctx.applicationContext.getSystemService(Context.WIFI_SERVICE) as WifiManager
            val ml = wm.createMulticastLock("lanclip")
            ml.setReferenceCounted(false)
            ml.acquire()
            multicastLock = ml
            val wl = wm.createWifiLock(WifiManager.WIFI_MODE_FULL_HIGH_PERF, "lanclip")
            wl.setReferenceCounted(false)
            wl.acquire()
            wifiLock = wl
        } catch (e: Exception) {
        }
        try {
            val pm = ctx.applicationContext.getSystemService(Context.POWER_SERVICE) as PowerManager
            val cl = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "lanclip:cpu")
            cl.setReferenceCounted(false)
            cl.acquire()
            cpuLock = cl
        } catch (e: Exception) {
        }
        pool.execute { serverLoop(g) }
        pool.execute { udpListen(g) }
        pool.execute { announceLoop(g) }
        kickAll()
        status("Ready. Open this app on other devices on the same Wi-Fi.")
    }

    fun stop() {
        if (!running) return
        running = false
        gen += 1
        try {
            serverSock?.close()
        } catch (e: Exception) {
        }
        try {
            udpSock?.close()
        } catch (e: Exception) {
        }
        try {
            multicastLock?.release()
        } catch (e: Exception) {
        }
        try {
            wifiLock?.release()
        } catch (e: Exception) {
        }
        try {
            cpuLock?.release()
        } catch (e: Exception) {
        }
        status("LAN copy is off.")
        changed()
    }

    // ---- discovery ----

    private fun helloBytes(reply: Boolean): ByteArray {
        val msg = "LANCLIP2|" + myId + "|" + myName.replace("|", " ") + "|" + (if (reply) "1" else "0")
        return msg.toByteArray(Charsets.UTF_8)
    }

    private fun broadcastAddresses(): List<InetAddress> {
        val list = ArrayList<InetAddress>()
        try {
            list.add(InetAddress.getByName("255.255.255.255"))
        } catch (e: Exception) {
        }
        try {
            val en = NetworkInterface.getNetworkInterfaces()
            while (en != null && en.hasMoreElements()) {
                val ni = en.nextElement()
                if (!ni.isUp || ni.isLoopback) continue
                for (ia in ni.interfaceAddresses) {
                    val b = ia.broadcast
                    if (b != null) list.add(b)
                }
            }
        } catch (e: Exception) {
        }
        return list
    }

    // Every address of the local /24 network. Used when the router blocks broadcast packets.
    private fun sweepAddresses(): List<InetAddress> {
        val list = ArrayList<InetAddress>()
        try {
            val en = NetworkInterface.getNetworkInterfaces()
            while (en != null && en.hasMoreElements()) {
                val ni = en.nextElement()
                if (!ni.isUp || ni.isLoopback) continue
                for (ia in ni.interfaceAddresses) {
                    val a = ia.address
                    if (a !is Inet4Address) continue
                    if (!a.isSiteLocalAddress) continue
                    val b = a.address
                    val me = b[3].toInt() and 0xFF
                    for (h in 1..254) {
                        if (h == me) continue
                        val nb = byteArrayOf(b[0], b[1], b[2], h.toByte())
                        list.add(InetAddress.getByAddress(nb))
                    }
                }
            }
        } catch (e: Exception) {
        }
        return list
    }

    private fun announceLoop(g: Int) {
        var sock: DatagramSocket? = null
        try {
            val s = DatagramSocket()
            s.broadcast = true
            sock = s
            annSock = s
            var tick = 0
            while (running && gen == g) {
                val data = helloBytes(false)
                for (addr in broadcastAddresses()) {
                    try {
                        s.send(DatagramPacket(data, data.size, addr, UDP_PORT))
                    } catch (e: Exception) {
                    }
                }
                if (tick < 3 || tick % 8 == 0) {
                    for (addr in sweepAddresses()) {
                        try {
                            s.send(DatagramPacket(data, data.size, addr, UDP_PORT))
                        } catch (e: Exception) {
                        }
                    }
                }
                val now = System.currentTimeMillis()
                var flip = false
                for (p in peers.values) {
                    try {
                        s.send(DatagramPacket(data, data.size, InetAddress.getByName(p.ip), UDP_PORT))
                    } catch (e: Exception) {
                    }
                    val on = now - p.lastSeen < 10000L
                    if (on != p.wasOnline) {
                        p.wasOnline = on
                        flip = true
                    }
                    kick(p)
                }
                if (flip) changed()
                tick += 1
                if (tick % 150 == 0) savePeers()
                try {
                    Thread.sleep(2000)
                } catch (e: InterruptedException) {
                }
            }
        } catch (e: Exception) {
            status("Discovery error: " + e.message)
        } finally {
            annSock = null
            try {
                sock?.close()
            } catch (e: Exception) {
            }
        }
    }

    private fun udpListen(g: Int) {
        while (running && gen == g) {
            var ds: DatagramSocket? = null
            try {
                val s = DatagramSocket(null as SocketAddress?)
                ds = s
                udpSock = s
                s.reuseAddress = true
                s.broadcast = true
                s.bind(InetSocketAddress(UDP_PORT))
                val buf = ByteArray(512)
                while (running && gen == g) {
                    val pk = DatagramPacket(buf, buf.size)
                    s.receive(pk)
                    val msg = String(pk.data, 0, pk.length, Charsets.UTF_8)
                    val parts = msg.split("|")
                    if (parts.size >= 3 && parts[0] == "LANCLIP2" && parts[1] != myId) {
                        val ip = pk.address.hostAddress
                        if (ip != null) {
                            val wasOff = onPeerSeen(parts[1], parts[2], ip)
                            val ann = annSock
                            if (wasOff && ann != null && parts.size >= 4 && parts[3] == "0") {
                                try {
                                    val d = helloBytes(true)
                                    ann.send(DatagramPacket(d, d.size, pk.address, UDP_PORT))
                                } catch (e: Exception) {
                                }
                            }
                        }
                    }
                }
            } catch (e: Exception) {
                try {
                    Thread.sleep(2000)
                } catch (e2: InterruptedException) {
                }
            } finally {
                try {
                    ds?.close()
                } catch (e: Exception) {
                }
            }
        }
    }

    // Returns true when the device was new or had been offline (so we answer it right away).
    private fun onPeerSeen(id: String, name: String, ip: String): Boolean {
        val now = System.currentTimeMillis()
        val existing = peers[id]
        if (existing == null) {
            val np = Peer(id, name, ip)
            np.lastSeen = now
            np.everSeen = now
            np.wasOnline = true
            peers[id] = np
            savePeers()
            status("Device found: " + name)
            changed()
            kick(np)
            return true
        }
        val wasOff = now - existing.lastSeen >= 10000L
        existing.lastSeen = now
        existing.everSeen = now
        var chg = false
        if (existing.ip != ip || existing.name != name) {
            existing.ip = ip
            existing.name = name
            chg = true
        }
        if (wasOff) {
            existing.wasOnline = true
            chg = true
            status("Device online: " + name)
        }
        if (chg) {
            savePeers()
            changed()
        }
        if (chg) kick(existing)
        return wasOff
    }

    // ---- receiving ----

    private fun serverLoop(g: Int) {
        while (running && gen == g) {
            var ss: ServerSocket? = null
            try {
                val s = ServerSocket()
                ss = s
                serverSock = s
                s.reuseAddress = true
                s.bind(InetSocketAddress(TCP_PORT), 50)
                while (running && gen == g) {
                    val c = s.accept()
                    pool.execute { handleIncoming(c) }
                }
            } catch (e: Exception) {
                if (running && gen == g) status("Listen error: " + e.message)
                try {
                    Thread.sleep(2000)
                } catch (e2: InterruptedException) {
                }
            } finally {
                try {
                    ss?.close()
                } catch (e: Exception) {
                }
            }
        }
    }

    private fun alreadyGot(id: String): Boolean {
        synchronized(seenIds) {
            return seenIds.contains(id)
        }
    }

    private fun markGot(id: String) {
        synchronized(seenIds) {
            seenIds.add(id)
            if (seenIds.size > 200) {
                val iter = seenIds.iterator()
                iter.next()
                iter.remove()
            }
        }
    }

    private fun handleIncoming(s: Socket) {
        var batchDir: File? = null
        try {
            s.soTimeout = 60000
            s.tcpNoDelay = true
            val input = DataInputStream(BufferedInputStream(s.getInputStream(), 65536))
            val os = s.getOutputStream()
            if (input.readInt() != MAGIC) return
            input.readUTF()
            val fromName = input.readUTF()
            val bid = input.readUTF()
            val count = input.readInt()
            if (count < 0 || count > 10000) return
            if (alreadyGot(bid)) {
                os.write(2)
                os.flush()
                return
            }
            os.write(0)
            os.flush()
            val batchId = System.currentTimeMillis().toString() + "_" + counter.incrementAndGet().toString()
            val dir = File(inboxDir, batchId)
            dir.mkdirs()
            batchDir = dir
            val items = ArrayList<InItem>()
            val buf = ByteArray(65536)
            for (i in 0 until count) {
                val isText = input.readByte().toInt() == 1
                val name = input.readUTF()
                val size = input.readLong()
                val f = File(dir, i.toString() + ".dat")
                var remaining = size
                var lastPct = -1
                FileOutputStream(f).use { out ->
                    while (remaining > 0L) {
                        val want = minOf(buf.size.toLong(), remaining).toInt()
                        val n = input.read(buf, 0, want)
                        if (n < 0) throw IOException("connection closed")
                        out.write(buf, 0, n)
                        remaining -= n.toLong()
                        if (size > 0L) {
                            val pct = (((size - remaining) * 100L) / size).toInt()
                            if (pct != lastPct) {
                                lastPct = pct
                                status("Receiving from " + fromName + ": " + pct.toString() + "%")
                            }
                        }
                    }
                }
                items.add(InItem(isText, name, f.absolutePath, size))
            }
            os.write(1)
            os.flush()
            markGot(bid)
            val batch = Batch(batchId, fromName, System.currentTimeMillis(), items)
            handler.post { addBatch(batch) }
        } catch (e: Exception) {
            status("Receive failed: " + e.message)
            try {
                batchDir?.deleteRecursively()
            } catch (e2: Exception) {
            }
        } finally {
            try {
                s.close()
            } catch (e: Exception) {
            }
        }
    }

    private fun addBatch(b: Batch) {
        inbox.add(0, b)
        while (inbox.size > 10) {
            val old = inbox.removeAt(inbox.size - 1)
            try {
                File(inboxDir, old.id).deleteRecursively()
            } catch (e: Exception) {
            }
        }
        saveInbox()
        var files = 0
        var texts = 0
        for (it2 in b.items) {
            if (it2.isText) texts++ else files++
        }
        putBatchOnClipboard(b)
        status("Received from " + b.from + ": " + files.toString() + " file(s), " + texts.toString() + " text(s). Now long-press in any app and tap Paste.")
        changed()
    }

    private fun applyTextToClipboard(b: Batch) {
        try {
            val parts = ArrayList<String>()
            for (it2 in b.items) {
                if (it2.isText && it2.size <= 500000L) {
                    val f = File(it2.path)
                    if (f.exists()) parts.add(String(f.readBytes(), Charsets.UTF_8))
                }
            }
            if (parts.isNotEmpty()) setClipboardText(parts.joinToString("\n"))
        } catch (e: Exception) {
        }
    }

    fun setClipboardText(t: String) {
        try {
            val cm = ctx.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            cm.setPrimaryClip(ClipData.newPlainText("LAN Clipboard", t))
        } catch (e: Exception) {
        }
    }

    fun findBatch(id: String): Batch? {
        for (x in inbox) {
            if (x.id == id) return x
        }
        return null
    }

    fun putBatchOnClipboard(b: Batch): Boolean {
        try {
            var clip: ClipData? = null
            for ((idx, item) in b.items.withIndex()) {
                val ci: ClipData.Item
                val mime: String
                if (item.isText) {
                    val f = File(item.path)
                    if (!f.exists() || f.length() > 500000L) continue
                    ci = ClipData.Item(String(f.readBytes(), Charsets.UTF_8))
                    mime = "text/plain"
                } else {
                    var nm = item.name
                    if (nm.isEmpty()) nm = "file"
                    val uri = Uri.Builder()
                        .scheme("content")
                        .authority(RECV_AUTH)
                        .appendPath(b.id)
                        .appendPath(idx.toString())
                        .appendPath(nm)
                        .build()
                    ci = ClipData.Item(uri)
                    mime = mimeForName(nm)
                }
                val cur = clip
                if (cur == null) {
                    clip = ClipData(ClipDescription("LAN Clipboard", arrayOf(mime)), ci)
                } else {
                    cur.addItem(ctx.contentResolver, ci)
                }
            }
            val fin = clip ?: return false
            val cm = ctx.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            cm.setPrimaryClip(fin)
            return true
        } catch (e: Exception) {
            return false
        }
    }

    // Reads the clipboard (works only when this app has focus) and sends it.
    // Returns 1 = sent, 2 = already sent / our own clip, 0 = nothing readable.
    fun sendCurrentClipboard(c: Context): Int {
        try {
            val cm = c.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            val clip = cm.primaryClip ?: return 0
            if (clip.itemCount == 0) return 0
            val lbl = clip.description.label
            if (lbl != null && lbl.toString() == "LAN Clipboard") return 2
            val uris = ArrayList<Uri>()
            val texts = ArrayList<String>()
            val sb = StringBuilder()
            for (k in 0 until clip.itemCount) {
                val item = clip.getItemAt(k)
                val u = item.uri
                if (u != null && u.scheme == "content") {
                    uris.add(u)
                    sb.append(u.toString()).append('|')
                } else {
                    val t = item.coerceToText(c)
                    if (t != null && t.isNotEmpty()) {
                        texts.add(t.toString())
                        sb.append(t.toString()).append('|')
                    }
                }
            }
            if (uris.isEmpty() && texts.isEmpty()) return 0
            val sig = sb.length.toString() + ":" + sb.toString().hashCode().toString()
            if (sig == prefs.getString("lastsig", "")) return 2
            prefs.edit().putString("lastsig", sig).apply()
            copyFiles(uris, texts)
            return 1
        } catch (e: Exception) {
            return 0
        }
    }

    // ---- copying (staging + sending) ----

    fun copyFiles(uris: List<Uri>, texts: List<String>) {
        pool.execute {
            val list = ArrayList<OutItem>()
            for (u in uris) {
                var name = "file"
                var size = -1L
                try {
                    val cur = ctx.contentResolver.query(u, null, null, null, null)
                    if (cur != null) {
                        cur.use { c ->
                            if (c.moveToFirst()) {
                                val ni = c.getColumnIndex(OpenableColumns.DISPLAY_NAME)
                                if (ni >= 0 && !c.isNull(ni)) name = c.getString(ni)
                                val si = c.getColumnIndex(OpenableColumns.SIZE)
                                if (si >= 0 && !c.isNull(si)) size = c.getLong(si)
                            }
                        }
                    }
                } catch (e: Exception) {
                }
                if (!name.contains('.')) {
                    var ext: String? = null
                    try {
                        val t = ctx.contentResolver.getType(u)
                        if (t != null) ext = MimeTypeMap.getSingleton().getExtensionFromMimeType(t)
                    } catch (e: Exception) {
                    }
                    if (ext != null) name = name + "." + ext
                }
                list.add(OutItem(newId(), false, name, u.toString(), "", size))
            }
            for (t in texts) {
                list.add(OutItem(newId(), true, "text", "", t, t.toByteArray(Charsets.UTF_8).size.toLong()))
            }
            handler.post { stageAndSend(list) }
        }
    }

    private fun stageAndSend(list: List<OutItem>) {
        if (list.isEmpty()) return
        staged.clear()
        staged.addAll(list)
        saveStaged()
        changed()
        resend()
    }

    fun resend() {
        if (staged.isEmpty()) {
            status("Nothing copied yet.")
            return
        }
        val items = ArrayList<OutItem>(staged)
        var n = 0
        for (p in peers.values) {
            if (!p.selected) continue
            n++
            enqueue(p, Delivery(newId(), items, System.currentTimeMillis()))
        }
        if (n == 0) {
            status("Copied. No other device found yet - open the app on the other phone (same Wi-Fi) and copy again.")
        }
    }

    private fun openSource(item: OutItem): Src {
        val uri = Uri.parse(item.uriStr)
        if (item.size >= 0L) {
            val st = ctx.contentResolver.openInputStream(uri) ?: throw IOException("cannot open " + item.name)
            return Src(st, item.size, null)
        }
        val tmp = File(ctx.cacheDir, "tmp_" + System.nanoTime().toString())
        val ins = ctx.contentResolver.openInputStream(uri) ?: throw IOException("cannot open " + item.name)
        val buf = ByteArray(65536)
        ins.use { i ->
            FileOutputStream(tmp).use { o ->
                while (true) {
                    val n = i.read(buf)
                    if (n < 0) break
                    o.write(buf, 0, n)
                }
            }
        }
        return Src(FileInputStream(tmp), tmp.length(), tmp)
    }

    private fun sendOnce(p: Peer, d: Delivery): Boolean {
        val items = d.items
        val s = Socket()
        try {
            s.tcpNoDelay = true
            s.connect(InetSocketAddress(p.ip, TCP_PORT), 3000)
            s.soTimeout = 60000
            val out = DataOutputStream(BufferedOutputStream(s.getOutputStream(), 65536))
            val inp = s.getInputStream()
            out.writeInt(MAGIC)
            out.writeUTF(myId)
            out.writeUTF(myName)
            out.writeUTF(d.batchId)
            out.writeInt(items.size)
            out.flush()
            val first = inp.read()
            if (first < 0) throw IOException("no reply")
            if (first == 2) {
                status("Sent " + items.size.toString() + " item(s) to " + p.name + " - done")
                return true
            }
            var total = 0L
            for (item in items) {
                total += if (item.isText) item.text.toByteArray(Charsets.UTF_8).size.toLong() else maxOf(item.size, 0L)
            }
            var sent = 0L
            var lastPct = -1
            val buf = ByteArray(65536)
            for (item in items) {
                if (item.isText) {
                    val bytes = item.text.toByteArray(Charsets.UTF_8)
                    out.writeByte(1)
                    out.writeUTF("")
                    out.writeLong(bytes.size.toLong())
                    out.write(bytes)
                    sent += bytes.size.toLong()
                } else {
                    val src = openSource(item)
                    try {
                        out.writeByte(0)
                        out.writeUTF(item.name)
                        out.writeLong(src.size)
                        var left = src.size
                        while (left > 0L) {
                            val want = minOf(buf.size.toLong(), left).toInt()
                            val n = src.stream.read(buf, 0, want)
                            if (n < 0) throw IOException("source ended early")
                            out.write(buf, 0, n)
                            left -= n.toLong()
                            sent += n.toLong()
                            val pct = if (total > 0L) ((sent * 100L) / total).toInt() else 100
                            if (pct != lastPct) {
                                lastPct = pct
                                status("Sending to " + p.name + ": " + pct.toString() + "%")
                            }
                        }
                    } finally {
                        src.close()
                    }
                }
            }
            out.flush()
            val ack = inp.read()
            if (ack < 0) throw IOException("no confirmation")
            status("Sent " + items.size.toString() + " item(s) to " + p.name + " - done")
            return true
        } catch (e: Exception) {
            lastErr = e.message ?: "error"
            return false
        } finally {
            try {
                s.close()
            } catch (e: Exception) {
            }
        }
    }

    // ---- delivery queue: every copy is kept until the other phone confirms it ----

    private fun enqueue(p: Peer, d: Delivery) {
        val list = pending.getOrPut(p.id) { ArrayList<Delivery>() }
        synchronized(list) {
            list.add(d)
            while (list.size > 20) list.removeAt(0)
        }
        kick(p)
    }

    fun kick(p: Peer) {
        if (!running) return
        val list = pending[p.id] ?: return
        val has = synchronized(list) { list.isNotEmpty() }
        if (!has) return
        if (p.sending.compareAndSet(false, true)) {
            pool.execute { drain(p) }
        }
    }

    private fun kickAll() {
        for (p in peers.values) kick(p)
    }

    private fun drain(p: Peer) {
        try {
            while (running) {
                val list = pending[p.id] ?: break
                val d: Delivery = synchronized(list) { if (list.isEmpty()) null else list[0] } ?: break
                if (System.currentTimeMillis() - d.created > 300000L) {
                    synchronized(list) {
                        if (list.isNotEmpty() && list[0] === d) list.removeAt(0)
                    }
                    continue
                }
                var ok = false
                var attempt = 0
                while (attempt < 3 && !ok) {
                    ok = sendOnce(p, d)
                    if (!ok) {
                        attempt += 1
                        try {
                            Thread.sleep(500)
                        } catch (e: InterruptedException) {
                        }
                    }
                }
                if (ok) {
                    synchronized(list) {
                        if (list.isNotEmpty() && list[0] === d) list.removeAt(0)
                    }
                } else {
                    status(p.name + " not reachable (" + lastErr + ") - will retry automatically")
                    break
                }
            }
        } finally {
            p.sending.set(false)
        }
    }

    fun removeStaged(id: String) {
        var idx = -1
        for (k in 0 until staged.size) {
            if (staged[k].id == id) idx = k
        }
        if (idx >= 0) {
            staged.removeAt(idx)
            saveStaged()
            changed()
        }
    }

    fun clearAll() {
        staged.clear()
        for (b in inbox) {
            try {
                File(inboxDir, b.id).deleteRecursively()
            } catch (e: Exception) {
            }
        }
        inbox.clear()
        saveStaged()
        saveInbox()
        changed()
        status("Cleared.")
    }

    // ---- pasting ----

    private fun maxNumber(tree: Uri): Long {
        var best = 0L
        try {
            val children = DocumentsContract.buildChildDocumentsUriUsingTree(tree, DocumentsContract.getTreeDocumentId(tree))
            val cur = ctx.contentResolver.query(children, arrayOf(DocumentsContract.Document.COLUMN_DISPLAY_NAME), null, null, null)
            if (cur != null) {
                cur.use { c ->
                    while (c.moveToNext()) {
                        val nm = c.getString(0)
                        if (nm != null) {
                            val dot = nm.lastIndexOf('.')
                            val base = if (dot > 0) nm.substring(0, dot) else nm
                            val v = base.toLongOrNull()
                            if (v != null && v > best) best = v
                        }
                    }
                }
            }
        } catch (e: Exception) {
        }
        return best
    }

    fun pasteBatch(b: Batch, tree: Uri?) {
        pool.execute {
            try {
                val texts = ArrayList<String>()
                var savedCount = 0
                var next = if (tree != null) maxNumber(tree) + 1L else 1L
                val parent: Uri? = if (tree != null) DocumentsContract.buildDocumentUriUsingTree(tree, DocumentsContract.getTreeDocumentId(tree)) else null
                val buf = ByteArray(65536)
                var totalFiles = 0
                for (it2 in b.items) {
                    if (!it2.isText) totalFiles++
                }
                for (item in b.items) {
                    if (item.isText) {
                        val f = File(item.path)
                        if (f.exists() && f.length() <= 2000000L) texts.add(String(f.readBytes(), Charsets.UTF_8))
                    } else {
                        if (parent == null) continue
                        val dot = item.name.lastIndexOf('.')
                        val ext = if (dot >= 0 && dot < item.name.length - 1) item.name.substring(dot + 1) else ""
                        var mime: String? = null
                        if (ext.isNotEmpty()) mime = MimeTypeMap.getSingleton().getMimeTypeFromExtension(ext.lowercase())
                        val mimeFinal: String = mime ?: "application/octet-stream"
                        val display = if (ext.isNotEmpty()) next.toString() + "." + ext else next.toString()
                        val doc = DocumentsContract.createDocument(ctx.contentResolver, parent, mimeFinal, display)
                            ?: throw IOException("Cannot create file in folder")
                        val os = ctx.contentResolver.openOutputStream(doc) ?: throw IOException("Cannot write file")
                        FileInputStream(File(item.path)).use { ins ->
                            os.use { o ->
                                while (true) {
                                    val n = ins.read(buf)
                                    if (n < 0) break
                                    o.write(buf, 0, n)
                                }
                            }
                        }
                        next++
                        savedCount++
                        status("Pasting " + savedCount.toString() + "/" + totalFiles.toString() + " ...")
                    }
                }
                val joined = texts.joinToString("\n")
                val msg = "Pasted " + savedCount.toString() + " file(s)" + (if (texts.isNotEmpty()) " + text (now in your clipboard)" else "") + "."
                handler.post {
                    if (joined.isNotEmpty()) setClipboardText(joined)
                }
                status(msg)
            } catch (e: Exception) {
                status("Paste failed: " + e.message)
            }
        }
    }

    // ---- remembered devices (kept for 30 days, never need to be picked again) ----

    fun savePeers() {
        try {
            val arr = JSONArray()
            for (p in peers.values) {
                val o = JSONObject()
                o.put("id", p.id)
                o.put("n", p.name)
                o.put("ip", p.ip)
                o.put("sel", p.selected)
                o.put("t", p.everSeen)
                arr.put(o)
            }
            prefs.edit().putString("peers", arr.toString()).apply()
        } catch (e: Exception) {
        }
    }

    private fun loadPeers() {
        try {
            val s = prefs.getString("peers", null) ?: return
            val a = JSONArray(s)
            val now = System.currentTimeMillis()
            for (k in 0 until a.length()) {
                val o = a.getJSONObject(k)
                val t = o.optLong("t", 0L)
                if (now - t > 30L * 24L * 3600L * 1000L) continue
                val p = Peer(o.getString("id"), o.getString("n"), o.getString("ip"))
                p.selected = o.optBoolean("sel", true)
                p.everSeen = t
                p.lastSeen = 0L
                peers[p.id] = p
            }
        } catch (e: Exception) {
        }
    }

    // ---- persistence ----

    fun saveStaged() {
        try {
            val arr = JSONArray()
            for (s in staged) {
                val o = JSONObject()
                o.put("id", s.id)
                o.put("t", s.isText)
                o.put("n", s.name)
                o.put("u", s.uriStr)
                o.put("x", s.text)
                o.put("s", s.size)
                arr.put(o)
            }
            prefs.edit().putString("staged", arr.toString()).apply()
        } catch (e: Exception) {
        }
    }

    fun saveInbox() {
        try {
            val arr = JSONArray()
            for (b in inbox) {
                val o = JSONObject()
                o.put("id", b.id)
                o.put("from", b.from)
                o.put("time", b.time)
                val ia = JSONArray()
                for (i in b.items) {
                    val io = JSONObject()
                    io.put("t", i.isText)
                    io.put("n", i.name)
                    io.put("p", i.path)
                    io.put("s", i.size)
                    ia.put(io)
                }
                o.put("items", ia)
                arr.put(o)
            }
            prefs.edit().putString("inbox", arr.toString()).apply()
        } catch (e: Exception) {
        }
    }

    fun saveAll() {
        saveStaged()
        saveInbox()
    }

    private fun loadState() {
        try {
            val s = prefs.getString("staged", null)
            if (s != null) {
                val a = JSONArray(s)
                for (k in 0 until a.length()) {
                    val o = a.getJSONObject(k)
                    staged.add(
                        OutItem(
                            o.getString("id"), o.getBoolean("t"), o.getString("n"),
                            o.getString("u"), o.getString("x"), o.getLong("s")
                        )
                    )
                }
            }
        } catch (e: Exception) {
        }
        try {
            val s = prefs.getString("inbox", null)
            if (s != null) {
                val a = JSONArray(s)
                for (k in 0 until a.length()) {
                    val o = a.getJSONObject(k)
                    val ia = o.getJSONArray("items")
                    val items = ArrayList<InItem>()
                    var ok = true
                    for (m in 0 until ia.length()) {
                        val io = ia.getJSONObject(m)
                        val path = io.getString("p")
                        if (!File(path).exists()) ok = false
                        items.add(InItem(io.getBoolean("t"), io.getString("n"), path, io.getLong("s")))
                    }
                    if (ok && items.isNotEmpty()) {
                        inbox.add(Batch(o.getString("id"), o.getString("from"), o.getLong("time"), items))
                    }
                }
            }
        } catch (e: Exception) {
        }
    }
}

// ───────────────────────── file provider (lets other apps paste received files) ─────────────────────────

class RecvProvider : ContentProvider() {
    override fun onCreate(): Boolean = true

    private fun fileFor(uri: Uri): File? {
        val c = context ?: return null
        val segs = uri.pathSegments
        if (segs.size < 3) return null
        val batch = segs[0]
        val idx = segs[1]
        if (!batch.matches(Regex("[0-9_]+"))) return null
        if (!idx.matches(Regex("[0-9]+"))) return null
        val f = File(File(File(c.filesDir, "inbox"), batch), idx + ".dat")
        return if (f.exists()) f else null
    }

    override fun query(
        uri: Uri,
        projection: Array<out String>?,
        selection: String?,
        selectionArgs: Array<out String>?,
        sortOrder: String?
    ): Cursor? {
        val f = fileFor(uri) ?: return null
        val name = uri.lastPathSegment ?: "file"
        val cols: Array<String> = if (projection != null) {
            Array(projection.size) { k -> projection[k] }
        } else {
            arrayOf(OpenableColumns.DISPLAY_NAME, OpenableColumns.SIZE)
        }
        val cur = MatrixCursor(cols)
        val row = arrayOfNulls<Any>(cols.size)
        for (k in cols.indices) {
            if (cols[k] == OpenableColumns.DISPLAY_NAME) row[k] = name
            else if (cols[k] == OpenableColumns.SIZE) row[k] = f.length()
        }
        cur.addRow(row)
        return cur
    }

    override fun getType(uri: Uri): String? {
        val name = uri.lastPathSegment ?: return "application/octet-stream"
        return mimeForName(name)
    }

    override fun openFile(uri: Uri, mode: String): ParcelFileDescriptor? {
        val f = fileFor(uri) ?: throw FileNotFoundException("not found")
        return ParcelFileDescriptor.open(f, ParcelFileDescriptor.MODE_READ_ONLY)
    }

    override fun insert(uri: Uri, values: ContentValues?): Uri? = null

    override fun delete(uri: Uri, selection: String?, selectionArgs: Array<out String>?): Int = 0

    override fun update(uri: Uri, values: ContentValues?, selection: String?, selectionArgs: Array<out String>?): Int = 0
}

object LanHolder {
    @Volatile var core: Lan? = null

    @Synchronized
    fun get(ctx: Context): Lan {
        val c = core
        if (c != null) return c
        val n = Lan(ctx.applicationContext)
        core = n
        return n
    }
}

// ───────────────────────── keep-alive service ─────────────────────────

class KeepAliveService : Service() {
    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        try {
            val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            val ch = NotificationChannel("lanclip", "LAN Clipboard", NotificationManager.IMPORTANCE_LOW)
            nm.createNotificationChannel(ch)
            val pi = PendingIntent.getActivity(
                this, 0, Intent(this, MainActivity::class.java), PendingIntent.FLAG_IMMUTABLE
            )
            val n = Notification.Builder(this, "lanclip")
                .setContentTitle("File Batch Copier: LAN copy is ON")
                .setContentText("Ready to send and receive files on your Wi-Fi")
                .setSmallIcon(android.R.drawable.stat_notify_sync)
                .setContentIntent(pi)
                .build()
            startForeground(1, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_DATA_SYNC)
        } catch (e: Exception) {
        }
        val on = getSharedPreferences("imgbatch", Context.MODE_PRIVATE).getBoolean("lanon", false)
        if (!on) {
            stopSelf()
            return START_NOT_STICKY
        }
        LanHolder.get(applicationContext).start()
        return START_STICKY
    }
}


// One shared brain used by both the main screen and the floating panel (same process, same state).
object Core {
    const val AUTH = "com.example.myapp.clip"

    private val main = Handler(Looper.getMainLooper())
    private val listeners = CopyOnWriteArrayList<Runnable>()
    private var inited = false
    private lateinit var app: Context
    private lateinit var prefs: SharedPreferences

    @Volatile
    var files: List<FileItem> = emptyList()
    var treeUri: Uri? = null
    var batch: Int = 7
    var pos: Int = 0
    var sub: Int = 0
    var lastMsg: String = ""
    var lastError: String = ""
    var loading: Boolean = false
    var loadCount: Int = 0
    var lanOn: Boolean = false

    // Text files chosen with "Choose txt files" (any size - they are streamed, never loaded into memory).
    @Volatile
    var txtFiles: List<TxtItem> = emptyList()

    @Volatile
    var txtAttach: Boolean = true

    @Volatile
    private var loadToken: Int = 0

    fun init(ctx: Context) {
        if (inited) return
        inited = true
        app = ctx.applicationContext
        prefs = app.getSharedPreferences("imgbatch", Context.MODE_PRIVATE)
        batch = prefs.getInt("batch", 7)
        pos = prefs.getInt("pos", 0)
        sub = prefs.getInt("sub", 0)
        val saved = prefs.getString("tree", null)
        if (saved != null) {
            treeUri = Uri.parse(saved)
            reload()
        }
        lanOn = prefs.getBoolean("lanon", false)
        txtAttach = prefs.getBoolean("txtattach", true)
        loadTxt()
        if (lanOn) startLanNow()
    }

    // ---------- Chosen txt files ----------

    private fun loadTxt() {
        try {
            val sv = prefs.getString("txtfiles", null) ?: return
            val a = JSONArray(sv)
            val out = ArrayList<TxtItem>()
            for (k in 0 until a.length()) {
                val o = a.getJSONObject(k)
                out.add(TxtItem(o.getString("u"), o.getString("n")))
            }
            txtFiles = out
        } catch (e: Exception) {
        }
    }

    private fun saveTxt() {
        try {
            val a = JSONArray()
            for (t in txtFiles) {
                val o = JSONObject()
                o.put("u", t.uri)
                o.put("n", t.name)
                a.put(o)
            }
            prefs.edit().putString("txtfiles", a.toString()).apply()
        } catch (e: Exception) {
        }
    }

    // Reads the file names on a background thread, then shows the new list.
    fun setTxtFromUris(uris: List<Uri>) {
        val old = txtFiles
        Thread {
            val out = ArrayList<TxtItem>()
            for (u in uris) {
                var name = "text.txt"
                try {
                    app.contentResolver.query(u, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)?.use { c ->
                        if (c.moveToFirst() && !c.isNull(0)) {
                            name = c.getString(0)
                        }
                    }
                } catch (e: Exception) {
                }
                out.add(TxtItem(u.toString(), name))
            }
            main.post {
                txtFiles = out
                saveTxt()
                for (o in old) {
                    var keep = false
                    for (n in out) {
                        if (n.uri == o.uri) keep = true
                    }
                    if (!keep) {
                        try {
                            app.contentResolver.releasePersistableUriPermission(
                                Uri.parse(o.uri), Intent.FLAG_GRANT_READ_URI_PERMISSION
                            )
                        } catch (e: Exception) {
                        }
                    }
                }
                lastMsg = out.size.toString() + " txt file(s) chosen. They are copied with every batch."
                changed()
            }
        }.start()
    }

    fun clearTxt() {
        txtFiles = emptyList()
        saveTxt()
        lastMsg = "Chosen txt files cleared."
        changed()
    }

    fun changeTxtAttach(on: Boolean) {
        txtAttach = on
        prefs.edit().putBoolean("txtattach", on).apply()
        changed()
    }

    // Only the chosen files that can still be opened (a moved or deleted file is skipped).
    fun usableTxt(): List<TxtItem> {
        val out = ArrayList<TxtItem>()
        if (!txtAttach) return out
        for (t in txtFiles) {
            try {
                val pfd = app.contentResolver.openFileDescriptor(Uri.parse(t.uri), "r")
                if (pfd != null) {
                    pfd.close()
                    out.add(t)
                }
            } catch (e: Exception) {
            }
        }
        return out
    }

    fun txtProviderUri(t: TxtItem): Uri {
        return Uri.Builder()
            .scheme("content")
            .authority(AUTH)
            .appendPath(t.uri)
            .appendPath(t.name)
            .build()
    }

    fun txtSummary(): String {
        val l = txtFiles
        if (l.isEmpty()) return "No txt files chosen."
        val sb = StringBuilder()
        sb.append(l.size).append(" txt file(s): ")
        for (k in 0 until minOf(l.size, 5)) {
            if (k > 0) sb.append(", ")
            sb.append(l[k].name)
        }
        if (l.size > 5) sb.append(" ...")
        if (!txtAttach) sb.append("   (switched off)")
        return sb.toString()
    }

    private fun textNote(): String {
        val n = usableTxt().size
        if (n > 0) {
            return "\n+ " + n + " chosen txt file(s) copied with the files."
        }
        return ""
    }

    fun addListener(r: Runnable) {
        if (!listeners.contains(r)) listeners.add(r)
    }

    fun removeListener(r: Runnable) {
        listeners.remove(r)
    }

    fun changed() {
        main.post {
            for (l in listeners) l.run()
        }
    }

    fun save() {
        val t = treeUri
        val e = prefs.edit().putInt("batch", batch).putInt("pos", pos).putInt("sub", sub).putBoolean("lanon", lanOn)
        if (t != null) e.putString("tree", t.toString())
        e.apply()
    }

    fun setTree(u: Uri) {
        treeUri = u
        files = emptyList()
        pos = 0
        sub = 0
        lastMsg = ""
        lastError = ""
        save()
        reload()
    }

    // ---------- LAN copy mode ----------

    fun lan(): Lan {
        val l = LanHolder.get(app)
        l.onChange = { changed() }
        l.statusListener = { _ -> changed() }
        return l
    }

    private fun startLanNow() {
        lan().start()
        try {
            app.startForegroundService(Intent(app, KeepAliveService::class.java))
        } catch (e: Exception) {
        }
    }

    private fun stopLanNow() {
        try {
            app.stopService(Intent(app, KeepAliveService::class.java))
        } catch (e: Exception) {
        }
        lan().stop()
    }

    fun setLan(on: Boolean) {
        lanOn = on
        save()
        if (on) startLanNow() else stopLanNow()
        changed()
    }

    fun lanText(): String {
        if (!lanOn) return "LAN copy: OFF"
        val l = lan()
        var sel = 0
        var on = 0
        for (p in l.peers.values) {
            if (p.selected) sel++
            if (p.online()) on++
        }
        return "LAN copy: ON   |   " + on + " online, " + l.peers.size + " remembered, " + sel + " selected\n" + l.lastStatus
    }

    private fun sendLan(items: List<FileItem>) {
        if (!lanOn) return
        try {
            val uris = ArrayList<Uri>()
            for (it2 in items) {
                uris.add(docUri(it2))
            }
            for (t in usableTxt()) {
                uris.add(Uri.parse(t.uri))
            }
            lan().copyFiles(uris, ArrayList<String>())
        } catch (ex: Exception) {
            lastMsg = "LAN send failed: " + ex.message
        }
    }

    fun copyReceived(): String? {
        val l = lan()
        if (l.inbox.isEmpty()) return "Nothing received yet."
        if (!l.putBatchOnClipboard(l.inbox[0])) return "Could not copy to clipboard."
        lastMsg = "Received files are on your clipboard. Now paste."
        changed()
        return null
    }

    // ---------- Folder reading (background, cached) ----------

    private fun cacheFile(t: Uri): File {
        return File(app.cacheDir, "all_" + t.toString().hashCode() + ".txt")
    }

    private fun loadCache(f: File): ArrayList<FileItem> {
        val out = ArrayList<FileItem>()
        try {
            if (!f.exists()) return out
            f.bufferedReader().use { r ->
                while (true) {
                    val line = r.readLine() ?: break
                    val tab = line.indexOf('\t')
                    if (tab > 0) {
                        out.add(FileItem(line.substring(tab + 1), line.substring(0, tab)))
                    }
                }
            }
        } catch (e: Exception) {
        }
        return out
    }

    private fun saveCache(f: File, list: List<FileItem>) {
        try {
            f.bufferedWriter().use { w ->
                for (e in list) {
                    w.write(e.docId)
                    w.write("\t")
                    w.write(e.name)
                    w.write("\n")
                }
            }
        } catch (ex: Exception) {
        }
    }

    private fun sameList(a: List<FileItem>, b: List<FileItem>): Boolean {
        if (a.size != b.size) return false
        for (i in a.indices) {
            if (a[i].docId != b[i].docId) return false
        }
        return true
    }

    private fun applyList(list: List<FileItem>) {
        files = list
        if (pos > list.size) {
            pos = 0
            sub = 0
        }
        save()
        changed()
    }

    // The screen is usable at once from the saved list, then the real folder is read in the background.
    fun reload() {
        val t = treeUri
        if (t == null) {
            changed()
            return
        }
        loadToken += 1
        val token = loadToken
        val cf = cacheFile(t)
        val needCache = files.isEmpty()
        loading = true
        loadCount = 0
        changed()
        Thread {
            if (needCache) {
                val cached = loadCache(cf)
                if (cached.isNotEmpty()) {
                    main.post {
                        if (token == loadToken) applyList(cached)
                    }
                }
            }
            val res = listFolder(t, token)
            main.post {
                if (token == loadToken) {
                    lastError = res.error
                    loading = false
                    if (res.error.isNotEmpty() && files.isNotEmpty()) {
                        changed()
                    } else if (files.isEmpty() || !sameList(files, res.items)) {
                        applyList(res.items)
                    } else {
                        changed()
                    }
                }
            }
            if (res.error.isEmpty() && token == loadToken) {
                saveCache(cf, res.items)
            }
        }.start()
    }

    private fun listFolder(tree: Uri, token: Int): ListRes {
        val out = ArrayList<FileItem>()
        var err = ""
        try {
            val treeId = DocumentsContract.getTreeDocumentId(tree)
            val kids = DocumentsContract.buildChildDocumentsUriUsingTree(tree, treeId)
            val cols = arrayOf(
                DocumentsContract.Document.COLUMN_DOCUMENT_ID,
                DocumentsContract.Document.COLUMN_DISPLAY_NAME,
                DocumentsContract.Document.COLUMN_MIME_TYPE
            )
            app.contentResolver.query(kids, cols, null, null, null)?.use { c ->
                while (c.moveToNext()) {
                    if (token != loadToken) break
                    val id: String? = c.getString(0)
                    val name: String = c.getString(1) ?: ""
                    val mime: String = c.getString(2) ?: ""
                    if (id != null && mime != DocumentsContract.Document.MIME_TYPE_DIR) {
                        out.add(FileItem(name, id))
                        if (out.size % 2000 == 0) {
                            val cnt = out.size
                            main.post {
                                if (token == loadToken) {
                                    loadCount = cnt
                                    changed()
                                }
                            }
                        }
                    }
                }
            }
        } catch (e: Exception) {
            err = e.message ?: "error"
        }
        out.sortWith(Comparator<FileItem> { a, b ->
            val c = natCompare(a.name, b.name)
            if (c != 0) c else a.name.compareTo(b.name)
        })
        return ListRes(out, err)
    }

    // ---------- Batch helpers ----------

    fun docUri(e: FileItem): Uri {
        val t = treeUri ?: throw IllegalStateException("No folder")
        return DocumentsContract.buildDocumentUriUsingTree(t, e.docId)
    }

    fun providerUri(e: FileItem): Uri {
        return Uri.Builder()
            .scheme("content")
            .authority(AUTH)
            .appendPath(docUri(e).toString())
            .appendPath(e.name)
            .build()
    }

    fun batchEnd(): Int {
        return minOf(pos.toLong() + batch.toLong(), files.size.toLong()).toInt()
    }

    fun currentBatch(): ArrayList<FileItem> {
        if (pos >= files.size) return ArrayList<FileItem>()
        return ArrayList<FileItem>(files.subList(pos, batchEnd()))
    }

    @Suppress("DEPRECATION")
    fun buildClip(items: List<FileItem>, withText: Boolean = true): ClipData {
        val mimes = LinkedHashSet<String>()
        for (e in items) mimes.add(mimeOfName(e.name))
        val extra: List<TxtItem> = if (withText) usableTxt() else ArrayList<TxtItem>()
        for (t in extra) mimes.add(mimeOfName(t.name))
        val desc = ClipDescription("files", mimes.toTypedArray())
        val clip = ClipData(desc, ClipData.Item(providerUri(items[0])))
        for (k in 1 until items.size) {
            clip.addItem(ClipData.Item(providerUri(items[k])))
        }
        for (t in extra) {
            clip.addItem(ClipData.Item(txtProviderUri(t)))
        }
        return clip
    }

    fun shareType(items: List<FileItem>): String {
        val first = mimeOfName(items[0].name)
        val major = first.substringBefore('/')
        var same = true
        var sameMajor = true
        for (e in items) {
            val m = mimeOfName(e.name)
            if (m != first) same = false
            if (m.substringBefore('/') != major) sameMajor = false
        }
        return if (same) first else if (sameMajor) "$major/*" else "*/*"
    }

    private fun putOnClipboard(items: List<FileItem>): String? {
        try {
            val cm = app.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
            cm.setPrimaryClip(buildClip(items))
            return null
        } catch (e: Exception) {
            return "Copy failed: " + e.message
        }
    }

    // ---------- Actions (return an error text, or null when fine) ----------

    fun copyBatch(): String? {
        val items = currentBatch()
        if (items.isEmpty()) return "Nothing to copy. Pick a folder or tap Reset."
        val err = putOnClipboard(items)
        if (err != null) return err
        sendLan(items)
        lastMsg = "Copied " + items.first().name + " to " + items.last().name +
            " (" + items.size + " files). Now paste in the other app." +
            textNote() +
            (if (lanOn) "\nAlso sending to your other devices (LAN)." else "")
        pos = batchEnd()
        sub = 0
        save()
        changed()
        return null
    }

    fun copyOne(): String? {
        val total = files.size
        if (pos >= total) return "Nothing to copy. Pick a folder or tap Reset."
        val count = batchEnd() - pos
        if (sub >= count) sub = 0
        val e = files[pos + sub]
        val err = putOnClipboard(listOf(e))
        if (err != null) return err
        sendLan(listOf(e))
        sub += 1
        if (sub >= count) {
            lastMsg = "Copied " + e.name + " (last one of this batch). Next batch is ready." + textNote()
            pos = batchEnd()
            sub = 0
        } else {
            lastMsg = "Copied " + e.name + " (" + sub + " of " + count + "). Now paste." + textNote()
        }
        save()
        changed()
        return null
    }

    fun afterShare(items: List<FileItem>) {
        lastMsg = "Shared " + items.first().name + " to " + items.last().name +
            " (" + items.size + " files)."
        pos = batchEnd()
        sub = 0
        save()
        changed()
    }

    fun prevBatch() {
        pos = maxOf(0, pos - batch)
        sub = 0
        lastMsg = "Went back one batch."
        save()
        changed()
    }

    // Jump so that the next batch starts at file number n (1 = first file in the list).
    // Returns an error text, or null when fine.
    fun jumpTo(n: Int): String? {
        val total = files.size
        if (treeUri == null || total == 0) return "Pick a folder first."
        if (n < 1 || n > total) return "Enter a file number from 1 to " + total + "."
        pos = n - 1
        sub = 0
        lastMsg = "Jumped to file " + n + " (" + files[pos].name + ")."
        save()
        changed()
        return null
    }

    fun resetAll() {
        pos = 0
        sub = 0
        lastMsg = "Reset to the start."
        save()
        changed()
    }

    fun changeBatch(n: Int) {
        batch = maxOf(1, n)
        sub = 0
        lastMsg = "Batch size set to " + batch + "."
        save()
        changed()
    }

    fun statusText(compact: Boolean): String {
        return statusBase(compact) + "\n\n" + lanText()
    }

    private fun statusBase(compact: Boolean): String {
        if (treeUri == null) {
            return if (compact) "No folder chosen. Open the app and pick a folder."
            else "No folder chosen yet.\nTap \"Pick folder\" and choose the folder with your files."
        }
        val total = files.size
        if (total == 0) {
            if (loading) return "Reading folder... " + loadCount + " files found"
            val extra = if (lastError.isEmpty()) "" else "\n(" + lastError + ")"
            return "No files found in that folder." + extra
        }
        if (pos >= total) {
            return "Done: all " + total + " files used.\nTap \"Reset\" to start again." +
                (if (lastMsg.isEmpty()) "" else "\n\n" + lastMsg)
        }
        val end = batchEnd()
        val sb = StringBuilder()
        sb.append("Folder: ").append(total).append(" files   |   Batch: ").append(batch)
        if (loading) sb.append("   (updating...)")
        sb.append("\n")
        sb.append("Next: #").append(pos + 1).append(" ").append(files[pos].name)
            .append(" to #").append(end).append(" ").append(files[end - 1].name)
            .append("  (").append(end - pos).append(" files)\n")
        if (sub > 0 && pos + sub < end) {
            sb.append("Copy one: next is ").append(files[pos + sub].name).append("\n")
        }
        if (lastMsg.isNotEmpty()) {
            sb.append("\n").append(lastMsg)
        }
        return sb.toString()
    }
}

class MainActivity : Activity() {

    companion object {
        const val REQ_TREE = 101
        const val REQ_NOTIF = 102
        const val REQ_TXT = 104
        const val REQ_LAN = 103
    }

    private lateinit var rootView: LinearLayout
    private lateinit var status: TextView
    private lateinit var batchEdit: EditText
    private lateinit var jumpEdit: EditText
    private lateinit var strip: LinearLayout
    private lateinit var stripScroll: HorizontalScrollView
    private lateinit var lanB: Button
    private lateinit var txtInfo: TextView

    private var thumbToken: Int = 0
    private var lastThumbKey: String = ""
    private val ui = Runnable { refreshAll() }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        Core.init(this)
        buildUi()
        refreshAll()
    }

    override fun onResume() {
        super.onResume()
        Core.addListener(ui)
        refreshAll()
    }

    override fun onPause() {
        super.onPause()
        Core.removeListener(ui)
        Core.save()
    }

    // ---------- UI ----------

    private fun dp(v: Int): Int {
        return (v * resources.displayMetrics.density).toInt()
    }

    private fun mkBtn(text: String, onClick: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.isAllCaps = false
        b.isFocusable = false
        b.textSize = 13f
        b.setOnClickListener { onClick() }
        return b
    }

    private fun mkRow(vararg views: View): LinearLayout {
        val r = LinearLayout(this)
        r.orientation = LinearLayout.HORIZONTAL
        for (v in views) {
            r.addView(v, LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f))
        }
        return r
    }

    private fun buildUi() {
        val root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        root.setPadding(dp(8), dp(8), dp(8), dp(8))
        root.isFocusable = true
        root.isFocusableInTouchMode = true

        val pickB = mkBtn("Pick folder") { pickFolder() }
        batchEdit = EditText(this)
        batchEdit.inputType = InputType.TYPE_CLASS_NUMBER
        batchEdit.setText(Core.batch.toString())
        batchEdit.gravity = Gravity.CENTER
        batchEdit.hint = "Batch"
        batchEdit.imeOptions = EditorInfo.IME_ACTION_DONE
        batchEdit.setOnEditorActionListener { _, _, _ ->
            applyBatchSize()
            true
        }
        val setB = mkBtn("Set size") { applyBatchSize() }
        root.addView(mkRow(pickB, batchEdit, setB))

        val copyB = mkBtn("Copy batch") { report(Core.copyBatch()) }
        val oneB = mkBtn("Copy one") { report(Core.copyOne()) }
        val shareB = mkBtn("Share batch") { shareBatch() }
        root.addView(mkRow(copyB, oneB, shareB))

        val prevB = mkBtn("Prev batch") { Core.prevBatch() }
        val resetB = mkBtn("Reset to 1") { Core.resetAll() }
        val refreshB = mkBtn("Refresh list") { Core.reload() }
        root.addView(mkRow(prevB, resetB, refreshB))

        // Jump straight to any file number
        jumpEdit = EditText(this)
        jumpEdit.inputType = InputType.TYPE_CLASS_NUMBER
        jumpEdit.gravity = Gravity.CENTER
        jumpEdit.hint = "File no."
        jumpEdit.imeOptions = EditorInfo.IME_ACTION_GO
        jumpEdit.setOnEditorActionListener { _, _, _ ->
            applyJump()
            true
        }
        val jumpB = mkBtn("Jump to file") { applyJump() }
        root.addView(mkRow(jumpEdit, jumpB))

        val floatB = mkBtn("Float on top") { startFloat() }
        val stopFloatB = mkBtn("Stop float") { stopFloat() }
        root.addView(mkRow(floatB, stopFloatB))

        lanB = mkBtn("LAN copy: OFF") { toggleLan() }
        val devB = mkBtn("Devices") { showDevices() }
        val gotB = mkBtn("Copy received") { report(Core.copyReceived()) }
        root.addView(mkRow(lanB, devB, gotB))

        // Text files (any size) that travel with every batch
        val txtCb = CheckBox(this)
        txtCb.text = "Also copy my chosen txt file(s) with every batch"
        txtCb.textSize = 14f
        txtCb.isChecked = Core.txtAttach
        txtCb.isFocusable = false
        txtCb.setOnCheckedChangeListener { _, c -> Core.changeTxtAttach(c) }
        root.addView(txtCb)
        val pickTxtB = mkBtn("Choose txt files") { pickTxt() }
        val clearTxtB = mkBtn("Clear txt files") { Core.clearTxt() }
        root.addView(mkRow(pickTxtB, clearTxtB))
        txtInfo = TextView(this)
        txtInfo.textSize = 12f
        txtInfo.setPadding(dp(6), dp(2), dp(6), dp(6))
        root.addView(txtInfo)

        status = TextView(this)
        status.textSize = 15f
        status.setPadding(dp(4), dp(10), dp(4), dp(10))
        root.addView(
            status,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT
            )
        )

        stripScroll = HorizontalScrollView(this)
        strip = LinearLayout(this)
        strip.orientation = LinearLayout.HORIZONTAL
        stripScroll.addView(strip)
        root.addView(
            stripScroll,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT
            )
        )

        val hint = TextView(this)
        hint.textSize = 12f
        hint.setPadding(dp(4), dp(14), dp(4), dp(4))
        hint.text = "Works with any file type (pdf, txt, images, zip ...). Files are copied in name order: " +
            "1, 2, 3 ... 10, 11.\n" +
            "After Copy: open the other app, tap in the box, then paste (long-press > Paste, or Ctrl+V).\n" +
            "Float on top: shows a small panel over every app. Drag the top bar to move it, drag the " +
            "bottom-right corner (finger or mouse) to resize it.\n" +
            "Choose txt files: pick one or more text files (any size). They are copied together with every batch " +
            "and sent to your other phones when LAN copy is ON. Large files are streamed, so the app does not freeze.\n" +
            "Keys: C copy batch, O copy one, S share, B previous, R reset, F float, L LAN on/off.\n" +
            "LAN copy: turn it ON in this app on every phone (same Wi-Fi). Then every Copy batch / Copy one " +
            "is also sent to the other phones and lands on their clipboards, ready to paste. " +
            "Use Devices to choose which phones receive the files."
        root.addView(
            hint,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT
            )
        )

        rootView = root
        val sv = ScrollView(this)
        sv.isFillViewport = true
        sv.addView(root, ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        setContentView(sv)
    }

    private fun toast(s: String) {
        Toast.makeText(this, s, Toast.LENGTH_SHORT).show()
    }

    private fun report(err: String?) {
        if (err != null) toast(err)
    }

    private fun hideKeyboard() {
        val imm = getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
        imm.hideSoftInputFromWindow(batchEdit.windowToken, 0)
    }

    // ---------- Folder ----------

    private fun pickFolder() {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        startActivityForResult(i, REQ_TREE)
    }

    private fun pickTxt() {
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "*/*"
        i.putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        startActivityForResult(i, REQ_TXT)
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (requestCode == REQ_TXT && resultCode == RESULT_OK && data != null) {
            val uris = ArrayList<Uri>()
            val cd = data.clipData
            if (cd != null) {
                for (k in 0 until cd.itemCount) {
                    val u = cd.getItemAt(k).uri
                    if (u != null) uris.add(u)
                }
            } else {
                val u = data.data
                if (u != null) uris.add(u)
            }
            for (u in uris) {
                try {
                    contentResolver.takePersistableUriPermission(u, Intent.FLAG_GRANT_READ_URI_PERMISSION)
                } catch (e: Exception) {
                }
            }
            if (uris.isNotEmpty()) Core.setTxtFromUris(uris)
        }
        if (requestCode == REQ_TREE && resultCode == RESULT_OK && data != null) {
            val u = data.data
            if (u != null) {
                try {
                    contentResolver.takePersistableUriPermission(u, Intent.FLAG_GRANT_READ_URI_PERMISSION)
                } catch (e: Exception) {
                }
                lastThumbKey = ""
                Core.setTree(u)
            }
        }
    }

    // ---------- Display ----------

    private fun refreshAll() {
        txtInfo.text = Core.txtSummary()
        status.text = Core.statusText(false)
        lanB.text = if (Core.lanOn) "LAN copy: ON" else "LAN copy: OFF"
        if (!batchEdit.hasFocus() && batchEdit.text.toString() != Core.batch.toString()) {
            batchEdit.setText(Core.batch.toString())
        }
        val total = Core.files.size
        if (Core.treeUri == null || total == 0 || Core.pos >= total) {
            if (lastThumbKey != "") {
                strip.removeAllViews()
                thumbToken += 1
                lastThumbKey = ""
            }
            return
        }
        val from = Core.pos
        val end = Core.batchEnd()
        val key = from.toString() + ":" + end + ":" + total + ":" + System.identityHashCode(Core.files)
        if (key != lastThumbKey) {
            lastThumbKey = key
            loadThumbs(from, end)
        }
    }

    private fun extLabel(name: String): String {
        val e = name.substringAfterLast('.', "").uppercase()
        if (e.isEmpty()) return "FILE"
        return if (e.length > 5) e.substring(0, 5) else e
    }

    // Only the first 30 files of the batch get a tile. Images show a preview, other files show their type.
    private fun loadThumbs(from: Int, to: Int) {
        strip.removeAllViews()
        thumbToken += 1
        val myToken = thumbToken
        val shownEnd = minOf(to, from + 30)
        val snapshot = ArrayList<FileItem>(Core.files.subList(from, shownEnd))
        val thumbs = ArrayList<ImageView?>()
        val docs = ArrayList<Uri?>()
        for (e in snapshot) {
            val lp = LinearLayout.LayoutParams(dp(96), dp(96))
            lp.setMargins(dp(2), dp(2), dp(2), dp(2))
            if (mimeOfName(e.name).startsWith("image/")) {
                val iv = ImageView(this)
                iv.scaleType = ImageView.ScaleType.CENTER_CROP
                iv.setBackgroundColor(Color.LTGRAY)
                strip.addView(iv, lp)
                thumbs.add(iv)
                docs.add(Core.docUri(e))
            } else {
                val tv = TextView(this)
                tv.gravity = Gravity.CENTER
                tv.setBackgroundColor(Color.LTGRAY)
                tv.setTextColor(Color.BLACK)
                tv.textSize = 12f
                tv.maxLines = 4
                tv.ellipsize = TextUtils.TruncateAt.END
                tv.setPadding(dp(4), dp(4), dp(4), dp(4))
                tv.text = extLabel(e.name) + "\n" + e.name
                strip.addView(tv, lp)
                thumbs.add(null)
                docs.add(null)
            }
        }
        Thread {
            for (k in docs.indices) {
                if (myToken != thumbToken) break
                val iv = thumbs[k] ?: continue
                val d = docs[k] ?: continue
                val bmp: Bitmap? = decodeThumb(d, 192)
                if (bmp != null) {
                    runOnUiThread {
                        if (myToken == thumbToken) {
                            iv.setImageBitmap(bmp)
                        }
                    }
                }
            }
        }.start()
    }

    private fun decodeThumb(doc: Uri, target: Int): Bitmap? {
        try {
            val o = BitmapFactory.Options()
            o.inJustDecodeBounds = true
            contentResolver.openInputStream(doc)?.use { BitmapFactory.decodeStream(it, null, o) }
            var s = 1
            while (o.outWidth / (s * 2) >= target && o.outHeight / (s * 2) >= target) {
                s *= 2
            }
            val o2 = BitmapFactory.Options()
            o2.inSampleSize = s
            return contentResolver.openInputStream(doc)?.use { BitmapFactory.decodeStream(it, null, o2) }
        } catch (e: Throwable) {
            return null
        }
    }

    // ---------- Actions ----------

    private fun applyBatchSize() {
        val n: Int? = batchEdit.text.toString().trim().toIntOrNull()
        if (n == null || n < 1) {
            toast("Enter a number, 1 or more")
            return
        }
        hideKeyboard()
        batchEdit.clearFocus()
        rootView.requestFocus()
        Core.changeBatch(n)
    }

    private fun applyJump() {
        val n: Int? = jumpEdit.text.toString().trim().toIntOrNull()
        if (n == null || n < 1) {
            toast("Enter a file number, 1 or more")
            return
        }
        val err = Core.jumpTo(n)
        if (err != null) {
            toast(err)
            return
        }
        hideKeyboard()
        jumpEdit.clearFocus()
        jumpEdit.setText("")
        rootView.requestFocus()
    }

    private fun shareBatch() {
        val items = Core.currentBatch()
        if (items.isEmpty()) {
            toast("Nothing to share. Pick a folder or tap Reset.")
            return
        }
        try {
            val uris = ArrayList<Uri>()
            for (e in items) {
                uris.add(Core.providerUri(e))
            }
            val extraTxt = Core.usableTxt()
            for (t in extraTxt) {
                uris.add(Core.txtProviderUri(t))
            }
            val i = Intent(if (uris.size == 1) Intent.ACTION_SEND else Intent.ACTION_SEND_MULTIPLE)
            if (uris.size == 1) {
                i.putExtra(Intent.EXTRA_STREAM, uris[0])
            } else {
                i.putParcelableArrayListExtra(Intent.EXTRA_STREAM, uris)
            }
            i.type = if (extraTxt.isNotEmpty()) "*/*" else Core.shareType(items)
            i.clipData = Core.buildClip(items)
            i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
            startActivity(Intent.createChooser(i, "Share files"))
            Core.afterShare(items)
        } catch (e: Exception) {
            toast("Share failed: " + e.message)
        }
    }

    // ---------- Floating always-on-top mode ----------

    private fun startFloat() {
        if (Core.treeUri == null) {
            toast("Pick a folder first")
            return
        }
        if (!Settings.canDrawOverlays(this)) {
            toast("Turn on \"Display over other apps\" for this app, come back, then tap Float on top")
            try {
                startActivity(
                    Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION, Uri.parse("package:" + packageName))
                )
            } catch (e: Exception) {
                toast("Open Settings > Apps > this app > Display over other apps")
            }
            return
        }
        if (Build.VERSION.SDK_INT >= 33 &&
            checkSelfPermission(Manifest.permission.POST_NOTIFICATIONS) != PackageManager.PERMISSION_GRANTED
        ) {
            requestPermissions(arrayOf(Manifest.permission.POST_NOTIFICATIONS), REQ_NOTIF)
            return
        }
        launchFloat()
    }

    override fun onRequestPermissionsResult(
        requestCode: Int,
        permissions: Array<out String>,
        grantResults: IntArray
    ) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == REQ_NOTIF) {
            launchFloat()
        } else if (requestCode == REQ_LAN) {
            Core.setLan(true)
            askBatteryExemption(this, getSharedPreferences("imgbatch", Context.MODE_PRIVATE))
        }
    }

    private fun launchFloat() {
        try {
            startForegroundService(Intent(this, FloatService::class.java))
            moveTaskToBack(true)
        } catch (e: Exception) {
            toast("Could not start floating panel: " + e.message)
        }
    }

    private fun stopFloat() {
        stopService(Intent(this, FloatService::class.java))
    }

    // ---------- LAN ----------

    private fun toggleLan() {
        if (Core.lanOn) {
            Core.setLan(false)
            return
        }
        if (Build.VERSION.SDK_INT >= 33 &&
            checkSelfPermission(Manifest.permission.POST_NOTIFICATIONS) != PackageManager.PERMISSION_GRANTED
        ) {
            requestPermissions(arrayOf(Manifest.permission.POST_NOTIFICATIONS), REQ_LAN)
            return
        }
        Core.setLan(true)
        askBatteryExemption(this, getSharedPreferences("imgbatch", Context.MODE_PRIVATE))
    }

    private fun showDevices() {
        if (!Core.lanOn) {
            toast("Turn LAN copy ON first")
            return
        }
        val ps = ArrayList<Peer>(Core.lan().peers.values)
        ps.sortBy { it.name }
        if (ps.isEmpty()) {
            toast("No devices found yet. Turn LAN copy ON on the other phones too (same Wi-Fi).")
            return
        }
        val names = ArrayList<CharSequence>()
        for (x in ps) {
            names.add(x.name + "  (" + x.ip + ")  -  " + (if (x.online()) "online" else "not seen"))
        }
        val checked = BooleanArray(ps.size)
        for (k in ps.indices) {
            checked[k] = ps[k].selected
        }
        AlertDialog.Builder(this)
            .setTitle("Send to which devices?")
            .setMultiChoiceItems(names.toTypedArray(), checked) { _, which, isChecked ->
                ps[which].selected = isChecked
            }
            .setPositiveButton("OK") { _, _ -> Core.lan().savePeers() }
            .show()
    }

    // ---------- Keyboard / mouse ----------

    override fun dispatchKeyEvent(event: KeyEvent): Boolean {
        if (event.action == KeyEvent.ACTION_DOWN && event.repeatCount == 0 && currentFocus !is EditText) {
            when (event.keyCode) {
                KeyEvent.KEYCODE_C -> {
                    report(Core.copyBatch())
                    return true
                }
                KeyEvent.KEYCODE_O -> {
                    report(Core.copyOne())
                    return true
                }
                KeyEvent.KEYCODE_S -> {
                    shareBatch()
                    return true
                }
                KeyEvent.KEYCODE_B, KeyEvent.KEYCODE_DPAD_LEFT -> {
                    Core.prevBatch()
                    return true
                }
                KeyEvent.KEYCODE_R -> {
                    Core.resetAll()
                    return true
                }
                KeyEvent.KEYCODE_F -> {
                    startFloat()
                    return true
                }
                KeyEvent.KEYCODE_L -> {
                    toggleLan()
                    return true
                }
            }
        }
        return super.dispatchKeyEvent(event)
    }

    override fun onGenericMotionEvent(event: MotionEvent): Boolean {
        if (event.action == MotionEvent.ACTION_SCROLL) {
            val v = event.getAxisValue(MotionEvent.AXIS_VSCROLL)
            val h = event.getAxisValue(MotionEvent.AXIS_HSCROLL)
            val d: Float = if (h != 0f) h else v
            stripScroll.scrollBy((-d * dp(60)).toInt(), 0)
            return true
        }
        return super.onGenericMotionEvent(event)
    }
}

// Floating panel that stays on top of every app. Drag the top bar to move, drag the bottom-right corner to resize.
class FloatService : Service() {

    companion object {
        const val ACTION_STOP = "com.example.myapp.STOP_FLOAT"
        const val CH = "floatpanel"
        const val NID = 7
    }

    private var wm: WindowManager? = null
    private var panel: View? = null
    private var statusTv: TextView? = null
    private var lanChip: TextView? = null
    private val ui = Runnable { updateStatus() }

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onCreate() {
        super.onCreate()
        Core.init(this)
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        if (intent != null && intent.action == ACTION_STOP) {
            stopSelf()
            return START_NOT_STICKY
        }
        startFg()
        if (!Settings.canDrawOverlays(this)) {
            stopSelf()
            return START_NOT_STICKY
        }
        if (panel == null) {
            createPanel()
        }
        return START_NOT_STICKY
    }

    override fun onDestroy() {
        Core.removeListener(ui)
        try {
            val p = panel
            if (p != null) wm?.removeView(p)
        } catch (e: Exception) {
        }
        panel = null
        super.onDestroy()
    }

    @Suppress("DEPRECATION")
    private fun startFg() {
        val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        nm.createNotificationChannel(NotificationChannel(CH, "Floating panel", NotificationManager.IMPORTANCE_LOW))
        val fl = PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT
        val open = PendingIntent.getActivity(this, 0, Intent(this, MainActivity::class.java), fl)
        val stopI = Intent(this, FloatService::class.java)
        stopI.action = ACTION_STOP
        val stop = PendingIntent.getService(this, 1, stopI, fl)
        val n = Notification.Builder(this, CH)
            .setSmallIcon(android.R.drawable.ic_menu_upload)
            .setContentTitle("File Batch Copier is floating on top")
            .setContentText("Tap to open the app. Tap Stop to close the floating panel.")
            .setContentIntent(open)
            .setOngoing(true)
            .addAction(android.R.drawable.ic_menu_close_clear_cancel, "Stop", stop)
            .build()
        if (Build.VERSION.SDK_INT >= 34) {
            startForeground(NID, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_SPECIAL_USE)
        } else {
            startForeground(NID, n)
        }
    }

    private fun dp(v: Int): Int {
        return (v * resources.displayMetrics.density).toInt()
    }

    private fun report(err: String?) {
        if (err != null) Toast.makeText(this, err, Toast.LENGTH_SHORT).show()
    }

    private fun updateStatus() {
        statusTv?.text = Core.statusText(true)
        lanChip?.text = if (Core.lanOn) "LAN: ON" else "LAN: OFF"
    }

    private fun chip(text: String, color: String, onClick: () -> Unit): TextView {
        val t = TextView(this)
        t.text = text
        t.setTextColor(Color.WHITE)
        t.textSize = 12f
        t.gravity = Gravity.CENTER
        t.maxLines = 1
        t.setPadding(dp(6), dp(9), dp(6), dp(9))
        val g = GradientDrawable()
        g.setColor(Color.parseColor(color))
        g.cornerRadius = dp(6).toFloat()
        t.background = g
        t.isClickable = true
        t.setOnClickListener { onClick() }
        return t
    }

    private fun row(vararg v: View): LinearLayout {
        val r = LinearLayout(this)
        r.orientation = LinearLayout.HORIZONTAL
        for (x in v) {
            val lp = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
            lp.setMargins(dp(2), dp(2), dp(2), dp(2))
            r.addView(x, lp)
        }
        return r
    }

    private fun savePanel(p: WindowManager.LayoutParams) {
        getSharedPreferences("imgbatch", Context.MODE_PRIVATE).edit()
            .putInt("fx", p.x).putInt("fy", p.y).putInt("fw", p.width).putInt("fh", p.height).apply()
    }

    private fun createPanel() {
        val wmgr = getSystemService(Context.WINDOW_SERVICE) as WindowManager
        wm = wmgr
        val sp = getSharedPreferences("imgbatch", Context.MODE_PRIVATE)
        val dm = resources.displayMetrics
        val minW = dp(170)
        val minH = dp(120)
        val w = sp.getInt("fw", dp(300)).coerceIn(minW, maxOf(minW, dm.widthPixels))
        val h = sp.getInt("fh", dp(240)).coerceIn(minH, maxOf(minH, dm.heightPixels))
        val p = WindowManager.LayoutParams(
            w,
            h,
            WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE or WindowManager.LayoutParams.FLAG_NOT_TOUCH_MODAL,
            PixelFormat.TRANSLUCENT
        )
        p.gravity = Gravity.TOP or Gravity.START
        p.x = sp.getInt("fx", dp(16)).coerceIn(0, maxOf(0, dm.widthPixels - w))
        p.y = sp.getInt("fy", dp(100)).coerceIn(0, maxOf(0, dm.heightPixels - h))

        val root = FrameLayout(this)
        val rootBg = GradientDrawable()
        rootBg.setColor(Color.parseColor("#F2202124"))
        rootBg.cornerRadius = dp(10).toFloat()
        rootBg.setStroke(dp(1), Color.parseColor("#5C6BC0"))
        root.background = rootBg

        val col = LinearLayout(this)
        col.orientation = LinearLayout.VERTICAL

        // Top bar: drag here to move
        val bar = LinearLayout(this)
        bar.orientation = LinearLayout.HORIZONTAL
        bar.gravity = Gravity.CENTER_VERTICAL
        val barBg = GradientDrawable()
        barBg.setColor(Color.parseColor("#3949AB"))
        val rr = dp(10).toFloat()
        barBg.cornerRadii = floatArrayOf(rr, rr, rr, rr, 0f, 0f, 0f, 0f)
        bar.background = barBg
        bar.setPadding(dp(8), dp(3), dp(4), dp(3))
        val title = TextView(this)
        title.text = "File copier (drag here)"
        title.setTextColor(Color.WHITE)
        title.textSize = 12f
        title.maxLines = 1
        title.ellipsize = TextUtils.TruncateAt.END
        bar.addView(title, LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f))
        val openB = chip("Open", "#00695C") {
            val i = Intent(this, MainActivity::class.java)
            i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            try {
                startActivity(i)
            } catch (e: Exception) {
            }
        }
        val closeB = chip("X", "#B71C1C") { stopSelf() }
        val lpOpen = LinearLayout.LayoutParams(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT)
        lpOpen.setMargins(dp(2), 0, dp(2), 0)
        bar.addView(openB, lpOpen)
        val lpClose = LinearLayout.LayoutParams(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT)
        lpClose.setMargins(dp(2), 0, dp(2), 0)
        bar.addView(closeB, lpClose)
        col.addView(
            bar,
            LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
        )

        // Body (scrolls, so every button stays reachable even when the panel is small)
        val scroll = ScrollView(this)
        val body = LinearLayout(this)
        body.orientation = LinearLayout.VERTICAL
        body.setPadding(dp(6), dp(4), dp(6), dp(32))
        val st = TextView(this)
        st.setTextColor(Color.WHITE)
        st.textSize = 12f
        st.setPadding(dp(2), dp(2), dp(2), dp(4))
        statusTv = st
        body.addView(st)
        body.addView(
            row(
                chip("Copy batch", "#2E7D32") { report(Core.copyBatch()) },
                chip("Copy one", "#00838F") { report(Core.copyOne()) }
            )
        )
        val lc = chip("LAN: OFF", "#C62828") { Core.setLan(!Core.lanOn) }
        lanChip = lc
        body.addView(
            row(
                lc,
                chip("Copy received", "#2E7D32") { report(Core.copyReceived()) }
            )
        )
        body.addView(
            row(
                chip("Prev", "#5D4037") { Core.prevBatch() },
                chip("Reset", "#6A1B9A") { Core.resetAll() },
                chip("Refresh", "#455A64") { Core.reload() }
            )
        )
        body.addView(
            row(
                chip("Batch -", "#37474F") { Core.changeBatch(Core.batch - 1) },
                chip("Batch +", "#37474F") { Core.changeBatch(Core.batch + 1) }
            )
        )
        scroll.addView(body)
        col.addView(scroll, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))
        root.addView(col, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT))

        // Resize handle: bottom-right corner
        val handle = object : View(this@FloatService) {
            private val paint = Paint()

            init {
                paint.color = Color.WHITE
                paint.strokeWidth = dp(2).toFloat()
                paint.isAntiAlias = true
            }

            override fun onDraw(canvas: Canvas) {
                val ww = width.toFloat()
                val hh = height.toFloat()
                for (i in 1..3) {
                    val o = ww * i / 4f
                    canvas.drawLine(ww - o, hh - 2f, ww - 2f, hh - o, paint)
                }
            }
        }
        handle.setBackgroundColor(Color.parseColor("#33FFFFFF"))
        root.addView(handle, FrameLayout.LayoutParams(dp(34), dp(34), Gravity.BOTTOM or Gravity.END))

        bar.setOnTouchListener(object : View.OnTouchListener {
            var sx = 0f
            var sy = 0f
            var ox = 0
            var oy = 0
            override fun onTouch(v: View, e: MotionEvent): Boolean {
                when (e.actionMasked) {
                    MotionEvent.ACTION_DOWN -> {
                        sx = e.rawX
                        sy = e.rawY
                        ox = p.x
                        oy = p.y
                    }
                    MotionEvent.ACTION_MOVE -> {
                        val d = resources.displayMetrics
                        p.x = (ox + (e.rawX - sx).toInt()).coerceIn(0, maxOf(0, d.widthPixels - p.width))
                        p.y = (oy + (e.rawY - sy).toInt()).coerceIn(0, maxOf(0, d.heightPixels - p.height))
                        try {
                            wmgr.updateViewLayout(root, p)
                        } catch (ex: Exception) {
                        }
                    }
                    MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> savePanel(p)
                }
                return true
            }
        })

        handle.setOnTouchListener(object : View.OnTouchListener {
            var sx = 0f
            var sy = 0f
            var ow = 0
            var oh = 0
            override fun onTouch(v: View, e: MotionEvent): Boolean {
                when (e.actionMasked) {
                    MotionEvent.ACTION_DOWN -> {
                        sx = e.rawX
                        sy = e.rawY
                        ow = p.width
                        oh = p.height
                    }
                    MotionEvent.ACTION_MOVE -> {
                        val d = resources.displayMetrics
                        p.width = (ow + (e.rawX - sx).toInt()).coerceIn(minW, maxOf(minW, d.widthPixels - p.x))
                        p.height = (oh + (e.rawY - sy).toInt()).coerceIn(minH, maxOf(minH, d.heightPixels - p.y))
                        try {
                            wmgr.updateViewLayout(root, p)
                        } catch (ex: Exception) {
                        }
                    }
                    MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> savePanel(p)
                }
                return true
            }
        })

        try {
            wmgr.addView(root, p)
            panel = root
        } catch (e: Exception) {
            Toast.makeText(this, "Could not show floating panel: " + e.message, Toast.LENGTH_LONG).show()
            stopSelf()
            return
        }
        Core.addListener(ui)
        updateStatus()
    }
}
