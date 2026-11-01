import base64
import ctypes
import math
import queue
import shutil
import subprocess
import sys
import threading
import tkinter as tk
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from tkinter import messagebox, ttk
from typing import BinaryIO
from urllib.parse import parse_qs, urlsplit


PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"
MAX_PNG_CHUNK_SIZE = 64 * 1024 * 1024


def read_png_frame(stream: BinaryIO) -> bytes | None:
    first_byte = stream.read(1)
    if not first_byte:
        return None
    signature = first_byte + _read_exact(stream, len(PNG_SIGNATURE) - 1)
    if signature != PNG_SIGNATURE:
        raise RuntimeError("ADB devolvió datos que no son una imagen PNG.")

    frame = bytearray(signature)
    while True:
        chunk_header = _read_exact(stream, 8)
        chunk_size = int.from_bytes(chunk_header[:4], "big")
        if chunk_size > MAX_PNG_CHUNK_SIZE:
            raise RuntimeError("La captura recibida supera el tamaño permitido.")

        frame.extend(chunk_header)
        frame.extend(_read_exact(stream, chunk_size + 4))
        if chunk_header[4:] == b"IEND":
            return bytes(frame)


def _read_exact(stream: BinaryIO, size: int) -> bytes:
    chunks = bytearray()
    while len(chunks) < size:
        chunk = stream.read(size - len(chunks))
        if not chunk:
            raise RuntimeError("La transmisión de pantalla se interrumpió.")
        chunks.extend(chunk)
    return bytes(chunks)


def hide_console() -> None:
    if sys.platform == "win32":
        console = ctypes.windll.kernel32.GetConsoleWindow()
        if console:
            ctypes.windll.user32.ShowWindow(console, 0)


def is_valid_adb_endpoint(endpoint: str) -> bool:
    if not endpoint or any(character.isspace() for character in endpoint):
        return False
    host, separator, port_text = endpoint.rpartition(":")
    if (
        not separator
        or not host
        or not port_text.isascii()
        or not port_text.isdecimal()
    ):
        return False
    port = int(port_text)
    return 1 <= port <= 65535


WEB_PAGE = """<!doctype html>
<html lang="es">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Pantalla del teléfono</title>
  <style>
    * { box-sizing: border-box; }
    body {
      margin: 0; min-height: 100vh; display: grid; place-items: center;
      background: #101418; color: #e6edf3; font: 16px system-ui, sans-serif;
    }
    main { width: min(96vw, 1100px); text-align: center; }
    h1 { font-size: 1.2rem; font-weight: 600; }
    #status { color: #9da7b3; min-height: 1.5em; }
    img {
      display: block; max-width: 100%; max-height: 82vh; object-fit: contain;
      margin: 1rem auto; background: #202830; border-radius: 8px;
    }
  </style>
</head>
<body>
  <main>
    <h1>Pantalla del teléfono</h1>
    <div id="status">Esperando la captura del teléfono...</div>
    <img id="screen" alt="Vista en vivo de la pantalla del teléfono">
  </main>
  <script>
    const screen = document.getElementById("screen");
    const status = document.getElementById("status");
    let lastSequence = -1;
    async function updateFrame() {
      try {
        const response = await fetch("/frame.png?after=" + lastSequence, { cache: "no-store" });
        if (!response.ok) throw new Error("Esperando la captura del teléfono...");
        lastSequence = Number(response.headers.get("X-Frame-Sequence"));
        const imageUrl = URL.createObjectURL(await response.blob());
        const previousUrl = screen.dataset.url;
        screen.onload = () => {
          if (previousUrl) URL.revokeObjectURL(previousUrl);
          status.textContent = "En vivo";
        };
        screen.onerror = () => {
          URL.revokeObjectURL(imageUrl);
          status.textContent = "No se pudo mostrar la imagen.";
        };
        screen.dataset.url = imageUrl;
        screen.src = imageUrl;
      } catch (error) {
        status.textContent = error.message || "No se pudo recibir la pantalla.";
      } finally {
        setTimeout(updateFrame, 100);
      }
    }
    updateFrame();
  </script>
</body>
</html>
"""


class PhoneScreenViewer:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Visualizador de pantalla Android")
        self.root.geometry("1000x720")
        self.root.minsize(720, 480)

        self.device_results: queue.Queue[
            tuple[list[tuple[str, str]] | None, str | None]
        ] = queue.Queue()
        self.wireless_results: queue.Queue[tuple[str, bool]] = queue.Queue()
        self.capture_messages: queue.Queue[str] = queue.Queue()
        self.frame_lock = threading.Lock()
        self.frame_condition = threading.Condition(self.frame_lock)
        self.latest_frame: bytes | None = None
        self.frame_sequence = 0
        self.capture_stop = threading.Event()
        self.capture_thread: threading.Thread | None = None
        self.capture_process: subprocess.Popen[bytes] | None = None
        self.capture_process_lock = threading.Lock()
        self.scrcpy_path = shutil.which("scrcpy")
        self.scrcpy_process: subprocess.Popen[bytes] | None = None
        self.device_refreshing = False
        self.wireless_busy = False
        self.web_server: ThreadingHTTPServer | None = None
        self.photo: tk.PhotoImage | None = None
        self.rendered_sequence = -1
        self.rendered_size = (0, 0)
        self.placeholder_id: int | None = None

        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self._close)
        self.root.after(150, self._poll)
        if self.scrcpy_path is None:
            self.status.set(
                "Instala scrcpy para abrir en PC el visor fluido; ADB mantiene el visor web."
            )
        self.refresh_devices()

    def _build_ui(self) -> None:
        frame = ttk.Frame(self.root, padding=16)
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(0, weight=1)
        header = ttk.Frame(frame)
        header.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        header.columnconfigure(0, weight=1)
        ttk.Label(
            header,
            text="Pantalla del teléfono Android",
            font=("Segoe UI", 18, "bold"),
        ).grid(row=0, column=0, sticky="w")

        controls = ttk.Frame(frame)
        controls.grid(row=1, column=0, sticky="ew", pady=(0, 10))
        ttk.Label(controls, text="Dispositivo:").pack(side="left", padx=(0, 6))
        self.device_combo = ttk.Combobox(
            controls, state="readonly", width=24, values=()
        )
        self.device_combo.pack(side="left", padx=(0, 8))
        self.refresh_button = ttk.Button(
            controls, text="Buscar dispositivos", command=self.refresh_devices
        )
        self.refresh_button.pack(side="left", padx=(0, 8))
        self.start_button = ttk.Button(
            controls, text="Iniciar", command=self.start_capture, state="disabled"
        )
        self.start_button.pack(side="left", padx=(0, 8))
        self.stop_button = ttk.Button(
            controls, text="Detener", command=self.stop_capture, state="disabled"
        )
        self.stop_button.pack(side="left", padx=(0, 8))
        self.web_button = ttk.Button(
            controls, text="Abrir visor web", command=self.open_web_viewer
        )
        self.web_button.pack(side="right")

        wireless = ttk.LabelFrame(
            frame, text="Depuración inalámbrica (Android 11+)", padding=(8, 6)
        )
        wireless.grid(row=2, column=0, sticky="ew", pady=(0, 10))
        wireless.columnconfigure(1, weight=1)
        ttk.Label(wireless, text="IP:puerto de emparejamiento:").grid(
            row=0, column=0, sticky="w", padx=(0, 6)
        )
        self.pairing_endpoint = ttk.Entry(wireless, width=24)
        self.pairing_endpoint.grid(row=0, column=1, sticky="ew", padx=(0, 8))
        ttk.Label(wireless, text="Código:").grid(
            row=0, column=2, sticky="w", padx=(0, 6)
        )
        self.pairing_code = ttk.Entry(wireless, width=10, show="*")
        self.pairing_code.grid(row=0, column=3, sticky="ew", padx=(0, 8))
        self.pair_button = ttk.Button(
            wireless, text="Emparejar", command=self.pair_wireless_device
        )
        self.pair_button.grid(row=0, column=4)
        ttk.Label(wireless, text="IP:puerto de conexión:").grid(
            row=1, column=0, sticky="w", padx=(0, 6), pady=(6, 0)
        )
        self.connection_endpoint = ttk.Entry(wireless, width=24)
        self.connection_endpoint.grid(
            row=1, column=1, columnspan=3, sticky="ew", padx=(0, 8), pady=(6, 0)
        )
        self.connect_button = ttk.Button(
            wireless, text="Conectar", command=self.connect_wireless_device
        )
        self.connect_button.grid(row=1, column=4, pady=(6, 0))

        self.status = tk.StringVar(value="Buscando dispositivos Android...")
        ttk.Label(frame, textvariable=self.status).grid(
            row=3, column=0, sticky="new", pady=(0, 8)
        )

        self.screen = tk.Canvas(
            frame,
            background="#101418",
            highlightthickness=1,
            highlightbackground="#39434d",
        )
        self.screen.grid(row=4, column=0, sticky="nsew")
        frame.rowconfigure(4, weight=1)
        self.screen.bind("<Configure>", self._on_screen_resize)

        ttk.Label(
            frame,
            text=(
                "Requiere Android y ADB. Activa Depuración USB o inalámbrica; "
                "el visor web solo acepta conexiones desde esta PC."
            ),
            foreground="#5c6773",
            wraplength=950,
        ).grid(row=5, column=0, sticky="w", pady=(10, 0))
        self.placeholder_id = self.screen.create_text(
            20,
            20,
            text="Conecta y selecciona tu teléfono para ver su pantalla.",
            fill="#c9d1d9",
            font=("Segoe UI", 12),
            anchor="nw",
        )

    def refresh_devices(self) -> None:
        if self.device_refreshing:
            return
        self.device_refreshing = True
        self.refresh_button.configure(state="disabled")
        self.status.set("Buscando dispositivos Android...")
        threading.Thread(target=self._device_worker, daemon=True).start()

    def pair_wireless_device(self) -> None:
        endpoint = self.pairing_endpoint.get().strip()
        code = self.pairing_code.get().strip()
        if not is_valid_adb_endpoint(endpoint):
            messagebox.showwarning(
                "Dirección no válida",
                "Escribe la IP y el puerto de emparejamiento que muestra "
                "Depuración inalámbrica.",
                parent=self.root,
            )
            return
        if not code.isascii() or not code.isdigit():
            messagebox.showwarning(
                "Código no válido",
                "Escribe el código numérico que muestra el teléfono.",
                parent=self.root,
            )
            return
        self._start_wireless_command(
            ["adb", "pair", endpoint, code], "Emparejamiento"
        )

    def connect_wireless_device(self) -> None:
        endpoint = self.connection_endpoint.get().strip()
        if not is_valid_adb_endpoint(endpoint):
            messagebox.showwarning(
                "Dirección no válida",
                "Escribe la IP y el puerto de conexión que muestra "
                "Depuración inalámbrica.",
                parent=self.root,
            )
            return
        self._start_wireless_command(
            ["adb", "connect", endpoint], "Conexión", refresh_devices=True
        )

    def _start_wireless_command(
        self, command: list[str], action: str, refresh_devices: bool = False
    ) -> None:
        if self.wireless_busy:
            return
        self.wireless_busy = True
        self.pair_button.configure(state="disabled")
        self.connect_button.configure(state="disabled")
        self.status.set(f"{action} inalámbrico...")
        threading.Thread(
            target=self._wireless_worker,
            args=(command, action, refresh_devices),
            daemon=True,
        ).start()

    def _wireless_worker(
        self, command: list[str], action: str, refresh_devices: bool
    ) -> None:
        try:
            result = subprocess.run(
                command,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=30,
                check=False,
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )
            output = "\n".join(
                part.strip() for part in (result.stdout, result.stderr) if part.strip()
            )
            output_lower = output.casefold()
            if result.returncode or output_lower.startswith(
                (
                    "failed:",
                    "failed to connect",
                    "cannot connect",
                    "unable to connect",
                    "error:",
                )
            ):
                detail = output or f"adb terminó con código {result.returncode}."
                raise RuntimeError(detail)
            if action == "Emparejamiento":
                output = (
                    f"{output or 'ADB informó éxito.'} "
                    "Ahora introduce la IP:puerto de conexión del teléfono."
                )
            self.wireless_results.put(
                (f"{action} completado: {output}", refresh_devices)
            )
        except (OSError, subprocess.SubprocessError, RuntimeError) as error:
            self.wireless_results.put((f"Error de {action.lower()}: {error}", False))

    def _device_worker(self) -> None:
        try:
            result = subprocess.run(
                ["adb", "devices"],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=10,
                check=False,
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )
            if result.returncode:
                detail = result.stderr.strip() or result.stdout.strip()
                raise RuntimeError(detail or f"adb terminó con código {result.returncode}")

            devices: list[tuple[str, str]] = []
            for line in result.stdout.splitlines()[1:]:
                fields = line.split()
                if len(fields) >= 2:
                    devices.append((fields[0], fields[1]))
            self.device_results.put((devices, None))
        except (OSError, subprocess.SubprocessError, RuntimeError) as error:
            self.device_results.put((None, str(error)))

    def _apply_device_results(self) -> None:
        try:
            devices, error = self.device_results.get_nowait()
        except queue.Empty:
            return

        self.device_refreshing = False
        self.refresh_button.configure(state="normal")
        if error:
            self.device_combo.configure(values=())
            self.start_button.configure(state="disabled")
            self.status.set("No se pudo ejecutar ADB.")
            messagebox.showerror(
                "Error de ADB",
                "No se pudieron consultar los dispositivos.\n\n"
                f"{error}\n\n"
                "Instala Android Platform Tools y vuelve a intentarlo.",
                parent=self.root,
            )
            return

        connected = [serial for serial, state in devices or [] if state == "device"]
        self.device_combo.configure(values=connected)
        if connected:
            self.device_combo.current(0)
            self.start_button.configure(state="normal")
            self.status.set(
                f"{len(connected)} dispositivo(s) listo(s). Selecciona uno e inicia la captura."
            )
        else:
            self.start_button.configure(state="disabled")
            unauthorized = any(state == "unauthorized" for _, state in devices or [])
            self.status.set(
                "Autoriza la depuración USB o inalámbrica en el teléfono y vuelve a buscar."
                if unauthorized
                else (
                    "No hay dispositivos. Conecta por USB o empareja y conecta "
                    "el teléfono mediante Depuración inalámbrica."
                )
            )

    def start_capture(self) -> None:
        serial = self.device_combo.get()
        if not serial or (self.capture_thread and self.capture_thread.is_alive()):
            return

        self._start_scrcpy(serial)
        self.capture_stop = threading.Event()
        with self.frame_lock:
            self.latest_frame = None
            self.frame_sequence += 1
        self.rendered_sequence = -1
        self.capture_thread = threading.Thread(
            target=self._capture_worker, args=(serial,), daemon=True
        )
        self.capture_thread.start()
        self.device_combo.configure(state="disabled")
        self.refresh_button.configure(state="disabled")
        self.start_button.configure(state="disabled")
        self.stop_button.configure(state="normal")
        if self.scrcpy_process is not None:
            self.status.set(
                "Vista fluida abierta en scrcpy; iniciando la captura para el visor web."
            )
        else:
            self.status.set(f"Capturando pantalla de {serial}...")

    def _start_scrcpy(self, serial: str) -> None:
        if self.scrcpy_path is None:
            return
        if self.scrcpy_process is not None and self.scrcpy_process.poll() is None:
            return
        try:
            self.scrcpy_process = subprocess.Popen(
                [self.scrcpy_path, "-s", serial, "--no-audio"],
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )
        except OSError as error:
            self.scrcpy_process = None
            self.capture_messages.put(f"No se pudo abrir scrcpy: {error}")

    def stop_capture(self) -> None:
        self.capture_stop.set()
        with self.capture_process_lock:
            process = self.capture_process
            if process is not None and process.poll() is None:
                try:
                    process.terminate()
                except OSError as error:
                    self.capture_messages.put(
                        f"No se pudo detener ADB: {error}"
                    )
        if self.scrcpy_process is not None:
            process = self.scrcpy_process
            self.scrcpy_process = None
            if process.poll() is None:
                try:
                    process.terminate()
                except OSError as error:
                    self.capture_messages.put(
                        f"No se pudo cerrar scrcpy: {error}"
                    )
        self.stop_button.configure(state="disabled")
        self.status.set("Deteniendo la captura...")

    def _capture_worker(self, serial: str) -> None:
        last_error: str | None = None
        while not self.capture_stop.is_set():
            process: subprocess.Popen[bytes] | None = None
            stderr_tail = bytearray()
            stderr_thread: threading.Thread | None = None
            error_message: str | None = None
            try:
                process = subprocess.Popen(
                    [
                        "adb",
                        "-s",
                        serial,
                        "exec-out",
                        "sh",
                        "-c",
                        "while true; do screencap -p; sleep 0.05; done",
                    ],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    bufsize=0,
                    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
                )
                if process.stdout is None or process.stderr is None:
                    raise RuntimeError("No se pudieron abrir los canales de ADB.")
                with self.capture_process_lock:
                    self.capture_process = process

                def collect_stderr() -> None:
                    assert process is not None and process.stderr is not None
                    while True:
                        chunk = process.stderr.read(1024)
                        if not chunk:
                            return
                        stderr_tail.extend(chunk)
                        if len(stderr_tail) > 4096:
                            del stderr_tail[:-4096]

                stderr_thread = threading.Thread(target=collect_stderr, daemon=True)
                stderr_thread.start()
                while not self.capture_stop.is_set():
                    frame = read_png_frame(process.stdout)
                    if frame is None:
                        if self.capture_stop.is_set():
                            break
                        raise RuntimeError("ADB cerró la transmisión de pantalla.")
                    with self.frame_condition:
                        self.latest_frame = frame
                        self.frame_sequence += 1
                        self.frame_condition.notify_all()
                    if last_error is not None:
                        self.capture_messages.put("La captura se ha reanudado.")
                        last_error = None
            except (OSError, subprocess.SubprocessError, RuntimeError) as error:
                if not self.capture_stop.is_set():
                    error_message = str(error)
            finally:
                if process is not None:
                    if process.poll() is None:
                        try:
                            process.terminate()
                        except OSError as error:
                            if error_message is None and not self.capture_stop.is_set():
                                error_message = str(error)
                    try:
                        process.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()
                    if process.stdout is not None:
                        process.stdout.close()
                    if stderr_thread is not None:
                        stderr_thread.join(timeout=1)
                    if process.stderr is not None:
                        process.stderr.close()
                    with self.capture_process_lock:
                        if self.capture_process is process:
                            self.capture_process = None

            if error_message is not None:
                detail = stderr_tail.decode("utf-8", errors="replace").strip()
                message = f"{error_message} {detail}".strip()
                if message != last_error:
                    self.capture_messages.put(f"Error de captura: {message}")
                    last_error = message
                if self.capture_stop.wait(1):
                    break

        self.capture_messages.put("Captura detenida.")

    def _on_screen_resize(self, event: tk.Event) -> None:
        self._render_frame(event.width, event.height)

    def _render_frame(self, width: int | None = None, height: int | None = None) -> None:
        with self.frame_lock:
            frame = self.latest_frame
            sequence = self.frame_sequence

        width = max(1, width or self.screen.winfo_width())
        height = max(1, height or self.screen.winfo_height())
        if self.scrcpy_process is not None and self.scrcpy_process.poll() is None:
            if self.placeholder_id is None:
                self.screen.delete("phone-image")
                self.photo = None
                self.placeholder_id = self.screen.create_text(
                    width // 2,
                    height // 2,
                    text=(
                        "Visor fluido para PC abierto en la ventana scrcpy.\n"
                        "El visor web se actualiza con capturas ADB."
                    ),
                    fill="#c9d1d9",
                    font=("Segoe UI", 12),
                    anchor="center",
                )
            else:
                self.screen.coords(self.placeholder_id, width // 2, height // 2)
                self.screen.itemconfigure(
                    self.placeholder_id,
                    text=(
                        "Visor fluido para PC abierto en la ventana scrcpy.\n"
                        "El visor web se actualiza con capturas ADB."
                    ),
                    anchor="center",
                )
            self.rendered_size = (width, height)
            return
        if frame is None:
            if self.placeholder_id is not None:
                self.screen.coords(self.placeholder_id, width // 2, height // 2)
                self.screen.itemconfigure(
                    self.placeholder_id, anchor="center"
                )
            self.rendered_sequence = sequence
            self.rendered_size = (width, height)
            self.photo = None
            return
        if sequence == self.rendered_sequence and (width, height) == self.rendered_size:
            return

        try:
            image = tk.PhotoImage(
                data=base64.b64encode(frame).decode("ascii"), format="png"
            )
            factor = max(
                1,
                math.ceil(image.width() / width),
                math.ceil(image.height() / height),
            )
            if factor > 1:
                image = image.subsample(factor, factor)
        except tk.TclError as error:
            self.status.set(f"No se pudo mostrar la pantalla: {error}")
            self.rendered_sequence = sequence
            return

        if self.placeholder_id is not None:
            self.screen.delete(self.placeholder_id)
            self.placeholder_id = None
        self.screen.delete("phone-image")
        self.photo = image
        self.screen.create_image(
            width // 2,
            height // 2,
            image=self.photo,
            anchor="center",
            tags="phone-image",
        )
        self.rendered_sequence = sequence
        self.rendered_size = (width, height)

    def open_web_viewer(self) -> None:
        if self.web_server is None:
            viewer = self

            class RequestHandler(BaseHTTPRequestHandler):
                def do_GET(self) -> None:
                    if self.path == "/" or self.path.startswith("/?"):
                        body = WEB_PAGE.encode("utf-8")
                        self.send_response(200)
                        self.send_header("Content-Type", "text/html; charset=utf-8")
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers()
                        self.wfile.write(body)
                        return

                    parsed_path = urlsplit(self.path)
                    if parsed_path.path == "/frame.png":
                        try:
                            after = int(parse_qs(parsed_path.query).get("after", ["-1"])[0])
                        except ValueError:
                            self.send_error(400, "Número de captura no válido.")
                            return
                        with viewer.frame_condition:
                            viewer.frame_condition.wait_for(
                                lambda: (
                                    viewer.latest_frame is not None
                                    and viewer.frame_sequence > after
                                ),
                                timeout=5,
                            )
                            image = viewer.latest_frame
                            sequence = viewer.frame_sequence
                        if image is None or sequence <= after:
                            self.send_error(503, "La captura aún no está disponible.")
                            return
                        self.send_response(200)
                        self.send_header("Content-Type", "image/png")
                        self.send_header("Content-Length", str(len(image)))
                        self.send_header("X-Frame-Sequence", str(sequence))
                        self.send_header("Cache-Control", "no-store")
                        self.end_headers()
                        self.wfile.write(image)
                        return

                    self.send_error(404)

                def log_message(self, _format: str, *_args: object) -> None:
                    del _format, _args

            self.web_server = ThreadingHTTPServer(
                ("127.0.0.1", 0), RequestHandler
            )
            self.web_server.daemon_threads = True
            threading.Thread(
                target=self.web_server.serve_forever, daemon=True
            ).start()

        host, port = self.web_server.server_address[:2]
        url = f"http://{host}:{port}/"
        if webbrowser.open(url):
            self.status.set(f"Visor web abierto en {url}")
        else:
            self.status.set(f"No se pudo abrir el navegador. Visita {url}")

    def _poll(self) -> None:
        self._apply_device_results()
        while True:
            try:
                message, refresh_devices = self.wireless_results.get_nowait()
            except queue.Empty:
                break
            self.wireless_busy = False
            self.pair_button.configure(state="normal")
            self.connect_button.configure(state="normal")
            self.status.set(message)
            if refresh_devices:
                self.refresh_devices()

        while True:
            try:
                message = self.capture_messages.get_nowait()
            except queue.Empty:
                break
            self.status.set(message)

        if self.capture_thread is not None and not self.capture_thread.is_alive():
            self.capture_thread = None
            self.device_combo.configure(state="readonly")
            self.refresh_button.configure(state="normal")
            self.start_button.configure(
                state="normal" if self.device_combo.get() else "disabled"
            )
            self.stop_button.configure(state="disabled")

        if self.scrcpy_process is not None and self.scrcpy_process.poll() is not None:
            return_code = self.scrcpy_process.returncode
            self.scrcpy_process = None
            if return_code:
                self.status.set(
                    f"scrcpy terminó con código {return_code}; el visor web sigue disponible."
                )

        self._render_frame()
        self.root.after(50, self._poll)

    def _close(self) -> None:
        self.capture_stop.set()
        if self.scrcpy_process is not None:
            process = self.scrcpy_process
            self.scrcpy_process = None
            if process.poll() is None:
                try:
                    process.terminate()
                except OSError as error:
                    messagebox.showwarning(
                        "Cerrar visor fluido",
                        f"No se pudo cerrar scrcpy automáticamente.\n\n{error}",
                        parent=self.root,
                    )
        if self.web_server is not None:
            server = self.web_server
            threading.Thread(
                target=server.shutdown, daemon=True
            ).start()
            server.server_close()
        self.root.destroy()


if __name__ == "__main__":
    hide_console()
    window = tk.Tk()
    PhoneScreenViewer(window)
    window.mainloop()
