import concurrent.futures
from datetime import datetime, timezone
import gzip
import os
import re
import shutil
import ssl
import subprocess
import threading
import time
import tkinter as tk
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from tkinter import filedialog, messagebox, ttk


COUNTRY_MAP = {
    "IT": "IT - Italia",
    "ITA": "IT - Italia",
    "ITALY": "IT - Italia",
    "ITALIA": "IT - Italia",
    "UK": "UK - Regno Unito",
    "GB": "UK - Regno Unito",
    "GBR": "UK - Regno Unito",
    "ENGLAND": "UK - Regno Unito",
    "US": "US - USA",
    "USA": "US - USA",
    "UNITED STATES": "US - USA",
    "FR": "FR - Francia",
    "FRA": "FR - Francia",
    "FRANCE": "FR - Francia",
    "FRANCIA": "FR - Francia",
    "DE": "DE - Germania",
    "GER": "DE - Germania",
    "GERMANY": "DE - Germania",
    "GERMANIA": "DE - Germania",
    "ES": "ES - Spagna",
    "ESP": "ES - Spagna",
    "SPAIN": "ES - Spagna",
    "SPAGNA": "ES - Spagna",
    "CH": "CH - Svizzera",
    "SWITZERLAND": "CH - Svizzera",
    "SVIZZERA": "CH - Svizzera",
    "AT": "AT - Austria",
    "AUSTRIA": "AT - Austria",
    "PT": "PT - Portogallo",
    "PORTUGAL": "PT - Portogallo",
    "PORTOGALLO": "PT - Portogallo",
    "NL": "NL - Paesi Bassi",
    "NETHERLANDS": "NL - Paesi Bassi",
    "BE": "BE - Belgio",
    "BELGIUM": "BE - Belgio",
    "RO": "RO - Romania",
    "ROMANIA": "RO - Romania",
    "AL": "AL - Albania",
    "ALBANIA": "AL - Albania",
    "GR": "GR - Grecia",
    "GREECE": "GR - Grecia",
    "TR": "TR - Turchia",
    "TURKEY": "TR - Turchia",
    "RU": "RU - Russia",
    "RUSSIA": "RU - Russia",
    "CA": "CA - Canada",
    "CANADA": "CA - Canada",
    "BR": "BR - Brasile",
    "BRAZIL": "BR - Brasile",
    "AR": "AR - Argentina",
    "ARGENTINA": "AR - Argentina",
    "INT": "INT - Internazionale",
    "INTERNATIONAL": "INT - Internazionale",
}


def detect_country(extinf, group_title, name, url):
    if extinf:
        m_country = re.search(r'tvg-country\s*=\s*"([^"]+)"', extinf, re.IGNORECASE)
        if m_country:
            raw = m_country.group(1).strip()
            if raw:
                return COUNTRY_MAP.get(raw.upper(), raw.upper())

    if group_title:
        gt_clean = group_title.strip()
        gt_up = gt_clean.upper()
        if gt_up in COUNTRY_MAP:
            return COUNTRY_MAP[gt_up]
        for code, label in COUNTRY_MAP.items():
            if len(code) >= 2 and re.search(rf'(?:^|[\s\|\-:/\[\(]){re.escape(code)}(?:$|[\s\|\-:/\]\)])', gt_up):
                return label

    if name:
        m_prefix = re.match(r'^[\[\(\{]?\s*([A-Za-z]{2,3})\s*[\]\)\}]?\s*[:\|\-\s]', name.strip())
        if m_prefix:
            code = m_prefix.group(1).upper()
            if code in COUNTRY_MAP:
                return COUNTRY_MAP[code]

        m_suffix = re.search(r'[\[\(]\s*([A-Za-z]{2,3})\s*[\]\)]\s*$', name.strip())
        if m_suffix:
            code = m_suffix.group(1).upper()
            if code in COUNTRY_MAP:
                return COUNTRY_MAP[code]

        name_up = name.upper()
        for kw, label in [
            ("ITALIA", "IT - Italia"),
            ("MEDIASET", "IT - Italia"),
            ("RAI ", "IT - Italia"),
            ("SKY SPORT", "IT - Italia"),
            ("LA7", "IT - Italia"),
            ("TV8", "IT - Italia"),
            ("NOVE", "IT - Italia"),
        ]:
            if kw in name_up:
                return label

    if url:
        low_url = url.lower()
        if any(k in low_url for k in ("mediaset", "rai.it", "la7.it", "/it/", ".it/")):
            return "IT - Italia"
        m_path = re.search(r'/([a-z]{2})/', low_url)
        if m_path:
            code = m_path.group(1).upper()
            if code in COUNTRY_MAP:
                return COUNTRY_MAP[code]

    return "N/D"


def normalize_key(text):
    if not text:
        return ""
    return re.sub(r"[^a-z0-9]", "", text.lower())


def parse_xmltv_datetime(dt_str):
    if not dt_str:
        return None
    s = dt_str.strip()
    m = re.match(r"^(\d{14})(?:\s*([+-]\d{4}))?$", s)
    if not m:
        return None
    base, offset = m.group(1), m.group(2)
    try:
        dt = datetime.strptime(base, "%Y%m%d%H%M%S")
        if offset:
            sign = 1 if offset[0] == "+" else -1
            hrs = int(offset[1:3])
            mins = int(offset[3:5])
            from datetime import timedelta
            tz = timezone(sign * timedelta(hours=hrs, minutes=mins))
            return dt.replace(tzinfo=tz).astimezone()
        return dt.astimezone()
    except Exception:
        return None


class IPTVCheckerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("IPTV M3U / M3U8 Validator, Player, EPG & Cleaner")
        self.root.geometry("1180x710")
        self.root.minsize(980, 600)

        self.default_ua = (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/130.0.0.0 Safari/537.36"
        )

        self.channels = []
        self.m3u_header_epg = ""
        self.epg_channels = {}      # id -> display-name
        self.epg_name_to_id = {}    # normalized_name -> id
        self.epg_programmes = {}    # id -> list of (start_dt, stop_dt, title, desc)

        self.is_running = False
        self.stop_requested = False

        self._build_ui()
        self._auto_detect_player()

    def _build_ui(self):
        main_frame = ttk.Frame(self.root, padding="12")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # --- Barra Superiore: Playlist, EPG, Player e Opzioni ---
        top_frame = ttk.LabelFrame(main_frame, text="1. Playlist, Guida EPG (XMLTV), Player & Parametri", padding="10")
        top_frame.pack(fill=tk.X, pady=(0, 10))

        # Riga 1: File M3U
        row1 = ttk.Frame(top_frame)
        row1.pack(fill=tk.X, pady=(0, 6))

        ttk.Label(row1, text="File M3U:", width=11).pack(side=tk.LEFT, padx=(0, 5))
        self.file_path_var = tk.StringVar()
        ttk.Entry(row1, textvariable=self.file_path_var).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))

        ttk.Button(row1, text="Apri .m3u / .m3u8...", command=self._load_file).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(row1, text="Incolla Lista / URL", command=self._open_paste_dialog).pack(side=tk.LEFT)

        # Riga 2: EPG XMLTV
        row_epg = ttk.Frame(top_frame)
        row_epg.pack(fill=tk.X, pady=(0, 6))

        ttk.Label(row_epg, text="EPG XMLTV:", width=11).pack(side=tk.LEFT, padx=(0, 5))
        self.epg_source_var = tk.StringVar()
        ttk.Entry(row_epg, textvariable=self.epg_source_var).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))

        ttk.Button(row_epg, text="Apri .xml / .gz...", command=self._browse_epg_file).pack(side=tk.LEFT, padx=(0, 5))
        self.load_epg_btn = ttk.Button(row_epg, text="Carica / Verifica EPG", command=self._start_epg_load)
        self.load_epg_btn.pack(side=tk.LEFT)

        # Riga 3: Player
        row_player = ttk.Frame(top_frame)
        row_player.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(row_player, text="Player:", width=11).pack(side=tk.LEFT, padx=(0, 5))
        self.player_type_var = tk.StringVar(value="vlc")
        ttk.Radiobutton(
            row_player, text="VLC", variable=self.player_type_var, value="vlc", command=self._on_player_type_change
        ).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Radiobutton(
            row_player, text="ffplay", variable=self.player_type_var, value="ffplay", command=self._on_player_type_change
        ).pack(side=tk.LEFT, padx=(0, 10))

        self.player_exe_var = tk.StringVar()
        ttk.Entry(row_player, textvariable=self.player_exe_var).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        ttk.Button(row_player, text="Sfoglia...", width=9, command=self._browse_player).pack(side=tk.LEFT)

        # Riga 4: Parametri controllo
        row2 = ttk.Frame(top_frame)
        row2.pack(fill=tk.X)

        ttk.Label(row2, text="Timeout (sec):").pack(side=tk.LEFT, padx=(0, 4))
        self.timeout_var = tk.IntVar(value=8)
        ttk.Spinbox(row2, from_=2, to=30, width=5, textvariable=self.timeout_var).pack(side=tk.LEFT, padx=(0, 15))

        ttk.Label(row2, text="Thread simultanei:").pack(side=tk.LEFT, padx=(0, 4))
        self.workers_var = tk.IntVar(value=10)
        ttk.Spinbox(row2, from_=1, to=30, width=5, textvariable=self.workers_var).pack(side=tk.LEFT, padx=(0, 15))

        self.deep_check_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            row2,
            text="Verifica contenuto manifest (#EXTM3U / segmenti)",
            variable=self.deep_check_var,
        ).pack(side=tk.LEFT, padx=(0, 15))

        self.stop_btn = ttk.Button(row2, text="Ferma", state=tk.DISABLED, command=self._stop_check)
        self.stop_btn.pack(side=tk.RIGHT)

        self.start_btn = ttk.Button(row2, text="Avvia Controllo Flussi", command=self._start_check)
        self.start_btn.pack(side=tk.RIGHT, padx=(0, 6))

        # --- Barra Statistiche e Filtri ---
        stats_frame = ttk.Frame(main_frame)
        stats_frame.pack(fill=tk.X, pady=(0, 8))

        self.stats_var = tk.StringVar(value="Totale: 0  |  Online: 0  |  Offline: 0  |  EPG abbinati: 0")
        ttk.Label(stats_frame, textvariable=self.stats_var, font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT)

        filter_box = ttk.Frame(stats_frame)
        filter_box.pack(side=tk.RIGHT)

        ttk.Label(filter_box, text="Paese:").pack(side=tk.LEFT, padx=(0, 4))
        self.country_filter_var = tk.StringVar(value="Tutti i paesi")
        self.country_combo = ttk.Combobox(
            filter_box,
            textvariable=self.country_filter_var,
            values=["Tutti i paesi"],
            state="readonly",
            width=16,
        )
        self.country_combo.pack(side=tk.LEFT, padx=(0, 12))
        self.country_combo.bind("<<ComboboxSelected>>", lambda e: self._refresh_tree())

        ttk.Label(filter_box, text="Stato:").pack(side=tk.LEFT, padx=(0, 5))
        self.filter_var = tk.StringVar(value="ALL")
        for label, val in [("Tutti", "ALL"), ("Solo Online", "ONLINE"), ("Solo Offline", "OFFLINE")]:
            ttk.Radiobutton(
                filter_box,
                text=label,
                variable=self.filter_var,
                value=val,
                command=self._refresh_tree,
            ).pack(side=tk.LEFT, padx=(0, 8))

        # --- Tabella Risultati (Treeview) ---
        table_frame = ttk.Frame(main_frame)
        table_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))

        columns = ("idx", "status", "country", "name", "epg", "latency", "detail", "url")
        self.tree = ttk.Treeview(table_frame, columns=columns, show="headings", selectmode="extended")

        self.tree.heading("idx", text="#")
        self.tree.heading("status", text="Stato")
        self.tree.heading("country", text="Paese")
        self.tree.heading("name", text="Canale")
        self.tree.heading("epg", text="EPG / In Onda Ora")
        self.tree.heading("latency", text="Latenza")
        self.tree.heading("detail", text="Esito / Codice HTTP")
        self.tree.heading("url", text="URL Flusso")

        self.tree.column("idx", width=42, anchor=tk.CENTER, stretch=False)
        self.tree.column("status", width=80, anchor=tk.CENTER, stretch=False)
        self.tree.column("country", width=115, anchor=tk.W, stretch=False)
        self.tree.column("name", width=170, anchor=tk.W)
        self.tree.column("epg", width=230, anchor=tk.W)
        self.tree.column("latency", width=70, anchor=tk.CENTER, stretch=False)
        self.tree.column("detail", width=155, anchor=tk.W)
        self.tree.column("url", width=260, anchor=tk.W)

        self.tree.tag_configure("ONLINE", foreground="#137333")
        self.tree.tag_configure("OFFLINE", foreground="#c5221f")
        self.tree.tag_configure("PENDING", foreground="#5f6368")

        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(table_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.tree.grid(row=0, column=0, sticky=tk.NSEW)
        vsb.grid(row=0, column=1, sticky=tk.NS)
        hsb.grid(row=1, column=0, sticky=tk.EW)

        table_frame.rowconfigure(0, weight=1)
        table_frame.columnconfigure(0, weight=1)

        self.tree.bind("<Double-1>", lambda e: self._play_selected())

        # Menu contestuale su riga
        self.ctx_menu = tk.Menu(self.root, tearoff=0)
        self.ctx_menu.add_command(label="Avvia su Player (VLC / ffplay)", command=self._play_selected)
        self.ctx_menu.add_command(label="Mostra Guida EPG Canale", command=self._show_channel_epg_dialog)
        self.ctx_menu.add_separator()
        self.ctx_menu.add_command(label="Copia URL flusso", command=self._copy_selected_url)
        self.ctx_menu.add_command(label="Ricontrolla selezionati", command=self._recheck_selected)
        self.ctx_menu.add_command(label="Rimuovi selezionati dalla lista", command=self._remove_selected)
        self.tree.bind("<Button-3>", self._show_context_menu)

        # --- Barra Inferiore: Progresso, Play ed Export ---
        bottom_frame = ttk.Frame(main_frame)
        bottom_frame.pack(fill=tk.X)

        self.progress = ttk.Progressbar(bottom_frame, mode="determinate")
        self.progress.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 12))

        self.play_btn = ttk.Button(
            bottom_frame,
            text="Riproduci Selezionato",
            command=self._play_selected,
        )
        self.play_btn.pack(side=tk.LEFT, padx=(0, 12))

        self.export_online_btn = ttk.Button(
            bottom_frame,
            text="Esporta M3U Pulita (Solo Online)",
            command=lambda: self._export_m3u(only_online=True),
        )
        self.export_online_btn.pack(side=tk.RIGHT)

        self.export_all_btn = ttk.Button(
            bottom_frame,
            text="Esporta Vista Corrente (.m3u)",
            command=lambda: self._export_m3u(only_online=False),
        )
        self.export_all_btn.pack(side=tk.RIGHT, padx=(0, 8))

    # --- Gestione EPG XMLTV ---
    def _browse_epg_file(self):
        path = filedialog.askopenfilename(
            title="Seleziona file EPG XMLTV",
            filetypes=[("File XMLTV", "*.xml *.gz"), ("Tutti i file", "*.*")],
        )
        if path:
            self.epg_source_var.set(path)
            self._start_epg_load()

    def _start_epg_load(self):
        src = self.epg_source_var.get().strip()
        if not src:
            messagebox.showwarning("EPG mancante", "Inserisci un URL XMLTV oppure seleziona un file .xml / .xml.gz locale.")
            return

        self.load_epg_btn.config(state=tk.DISABLED)
        thread = threading.Thread(target=self._epg_worker, args=(src,), daemon=True)
        thread.start()

    def _epg_worker(self, src):
        err = None
        epg_channels = {}
        epg_name_to_id = {}
        epg_programmes = {}

        try:
            if src.lower().startswith(("http://", "https://")):
                ctx = ssl.create_default_context()
                ctx.check_hostname = False
                ctx.verify_mode = ssl.CERT_NONE
                req = urllib.request.Request(src, headers={"User-Agent": self.default_ua})
                with urllib.request.urlopen(req, timeout=20, context=ctx) as resp:
                    raw_bytes = resp.read()
            else:
                with open(src, "rb") as f:
                    raw_bytes = f.read()

            if raw_bytes[:2] == b"\x1f\x8b" or src.lower().endswith(".gz"):
                xml_bytes = gzip.decompress(raw_bytes)
            else:
                xml_bytes = raw_bytes

            root_xml = ET.fromstring(xml_bytes)

            for ch_el in root_xml.findall("channel"):
                cid = (ch_el.get("id") or "").strip()
                if not cid:
                    continue
                disp_names = [dn.text.strip() for dn in ch_el.findall("display-name") if dn.text and dn.text.strip()]
                label = disp_names[0] if disp_names else cid
                epg_channels[cid] = label
                epg_name_to_id[normalize_key(cid)] = cid
                for dn in disp_names:
                    epg_name_to_id[normalize_key(dn)] = cid

            for prog_el in root_xml.findall("programme"):
                cid = (prog_el.get("channel") or "").strip()
                if not cid:
                    continue
                start_dt = parse_xmltv_datetime(prog_el.get("start"))
                stop_dt = parse_xmltv_datetime(prog_el.get("stop"))
                title_el = prog_el.find("title")
                desc_el = prog_el.find("desc")
                title = title_el.text.strip() if (title_el is not None and title_el.text) else "Senza titolo"
                desc = desc_el.text.strip() if (desc_el is not None and desc_el.text) else ""
                epg_programmes.setdefault(cid, []).append((start_dt, stop_dt, title, desc))

            for cid in epg_programmes:
                epg_programmes[cid].sort(key=lambda x: x[0] or datetime.min.replace(tzinfo=timezone.utc))

        except Exception as e:
            err = str(e)

        self.root.after(0, self._on_epg_loaded, epg_channels, epg_name_to_id, epg_programmes, err)

    def _on_epg_loaded(self, epg_channels, epg_name_to_id, epg_programmes, err):
        self.load_epg_btn.config(state=tk.NORMAL)
        if err:
            messagebox.showerror("Errore caricamento EPG", f"Impossibile caricare o analizzare la guida EPG:\n{err}")
            return

        self.epg_channels = epg_channels
        self.epg_name_to_id = epg_name_to_id
        self.epg_programmes = epg_programmes

        self._match_channels_with_epg()
        self._refresh_tree()
        self._update_stats()

        tot_progs = sum(len(v) for v in epg_programmes.values())
        messagebox.showinfo(
            "EPG Caricata",
            f"Guida XMLTV caricata con successo!\n"
            f"- Canali nella guida: {len(epg_channels)}\n"
            f"- Eventi / programmi letti: {tot_progs}",
        )

    def _match_channels_with_epg(self):
        now = datetime.now().astimezone()
        for ch in self.channels:
            matched_id = None
            tvg_id = ch.get("tvg_id", "")
            tvg_name = ch.get("tvg_name", "")

            if tvg_id and tvg_id in self.epg_channels:
                matched_id = tvg_id
            elif tvg_id and normalize_key(tvg_id) in self.epg_name_to_id:
                matched_id = self.epg_name_to_id[normalize_key(tvg_id)]
            elif tvg_name and normalize_key(tvg_name) in self.epg_name_to_id:
                matched_id = self.epg_name_to_id[normalize_key(tvg_name)]
            elif normalize_key(ch["name"]) in self.epg_name_to_id:
                matched_id = self.epg_name_to_id[normalize_key(ch["name"])]

            ch["epg_matched_id"] = matched_id
            if not matched_id:
                ch["epg_text"] = f"tvg-id: {tvg_id}" if tvg_id else "Non abbinato"
                continue

            progs = self.epg_programmes.get(matched_id, [])
            current_prog = None
            for start_dt, stop_dt, title, _ in progs:
                if start_dt and stop_dt and start_dt <= now <= stop_dt:
                    current_prog = (start_dt, stop_dt, title)
                    break

            if current_prog:
                s_str = current_prog[0].strftime("%H:%M")
                e_str = current_prog[1].strftime("%H:%M")
                ch["epg_text"] = f"[{s_str}-{e_str}] {current_prog[2]}"
            elif progs:
                ch["epg_text"] = f"OK ({len(progs)} eventi)"
            else:
                ch["epg_text"] = f"ID OK ({matched_id})"

    def _show_channel_epg_dialog(self):
        sel = self._get_selected_channels()
        if not sel:
            return
        ch = sel[0]
        cid = ch.get("epg_matched_id")
        if not cid or cid not in self.epg_programmes:
            messagebox.showinfo(
                "Nessun dato EPG",
                f"Nessuna programmazione trovata per '{ch['name']}'.\n"
                "Assicurati di aver caricato un file/URL XMLTV valido nella riga 'EPG XMLTV'.",
            )
            return

        win = tk.Toplevel(self.root)
        win.title(f"Guida EPG - {ch['name']} ({cid})")
        win.geometry("640x420")
        win.transient(self.root)

        txt = tk.Text(win, wrap=tk.WORD, padx=10, pady=10)
        txt.pack(fill=tk.BOTH, expand=True)

        now = datetime.now().astimezone()
        progs = self.epg_programmes[cid]
        for start_dt, stop_dt, title, desc in progs[:60]:
            s_str = start_dt.strftime("%d/%m %H:%M") if start_dt else "??:??"
            e_str = stop_dt.strftime("%H:%M") if stop_dt else "??:??"
            marker = " >>> IN ONDA ORA <<<" if (start_dt and stop_dt and start_dt <= now <= stop_dt) else ""
            txt.insert(tk.END, f"[{s_str} - {e_str}] {title}{marker}\n")
            if desc:
                txt.insert(tk.END, f"    {desc}\n")
            txt.insert(tk.END, "\n")
        txt.config(state=tk.DISABLED)

    # --- Gestione Player ---
    def _auto_detect_player(self):
        self.detected_players = {"vlc": "", "ffplay": ""}
        vlc_path = shutil.which("vlc")
        if not vlc_path:
            for candidate in [
                r"C:\Program Files\VideoLAN\VLC\vlc.exe",
                r"C:\Program Files (x86)\VideoLAN\VLC\vlc.exe",
            ]:
                if os.path.isfile(candidate):
                    vlc_path = candidate
                    break
        self.detected_players["vlc"] = vlc_path or ""
        self.detected_players["ffplay"] = shutil.which("ffplay") or ""
        self._on_player_type_change()

    def _on_player_type_change(self):
        choice = self.player_type_var.get()
        self.player_exe_var.set(self.detected_players.get(choice, ""))

    def _browse_player(self):
        path = filedialog.askopenfilename(
            title="Seleziona eseguibile player",
            filetypes=[("Eseguibili", "*.exe"), ("Tutti i file", "*.*")],
        )
        if path:
            choice = self.player_type_var.get()
            self.detected_players[choice] = path
            self.player_exe_var.set(path)

    def _play_selected(self):
        sel = self._get_selected_channels()
        if not sel:
            messagebox.showinfo("Nessuna selezione", "Seleziona un canale nella tabella (o fai doppio clic) per avviarlo.")
            return

        ch = sel[0]
        exe = self.player_exe_var.get().strip()
        player = self.player_type_var.get()

        if not exe or not os.path.isfile(exe):
            messagebox.showerror(
                "Player non trovato",
                f"Impossibile trovare l'eseguibile per {player.upper()}.\nSelezionalo con il pulsante 'Sfoglia...'.",
            )
            return

        ua = ch["ua"] or self.default_ua
        referer = ch["referer"]
        url = ch["url"]

        cmd = [exe]
        if player == "vlc":
            if ua:
                cmd.append(f":http-user-agent={ua}")
            if referer:
                cmd.append(f":http-referrer={referer}")
            cmd.append(url)
        else:
            if ua:
                cmd.extend(["-user_agent", ua])
            if referer:
                cmd.extend(["-headers", f"Referer: {referer}\r\n"])
            cmd.extend(["-window_title", ch["name"], url])

        try:
            subprocess.Popen(cmd)
        except Exception as e:
            messagebox.showerror("Errore avvio player", f"Impossibile avviare il player:\n{e}")

    # --- Parsing Playlist M3U ---
    def _load_file(self):
        path = filedialog.askopenfilename(
            title="Seleziona playlist IPTV",
            filetypes=[("Playlist M3U / M3U8", "*.m3u *.m3u8"), ("Tutti i file", "*.*")],
        )
        if not path:
            return
        self.file_path_var.set(path)
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                content = f.read()
            self._parse_m3u_content(content)
        except Exception as e:
            messagebox.showerror("Errore lettura file", f"Impossibile aprire il file:\n{e}")

    def _open_paste_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("Incolla contenuto M3U o elenco URL")
        win.geometry("620x400")
        win.transient(self.root)
        win.grab_set()

        ttk.Label(win, text="Incolla qui il testo della playlist M3U oppure uno o più URL (uno per riga):").pack(
            anchor=tk.W, padx=10, pady=(10, 5)
        )
        txt = tk.Text(win, wrap=tk.NONE)
        txt.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        try:
            clip = self.root.clipboard_get()
            if clip:
                txt.insert("1.0", clip)
        except tk.TclError:
            pass

        def on_confirm():
            raw = txt.get("1.0", tk.END).strip()
            if raw:
                self.file_path_var.set("[Lista incollata]")
                self._parse_m3u_content(raw)
            win.destroy()

        btn_row = ttk.Frame(win)
        btn_row.pack(fill=tk.X, padx=10, pady=(0, 10))
        ttk.Button(btn_row, text="Carica nella tabella", command=on_confirm).pack(side=tk.RIGHT)
        ttk.Button(btn_row, text="Annulla", command=win.destroy).pack(side=tk.RIGHT, padx=(0, 6))

    def _parse_m3u_content(self, content):
        lines = [line.strip() for line in content.splitlines() if line.strip()]
        parsed = []
        self.m3u_header_epg = ""

        current_extinf = None
        current_name = None
        current_group = ""
        current_tvg_id = ""
        current_tvg_name = ""
        current_ua = ""
        current_ref = ""
        extra_opts = []

        for line in lines:
            if line.startswith("#EXTM3U"):
                m_epg = re.search(r'(?:url-tvg|x-tvg-url)\s*=\s*"([^"]+)"', line, re.IGNORECASE)
                if m_epg:
                    self.m3u_header_epg = m_epg.group(1).strip()
                    if not self.epg_source_var.get().strip():
                        self.epg_source_var.set(self.m3u_header_epg)
                continue
            elif line.startswith("#EXTINF:"):
                current_extinf = line
                m_grp = re.search(r'group-title\s*=\s*"([^"]*)"', line, re.IGNORECASE)
                if m_grp:
                    current_group = m_grp.group(1).strip()
                m_tid = re.search(r'tvg-id\s*=\s*"([^"]*)"', line, re.IGNORECASE)
                if m_tid:
                    current_tvg_id = m_tid.group(1).strip()
                m_tname = re.search(r'tvg-name\s*=\s*"([^"]*)"', line, re.IGNORECASE)
                if m_tname:
                    current_tvg_name = m_tname.group(1).strip()
                if "," in line:
                    current_name = line.split(",", 1)[1].strip()
                else:
                    current_name = "Canale senza nome"
            elif line.startswith("#EXTVLCOPT:"):
                opt = line.split(":", 1)[1].strip()
                low = opt.lower()
                if low.startswith("http-user-agent="):
                    current_ua = opt.split("=", 1)[1].strip()
                elif low.startswith("http-referrer="):
                    current_ref = opt.split("=", 1)[1].strip()
                else:
                    extra_opts.append(line)
            elif line.startswith("#EXTGRP:"):
                current_group = line.split(":", 1)[1].strip()
                extra_opts.append(line)
            elif line.startswith("#"):
                continue
            else:
                raw_url = line
                clean_url = raw_url
                ua = current_ua
                ref = current_ref

                if "|" in raw_url:
                    base_part, pipe_part = raw_url.split("|", 1)
                    clean_url = base_part.strip()
                    for kv in pipe_part.split("&"):
                        if "=" in kv:
                            k, v = kv.split("=", 1)
                            kl = k.strip().lower()
                            val = urllib.parse.unquote(v.strip())
                            if kl == "user-agent" and not ua:
                                ua = val
                            elif kl in ("referer", "referrer") and not ref:
                                ref = val

                idx = len(parsed) + 1
                name = current_name or f"Canale {idx}"
                country = detect_country(current_extinf, current_group, name, clean_url)
                epg_label = f"tvg-id: {current_tvg_id}" if current_tvg_id else "N/D"

                parsed.append(
                    {
                        "idx": idx,
                        "name": name,
                        "country": country,
                        "tvg_id": current_tvg_id,
                        "tvg_name": current_tvg_name,
                        "epg_matched_id": None,
                        "epg_text": epg_label,
                        "extinf": current_extinf or f"#EXTINF:-1,{name}",
                        "url": clean_url,
                        "raw_url": raw_url,
                        "ua": ua,
                        "referer": ref,
                        "extra_opts": list(extra_opts),
                        "status": "PENDING",
                        "latency": "-",
                        "detail": "In attesa",
                    }
                )

                current_extinf = None
                current_name = None
                current_group = ""
                current_tvg_id = ""
                current_tvg_name = ""
                current_ua = ""
                current_ref = ""
                extra_opts = []

        self.channels = parsed
        if self.epg_channels:
            self._match_channels_with_epg()
        self._update_country_filter_options()
        self.progress["value"] = 0
        self.progress["maximum"] = max(1, len(self.channels))
        self._refresh_tree()
        self._update_stats()

    def _update_country_filter_options(self):
        countries = sorted({ch["country"] for ch in self.channels if ch["country"]})
        options = ["Tutti i paesi"] + countries
        self.country_combo["values"] = options
        if self.country_filter_var.get() not in options:
            self.country_filter_var.set("Tutti i paesi")

    def _matches_filters(self, ch):
        flt = self.filter_var.get()
        if flt != "ALL" and ch["status"] != flt:
            return False
        c_flt = self.country_filter_var.get()
        if c_flt and c_flt != "Tutti i paesi" and ch["country"] != c_flt:
            return False
        return True

    def _refresh_tree(self):
        self.tree.delete(*self.tree.get_children())

        for ch in self.channels:
            if not self._matches_filters(ch):
                continue
            status_label = {
                "ONLINE": "ONLINE",
                "OFFLINE": "OFFLINE",
                "PENDING": "IN ATTESA",
            }.get(ch["status"], ch["status"])

            self.tree.insert(
                "",
                tk.END,
                iid=str(ch["idx"]),
                values=(
                    ch["idx"],
                    status_label,
                    ch["country"],
                    ch["name"],
                    ch["epg_text"],
                    ch["latency"],
                    ch["detail"],
                    ch["url"],
                ),
                tags=(ch["status"],),
            )

    def _update_stats(self):
        total = len(self.channels)
        online = sum(1 for c in self.channels if c["status"] == "ONLINE")
        offline = sum(1 for c in self.channels if c["status"] == "OFFLINE")
        epg_ok = sum(1 for c in self.channels if c.get("epg_matched_id") or c.get("tvg_id"))
        self.stats_var.set(
            f"Totale: {total}  |  Online: {online}  |  Offline: {offline}  |  Con EPG: {epg_ok}"
        )

    def _check_single_channel(self, ch, timeout, deep_check):
        if self.stop_requested:
            return ch

        url = ch["url"]
        ua = ch["ua"] or self.default_ua
        referer = ch["referer"]

        headers = {
            "User-Agent": ua,
            "Accept": "*/*",
            "Connection": "close",
        }
        if referer:
            headers["Referer"] = referer

        ctx = ssl.create_default_context()
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE

        start_t = time.perf_counter()
        try:
            req = urllib.request.Request(url, headers=headers, method="GET")
            with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
                code = resp.getcode()
                content_type = (resp.headers.get("Content-Type") or "").lower()
                chunk = resp.read(2048) if deep_check else resp.read(16)
                elapsed_ms = int((time.perf_counter() - start_t) * 1000)

                if code not in (200, 206):
                    ch["status"] = "OFFLINE"
                    ch["latency"] = f"{elapsed_ms} ms"
                    ch["detail"] = f"HTTP {code}"
                    return ch

                if deep_check:
                    if not chunk:
                        ch["status"] = "OFFLINE"
                        ch["latency"] = f"{elapsed_ms} ms"
                        ch["detail"] = "Risposta vuota (0 byte)"
                        return ch

                    text_sample = chunk.decode("utf-8", errors="ignore").lstrip()
                    is_m3u_url = ".m3u8" in url.lower() or ".m3u" in url.lower() or "mpegurl" in content_type

                    if text_sample.startswith("#EXTM3U"):
                        if "#EXT-X-ENDLIST" in text_sample and "#EXTINF" not in text_sample:
                            ch["status"] = "OFFLINE"
                            ch["latency"] = f"{elapsed_ms} ms"
                            ch["detail"] = "Manifest vuoto / scaduto"
                        else:
                            ch["status"] = "ONLINE"
                            ch["latency"] = f"{elapsed_ms} ms"
                            ch["detail"] = f"HTTP {code} (HLS valido)"
                    elif text_sample.lower().startswith("<!doctype html") or text_sample.lower().startswith("<html"):
                        ch["status"] = "OFFLINE"
                        ch["latency"] = f"{elapsed_ms} ms"
                        ch["detail"] = "Pagina HTML (no stream)"
                    elif is_m3u_url and "#EXT" not in text_sample:
                        ch["status"] = "OFFLINE"
                        ch["latency"] = f"{elapsed_ms} ms"
                        ch["detail"] = "Manifest non valido"
                    else:
                        ch["status"] = "ONLINE"
                        ch["latency"] = f"{elapsed_ms} ms"
                        ch["detail"] = f"HTTP {code} (Flusso attivo)"
                else:
                    ch["status"] = "ONLINE"
                    ch["latency"] = f"{elapsed_ms} ms"
                    ch["detail"] = f"HTTP {code}"

        except urllib.error.HTTPError as e:
            elapsed_ms = int((time.perf_counter() - start_t) * 1000)
            ch["status"] = "OFFLINE"
            ch["latency"] = f"{elapsed_ms} ms"
            ch["detail"] = f"HTTP {e.code} ({e.reason})"
        except urllib.error.URLError as e:
            ch["status"] = "OFFLINE"
            ch["latency"] = "-"
            reason = str(getattr(e, "reason", e))
            if "timed out" in reason.lower():
                ch["detail"] = "Timeout connessione"
            else:
                ch["detail"] = f"Errore rete: {reason[:32]}"
        except socket.timeout:
            ch["status"] = "OFFLINE"
            ch["latency"] = "-"
            ch["detail"] = "Timeout lettura flusso"
        except Exception as e:
            ch["status"] = "OFFLINE"
            ch["latency"] = "-"
            ch["detail"] = f"Errore: {str(e)[:35]}"

        return ch

    def _start_check(self, subset=None):
        if self.is_running:
            return
        targets = subset if subset is not None else self.channels
        if not targets:
            messagebox.showwarning("Nessun canale", "Carica o incolla prima una playlist M3U.")
            return

        for ch in targets:
            ch["status"] = "PENDING"
            ch["latency"] = "-"
            ch["detail"] = "Verifica..."

        self._refresh_tree()
        self._update_stats()

        self.is_running = True
        self.stop_requested = False
        self.start_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.NORMAL)
        self.progress["value"] = 0
        self.progress["maximum"] = len(targets)

        timeout = max(2, int(self.timeout_var.get()))
        workers = max(1, min(30, int(self.workers_var.get())))
        deep_check = self.deep_check_var.get()

        thread = threading.Thread(
            target=self._worker_pool,
            args=(list(targets), timeout, workers, deep_check),
            daemon=True,
        )
        thread.start()

    def _stop_check(self):
        if self.is_running:
            self.stop_requested = True
            self.stop_btn.config(state=tk.DISABLED)

    def _worker_pool(self, targets, timeout, workers, deep_check):
        completed = 0
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
            futures = [
                executor.submit(self._check_single_channel, ch, timeout, deep_check)
                for ch in targets
            ]
            for fut in concurrent.futures.as_completed(futures):
                if self.stop_requested:
                    for f in futures:
                        f.cancel()
                    break
                ch = fut.result()
                completed += 1
                self.root.after(0, self._on_channel_checked, ch, completed)

        self.root.after(0, self._on_all_done)

    def _on_channel_checked(self, ch, completed):
        self.progress["value"] = completed
        self._update_stats()

        iid = str(ch["idx"])
        visible = self._matches_filters(ch)
        if self.tree.exists(iid):
            if not visible:
                self.tree.delete(iid)
            else:
                self.tree.item(
                    iid,
                    values=(
                        ch["idx"],
                        ch["status"],
                        ch["country"],
                        ch["name"],
                        ch["epg_text"],
                        ch["latency"],
                        ch["detail"],
                        ch["url"],
                    ),
                    tags=(ch["status"],),
                )
        elif visible:
            self._refresh_tree()

    def _on_all_done(self):
        self.is_running = False
        self.stop_requested = False
        self.start_btn.config(state=tk.NORMAL)
        self.stop_btn.config(state=tk.DISABLED)
        self._update_stats()

    def _show_context_menu(self, event):
        row_id = self.tree.identify_row(event.y)
        if row_id:
            if row_id not in self.tree.selection():
                self.tree.selection_set(row_id)
            self.ctx_menu.post(event.x_root, event.y_root)

    def _get_selected_channels(self):
        selected_ids = set(self.tree.selection())
        return [ch for ch in self.channels if str(ch["idx"]) in selected_ids]

    def _copy_selected_url(self):
        sel = self._get_selected_channels()
        if not sel:
            return
        urls = "\n".join(ch["url"] for ch in sel)
        self.root.clipboard_clear()
        self.root.clipboard_append(urls)

    def _recheck_selected(self):
        sel = self._get_selected_channels()
        if sel and not self.is_running:
            self._start_check(subset=sel)

    def _remove_selected(self):
        if self.is_running:
            return
        selected_ids = set(self.tree.selection())
        if not selected_ids:
            return
        self.channels = [ch for ch in self.channels if str(ch["idx"]) not in selected_ids]
        for i, ch in enumerate(self.channels, start=1):
            ch["idx"] = i
        self._update_country_filter_options()
        self._refresh_tree()
        self._update_stats()

    def _export_m3u(self, only_online=True):
        if not self.channels:
            messagebox.showwarning("Lista vuota", "Nessun canale da esportare.")
            return

        c_flt = self.country_filter_var.get()
        to_export = []
        for ch in self.channels:
            if only_online and ch["status"] != "ONLINE":
                continue
            if not only_online and not self._matches_filters(ch):
                continue
            if only_online and c_flt and c_flt != "Tutti i paesi" and ch["country"] != c_flt:
                continue
            to_export.append(ch)

        if not to_export:
            messagebox.showwarning(
                "Nessun canale valido",
                "Non ci sono canali corrispondenti ai filtri selezionati da esportare.",
            )
            return

        default_name = "playlist_valida.m3u" if only_online else "playlist_filtrata.m3u"
        save_path = filedialog.asksaveasfilename(
            title="Salva playlist M3U",
            defaultextension=".m3u",
            initialfile=default_name,
            filetypes=[("Playlist M3U", "*.m3u"), ("Playlist M3U8", "*.m3u8"), ("Tutti i file", "*.*")],
        )
        if not save_path:
            return

        epg_attr = self.epg_source_var.get().strip() or self.m3u_header_epg
        header = f'#EXTM3U url-tvg="{epg_attr}"' if epg_attr.startswith(("http://", "https://")) else "#EXTM3U"

        out_lines = [header]
        for ch in to_export:
            extinf_line = ch["extinf"]
            matched_id = ch.get("epg_matched_id")
            if matched_id and 'tvg-id="' not in extinf_line.lower():
                extinf_line = extinf_line.replace("#EXTINF:-1", f'#EXTINF:-1 tvg-id="{matched_id}"', 1)
            out_lines.append(extinf_line)
            for opt in ch["extra_opts"]:
                out_lines.append(opt)
            if ch["ua"]:
                out_lines.append(f"#EXTVLCOPT:http-user-agent={ch['ua']}")
            if ch["referer"]:
                out_lines.append(f"#EXTVLCOPT:http-referrer={ch['referer']}")
            out_lines.append(ch["url"])

        try:
            with open(save_path, "w", encoding="utf-8") as f:
                f.write("\n".join(out_lines) + "\n")
            messagebox.showinfo(
                "Esportazione completata",
                f"Esportati {len(to_export)} canali in:\n{save_path}",
            )
        except Exception as e:
            messagebox.showerror("Errore salvataggio", f"Impossibile salvare il file:\n{e}")


if __name__ == "__main__":
    root = tk.Tk()
    app = IPTVCheckerApp(root)
    root.mainloop()
