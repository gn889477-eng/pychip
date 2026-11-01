#!/usr/bin/env python3
"""Pychip - emulador de CHIP-8 em Python (Tkinter, sem dependências externas).

Uso:
    python pychip.py              # abre com uma ROM de demonstração
    python pychip.py jogo.ch8     # abre uma ROM direto
    (ou use o menu Arquivo > Abrir ROM...)

Teclado (layout CHIP-8 -> teclado do PC):
    1 2 3 C        1 2 3 4
    4 5 6 D   ->   Q W E R
    7 8 9 E        A S D F
    A 0 B F        Z X C V

Atalhos: F5 = reiniciar, P = pausar, M = som on/off, +/- = velocidade, Esc = sair.
"""
import io
import math
import os
import random
import shutil
import struct
import subprocess
import sys
import tempfile
import tkinter as tk
import wave
from tkinter import filedialog, messagebox

# ---------------------------------------------------------------- quirks
SHIFT_USES_VY = False      # True = 8XY6/8XYE usam VY (CHIP-8 original)
LOAD_STORE_INC_I = False   # True = FX55/FX65 incrementam I (CHIP-8 original)
JUMP_V0_USES_VX = False    # True = BXNN usa VX (SUPER-CHIP)

W, H = 64, 32
SCALE = 12
FG, BG = "#33ff66", "#0a1a0f"

FONT = [
    0xF0, 0x90, 0x90, 0x90, 0xF0, 0x20, 0x60, 0x20, 0x20, 0x70,
    0xF0, 0x10, 0xF0, 0x80, 0xF0, 0xF0, 0x10, 0xF0, 0x10, 0xF0,
    0x90, 0x90, 0xF0, 0x10, 0x10, 0xF0, 0x80, 0xF0, 0x10, 0xF0,
    0xF0, 0x80, 0xF0, 0x90, 0xF0, 0xF0, 0x10, 0x20, 0x40, 0x40,
    0xF0, 0x90, 0xF0, 0x90, 0xF0, 0xF0, 0x90, 0xF0, 0x10, 0xF0,
    0xF0, 0x90, 0xF0, 0x90, 0x90, 0xE0, 0x90, 0xE0, 0x90, 0xE0,
    0xF0, 0x80, 0x80, 0x80, 0xF0, 0xE0, 0x90, 0x90, 0x90, 0xE0,
    0xF0, 0x80, 0xF0, 0x80, 0xF0, 0xF0, 0x80, 0xF0, 0x80, 0x80,
]

KEYMAP = {
    "1": 0x1, "2": 0x2, "3": 0x3, "4": 0xC,
    "q": 0x4, "w": 0x5, "e": 0x6, "r": 0xD,
    "a": 0x7, "s": 0x8, "d": 0x9, "f": 0xE,
    "z": 0xA, "x": 0x0, "c": 0xB, "v": 0xF,
}

# ROM de demonstração: desenha os dígitos 0-7 com a fonte embutida
DEMO_ROM = bytes([
    0x60, 0x00,  # V0 = 0 (x)
    0x61, 0x0A,  # V1 = 10 (y)
    0x62, 0x00,  # V2 = 0 (dígito)
    0xF2, 0x29,  # I = sprite do dígito V2
    0xD0, 0x15,  # draw V0,V1, 5 linhas
    0x70, 0x06,  # V0 += 6
    0x72, 0x01,  # V2 += 1
    0x32, 0x08,  # pula se V2 == 8
    0x12, 0x06,  # volta ao loop
    0x12, 0x10,  # fim: loop infinito
])


class Chip8:
    def __init__(self):
        self.reset()

    def reset(self):
        self.mem = bytearray(4096)
        self.mem[0x50:0x50 + len(FONT)] = bytes(FONT)
        self.V = [0] * 16
        self.I = 0
        self.pc = 0x200
        self.stack = []
        self.dt = 0
        self.st = 0
        self.display = [0] * (W * H)
        self.keys = [False] * 16
        self.wait_reg = None  # registrador aguardando tecla (FX0A)
        self.draw_flag = True

    def load(self, data):
        self.reset()
        if len(data) > 4096 - 0x200:
            raise ValueError("ROM grande demais (máx. 3584 bytes)")
        self.mem[0x200:0x200 + len(data)] = data

    def tick_timers(self):
        if self.dt:
            self.dt -= 1
        if self.st:
            self.st -= 1

    def key_pressed(self, k):
        if self.wait_reg is not None:
            self.V[self.wait_reg] = k
            self.wait_reg = None

    def step(self):
        if self.wait_reg is not None:
            return
        op = (self.mem[self.pc] << 8) | self.mem[(self.pc + 1) & 0xFFF]
        self.pc = (self.pc + 2) & 0xFFF
        n1 = (op >> 12) & 0xF
        x = (op >> 8) & 0xF
        y = (op >> 4) & 0xF
        n = op & 0xF
        nn = op & 0xFF
        nnn = op & 0xFFF
        V = self.V

        if n1 == 0x0:
            if op == 0x00E0:
                self.display = [0] * (W * H)
                self.draw_flag = True
            elif op == 0x00EE:
                if self.stack:
                    self.pc = self.stack.pop()
        elif n1 == 0x1:
            self.pc = nnn
        elif n1 == 0x2:
            if len(self.stack) >= 64:
                raise RuntimeError("estouro de pilha")
            self.stack.append(self.pc)
            self.pc = nnn
        elif n1 == 0x3:
            if V[x] == nn:
                self.pc += 2
        elif n1 == 0x4:
            if V[x] != nn:
                self.pc += 2
        elif n1 == 0x5:
            if V[x] == V[y]:
                self.pc += 2
        elif n1 == 0x6:
            V[x] = nn
        elif n1 == 0x7:
            V[x] = (V[x] + nn) & 0xFF
        elif n1 == 0x8:
            if n == 0x0:
                V[x] = V[y]
            elif n == 0x1:
                V[x] |= V[y]
                V[0xF] = 0
            elif n == 0x2:
                V[x] &= V[y]
                V[0xF] = 0
            elif n == 0x3:
                V[x] ^= V[y]
                V[0xF] = 0
            elif n == 0x4:
                r = V[x] + V[y]
                V[x] = r & 0xFF
                V[0xF] = 1 if r > 0xFF else 0
            elif n == 0x5:
                f = 1 if V[x] >= V[y] else 0
                V[x] = (V[x] - V[y]) & 0xFF
                V[0xF] = f
            elif n == 0x6:
                src = V[y] if SHIFT_USES_VY else V[x]
                f = src & 1
                V[x] = src >> 1
                V[0xF] = f
            elif n == 0x7:
                f = 1 if V[y] >= V[x] else 0
                V[x] = (V[y] - V[x]) & 0xFF
                V[0xF] = f
            elif n == 0xE:
                src = V[y] if SHIFT_USES_VY else V[x]
                f = (src >> 7) & 1
                V[x] = (src << 1) & 0xFF
                V[0xF] = f
        elif n1 == 0x9:
            if V[x] != V[y]:
                self.pc += 2
        elif n1 == 0xA:
            self.I = nnn
        elif n1 == 0xB:
            self.pc = (nnn + (V[x] if JUMP_V0_USES_VX else V[0])) & 0xFFF
        elif n1 == 0xC:
            V[x] = random.randint(0, 255) & nn
        elif n1 == 0xD:
            px, py = V[x] % W, V[y] % H
            V[0xF] = 0
            for row in range(n):
                yy = py + row
                if yy >= H:
                    break
                byte = self.mem[(self.I + row) & 0xFFF]
                for col in range(8):
                    xx = px + col
                    if xx >= W:
                        break
                    if byte & (0x80 >> col):
                        idx = yy * W + xx
                        if self.display[idx]:
                            V[0xF] = 1
                        self.display[idx] ^= 1
            self.draw_flag = True
        elif n1 == 0xE:
            if nn == 0x9E:
                if self.keys[V[x] & 0xF]:
                    self.pc += 2
            elif nn == 0xA1:
                if not self.keys[V[x] & 0xF]:
                    self.pc += 2
        elif n1 == 0xF:
            if nn == 0x07:
                V[x] = self.dt
            elif nn == 0x0A:
                self.wait_reg = x
            elif nn == 0x15:
                self.dt = V[x]
            elif nn == 0x18:
                self.st = V[x]
            elif nn == 0x1E:
                self.I = (self.I + V[x]) & 0xFFF
            elif nn == 0x29:
                self.I = 0x50 + (V[x] & 0xF) * 5
            elif nn == 0x33:
                v = V[x]
                self.mem[self.I & 0xFFF] = v // 100
                self.mem[(self.I + 1) & 0xFFF] = (v // 10) % 10
                self.mem[(self.I + 2) & 0xFFF] = v % 10
            elif nn == 0x55:
                for i in range(x + 1):
                    self.mem[(self.I + i) & 0xFFF] = V[i]
                if LOAD_STORE_INC_I:
                    self.I = (self.I + x + 1) & 0xFFF
            elif nn == 0x65:
                for i in range(x + 1):
                    V[i] = self.mem[(self.I + i) & 0xFFF]
                if LOAD_STORE_INC_I:
                    self.I = (self.I + x + 1) & 0xFFF


class Beeper:
    """Beep do CHIP-8 (toca enquanto o timer de som for > 0), sem dependências.

    Windows: winsound | macOS: afplay | Linux: paplay/aplay | senão: bell do Tk.
    """

    def __init__(self, bell=None, freq=600, rate=22050, dur=0.2):
        self.enabled = True
        self.playing = False
        self.proc = None
        self.mode = None
        self.bell = bell
        n = int(rate * dur)
        frames = b"".join(
            struct.pack("<h", int(9000 * math.sin(2 * math.pi * freq * i / rate)))
            for i in range(n))
        buf = io.BytesIO()
        with wave.open(buf, "wb") as w:
            w.setnchannels(1)
            w.setsampwidth(2)
            w.setframerate(rate)
            w.writeframes(frames)
        self.wav = buf.getvalue()
        if sys.platform.startswith("win"):
            try:
                import winsound
                self.winsound = winsound
                self.mode = "win"
            except ImportError:
                pass
        else:
            for cmd in (["afplay"], ["paplay"], ["aplay", "-q"]):
                if shutil.which(cmd[0]):
                    fd, self.path = tempfile.mkstemp(suffix=".wav")
                    with os.fdopen(fd, "wb") as f:
                        f.write(self.wav)
                    self.cmd = cmd
                    self.mode = "proc"
                    break

    def update(self, active):
        active = active and self.enabled
        try:
            if self.mode == "win":
                ws = self.winsound
                if active and not self.playing:
                    ws.PlaySound(self.wav, ws.SND_MEMORY | ws.SND_ASYNC | ws.SND_LOOP)
                elif not active and self.playing:
                    ws.PlaySound(None, ws.SND_PURGE)
            elif self.mode == "proc":
                if active:
                    if self.proc is None or self.proc.poll() is not None:
                        self.proc = subprocess.Popen(
                            self.cmd + [self.path],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                elif self.proc is not None:
                    if self.proc.poll() is None:
                        self.proc.terminate()
                    self.proc = None
            elif active and not self.playing and self.bell:
                self.bell()
        except Exception:
            pass
        self.playing = active

    def close(self):
        self.update(False)
        if getattr(self, "path", None):
            try:
                os.remove(self.path)
            except OSError:
                pass


class App:
    def __init__(self, root):
        self.root = root
        self.cpu = Chip8()
        self.beeper = Beeper(bell=root.bell)
        self.cycles_per_frame = 10
        self.paused = False
        self.rom_name = "demo"
        self.error = None

        root.title("Pychip - emulador CHIP-8")
        root.resizable(False, False)
        root.configure(bg="#000")

        menu = tk.Menu(root)
        fm = tk.Menu(menu, tearoff=0)
        fm.add_command(label="Abrir ROM...", command=self.open_rom)
        fm.add_command(label="Reiniciar (F5)", command=self.restart)
        fm.add_separator()
        fm.add_command(label="Sair", command=self.quit)
        menu.add_cascade(label="Arquivo", menu=fm)
        root.config(menu=menu)

        self.canvas = tk.Canvas(root, width=W * SCALE, height=H * SCALE,
                                bg=BG, highlightthickness=0)
        self.canvas.pack()
        self.rects = []
        for i in range(W * H):
            cx, cy = (i % W) * SCALE, (i // W) * SCALE
            self.rects.append(self.canvas.create_rectangle(
                cx, cy, cx + SCALE, cy + SCALE, fill=BG, outline=""))
        self.shown = [0] * (W * H)

        self.status = tk.Label(root, text="", bg="#000", fg=FG,
                               font=("Courier", 10), anchor="w")
        self.status.pack(fill="x")

        # --- barra de controle
        bar = tk.Frame(root, bg="#000")
        bar.pack(fill="x", padx=6, pady=(2, 0))
        btn_style = dict(bg="#12301c", fg=FG, activebackground="#1d4d2e",
                         activeforeground=FG, relief="flat", bd=0,
                         font=("Courier", 10, "bold"), padx=10, pady=4,
                         takefocus=0)
        tk.Button(bar, text="Abrir ROM", command=self.open_rom,
                  **btn_style).pack(side="left", padx=2)
        tk.Button(bar, text="Reiniciar", command=self.restart,
                  **btn_style).pack(side="left", padx=2)
        self.pause_btn = tk.Button(bar, text="Pausar",
                                   command=self.toggle_pause, **btn_style)
        self.pause_btn.pack(side="left", padx=2)
        self.sound_btn = tk.Button(bar, text="Som: ON",
                                   command=self.toggle_sound, **btn_style)
        self.sound_btn.pack(side="left", padx=2)
        tk.Button(bar, text="Vel -", command=lambda: self.change_speed(-2),
                  **btn_style).pack(side="right", padx=2)
        tk.Button(bar, text="Vel +", command=lambda: self.change_speed(2),
                  **btn_style).pack(side="right", padx=2)

        # --- teclado hexadecimal na tela (segure o botão para manter a tecla)
        pad = tk.Frame(root, bg="#000")
        pad.pack(pady=6)
        layout = [[0x1, 0x2, 0x3, 0xC],
                  [0x4, 0x5, 0x6, 0xD],
                  [0x7, 0x8, 0x9, 0xE],
                  [0xA, 0x0, 0xB, 0xF]]
        pc_key = {v: k.upper() for k, v in KEYMAP.items()}
        for r, row in enumerate(layout):
            for c, code in enumerate(row):
                b = tk.Button(pad, text=f"{code:X}\n{pc_key[code]}", width=5,
                              height=2, bg="#12301c", fg=FG,
                              activebackground=FG, activeforeground="#000",
                              relief="flat", bd=0, takefocus=0,
                              font=("Courier", 11, "bold"))
                b.grid(row=r, column=c, padx=3, pady=3)
                b.bind("<ButtonPress-1>", lambda e, k=code: self.press(k))
                b.bind("<ButtonRelease-1>", lambda e, k=code: self.release(k))

        root.bind("<KeyPress>", self.on_down)
        root.bind("<KeyRelease>", self.on_up)
        root.bind("<F5>", lambda e: self.restart())
        root.bind("<Escape>", lambda e: self.quit())
        root.protocol("WM_DELETE_WINDOW", self.quit)

        self.rom_data = DEMO_ROM
        self.cpu.load(self.rom_data)
        self.frame()

    def open_rom(self):
        path = filedialog.askopenfilename(
            title="Abrir ROM CHIP-8",
            filetypes=[("ROM CHIP-8", "*.ch8 *.c8 *.chip8 *.rom *.bin"),
                       ("Todos", "*.*")])
        if path:
            self.load_path(path)

    def load_path(self, path):
        try:
            with open(path, "rb") as f:
                data = f.read()
            self.cpu.load(data)
        except Exception as e:
            messagebox.showerror("Pychip", f"Erro ao carregar ROM:\n{e}")
            return
        self.rom_data = data
        self.rom_name = path.replace("\\", "/").split("/")[-1]
        self.error = None
        self.paused = False
        self.pause_btn.config(text="Pausar")

    def restart(self):
        self.cpu.load(self.rom_data)
        self.error = None
        self.paused = False
        self.pause_btn.config(text="Pausar")

    def press(self, c):
        if not self.cpu.keys[c]:
            self.cpu.keys[c] = True
            self.cpu.key_pressed(c)

    def release(self, c):
        self.cpu.keys[c] = False

    def toggle_sound(self):
        self.beeper.enabled = not self.beeper.enabled
        self.sound_btn.config(text="Som: ON" if self.beeper.enabled else "Som: OFF")

    def quit(self):
        self.beeper.close()
        self.root.destroy()

    def toggle_pause(self):
        self.paused = not self.paused
        self.pause_btn.config(text="Continuar" if self.paused else "Pausar")

    def change_speed(self, delta):
        self.cycles_per_frame = max(1, min(200, self.cycles_per_frame + delta))

    def on_down(self, e):
        k = e.keysym.lower()
        if k in KEYMAP:
            c = KEYMAP[k]
            if not self.cpu.keys[c]:
                self.cpu.keys[c] = True
                self.cpu.key_pressed(c)
        elif k == "p":
            self.toggle_pause()
        elif k == "m":
            self.toggle_sound()
        elif k in ("plus", "equal"):
            self.change_speed(2)
        elif k in ("minus", "underscore"):
            self.change_speed(-2)

    def on_up(self, e):
        k = e.keysym.lower()
        if k in KEYMAP:
            self.cpu.keys[KEYMAP[k]] = False

    def frame(self):
        if not self.paused and not self.error:
            try:
                for _ in range(self.cycles_per_frame):
                    self.cpu.step()
            except Exception as ex:
                self.error = f"erro em PC={self.cpu.pc:03X}: {ex}"
            self.cpu.tick_timers()
        self.beeper.update(self.cpu.st > 0 and not self.paused and not self.error)
        self.render()
        state = self.error or ("PAUSADO" if self.paused else "rodando")
        self.status.config(
            text=f" {self.rom_name} | {state} | "
                 f"{self.cycles_per_frame * 60} ciclos/s | "
                 f"PC={self.cpu.pc:03X} I={self.cpu.I:03X}")
        self.root.after(16, self.frame)

    def render(self):
        if not self.cpu.draw_flag:
            return
        self.cpu.draw_flag = False
        d, s = self.cpu.display, self.shown
        for i in range(W * H):
            if d[i] != s[i]:
                s[i] = d[i]
                self.canvas.itemconfig(self.rects[i], fill=FG if d[i] else BG)


def main():
    root = tk.Tk()
    app = App(root)
    if len(sys.argv) > 1:
        app.load_path(sys.argv[1])
    root.mainloop()


if __name__ == "__main__":
    main()
