#!/usr/bin/env python3
"""
mewnesemu – Single-file NES emulator with FCEUX 1.0 style GUI.
Requirements:
  - black background, blue text
  - import math, import python3.14 (as a joke)
  - 60 fps, speed slider
  - internal CPU core (named mewnesemu01)
"""
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog
import threading
import time
import math
import os
import json
# "import python3.14" joke – keeping the hack below:
# import sys as python314   # Uncomment if you want the gag, otherwise delete.

# ============================================================
#  NES CPU Core (mewnesemu01)
# ============================================================
class Mewnesemu01:
    """Minimal 6502 emulator – enough to run simple code."""
    def __init__(self, rom_data):
        if rom_data[:4] != b"NES\x1a":
            raise ValueError("Not a valid iNES ROM")
        if len(rom_data) < 16:
            raise ValueError("ROM too small (missing iNES header)")

        self.mem = bytearray(0x10000)
        flags6 = rom_data[6]
        mapper = (flags6 >> 4) | (rom_data[7] & 0xF0)
        if mapper not in (0, 2):
            raise ValueError(f"Unsupported mapper {mapper} for internal core (supported: 0, 2)")
        self.mapper = mapper

        prg_banks = rom_data[4]
        prg_size = prg_banks * 0x4000
        if prg_size == 0:
            raise ValueError("ROM has no PRG data")

        trainer_size = 512 if (flags6 & 0x04) else 0
        prg_offset = 16 + trainer_size

        # Load PRG ROM, honor 16KB mirror mapping.
        prg_bytes = rom_data[prg_offset:prg_offset + prg_size]
        if len(prg_bytes) < prg_size:
            raise ValueError("ROM is truncated (PRG section incomplete)")

        self.prg_banks = [
            prg_bytes[i * 0x4000:(i + 1) * 0x4000] for i in range(prg_banks)
        ]
        self.prg_bank_count = len(self.prg_banks)
        self.bank_select = 0

        if self.mapper == 0 and prg_banks == 1:
            self.mem[0x8000:0xC000] = self.prg_banks[0]
            self.mem[0xC000:0x10000] = self.prg_banks[0]
        elif self.mapper == 0:
            self.mem[0x8000:0xC000] = self.prg_banks[0]
            self.mem[0xC000:0x10000] = self.prg_banks[1]
        else:
            # Mapper 2: initialise with bank 0 at $8000-$BFFF, last bank at $C000-$FFFF
            self.bank_select = 0
            self.mem[0x8000:0xC000] = self.prg_banks[0]
            self.mem[0xC000:0x10000] = self.prg_banks[-1]

        # Reset vector (little-endian at $FFFC)
        lo = self._read(0xFFFC)
        hi = self._read(0xFFFD)
        self.PC = (hi << 8) | lo
        if self.PC < 0x8000 or self.PC in (0x0000, 0xFFFF):
            self.PC = 0x8000
        self.A = self.X = self.Y = 0
        self.SP = 0xFD
        self.status = 0x24   # I flag set (IRQs disabled)
        self.running = True
        self.cycles = 0
        self.frame_cycles_target = 29780  # NTSC per frame

    def _read(self, addr):
        # Minimal memory map (ignore PPU/APU mirrors)
        if addr < 0x2000:
            return self.mem[addr & 0x07FF]
        elif addr < 0x4000:
            return 0  # PPU stub
        elif addr >= 0x8000:
            # Mapper 2: switchable 0x8000-0xBFFF, fixed 0xC000-0xFFFF
            if self.mapper == 2 and addr < 0xC000:
                # Read directly from the selected bank (not from self.mem, which may be stale)
                bank = self.prg_banks[self.bank_select % self.prg_bank_count]
                return bank[addr - 0x8000]
            return self.mem[addr]
        else:
            return self.mem[addr]

    def _write(self, addr, val):
        if addr < 0x2000:
            self.mem[addr & 0x07FF] = val
        elif addr < 0x4000:
            pass  # ignore PPU writes
        elif addr == 0x4014:  # OAM DMA (stub)
            pass
        elif addr >= 0x8000 and self.mapper == 2:
            # Bank switch: copy the selected PRG bank into $8000-$BFFF
            self.bank_select = val % self.prg_bank_count
            self.mem[0x8000:0xC000] = self.prg_banks[self.bank_select]
        else:
            self.mem[addr] = val

    # Flag helpers
    def _set_nz(self, v):
        if v == 0:
            self.status |= 0x02
        else:
            self.status &= ~0x02
        if v & 0x80:
            self.status |= 0x80
        else:
            self.status &= ~0x80

    def _get_carry(self):
        return 1 if (self.status & 0x01) else 0

    def _set_carry(self, cond):
        if cond:
            self.status |= 0x01
        else:
            self.status &= ~0x01

    def _set_overflow(self, cond):
        if cond:
            self.status |= 0x40
        else:
            self.status &= ~0x40

    def _adc(self, val):
        total = self.A + val + self._get_carry()
        result = total & 0xFF
        self._set_carry(total > 0xFF)
        self._set_overflow(((~(self.A ^ val) & (self.A ^ result)) & 0x80) != 0)
        self.A = result
        self._set_nz(self.A)

    def _sbc(self, val):
        # Invert carry before ADC for correct subtraction
        self._set_carry(not (self.status & 0x01))
        self._adc((val ^ 0xFF) & 0xFF)

    def step(self):
        """Execute one instruction and return."""
        op = self._read(self.PC)
        self.PC = (self.PC + 1) & 0xFFFF
        # ---- Implemented opcodes ----
        if op == 0xEA:          # NOP
            self.cycles += 2
        elif op == 0x78:        # SEI
            self.status |= 0x04
            self.cycles += 2
        elif op == 0x58:        # CLI
            self.status &= ~0x04
            self.cycles += 2
        elif op == 0xD8:        # CLD
            self.status &= ~0x08
            self.cycles += 2
        elif op == 0xF8:        # SED
            self.status |= 0x08
            self.cycles += 2
        elif op == 0x18:        # CLC
            self.status &= ~0x01
            self.cycles += 2
        elif op == 0x38:        # SEC
            self.status |= 0x01
            self.cycles += 2
        elif op == 0xA9:        # LDA immediate
            self.A = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._set_nz(self.A)
            self.cycles += 2
        elif op == 0xA5:        # LDA zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self.A = self._read(zp)
            self._set_nz(self.A)
            self.cycles += 3
        elif op == 0xB5:        # LDA zero page,X
            zp = (self._read(self.PC) + self.X) & 0xFF
            self.PC = (self.PC + 1) & 0xFFFF
            self.A = self._read(zp)
            self._set_nz(self.A)
            self.cycles += 4
        elif op == 0xAD:        # LDA absolute
            addr = self._read(self.PC) | (self._read((self.PC + 1) & 0xFFFF) << 8)
            self.PC = (self.PC + 2) & 0xFFFF
            self.A = self._read(addr)
            self._set_nz(self.A)
            self.cycles += 4
        elif op == 0xA2:        # LDX immediate
            self.X = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._set_nz(self.X)
            self.cycles += 2
        elif op == 0xA6:        # LDX zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self.X = self._read(zp)
            self._set_nz(self.X)
            self.cycles += 3
        elif op == 0xAE:        # LDX absolute
            addr = self._read(self.PC) | (self._read((self.PC + 1) & 0xFFFF) << 8)
            self.PC = (self.PC + 2) & 0xFFFF
            self.X = self._read(addr)
            self._set_nz(self.X)
            self.cycles += 4
        elif op == 0xA0:        # LDY immediate
            self.Y = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._set_nz(self.Y)
            self.cycles += 2
        elif op == 0xA4:        # LDY zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self.Y = self._read(zp)
            self._set_nz(self.Y)
            self.cycles += 3
        elif op == 0xAC:        # LDY absolute
            addr = self._read(self.PC) | (self._read((self.PC + 1) & 0xFFFF) << 8)
            self.PC = (self.PC + 2) & 0xFFFF
            self.Y = self._read(addr)
            self._set_nz(self.Y)
            self.cycles += 4
        elif op == 0x85:        # STA zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._write(zp, self.A)
            self.cycles += 3
        elif op == 0x8D:        # STA absolute
            addr = self._read(self.PC) | (self._read((self.PC + 1) & 0xFFFF) << 8)
            self.PC = (self.PC + 2) & 0xFFFF
            self._write(addr, self.A)
            self.cycles += 4
        elif op == 0x95:        # STA zero page,X
            zp = (self._read(self.PC) + self.X) & 0xFF
            self.PC = (self.PC + 1) & 0xFFFF
            self._write(zp, self.A)
            self.cycles += 4
        elif op == 0x86:        # STX zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._write(zp, self.X)
            self.cycles += 3
        elif op == 0x84:        # STY zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._write(zp, self.Y)
            self.cycles += 3
        elif op == 0x4C:        # JMP absolute
            addr = self._read(self.PC) | (self._read((self.PC + 1) & 0xFFFF) << 8)
            self.PC = addr
            self.cycles += 3
        elif op == 0x6C:        # JMP indirect
            ptr = self._read(self.PC) | (self._read((self.PC + 1) & 0xFFFF) << 8)
            lo = self._read(ptr)
            hi = self._read((ptr & 0xFF00) | ((ptr + 1) & 0x00FF))  # 6502 page-wrap bug
            self.PC = (hi << 8) | lo
            self.cycles += 5
        elif op == 0x20:        # JSR
            sub = self._read(self.PC) | (self._read((self.PC + 1) & 0xFFFF) << 8)
            self.PC = (self.PC + 2) & 0xFFFF
            ret_addr = self.PC - 1  # push return address -1
            self._push_word(ret_addr)
            self.PC = sub
            self.cycles += 6
        elif op == 0x60:        # RTS
            self.PC = (self._pull_word() + 1) & 0xFFFF
            self.cycles += 6
        elif op == 0xD0:        # BNE
            offset = self._read(self.PC)
            if offset > 127:
                offset -= 256
            self.PC = (self.PC + 1) & 0xFFFF
            if not (self.status & 0x02):  # Z clear
                self.PC = (self.PC + offset) & 0xFFFF
                self.cycles += 1
            self.cycles += 2
        elif op == 0xF0:        # BEQ
            offset = self._read(self.PC)
            if offset > 127:
                offset -= 256
            self.PC = (self.PC + 1) & 0xFFFF
            if self.status & 0x02:  # Z set
                self.PC = (self.PC + offset) & 0xFFFF
                self.cycles += 1
            self.cycles += 2
        elif op == 0xE6:        # INC zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            val = (self._read(zp) + 1) & 0xFF
            self._write(zp, val)
            self._set_nz(val)
            self.cycles += 5
        elif op == 0xE8:        # INX
            self.X = (self.X + 1) & 0xFF
            self._set_nz(self.X)
            self.cycles += 2
        elif op == 0xCA:        # DEX
            self.X = (self.X - 1) & 0xFF
            self._set_nz(self.X)
            self.cycles += 2
        elif op == 0xC8:        # INY
            self.Y = (self.Y + 1) & 0xFF
            self._set_nz(self.Y)
            self.cycles += 2
        elif op == 0x88:        # DEY
            self.Y = (self.Y - 1) & 0xFF
            self._set_nz(self.Y)
            self.cycles += 2
        elif op == 0xAA:        # TAX
            self.X = self.A
            self._set_nz(self.X)
            self.cycles += 2
        elif op == 0xA8:        # TAY
            self.Y = self.A
            self._set_nz(self.Y)
            self.cycles += 2
        elif op == 0x8A:        # TXA
            self.A = self.X
            self._set_nz(self.A)
            self.cycles += 2
        elif op == 0x98:        # TYA
            self.A = self.Y
            self._set_nz(self.A)
            self.cycles += 2
        elif op == 0x9A:        # TXS
            self.SP = self.X
            self.cycles += 2
        elif op == 0xBA:        # TSX
            self.X = self.SP
            self._set_nz(self.X)
            self.cycles += 2
        elif op == 0x48:        # PHA
            self._push_byte(self.A)
            self.cycles += 3
        elif op == 0x68:        # PLA
            self.A = self._pull_byte()
            self._set_nz(self.A)
            self.cycles += 4
        elif op == 0x08:        # PHP
            self._push_byte(self.status | 0x10)   # B flag set on push
            self.cycles += 3
        elif op == 0x28:        # PLP
            # Pull status without forcing bits (B flag & unused bit are ignored by most games)
            self.status = self._pull_byte()
            self.cycles += 4
        elif op == 0x69:        # ADC immediate
            self._adc(self._read(self.PC))
            self.PC = (self.PC + 1) & 0xFFFF
            self.cycles += 2
        elif op == 0x65:        # ADC zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._adc(self._read(zp))
            self.cycles += 3
        elif op == 0xE9:        # SBC immediate
            self._sbc(self._read(self.PC))
            self.PC = (self.PC + 1) & 0xFFFF
            self.cycles += 2
        elif op == 0xE5:        # SBC zero page
            zp = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._sbc(self._read(zp))
            self.cycles += 3
        elif op == 0x29:        # AND immediate
            self.A &= self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._set_nz(self.A)
            self.cycles += 2
        elif op == 0x09:        # ORA immediate
            self.A |= self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._set_nz(self.A)
            self.cycles += 2
        elif op == 0x49:        # EOR immediate
            self.A ^= self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            self._set_nz(self.A)
            self.cycles += 2
        elif op == 0xC9:        # CMP immediate
            val = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            tmp = (self.A - val) & 0x1FF
            self._set_carry(self.A >= val)
            self._set_nz(tmp & 0xFF)
            self.cycles += 2
        elif op == 0xE0:        # CPX immediate
            val = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            tmp = (self.X - val) & 0x1FF
            self._set_carry(self.X >= val)
            self._set_nz(tmp & 0xFF)
            self.cycles += 2
        elif op == 0xC0:        # CPY immediate
            val = self._read(self.PC)
            self.PC = (self.PC + 1) & 0xFFFF
            tmp = (self.Y - val) & 0x1FF
            self._set_carry(self.Y >= val)
            self._set_nz(tmp & 0xFF)
            self.cycles += 2
        elif op == 0x24:        # BIT zero page
            val = self._read(self._read(self.PC))
            self.PC = (self.PC + 1) & 0xFFFF
            if (self.A & val) == 0:
                self.status |= 0x02
            else:
                self.status &= ~0x02
            self.status = (self.status & ~0xC0) | (val & 0xC0)
            self.cycles += 3
        elif op == 0x10:        # BPL
            offset = self._read(self.PC)
            if offset > 127:
                offset -= 256
            self.PC = (self.PC + 1) & 0xFFFF
            if not (self.status & 0x80):
                self.PC = (self.PC + offset) & 0xFFFF
                self.cycles += 1
            self.cycles += 2
        elif op == 0x30:        # BMI
            offset = self._read(self.PC)
            if offset > 127:
                offset -= 256
            self.PC = (self.PC + 1) & 0xFFFF
            if self.status & 0x80:
                self.PC = (self.PC + offset) & 0xFFFF
                self.cycles += 1
            self.cycles += 2
        elif op == 0x90:        # BCC
            offset = self._read(self.PC)
            if offset > 127:
                offset -= 256
            self.PC = (self.PC + 1) & 0xFFFF
            if not (self.status & 0x01):
                self.PC = (self.PC + offset) & 0xFFFF
                self.cycles += 1
            self.cycles += 2
        elif op == 0xB0:        # BCS
            offset = self._read(self.PC)
            if offset > 127:
                offset -= 256
            self.PC = (self.PC + 1) & 0xFFFF
            if self.status & 0x01:
                self.PC = (self.PC + offset) & 0xFFFF
                self.cycles += 1
            self.cycles += 2
        elif op == 0x50:        # BVC
            offset = self._read(self.PC)
            if offset > 127:
                offset -= 256
            self.PC = (self.PC + 1) & 0xFFFF
            if not (self.status & 0x40):
                self.PC = (self.PC + offset) & 0xFFFF
                self.cycles += 1
            self.cycles += 2
        elif op == 0x70:        # BVS
            offset = self._read(self.PC)
            if offset > 127:
                offset -= 256
            self.PC = (self.PC + 1) & 0xFFFF
            if self.status & 0x40:
                self.PC = (self.PC + offset) & 0xFFFF
                self.cycles += 1
            self.cycles += 2
        elif op == 0x00:        # BRK
            # Proper BRK: push status (with B flag), PC+2, then load IRQ vector
            self._push_word((self.PC + 1) & 0xFFFF)   # PC+2 after BRK
            self._push_byte(self.status | 0x10)       # B flag set
            self.status |= 0x04                        # disable IRQ
            lo = self._read(0xFFFE)
            hi = self._read(0xFFFF)
            self.PC = (hi << 8) | lo
            self.cycles += 7
        else:
            # Unknown opcode → treat as NOP
            self.cycles += 2

    def _push_byte(self, val):
        self.mem[0x100 + self.SP] = val
        self.SP = (self.SP - 1) & 0xFF

    def _pull_byte(self):
        self.SP = (self.SP + 1) & 0xFF
        return self.mem[0x100 + self.SP]

    def _push_word(self, val):
        self._push_byte((val >> 8) & 0xFF)
        self._push_byte(val & 0xFF)

    def _pull_word(self):
        lo = self._pull_byte()
        hi = self._pull_byte()
        return (hi << 8) | lo

    def run_frame(self):
        """Run enough cycles for one frame and return."""
        start_cycles = self.cycles
        while self.running and self.cycles - start_cycles < self.frame_cycles_target:
            self.step()

# ============================================================
#  FCEUX 1.0 – style GUI
# ============================================================
class FCEUXGui:
    def __init__(self):
        self.config_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mewnesemu_config.json")
        self.settings = self._load_config()

        self.root = tk.Tk()
        self.root.title("mewnesemu – FCEUX 1.0")
        self.root.configure(bg="#d9d9d9")
        self.root.geometry(self.settings.get("window_geometry", "980x620"))
        self.root.resizable(True, True)

        self.nes = None
        self.current_rom_path = ""
        self.current_rom_data = None
        self.rom_loaded = False
        self.running = False
        self.emu_thread = None
        self.speed_multiplier = float(self.settings.get("default_speed", 1.0))
        self.closing = False
        self.state_lock = threading.Lock()
        self.emu_lock = threading.Lock()
        self.internal_ready = False
        self.fps_after_id = None

        # FPS tracking
        self.last_time = time.time()
        self.frame_count = 0
        self.fps = "0"
        self.status_text = tk.StringVar(value="Ready")

        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.quit_app)
        self._update_fps_label()

    def _load_config(self):
        defaults = {"default_speed": 1.0, "window_geometry": "980x620"}
        try:
            if os.path.exists(self.config_path):
                with open(self.config_path, "r", encoding="utf-8") as f:
                    loaded = json.load(f)
                defaults.update(loaded)
        except Exception:
            pass
        return defaults

    def _save_config(self):
        data = {
            "default_speed": max(0.1, float(self.speed_var.get())),
            "window_geometry": self.root.winfo_geometry(),
        }
        with open(self.config_path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
        self.settings = data

    def _build_ui(self):
        self._build_menubar()

        toolbar = tk.Frame(self.root, bg="#dcdcdc", relief="groove", bd=1)
        toolbar.pack(fill="x", padx=4, pady=(2, 4))

        tk.Label(toolbar, text="ROM:", bg="#dcdcdc", fg="#1f1f1f").pack(side="left", padx=(6, 3))
        self.rom_entry = tk.Entry(toolbar, width=48, bg="white", fg="#111", insertbackground="#111")
        self.rom_entry.pack(side="left", padx=3, pady=4)
        tk.Button(toolbar, text="Browse", command=self.load_rom, width=8).pack(side="left", padx=3)

        self.run_btn = tk.Button(toolbar, text="Run", command=self.toggle_run, width=7)
        self.run_btn.pack(side="left", padx=3)
        tk.Button(toolbar, text="Reset", command=self.reset, width=7).pack(side="left", padx=3)
        tk.Button(toolbar, text="Save", command=self.save_state, width=7).pack(side="left", padx=3)
        tk.Button(toolbar, text="Load", command=self.load_state, width=7).pack(side="left", padx=3)
        tk.Button(toolbar, text="Quit", command=self.quit_app, width=7).pack(side="right", padx=6)

        tk.Label(toolbar, text="Speed", bg="#dcdcdc", fg="#1f1f1f").pack(side="right", padx=(8, 2))
        self.speed_var = tk.DoubleVar(value=self.speed_multiplier)
        tk.Scale(
            toolbar,
            from_=0.5,
            to=2.0,
            resolution=0.1,
            orient="horizontal",
            length=140,
            variable=self.speed_var,
            command=self._speed_changed,
            bg="#dcdcdc",
            highlightthickness=0,
        ).pack(side="right", padx=(2, 8))

        content = tk.Frame(self.root, bg="#cfcfcf")
        content.pack(fill="both", expand=True, padx=6, pady=4)

        left_panel = tk.Frame(content, bg="#6ba0ff", relief="sunken", bd=2)
        left_panel.pack(side="left", fill="y")
        tk.Label(left_panel, text="Name Table Viewer", bg="#2e5dad", fg="white", anchor="w", padx=4).pack(fill="x")
        self.name_table = tk.Listbox(left_panel, width=20, height=30, bg="#8cb7ff", fg="#001d4d")
        self.name_table.pack(fill="both", padx=4, pady=4)
        for i in range(64):
            self.name_table.insert("end", f"${i * 0x40:04X}  tile row {i:02d}")

        center_panel = tk.Frame(content, bg="#4f87dd", relief="sunken", bd=2)
        center_panel.pack(side="left", fill="both", expand=True, padx=5)
        tk.Label(center_panel, text="mewnesemu display", bg="#2e5dad", fg="white", anchor="w", padx=4).pack(fill="x")
        self.fps_lbl = tk.Label(center_panel, text="FPS: 0 | Speed: 1.0x", bg="#4f87dd", fg="white", font=("Tahoma", 9, "bold"))
        self.fps_lbl.pack(anchor="w", padx=6, pady=(4, 0))
        self.screen_canvas = tk.Canvas(
            center_panel, width=512, height=480, bg="#1b4ca0", highlightthickness=1, highlightbackground="#24457f"
        )
        self.screen_canvas.pack(padx=6, pady=6)

        right_panel = tk.Frame(content, bg="#c6c6c6", relief="sunken", bd=2)
        right_panel.pack(side="right", fill="y")

        tk.Label(right_panel, text="Debugger", bg="#9e9e9e", fg="#111", anchor="w", padx=4).pack(fill="x")
        self.debug_list = tk.Listbox(right_panel, width=34, height=15, bg="white", fg="#111")
        self.debug_list.pack(padx=4, pady=4)
        for i in range(20):
            self.debug_list.insert("end", f"$80{i:02X}: EA  NOP")

        tk.Label(right_panel, text="CPU Registers", bg="#9e9e9e", fg="#111", anchor="w", padx=4).pack(fill="x", pady=(4, 0))
        self.reg_lbl = tk.Label(right_panel, justify="left", anchor="w", bg="#e8e8e8", fg="#111", width=32, height=6)
        self.reg_lbl.pack(fill="x", padx=4, pady=4)

        tk.Label(right_panel, text="Hex View", bg="#9e9e9e", fg="#111", anchor="w", padx=4).pack(fill="x")
        self.hex_list = tk.Listbox(right_panel, width=34, height=8, bg="white", fg="#111")
        self.hex_list.pack(padx=4, pady=4)
        for i in range(8):
            self.hex_list.insert("end", f"{i*16:04X}: " + " ".join(["00"] * 16))

        status = tk.Frame(self.root, bg="#efefef", relief="sunken", bd=1)
        status.pack(fill="x", side="bottom")
        tk.Label(status, textvariable=self.status_text, bg="#efefef", fg="#111", anchor="w", padx=6).pack(fill="x")

    def _build_menubar(self):
        self.menubar = tk.Menu(self.root)
        self.root.config(menu=self.menubar)

        file_menu = tk.Menu(self.menubar, tearoff=0)
        file_menu.add_command(label="Open ROM...", command=self.load_rom)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit_app)
        self.menubar.add_cascade(label="File", menu=file_menu)

        config_menu = tk.Menu(self.menubar, tearoff=0)
        config_menu.add_command(label="Set Default Speed...", command=self._set_default_speed)
        config_menu.add_command(label="Save Window Size", command=self._save_window_geometry)
        self.menubar.add_cascade(label="Config", menu=config_menu)

        nes_menu = tk.Menu(self.menubar, tearoff=0)
        nes_menu.add_command(label="Run/Pause", command=self.toggle_run)
        nes_menu.add_command(label="Reset", command=self.reset)
        self.menubar.add_cascade(label="NES", menu=nes_menu)

        tools_menu = tk.Menu(self.menubar, tearoff=0)
        tools_menu.add_command(label="Save State", command=self.save_state)
        tools_menu.add_command(label="Load State", command=self.load_state)
        self.menubar.add_cascade(label="Tools", menu=tools_menu)

        debug_menu = tk.Menu(self.menubar, tearoff=0)
        debug_menu.add_command(label="Refresh Debug Panels", command=self._update_debug_panel)
        debug_menu.add_command(label="Clear Status", command=lambda: self.status_text.set("Ready"))
        self.menubar.add_cascade(label="Debug", menu=debug_menu)

        help_menu = tk.Menu(self.menubar, tearoff=0)
        help_menu.add_command(label="About", command=self._show_about)
        self.menubar.add_cascade(label="Help", menu=help_menu)

    def _show_about(self):
        messagebox.showinfo("About", "mewnesemu GUI\nFCEUX-style frontend with minimal emulator core.")

    def _set_default_speed(self):
        val = simpledialog.askfloat(
            "Default Speed",
            "Set default speed (0.1 to 3.0):",
            minvalue=0.1,
            maxvalue=3.0,
            initialvalue=float(self.speed_var.get()),
            parent=self.root,
        )
        if val is None:
            return
        self.speed_var.set(val)
        self._speed_changed(str(val))
        self._save_config()
        self.status_text.set(f"Default speed set to {val:.1f}x")

    def _save_window_geometry(self):
        self._save_config()
        self.status_text.set("Window size saved")

    def _set_running_state(self, is_running, reason):
        self.running = is_running
        self.run_btn.config(text="Pause" if is_running else "Run")
        self.status_text.set(reason)

    def _stop_emulation(self, join_timeout=1.0):
        self.running = False
        thread = self.emu_thread
        if thread and thread.is_alive():
            thread.join(timeout=join_timeout)

    def _load_rom_bytes(self, path):
        with open(path, "rb") as f:
            return f.read()

    def _load_rom_from_path(self, path):
        data = self._load_rom_bytes(path)
        nes = Mewnesemu01(data)
        with self.emu_lock:
            self.nes = nes
        self.current_rom_path = path
        self.current_rom_data = data
        self.rom_loaded = True
        self.internal_ready = True
        self._set_running_state(False, "ROM loaded")
        self.rom_entry.delete(0, "end")
        self.rom_entry.insert(0, path)
        self.status_text.set(f"Loaded ROM: {os.path.basename(path)} | Core: Internal")
        self._update_debug_panel()

    def load_rom(self):
        path = filedialog.askopenfilename(
            title="Open NES ROM",
            filetypes=[("NES ROMs", "*.nes"), ("All files", "*.*")]
        )
        if not path:
            return
        try:
            self._stop_emulation()
            self._load_rom_from_path(path)
            messagebox.showinfo("Success", "ROM loaded successfully.")
        except Exception as e:
            self.rom_loaded = False
            self.internal_ready = False
            with self.emu_lock:
                self.nes = None
            self.current_rom_path = ""
            self.current_rom_data = None
            self._set_running_state(False, "ROM load failed")
            messagebox.showerror("Error", f"Failed to load ROM:\n{e}")

    def toggle_run(self):
        if not self.rom_loaded:
            messagebox.showwarning("No ROM", "Load a ROM first!")
            self.status_text.set("No ROM loaded")
            return
        if not self.internal_ready:
            messagebox.showerror(
                "Unsupported ROM",
                "This ROM is not supported by the internal core yet.\n"
                "Currently supported mappers: 0 (NROM), 2 (UxROM)."
            )
            self.status_text.set("Unsupported mapper for internal core")
            return
        if self.running:
            self._set_running_state(False, "Paused")
        else:
            if self.emu_thread and self.emu_thread.is_alive():
                self.status_text.set("Already running")
                return
            self._set_running_state(True, "Running")
            self.emu_thread = threading.Thread(target=self._emulation_loop, daemon=True)
            self.emu_thread.start()

    def _emulation_loop(self):
        target_fps = 60.0
        halted = False
        while self.running and self.nes is not None:
            frame_start = time.time()
            with self.emu_lock:
                if self.nes is None:
                    break
                self.nes.run_frame()
                if not self.nes.running:   # BRK or other halt condition
                    halted = True
                    break
            # Update visual feedback on the canvas (can be heavy, but okay)
            self.root.after(0, self._update_screen)
            # FPS accounting
            with self.state_lock:
                self.frame_count += 1
                now = time.time()
                if now - self.last_time >= 1.0:
                    self.fps = str(math.floor(self.frame_count / (now - self.last_time)))
                    self.last_time = now
                    self.frame_count = 0
            # Respect speed slider
            speed = self.speed_multiplier
            elapsed = time.time() - frame_start
            sleep = (1.0 / target_fps) / speed - elapsed
            if sleep > 0:
                time.sleep(sleep)
        if halted and not self.closing:
            self.root.after(0, lambda: self._set_running_state(False, "CPU halted (BRK)"))
        elif not self.closing and self.running:
            self.root.after(0, lambda: self._set_running_state(False, "Stopped"))
        self.emu_thread = None

    def _update_screen(self):
        # Change canvas colour slightly to indicate activity
        t = time.time() % 1
        r = int(0x1B + t * 0x15) & 0xFF
        g = int(0x4C + t * 0x25) & 0xFF
        b = int(0xA0 + t * 0x35) & 0xFF
        self.screen_canvas.configure(bg=f"#{r:02x}{g:02x}{b:02x}")
        self.screen_canvas.delete("activity")
        x = int((time.time() * 120) % 500) + 6
        self.screen_canvas.create_rectangle(x, 20, x + 10, 30, fill="#ffd000", outline="", tags="activity")
        self._update_debug_panel()

    def _update_debug_panel(self):
        with self.emu_lock:
            nes = self.nes
            if nes:
                pc = nes.PC
                a = nes.A
                x = nes.X
                y = nes.Y
                sp = nes.SP
                status = nes.status
                mem_snapshot = bytes(nes.mem[:128])
            else:
                pc = a = x = y = sp = status = None
                mem_snapshot = None

        if not nes:
            self.reg_lbl.config(text="PC: ----\nA : --\nX : --\nY : --\nSP: --\nP : --")
            self.hex_list.delete(0, "end")
            for i in range(8):
                self.hex_list.insert("end", f"{i*16:04X}: " + " ".join(["--"] * 16))
            return
        self.reg_lbl.config(
            text=(
                f"PC: ${pc:04X}\n"
                f"A : ${a:02X}\n"
                f"X : ${x:02X}\n"
                f"Y : ${y:02X}\n"
                f"SP: ${sp:02X}\n"
                f"P : ${status:02X}"
            )
        )
        self.hex_list.delete(0, "end")
        for row in range(8):
            base = row * 16
            data = " ".join(f"{mem_snapshot[base + col]:02X}" for col in range(16))
            self.hex_list.insert("end", f"{base:04X}: {data}")

    def reset(self):
        if not self.rom_loaded:
            messagebox.showwarning("No ROM", "Load a ROM first!")
            self.status_text.set("Reset ignored: no ROM loaded")
            return
        self._set_running_state(False, "Resetting")
        path = self.current_rom_path or self.rom_entry.get().strip()
        try:
            self._stop_emulation()
            self._load_rom_from_path(path)
            self._set_running_state(False, "Reset complete")
            messagebox.showinfo("Reset", "Emulator reset.")
        except Exception as e:
            self._set_running_state(False, "Reset failed")
            messagebox.showerror("Error", f"Reset failed:\n{e}")

    def save_state(self):
        if not self.internal_ready or not self.nes:
            messagebox.showwarning("No ROM", "Load a ROM first!")
            return
        path = filedialog.asksaveasfilename(
            title="Save Emulator State",
            defaultextension=".mns",
            filetypes=[("Mewnesemu State", "*.mns"), ("JSON", "*.json"), ("All files", "*.*")],
        )
        if not path:
            return
        try:
            was_running = self.running
            self._stop_emulation()
            with self.emu_lock:
                nes = self.nes
                if nes is None:
                    raise ValueError("No active emulator state to save")
                payload = {
                    "version": 1,
                    "rom_path": self.current_rom_path,
                    "cpu": {
                        "PC": nes.PC,
                        "A": nes.A,
                        "X": nes.X,
                        "Y": nes.Y,
                        "SP": nes.SP,
                        "status": nes.status,
                        "cycles": nes.cycles,
                        "running": nes.running,
                    },
                    "mapper": {
                        "id": nes.mapper,
                        "bank_select": nes.bank_select,
                        "prg_bank_count": nes.prg_bank_count,
                    },
                    "mem": list(nes.mem),
                }
            with open(path, "w", encoding="utf-8") as f:
                json.dump(payload, f)
            self.status_text.set(f"State saved: {os.path.basename(path)}")
            if was_running:
                self.toggle_run()
        except Exception as e:
            self.status_text.set("Save state failed")
            messagebox.showerror("Save State", f"Failed to save state:\n{e}")

    def load_state(self):
        path = filedialog.askopenfilename(
            title="Load Emulator State",
            filetypes=[("Mewnesemu State", "*.mns *.json"), ("All files", "*.*")],
        )
        if not path:
            return
        try:
            self._stop_emulation()
            with open(path, "r", encoding="utf-8") as f:
                payload = json.load(f)

            rom_path = payload.get("rom_path", "")
            if not rom_path:
                raise ValueError("State file missing ROM path")
            if not os.path.exists(rom_path):
                raise ValueError(f"ROM referenced by state not found:\n{rom_path}")

            self._load_rom_from_path(rom_path)
            with self.emu_lock:
                nes = self.nes
                if nes is None:
                    raise ValueError("Failed to initialize emulator before restore")
                cpu = payload["cpu"]
                mapper = payload["mapper"]
                mem = payload["mem"]
                if len(mem) != 0x10000:
                    raise ValueError("Invalid memory size in state file")
                nes.PC = int(cpu["PC"]) & 0xFFFF
                nes.A = int(cpu["A"]) & 0xFF
                nes.X = int(cpu["X"]) & 0xFF
                nes.Y = int(cpu["Y"]) & 0xFF
                nes.SP = int(cpu["SP"]) & 0xFF
                nes.status = int(cpu["status"]) & 0xFF
                nes.cycles = int(cpu["cycles"])
                nes.running = bool(cpu.get("running", True))
                if int(mapper["id"]) != nes.mapper:
                    raise ValueError("State mapper does not match ROM mapper")
                nes.bank_select = int(mapper.get("bank_select", 0)) % max(1, nes.prg_bank_count)
                nes.mem[:] = bytes(mem)

            self._set_running_state(False, "State loaded")
            self._update_debug_panel()
            self.status_text.set(f"State loaded: {os.path.basename(path)}")
            messagebox.showinfo("Load State", "State loaded successfully.")
        except Exception as e:
            self.status_text.set("Load state failed")
            messagebox.showerror("Load State", f"Failed to load state:\n{e}")

    def _speed_changed(self, val):
        try:
            self.speed_multiplier = max(0.1, float(val))
        except (TypeError, ValueError):
            self.speed_multiplier = 1.0

    def _update_fps_label(self):
        if self.closing:
            return
        with self.state_lock:
            fps = self.fps
        self.fps_lbl.config(
            text=f"FPS: {fps} | Speed: {self.speed_var.get():.1f}x"
        )
        self.fps_after_id = self.root.after(100, self._update_fps_label)

    def quit_app(self):
        self.closing = True
        self._set_running_state(False, "Closing...")
        if self.fps_after_id is not None:
            try:
                self.root.after_cancel(self.fps_after_id)
            except Exception:
                pass
        self._save_config()
        self._stop_emulation(join_timeout=0.3)
        self.root.destroy()

    def run(self):
        self.root.mainloop()

# ============================================================
if __name__ == "__main__":
    app = FCEUXGui()
    app.run()