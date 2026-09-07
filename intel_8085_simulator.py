#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════╗
║       Intel 8085 Microprocessor Simulator - Lab Trainer Kit      ║
║                                                                  ║
║  A comprehensive simulator with GUI that mimics a real 8085      ║
║  trainer kit. Features complete instruction set, two-pass        ║
║  assembler, step execution, breakpoints, and memory viewer.      ║
╚══════════════════════════════════════════════════════════════════╝
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, font as tkfont
import re
import threading
import time

# ═══════════════════════════════════════════════════════════════════
# SECTION 1: Intel 8085 CPU Core
# ═══════════════════════════════════════════════════════════════════

class Intel8085:
    """Complete Intel 8085 Microprocessor Emulator with all 246 opcodes."""

    # Register indices
    B, C, D, E, H, L, M, A = 0, 1, 2, 3, 4, 5, 6, 7

    def __init__(self):
        self.reset()
        self.output_callback = None  # For OUT instruction
        self.input_callback = None   # For IN instruction

    def reset(self):
        """Reset CPU to initial state."""
        self.reg = [0] * 8  # B, C, D, E, H, L, (M placeholder), A
        self.SP = 0xFFFF
        self.PC = 0x0000
        self.memory = bytearray(65536)
        self.io = bytearray(256)
        self.flags = {'S': 0, 'Z': 0, 'AC': 0, 'P': 0, 'CY': 0}
        self.halted = False
        self.inte = False  # Interrupt enable
        self.cycles = 0

    # ── Register Access ──────────────────────────────────────────
    def _get_reg(self, r):
        if r == 6:  # M = (HL)
            addr = (self.reg[self.H] << 8) | self.reg[self.L]
            return self.memory[addr]
        return self.reg[r]

    def _set_reg(self, r, v):
        v &= 0xFF
        if r == 6:  # M = (HL)
            addr = (self.reg[self.H] << 8) | self.reg[self.L]
            self.memory[addr] = v
        else:
            self.reg[r] = v

    def _get_rp(self, rp):
        """Get register pair: 0=BC, 1=DE, 2=HL, 3=SP"""
        if rp == 0: return (self.reg[0] << 8) | self.reg[1]
        if rp == 1: return (self.reg[2] << 8) | self.reg[3]
        if rp == 2: return (self.reg[4] << 8) | self.reg[5]
        if rp == 3: return self.SP
        return 0

    def _set_rp(self, rp, v):
        v &= 0xFFFF
        if rp == 0: self.reg[0], self.reg[1] = (v >> 8) & 0xFF, v & 0xFF
        elif rp == 1: self.reg[2], self.reg[3] = (v >> 8) & 0xFF, v & 0xFF
        elif rp == 2: self.reg[4], self.reg[5] = (v >> 8) & 0xFF, v & 0xFF
        elif rp == 3: self.SP = v

    # ── Memory Access ────────────────────────────────────────────
    def _fetch(self):
        b = self.memory[self.PC]
        self.PC = (self.PC + 1) & 0xFFFF
        return b

    def _fetch16(self):
        lo = self._fetch()
        hi = self._fetch()
        return (hi << 8) | lo

    def _push16(self, v):
        self.SP = (self.SP - 1) & 0xFFFF
        self.memory[self.SP] = (v >> 8) & 0xFF
        self.SP = (self.SP - 1) & 0xFFFF
        self.memory[self.SP] = v & 0xFF

    def _pop16(self):
        lo = self.memory[self.SP]
        self.SP = (self.SP + 1) & 0xFFFF
        hi = self.memory[self.SP]
        self.SP = (self.SP + 1) & 0xFFFF
        return (hi << 8) | lo

    # ── Flag Operations ──────────────────────────────────────────
    def _parity(self, v):
        return 1 if bin(v & 0xFF).count('1') % 2 == 0 else 0

    def _update_flags_arith(self, result, carry=True):
        r = result & 0xFF
        self.flags['S'] = 1 if (r & 0x80) else 0
        self.flags['Z'] = 1 if r == 0 else 0
        self.flags['P'] = self._parity(r)
        if carry:
            self.flags['CY'] = 1 if (result > 0xFF or result < 0) else 0

    def _update_flags_logic(self, result, ac=0):
        r = result & 0xFF
        self.flags['S'] = 1 if (r & 0x80) else 0
        self.flags['Z'] = 1 if r == 0 else 0
        self.flags['P'] = self._parity(r)
        self.flags['CY'] = 0
        self.flags['AC'] = ac

    def _get_psw(self):
        f = ((self.flags['S'] << 7) | (self.flags['Z'] << 6) |
             (self.flags['AC'] << 4) | (self.flags['P'] << 2) |
             0x02 | self.flags['CY'])
        return (self.reg[self.A] << 8) | f

    def _set_psw(self, v):
        self.reg[self.A] = (v >> 8) & 0xFF
        f = v & 0xFF
        self.flags['S'] = (f >> 7) & 1
        self.flags['Z'] = (f >> 6) & 1
        self.flags['AC'] = (f >> 4) & 1
        self.flags['P'] = (f >> 2) & 1
        self.flags['CY'] = f & 1

    def _check_condition(self, cond):
        """Check condition code: 0=NZ,1=Z,2=NC,3=C,4=PO,5=PE,6=P,7=M"""
        if cond == 0: return self.flags['Z'] == 0
        if cond == 1: return self.flags['Z'] == 1
        if cond == 2: return self.flags['CY'] == 0
        if cond == 3: return self.flags['CY'] == 1
        if cond == 4: return self.flags['P'] == 0
        if cond == 5: return self.flags['P'] == 1
        if cond == 6: return self.flags['S'] == 0
        if cond == 7: return self.flags['S'] == 1
        return False

    # ── ALU Operations ───────────────────────────────────────────
    def _add(self, val, carry=0):
        a = self.reg[self.A]
        result = a + val + carry
        self.flags['AC'] = 1 if ((a & 0x0F) + (val & 0x0F) + carry) > 0x0F else 0
        self._update_flags_arith(result)
        self.reg[self.A] = result & 0xFF

    def _sub(self, val, borrow=0):
        a = self.reg[self.A]
        result = a - val - borrow
        self.flags['AC'] = 0 if ((a & 0x0F) - (val & 0x0F) - borrow) < 0 else 1
        self._update_flags_arith(result)
        self.reg[self.A] = result & 0xFF

    def _ana(self, val):
        result = self.reg[self.A] & val
        self.flags['AC'] = 1 if ((self.reg[self.A] | val) & 0x08) else 0
        self._update_flags_logic(result, self.flags['AC'])
        self.reg[self.A] = result

    def _xra(self, val):
        result = self.reg[self.A] ^ val
        self._update_flags_logic(result)
        self.reg[self.A] = result

    def _ora(self, val):
        result = self.reg[self.A] | val
        self._update_flags_logic(result)
        self.reg[self.A] = result

    def _cmp(self, val):
        a = self.reg[self.A]
        result = a - val
        self.flags['AC'] = 0 if ((a & 0x0F) - (val & 0x0F)) < 0 else 1
        self._update_flags_arith(result)
        # A is NOT modified for CMP

    # ── Instruction Execution ────────────────────────────────────
    def execute_one(self):
        """Execute one instruction. Returns the PC before execution."""
        if self.halted:
            return None

        old_pc = self.PC
        op = self._fetch()
        self.cycles += 1

        hi2 = (op >> 6) & 3
        mid3 = (op >> 3) & 7
        lo3 = op & 7
        rp = (op >> 4) & 3

        # ── Group 01: MOV / HLT ─────────────────────────────
        if hi2 == 1:
            if op == 0x76:  # HLT
                self.halted = True
            else:  # MOV dst, src
                self._set_reg(mid3, self._get_reg(lo3))

        # ── Group 10: Arithmetic/Logic with register ─────────
        elif hi2 == 2:
            val = self._get_reg(lo3)
            alu_op = mid3
            if alu_op == 0:   self._add(val)           # ADD
            elif alu_op == 1: self._add(val, self.flags['CY'])  # ADC
            elif alu_op == 2: self._sub(val)            # SUB
            elif alu_op == 3: self._sub(val, self.flags['CY'])  # SBB
            elif alu_op == 4: self._ana(val)            # ANA
            elif alu_op == 5: self._xra(val)            # XRA
            elif alu_op == 6: self._ora(val)            # ORA
            elif alu_op == 7: self._cmp(val)            # CMP

        # ── Group 00: Misc ───────────────────────────────────
        elif hi2 == 0:
            if op == 0x00:  # NOP
                pass
            elif lo3 == 1 and (op & 0x08) == 0:  # LXI rp, d16
                d16 = self._fetch16()
                self._set_rp(rp, d16)
            elif lo3 == 1 and (op & 0x08) != 0:  # DAD rp
                hl = self._get_rp(2)
                val = self._get_rp(rp)
                result = hl + val
                self.flags['CY'] = 1 if result > 0xFFFF else 0
                self._set_rp(2, result & 0xFFFF)
            elif op == 0x02:  # STAX B
                self.memory[self._get_rp(0)] = self.reg[self.A]
            elif op == 0x12:  # STAX D
                self.memory[self._get_rp(1)] = self.reg[self.A]
            elif op == 0x0A:  # LDAX B
                self.reg[self.A] = self.memory[self._get_rp(0)]
            elif op == 0x1A:  # LDAX D
                self.reg[self.A] = self.memory[self._get_rp(1)]
            elif op == 0x22:  # SHLD addr
                addr = self._fetch16()
                self.memory[addr] = self.reg[self.L]
                self.memory[(addr + 1) & 0xFFFF] = self.reg[self.H]
            elif op == 0x2A:  # LHLD addr
                addr = self._fetch16()
                self.reg[self.L] = self.memory[addr]
                self.reg[self.H] = self.memory[(addr + 1) & 0xFFFF]
            elif op == 0x32:  # STA addr
                addr = self._fetch16()
                self.memory[addr] = self.reg[self.A]
            elif op == 0x3A:  # LDA addr
                addr = self._fetch16()
                self.reg[self.A] = self.memory[addr]
            elif lo3 == 3 and (op & 0x08) == 0:  # INX rp
                self._set_rp(rp, (self._get_rp(rp) + 1) & 0xFFFF)
            elif lo3 == 3 and (op & 0x08) != 0:  # DCX rp
                self._set_rp(rp, (self._get_rp(rp) - 1) & 0xFFFF)
            elif lo3 == 4:  # INR r
                val = self._get_reg(mid3)
                result = (val + 1) & 0xFF
                self.flags['AC'] = 1 if (val & 0x0F) == 0x0F else 0
                self._set_reg(mid3, result)
                self._update_flags_arith(result, carry=False)
            elif lo3 == 5:  # DCR r
                val = self._get_reg(mid3)
                result = (val - 1) & 0xFF
                self.flags['AC'] = 0 if (val & 0x0F) == 0x00 else 1
                self._set_reg(mid3, result)
                self._update_flags_arith(result, carry=False)
            elif lo3 == 6:  # MVI r, d8
                d8 = self._fetch()
                self._set_reg(mid3, d8)
            elif op == 0x07:  # RLC
                a = self.reg[self.A]
                self.flags['CY'] = (a >> 7) & 1
                self.reg[self.A] = ((a << 1) | self.flags['CY']) & 0xFF
            elif op == 0x0F:  # RRC
                a = self.reg[self.A]
                self.flags['CY'] = a & 1
                self.reg[self.A] = ((a >> 1) | (self.flags['CY'] << 7)) & 0xFF
            elif op == 0x17:  # RAL
                a = self.reg[self.A]
                old_cy = self.flags['CY']
                self.flags['CY'] = (a >> 7) & 1
                self.reg[self.A] = ((a << 1) | old_cy) & 0xFF
            elif op == 0x1F:  # RAR
                a = self.reg[self.A]
                old_cy = self.flags['CY']
                self.flags['CY'] = a & 1
                self.reg[self.A] = ((a >> 1) | (old_cy << 7)) & 0xFF
            elif op == 0x27:  # DAA
                a = self.reg[self.A]
                add_val = 0
                new_cy = self.flags['CY']
                if (a & 0x0F) > 9 or self.flags['AC']:
                    add_val += 0x06
                if ((a >> 4) & 0x0F) > 9 or self.flags['CY'] or \
                   (((a >> 4) & 0x0F) >= 9 and (a & 0x0F) > 9):
                    add_val += 0x60
                    new_cy = 1
                self.flags['AC'] = 1 if ((a & 0x0F) + (add_val & 0x0F)) > 0x0F else 0
                result = a + add_val
                self.reg[self.A] = result & 0xFF
                self.flags['CY'] = new_cy
                r = self.reg[self.A]
                self.flags['S'] = 1 if (r & 0x80) else 0
                self.flags['Z'] = 1 if r == 0 else 0
                self.flags['P'] = self._parity(r)
            elif op == 0x2F:  # CMA
                self.reg[self.A] = (~self.reg[self.A]) & 0xFF
            elif op == 0x37:  # STC
                self.flags['CY'] = 1
            elif op == 0x3F:  # CMC
                self.flags['CY'] = 1 - self.flags['CY']
            elif op == 0x20:  # RIM (simplified)
                pass
            elif op == 0x30:  # SIM (simplified)
                pass

        # ── Group 11: Jumps, Calls, Returns, IO, Immediate ──
        elif hi2 == 3:
            if lo3 == 0:  # Conditional RET
                if self._check_condition(mid3):
                    self.PC = self._pop16()
            elif lo3 == 1:
                if (op & 0x08) == 0:  # POP rp
                    val = self._pop16()
                    if rp == 3:  # POP PSW
                        self._set_psw(val)
                    else:
                        self._set_rp(rp, val)
                else:
                    if op == 0xC9:    # RET
                        self.PC = self._pop16()
                    elif op == 0xD9:  # (undocumented RET)
                        self.PC = self._pop16()
                    elif op == 0xE9:  # PCHL
                        self.PC = self._get_rp(2)
                    elif op == 0xF9:  # SPHL
                        self.SP = self._get_rp(2)
            elif lo3 == 2:  # Conditional JMP
                addr = self._fetch16()
                if self._check_condition(mid3):
                    self.PC = addr
            elif lo3 == 3:
                if op == 0xC3:    # JMP
                    self.PC = self._fetch16()
                elif op == 0xCB:  # (undocumented JMP)
                    self.PC = self._fetch16()
                elif op == 0xD3:  # OUT port
                    port = self._fetch()
                    self.io[port] = self.reg[self.A]
                    if self.output_callback:
                        self.output_callback(port, self.reg[self.A])
                elif op == 0xDB:  # IN port
                    port = self._fetch()
                    if self.input_callback:
                        self.reg[self.A] = self.input_callback(port) & 0xFF
                    else:
                        self.reg[self.A] = self.io[port]
                elif op == 0xE3:  # XTHL
                    lo = self.memory[self.SP]
                    hi = self.memory[(self.SP + 1) & 0xFFFF]
                    self.memory[self.SP] = self.reg[self.L]
                    self.memory[(self.SP + 1) & 0xFFFF] = self.reg[self.H]
                    self.reg[self.L] = lo
                    self.reg[self.H] = hi
                elif op == 0xEB:  # XCHG
                    self.reg[self.D], self.reg[self.H] = self.reg[self.H], self.reg[self.D]
                    self.reg[self.E], self.reg[self.L] = self.reg[self.L], self.reg[self.E]
                elif op == 0xF3:  # DI
                    self.inte = False
                elif op == 0xFB:  # EI
                    self.inte = True
            elif lo3 == 4:  # Conditional CALL
                addr = self._fetch16()
                if self._check_condition(mid3):
                    self._push16(self.PC)
                    self.PC = addr
            elif lo3 == 5:
                if (op & 0x08) == 0:  # PUSH rp
                    if rp == 3:  # PUSH PSW
                        self._push16(self._get_psw())
                    else:
                        self._push16(self._get_rp(rp))
                else:
                    if op == 0xCD:  # CALL
                        addr = self._fetch16()
                        self._push16(self.PC)
                        self.PC = addr
                    elif op == 0xDD:  # (undocumented CALL)
                        addr = self._fetch16()
                        self._push16(self.PC)
                        self.PC = addr
                    elif op == 0xED:  # (undocumented CALL)
                        addr = self._fetch16()
                        self._push16(self.PC)
                        self.PC = addr
                    elif op == 0xFD:  # (undocumented CALL)
                        addr = self._fetch16()
                        self._push16(self.PC)
                        self.PC = addr
            elif lo3 == 6:  # Immediate ALU
                d8 = self._fetch()
                if mid3 == 0:   self._add(d8)            # ADI
                elif mid3 == 1: self._add(d8, self.flags['CY'])  # ACI
                elif mid3 == 2: self._sub(d8)             # SUI
                elif mid3 == 3: self._sub(d8, self.flags['CY'])  # SBI
                elif mid3 == 4: self._ana(d8)             # ANI
                elif mid3 == 5: self._xra(d8)             # XRI
                elif mid3 == 6: self._ora(d8)             # ORI
                elif mid3 == 7: self._cmp(d8)             # CPI
            elif lo3 == 7:  # RST n
                self._push16(self.PC)
                self.PC = mid3 * 8

        return old_pc

    def load_program(self, start_addr, data):
        """Load binary data into memory at given address."""
        for i, b in enumerate(data):
            if start_addr + i < 65536:
                self.memory[start_addr + i] = b & 0xFF


# ═══════════════════════════════════════════════════════════════════
# SECTION 2: Two-Pass Assembler
# ═══════════════════════════════════════════════════════════════════

class Assembler8085:
    """Two-pass assembler for Intel 8085 assembly language."""

    REG_MAP = {'B': 0, 'C': 1, 'D': 2, 'E': 3, 'H': 4, 'L': 5, 'M': 6, 'A': 7}
    RP_MAP = {'B': 0, 'BC': 0, 'D': 1, 'DE': 1, 'H': 2, 'HL': 2, 'SP': 3, 'PSW': 3}

    # Single-byte instructions (no operands)
    SINGLE_BYTE = {
        'NOP': 0x00, 'RLC': 0x07, 'RRC': 0x0F, 'RAL': 0x17, 'RAR': 0x1F,
        'DAA': 0x27, 'CMA': 0x2F, 'STC': 0x37, 'CMC': 0x3F, 'HLT': 0x76,
        'RET': 0xC9, 'PCHL': 0xE9, 'SPHL': 0xF9, 'XCHG': 0xEB, 'XTHL': 0xE3,
        'EI': 0xFB, 'DI': 0xF3, 'RIM': 0x20, 'SIM': 0x30,
        'RNZ': 0xC0, 'RZ': 0xC8, 'RNC': 0xD0, 'RC': 0xD8,
        'RPO': 0xE0, 'RPE': 0xE8, 'RP': 0xF0, 'RM': 0xF8,
    }

    # Instructions with 16-bit address operand
    ADDR16_OPS = {
        'JMP': 0xC3, 'JNZ': 0xC2, 'JZ': 0xCA, 'JNC': 0xD2, 'JC': 0xDA,
        'JPO': 0xE2, 'JPE': 0xEA, 'JP': 0xF2, 'JM': 0xFA,
        'CALL': 0xCD, 'CNZ': 0xC4, 'CZ': 0xCC, 'CNC': 0xD4, 'CC': 0xDC,
        'CPO': 0xE4, 'CPE': 0xEC, 'CP': 0xF4, 'CM': 0xFC,
        'LDA': 0x3A, 'STA': 0x32, 'LHLD': 0x2A, 'SHLD': 0x22,
    }

    # Instructions with 8-bit immediate operand
    IMM8_OPS = {
        'ADI': 0xC6, 'ACI': 0xCE, 'SUI': 0xD6, 'SBI': 0xDE,
        'ANI': 0xE6, 'XRI': 0xEE, 'ORI': 0xF6, 'CPI': 0xFE,
        'IN': 0xDB, 'OUT': 0xD3,
    }

    def __init__(self):
        self.labels = {}
        self.errors = []
        self.listing = []  # (addr, bytes, source_line, line_num)
        self.start_addr = 0
        self.end_addr = 0

    def _parse_number(self, s):
        """Parse a number from string, supporting hex (FFH, 0xFF, 0FFH), decimal, binary (1010B)."""
        s = s.strip()
        if not s:
            raise ValueError("Empty number")

        # Handle expressions with + and -
        if '+' in s[1:] or (s[0] != '-' and '-' in s[1:]):
            # Simple expression: split on last + or -
            for i in range(len(s) - 1, 0, -1):
                if s[i] in '+-':
                    left = self._parse_number(s[:i])
                    right = self._parse_number(s[i + 1:])
                    return left + right if s[i] == '+' else left - right
            raise ValueError(f"Bad expression: {s}")

        # Check if it's a label
        if s.upper() in self.labels:
            return self.labels[s.upper()]

        # Binary: 10101010B
        if s.upper().endswith('B') and all(c in '01' for c in s[:-1]):
            return int(s[:-1], 2)

        # Hex: 0xFF or 0XFF
        if s.upper().startswith('0X'):
            return int(s, 16)

        # Hex: FFH or 0FFH
        if s.upper().endswith('H'):
            hex_str = s[:-1]
            return int(hex_str, 16)

        # Decimal
        if s.lstrip('-').isdigit():
            return int(s)

        # Could be a forward-reference label
        raise ValueError(f"Unknown symbol: {s}")

    def _parse_number_safe(self, s, pass_num):
        """Parse number, allowing forward refs in pass 1."""
        try:
            return self._parse_number(s)
        except ValueError:
            if pass_num == 1:
                return 0  # Placeholder for pass 1
            raise

    def _get_instruction_size(self, mnemonic, operands):
        """Calculate instruction size in bytes."""
        mn = mnemonic.upper()
        if mn in self.SINGLE_BYTE:
            return 1
        if mn in self.ADDR16_OPS:
            return 3
        if mn in self.IMM8_OPS:
            return 2
        if mn == 'MOV':
            return 1
        if mn == 'MVI':
            return 2
        if mn in ('ADD', 'ADC', 'SUB', 'SBB', 'ANA', 'XRA', 'ORA', 'CMP'):
            return 1
        if mn in ('INR', 'DCR'):
            return 1
        if mn == 'LXI':
            return 3
        if mn in ('STAX', 'LDAX'):
            return 1
        if mn in ('PUSH', 'POP'):
            return 1
        if mn in ('INX', 'DCX', 'DAD'):
            return 1
        if mn == 'RST':
            return 1
        if mn == 'DB':
            return len(operands.split(',')) if operands else 1
        if mn == 'DW':
            return len(operands.split(',')) * 2 if operands else 2
        if mn == 'DS':
            try:
                return self._parse_number(operands)
            except:
                return 0
        return 0

    def _assemble_instruction(self, mnemonic, operands, pass_num):
        """Assemble a single instruction, return bytes list."""
        mn = mnemonic.upper()
        ops = operands.strip() if operands else ''
        result = []

        # ── Single byte instructions ──
        if mn in self.SINGLE_BYTE:
            result = [self.SINGLE_BYTE[mn]]

        # ── 16-bit address instructions ──
        elif mn in self.ADDR16_OPS:
            addr = self._parse_number_safe(ops, pass_num) & 0xFFFF
            result = [self.ADDR16_OPS[mn], addr & 0xFF, (addr >> 8) & 0xFF]

        # ── 8-bit immediate instructions ──
        elif mn in self.IMM8_OPS:
            val = self._parse_number_safe(ops, pass_num) & 0xFF
            result = [self.IMM8_OPS[mn], val]

        # ── MOV dst, src ──
        elif mn == 'MOV':
            parts = [p.strip().upper() for p in ops.split(',')]
            if len(parts) != 2:
                raise ValueError("MOV requires two register operands")
            dst = self.REG_MAP.get(parts[0])
            src = self.REG_MAP.get(parts[1])
            if dst is None or src is None:
                raise ValueError(f"Invalid register in MOV: {ops}")
            if dst == 6 and src == 6:
                raise ValueError("MOV M,M is HLT (use HLT instead)")
            result = [0x40 | (dst << 3) | src]

        # ── MVI reg, data ──
        elif mn == 'MVI':
            parts = [p.strip() for p in ops.split(',', 1)]
            if len(parts) != 2:
                raise ValueError("MVI requires register and data")
            reg = self.REG_MAP.get(parts[0].upper())
            if reg is None:
                raise ValueError(f"Invalid register: {parts[0]}")
            val = self._parse_number_safe(parts[1], pass_num) & 0xFF
            result = [0x06 | (reg << 3), val]

        # ── ALU with register ──
        elif mn in ('ADD', 'ADC', 'SUB', 'SBB', 'ANA', 'XRA', 'ORA', 'CMP'):
            alu_map = {'ADD': 0, 'ADC': 1, 'SUB': 2, 'SBB': 3,
                       'ANA': 4, 'XRA': 5, 'ORA': 6, 'CMP': 7}
            reg = self.REG_MAP.get(ops.upper())
            if reg is None:
                raise ValueError(f"Invalid register: {ops}")
            result = [0x80 | (alu_map[mn] << 3) | reg]

        # ── INR / DCR ──
        elif mn in ('INR', 'DCR'):
            reg = self.REG_MAP.get(ops.upper())
            if reg is None:
                raise ValueError(f"Invalid register: {ops}")
            base = 0x04 if mn == 'INR' else 0x05
            result = [base | (reg << 3)]

        # ── LXI rp, d16 ──
        elif mn == 'LXI':
            parts = [p.strip() for p in ops.split(',', 1)]
            if len(parts) != 2:
                raise ValueError("LXI requires register pair and data")
            rp = self.RP_MAP.get(parts[0].upper())
            if rp is None:
                raise ValueError(f"Invalid register pair: {parts[0]}")
            val = self._parse_number_safe(parts[1], pass_num) & 0xFFFF
            result = [0x01 | (rp << 4), val & 0xFF, (val >> 8) & 0xFF]

        # ── STAX / LDAX ──
        elif mn in ('STAX', 'LDAX'):
            rp = self.RP_MAP.get(ops.upper())
            if rp is None or rp > 1:
                raise ValueError(f"STAX/LDAX only with B or D: {ops}")
            base = 0x02 if mn == 'STAX' else 0x0A
            result = [base | (rp << 4)]

        # ── PUSH / POP ──
        elif mn in ('PUSH', 'POP'):
            rp = self.RP_MAP.get(ops.upper())
            if rp is None:
                raise ValueError(f"Invalid register pair: {ops}")
            base = 0xC5 if mn == 'PUSH' else 0xC1
            result = [base | (rp << 4)]

        # ── INX / DCX / DAD ──
        elif mn in ('INX', 'DCX', 'DAD'):
            rp = self.RP_MAP.get(ops.upper())
            if rp is None:
                raise ValueError(f"Invalid register pair: {ops}")
            if mn == 'INX':   result = [0x03 | (rp << 4)]
            elif mn == 'DCX': result = [0x0B | (rp << 4)]
            elif mn == 'DAD': result = [0x09 | (rp << 4)]

        # ── RST n ──
        elif mn == 'RST':
            n = self._parse_number_safe(ops, pass_num)
            if n < 0 or n > 7:
                raise ValueError(f"RST number must be 0-7: {n}")
            result = [0xC7 | (n << 3)]

        # ── DB (Define Byte) ──
        elif mn == 'DB':
            for part in ops.split(','):
                part = part.strip()
                if part.startswith("'") or part.startswith('"'):
                    # String literal
                    s = part[1:-1] if len(part) >= 2 else part[1:]
                    for ch in s:
                        result.append(ord(ch) & 0xFF)
                else:
                    result.append(self._parse_number_safe(part, pass_num) & 0xFF)

        # ── DW (Define Word) ──
        elif mn == 'DW':
            for part in ops.split(','):
                val = self._parse_number_safe(part.strip(), pass_num) & 0xFFFF
                result.extend([val & 0xFF, (val >> 8) & 0xFF])

        # ── DS (Define Storage) ──
        elif mn == 'DS':
            count = self._parse_number_safe(ops, pass_num)
            result = [0] * count

        else:
            raise ValueError(f"Unknown mnemonic: {mn}")

        return result

    def assemble(self, source):
        """Assemble source code. Returns (success, machine_code_dict, errors, listing)."""
        self.labels = {}
        self.errors = []
        self.listing = []
        lines = source.split('\n')

        # ── Pass 1: Collect labels and calculate addresses ──
        addr = 0x0000
        parsed_lines = []

        for line_num, line in enumerate(lines, 1):
            original = line
            # Remove comments
            comment_pos = line.find(';')
            if comment_pos >= 0:
                line = line[:comment_pos]
            line = line.strip()
            if not line:
                parsed_lines.append((line_num, original, None, None, addr))
                continue

            # Check for label
            label = None
            match = re.match(r'^([A-Za-z_]\w*)\s*:\s*(.*)', line)
            if match:
                label = match.group(1).upper()
                line = match.group(2).strip()
                self.labels[label] = addr

            if not line:
                parsed_lines.append((line_num, original, label, None, addr))
                continue

            # Parse mnemonic and operands
            parts = line.split(None, 1)
            mnemonic = parts[0].upper()
            operands = parts[1].strip() if len(parts) > 1 else ''

            # Handle ORG directive
            if mnemonic == 'ORG':
                try:
                    addr = self._parse_number(operands)
                except ValueError as e:
                    self.errors.append(f"Line {line_num}: {e}")
                parsed_lines.append((line_num, original, label, ('ORG', operands), addr))
                continue

            # Handle EQU directive
            if mnemonic == 'EQU':
                if label:
                    try:
                        self.labels[label] = self._parse_number(operands)
                    except ValueError as e:
                        self.errors.append(f"Line {line_num}: {e}")
                parsed_lines.append((line_num, original, label, ('EQU', operands), addr))
                continue

            # Handle END directive
            if mnemonic == 'END':
                parsed_lines.append((line_num, original, label, ('END', operands), addr))
                break

            # Calculate size
            try:
                size = self._get_instruction_size(mnemonic, operands)
            except Exception as e:
                self.errors.append(f"Line {line_num}: {e}")
                size = 0

            parsed_lines.append((line_num, original, label, (mnemonic, operands), addr))
            addr += size

        # ── Pass 2: Generate machine code ──
        machine_code = {}
        self.listing = []
        first_addr = None

        for line_num, original, label, instruction, addr in parsed_lines:
            if instruction is None:
                self.listing.append((addr, [], original.strip(), line_num))
                continue

            mnemonic, operands = instruction

            if mnemonic in ('ORG', 'EQU', 'END'):
                self.listing.append((addr, [], original.strip(), line_num))
                continue

            try:
                code_bytes = self._assemble_instruction(mnemonic, operands, 2)
                for i, b in enumerate(code_bytes):
                    machine_code[addr + i] = b
                if first_addr is None and code_bytes:
                    first_addr = addr
                self.listing.append((addr, code_bytes, original.strip(), line_num))
            except ValueError as e:
                self.errors.append(f"Line {line_num}: {e}")
                self.listing.append((addr, [], f"ERROR: {original.strip()}", line_num))

        if first_addr is not None:
            self.start_addr = first_addr
        if machine_code:
            self.end_addr = max(machine_code.keys())

        return len(self.errors) == 0, machine_code, self.errors, self.listing


# ═══════════════════════════════════════════════════════════════════
# SECTION 3: Disassembler
# ═══════════════════════════════════════════════════════════════════

def disassemble(memory, addr):
    """Disassemble one instruction at addr. Returns (mnemonic_str, num_bytes)."""
    REG_NAMES = ['B', 'C', 'D', 'E', 'H', 'L', 'M', 'A']
    RP_NAMES = ['B', 'D', 'H', 'SP']
    RP_PUSH = ['B', 'D', 'H', 'PSW']

    op = memory[addr]
    hi2 = (op >> 6) & 3
    mid3 = (op >> 3) & 7
    lo3 = op & 7
    rp = (op >> 4) & 3

    def d8():
        return memory[(addr + 1) & 0xFFFF]
    def d16():
        return memory[(addr + 1) & 0xFFFF] | (memory[(addr + 2) & 0xFFFF] << 8)

    # Group 01: MOV / HLT
    if hi2 == 1:
        if op == 0x76:
            return "HLT", 1
        return f"MOV {REG_NAMES[mid3]},{REG_NAMES[lo3]}", 1

    # Group 10: ALU with register
    if hi2 == 2:
        alu_names = ['ADD', 'ADC', 'SUB', 'SBB', 'ANA', 'XRA', 'ORA', 'CMP']
        return f"{alu_names[mid3]} {REG_NAMES[lo3]}", 1

    # Group 00
    if hi2 == 0:
        single = {
            0x00: 'NOP', 0x07: 'RLC', 0x0F: 'RRC', 0x17: 'RAL', 0x1F: 'RAR',
            0x27: 'DAA', 0x2F: 'CMA', 0x37: 'STC', 0x3F: 'CMC',
            0x20: 'RIM', 0x30: 'SIM',
        }
        if op in single:
            return single[op], 1
        if lo3 == 1 and (op & 0x08) == 0:  # LXI
            return f"LXI {RP_NAMES[rp]},{d16():04X}H", 3
        if lo3 == 1 and (op & 0x08) != 0:  # DAD
            return f"DAD {RP_NAMES[rp]}", 1
        if op == 0x02: return "STAX B", 1
        if op == 0x12: return "STAX D", 1
        if op == 0x0A: return "LDAX B", 1
        if op == 0x1A: return "LDAX D", 1
        if op == 0x22: return f"SHLD {d16():04X}H", 3
        if op == 0x2A: return f"LHLD {d16():04X}H", 3
        if op == 0x32: return f"STA {d16():04X}H", 3
        if op == 0x3A: return f"LDA {d16():04X}H", 3
        if lo3 == 3 and (op & 0x08) == 0:
            return f"INX {RP_NAMES[rp]}", 1
        if lo3 == 3 and (op & 0x08) != 0:
            return f"DCX {RP_NAMES[rp]}", 1
        if lo3 == 4: return f"INR {REG_NAMES[mid3]}", 1
        if lo3 == 5: return f"DCR {REG_NAMES[mid3]}", 1
        if lo3 == 6: return f"MVI {REG_NAMES[mid3]},{d8():02X}H", 2

    # Group 11
    if hi2 == 3:
        cond_names = ['NZ', 'Z', 'NC', 'C', 'PO', 'PE', 'P', 'M']

        if lo3 == 0:  # Conditional RET
            return f"R{cond_names[mid3]}", 1
        if lo3 == 1:
            if (op & 0x08) == 0:  # POP
                return f"POP {RP_PUSH[rp]}", 1
            single_11 = {0xC9: 'RET', 0xD9: 'RET*', 0xE9: 'PCHL', 0xF9: 'SPHL'}
            if op in single_11:
                return single_11[op], 1
        if lo3 == 2:  # Conditional JMP
            return f"J{cond_names[mid3]} {d16():04X}H", 3
        if lo3 == 3:
            if op == 0xC3: return f"JMP {d16():04X}H", 3
            if op == 0xCB: return f"JMP* {d16():04X}H", 3
            if op == 0xD3: return f"OUT {d8():02X}H", 2
            if op == 0xDB: return f"IN {d8():02X}H", 2
            if op == 0xE3: return "XTHL", 1
            if op == 0xEB: return "XCHG", 1
            if op == 0xF3: return "DI", 1
            if op == 0xFB: return "EI", 1
        if lo3 == 4:  # Conditional CALL
            return f"C{cond_names[mid3]} {d16():04X}H", 3
        if lo3 == 5:
            if (op & 0x08) == 0:  # PUSH
                return f"PUSH {RP_PUSH[rp]}", 1
            if op == 0xCD: return f"CALL {d16():04X}H", 3
            return f"CALL* {d16():04X}H", 3
        if lo3 == 6:
            imm_names = ['ADI', 'ACI', 'SUI', 'SBI', 'ANI', 'XRI', 'ORI', 'CPI']
            return f"{imm_names[mid3]} {d8():02X}H", 2
        if lo3 == 7:
            return f"RST {mid3}", 1

    return f"DB {op:02X}H", 1


# ═══════════════════════════════════════════════════════════════════
# SECTION 4: Sample Programs
# ═══════════════════════════════════════════════════════════════════

SAMPLE_PROGRAMS = {
    "Add Two Numbers": """; Program: Add Two Numbers
; Adds 25H and 1AH, stores result at 3000H
    ORG 2000H

    MVI A, 25H      ; Load first number
    MVI B, 1AH      ; Load second number
    ADD B            ; A = A + B
    STA 3000H        ; Store result at 3000H
    HLT              ; Stop
""",

    "Multiply (Repeated Add)": """; Program: 8-bit Multiplication by Repeated Addition
; Multiplies values at 2050H and 2051H
; Result (16-bit) stored at 2052H-2053H
    ORG 2000H

    LDA 2050H        ; Load multiplicand
    MOV B, A
    LDA 2051H        ; Load multiplier
    MOV C, A
    MVI A, 00H       ; Clear accumulator
    MVI D, 00H       ; Clear D for carry

LOOP:
    ADD B             ; Add multiplicand
    JNC NOCARRY       ; Jump if no carry
    INR D             ; Increment high byte
NOCARRY:
    DCR C             ; Decrement counter
    JNZ LOOP          ; Repeat until zero

    STA 2052H         ; Store low byte
    MOV A, D
    STA 2053H         ; Store high byte
    HLT

; Initialize data
    ORG 2050H
    DB 05H            ; Multiplicand = 5
    DB 04H            ; Multiplier = 4
""",

    "Fibonacci Series": """; Program: Generate Fibonacci Series
; Generates first N Fibonacci numbers starting at 3000H
    ORG 2000H

    MVI C, 0AH       ; Count = 10 numbers
    MVI A, 00H        ; First number = 0
    MVI B, 01H        ; Second number = 1
    LXI H, 3000H      ; Result storage address

    MOV M, A          ; Store first number
    INX H
    MOV M, B          ; Store second number
    INX H
    DCR C
    DCR C             ; Already stored 2 numbers

NEXT:
    MOV A, B          ; A = previous
    ADD M             ; Oops, need different approach
    ; Actually, let's use a proper method
    HLT

; Restart with corrected logic
    ORG 2000H
    MVI C, 0AH       ; Count = 10 numbers
    LXI H, 3000H     ; Storage address
    MVI A, 00H
    MOV M, A          ; Store F(0) = 0
    INX H
    MVI A, 01H
    MOV M, A          ; Store F(1) = 1
    INX H
    DCR C
    DCR C

    MVI D, 00H        ; D = F(n-2) = 0
    MVI E, 01H        ; E = F(n-1) = 1

FIB:
    MOV A, D
    ADD E              ; A = F(n-2) + F(n-1)
    MOV M, A           ; Store F(n)
    MOV D, E           ; D = old F(n-1)
    MOV E, A           ; E = new F(n)
    INX H
    DCR C
    JNZ FIB
    HLT
""",

    "Bubble Sort": """; Program: Bubble Sort (Ascending)
; Sorts N bytes starting at 2050H
    ORG 2000H

    LDA 2050H         ; Load count N
    DCR A              ; N-1 passes needed
    MOV C, A           ; C = outer loop counter

OUTER:
    MOV D, C           ; D = inner loop counter
    LXI H, 2051H      ; Point to start of array

INNER:
    MOV A, M           ; Load current element
    INX H
    CMP M              ; Compare with next
    JC NOSWAP          ; If current < next, no swap
    JZ NOSWAP          ; If equal, no swap

    ; Swap elements
    MOV B, M           ; B = next element
    MOV M, A           ; Store current in next position
    DCX H
    MOV M, B           ; Store next in current position
    INX H

NOSWAP:
    DCR D
    JNZ INNER
    DCR C
    JNZ OUTER
    HLT

; Test data
    ORG 2050H
    DB 05H             ; Count = 5
    DB 64H, 19H, 2DH, 07H, 48H  ; Array: 100, 25, 45, 7, 72
""",

    "Largest in Array": """; Program: Find Largest Number in Array
; Array at 2050H, count at 2050H, data from 2051H
; Result stored at 2060H
    ORG 2000H

    LDA 2050H          ; Load count
    DCR A               ; Counter = N-1
    MOV C, A
    LXI H, 2051H       ; Point to array
    MOV A, M            ; A = first element (assume largest)

FIND:
    INX H
    CMP M               ; Compare A with next
    JNC SKIP            ; If A >= M[HL], skip
    MOV A, M            ; A = new largest
SKIP:
    DCR C
    JNZ FIND
    STA 2060H           ; Store largest
    HLT

; Test data
    ORG 2050H
    DB 05H              ; Count = 5
    DB 34H, 78H, 12H, 9AH, 56H  ; Array data
""",

    "BCD Addition": """; Program: BCD Addition
; Add two BCD numbers and store result
    ORG 2000H

    MVI A, 29H         ; First BCD number (29)
    MVI B, 48H         ; Second BCD number (48)
    ADD B               ; Binary add
    DAA                 ; Decimal adjust (29+48=77 BCD)
    STA 3000H           ; Store BCD result
    HLT
""",

    "Block Transfer": """; Program: Block Data Transfer
; Transfer N bytes from 2050H to 2060H
    ORG 2000H

    MVI C, 05H         ; Count = 5 bytes
    LXI H, 2050H       ; Source address
    LXI D, 2060H       ; Destination address

XFER:
    MOV A, M            ; Load from source
    STAX D              ; Store to destination
    INX H               ; Next source
    INX D               ; Next destination
    DCR C               ; Decrement counter
    JNZ XFER            ; Repeat until done
    HLT

; Source data
    ORG 2050H
    DB 11H, 22H, 33H, 44H, 55H
""",

    "Complement & Rotate": """; Program: Demonstrate Complement and Rotate
    ORG 2000H

    MVI A, 53H         ; A = 0101 0011
    CMA                ; A = 1010 1100 (complement)
    STA 3000H           ; Store complement

    MVI A, 81H         ; A = 1000 0001
    RLC                 ; Rotate left through carry
    STA 3001H           ; Store result

    MVI A, 81H
    RRC                 ; Rotate right through carry
    STA 3002H           ; Store result

    MVI A, 0B5H        ; A = 1011 0101
    ANI 0FH            ; Mask lower nibble
    STA 3003H           ; Store masked value

    HLT
""",

    "Stack Operations": """; Program: Demonstrate Stack Operations
    ORG 2000H

    LXI SP, 20FFH      ; Initialize stack pointer
    MVI A, 11H
    MVI B, 22H
    MVI C, 33H

    PUSH B              ; Push BC onto stack
    PUSH PSW            ; Push A and flags

    MVI A, 00H          ; Clear A
    MVI B, 00H          ; Clear B
    MVI C, 00H          ; Clear C

    POP PSW             ; Restore A and flags
    POP B               ; Restore BC

    STA 3000H           ; A should be 11H
    MOV A, B
    STA 3001H           ; B should be 22H
    MOV A, C
    STA 3002H           ; C should be 33H
    HLT
""",

    "Subroutine Call": """; Program: Subroutine to Add Array Elements
; Sum of 5 bytes at 2050H, result at 2060H
    ORG 2000H

    LXI SP, 20FFH      ; Initialize stack
    LXI H, 2050H       ; Array address
    MVI C, 05H          ; Count

    CALL SUM            ; Call subroutine
    STA 2060H           ; Store sum
    HLT

; Subroutine: SUM
; Input: HL = array address, C = count
; Output: A = sum
SUM:
    MVI A, 00H          ; Clear accumulator
ADDNXT:
    ADD M                ; Add array element
    INX H                ; Next element
    DCR C                ; Decrement counter
    JNZ ADDNXT
    RET                  ; Return

; Data
    ORG 2050H
    DB 10H, 20H, 30H, 40H, 50H
""",

    "1's and 2's Complement": """; Program: Find 1's and 2's Complement
; Input at 2050H
; 1's complement at 2051H, 2's complement at 2052H
    ORG 2000H

    LDA 2050H           ; Load number
    CMA                  ; 1's complement
    STA 2051H            ; Store 1's complement
    INR A                ; Add 1 for 2's complement
    STA 2052H            ; Store 2's complement
    HLT

; Data
    ORG 2050H
    DB 54H               ; Input number
""",

    "Count Set Bits": """; Program: Count number of 1-bits in a byte
; Input at 2050H, bit count at 2051H
    ORG 2000H

    LDA 2050H            ; Load the byte
    MVI B, 08H           ; 8 bits to check
    MVI C, 00H           ; Bit counter = 0

BITLP:
    RRC                   ; Rotate right, LSB into carry
    JNC ZERO              ; If carry = 0, skip increment
    INR C                 ; Increment bit count
ZERO:
    DCR B                 ; Decrement bit counter
    JNZ BITLP             ; Repeat for all 8 bits

    MOV A, C
    STA 2051H             ; Store count
    HLT

; Data
    ORG 2050H
    DB 0A7H               ; 1010 0111 = 5 set bits
""",

    "I/O Port Demo": """; Program: I/O Port Demonstration
; Reads from port 01H, processes, outputs to port 02H
    ORG 2000H

    IN 01H               ; Read from input port 1
    RLC                   ; Rotate left
    RLC                   ; Rotate left again (shift left 2)
    OUT 02H              ; Output to port 2
    HLT
""",
}


# ═══════════════════════════════════════════════════════════════════
# SECTION 5: GUI Application - Lab Trainer Kit Interface
# ═══════════════════════════════════════════════════════════════════

class SimulatorApp:
    """Intel 8085 Lab Trainer Kit Simulator GUI."""

    # ── Color Scheme (Dark Retro Theme) ──
    BG_DARK = '#0d1117'
    BG_PANEL = '#161b22'
    BG_EDITOR = '#0d1117'
    BG_INPUT = '#1c2333'
    BG_HEADER = '#1f2937'
    FG_TEXT = '#c9d1d9'
    FG_DIM = '#6e7681'
    FG_BRIGHT = '#e6edf3'
    FG_GREEN = '#00ff41'
    FG_AMBER = '#ffb700'
    FG_RED = '#ff4757'
    FG_CYAN = '#00d4ff'
    FG_PURPLE = '#bc8cff'
    FG_ORANGE = '#ff8c42'
    FG_BLUE = '#58a6ff'
    ACCENT_BG = '#21262d'
    BORDER = '#30363d'
    HIGHLIGHT = '#1f6feb'
    SEG_GREEN = '#39ff14'
    BTN_GREEN = '#238636'
    BTN_RED = '#da3633'
    BTN_BLUE = '#1f6feb'
    BTN_AMBER = '#9e6a03'

    def __init__(self, root):
        self.root = root
        self.root.title("Intel 8085 Microprocessor Simulator ─ Lab Trainer Kit")
        self.root.configure(bg=self.BG_DARK)

        # Set minimum size and start maximized
        self.root.minsize(1200, 750)
        try:
            self.root.state('zoomed')
        except tk.TclError:
            self.root.geometry("1400x850")

        # CPU and Assembler
        self.cpu = Intel8085()
        self.asm = Assembler8085()
        self.cpu.output_callback = self._on_output
        self.cpu.input_callback = self._on_input
        self.breakpoints = set()
        self.running = False
        self.run_speed = 100  # ms between steps when running
        self.addr_to_line = {}  # Maps memory address to source line number
        self.line_to_addr = {}  # Maps source line number to memory address
        self.assembled = False
        self.io_log = []

        # Trainer kit mode variables
        self.trainer_addr = 0x2000
        self.trainer_mode = 'ADDR'  # 'ADDR' or 'DATA'

        # ── Fonts ──
        self.mono_font = tkfont.Font(family="Consolas", size=11)
        self.mono_small = tkfont.Font(family="Consolas", size=10)
        self.mono_large = tkfont.Font(family="Consolas", size=14, weight="bold")
        self.seg_font = tkfont.Font(family="Consolas", size=28, weight="bold")
        self.title_font = tkfont.Font(family="Segoe UI", size=11, weight="bold")
        self.label_font = tkfont.Font(family="Segoe UI", size=9)
        self.btn_font = tkfont.Font(family="Segoe UI", size=9, weight="bold")

        # ── Build GUI ──
        self._setup_styles()
        self._build_menu()
        self._build_title_bar()
        self._build_main_layout()
        self._build_status_bar()

        # Load default program
        self._load_sample("Add Two Numbers")

        # Initial display update
        self._update_all_displays()

        # Key bindings
        self.root.bind('<F5>', lambda e: self._run_program())
        self.root.bind('<F6>', lambda e: self._step_program())
        self.root.bind('<F7>', lambda e: self._stop_program())
        self.root.bind('<F8>', lambda e: self._assemble())
        self.root.bind('<F9>', lambda e: self._reset_cpu())

    def _setup_styles(self):
        style = ttk.Style()
        style.theme_use('clam')

        style.configure('.', background=self.BG_DARK, foreground=self.FG_TEXT)
        style.configure('TFrame', background=self.BG_DARK)
        style.configure('TLabel', background=self.BG_DARK, foreground=self.FG_TEXT,
                        font=self.label_font)
        style.configure('TLabelframe', background=self.BG_PANEL, foreground=self.FG_CYAN,
                        borderwidth=2, relief='groove')
        style.configure('TLabelframe.Label', background=self.BG_DARK, foreground=self.FG_CYAN,
                        font=self.title_font)
        style.configure('TNotebook', background=self.BG_DARK, borderwidth=0)
        style.configure('TNotebook.Tab', background=self.ACCENT_BG, foreground=self.FG_TEXT,
                        padding=[12, 4], font=self.btn_font)
        style.map('TNotebook.Tab',
                  background=[('selected', self.HIGHLIGHT)],
                  foreground=[('selected', '#ffffff')])
        style.configure('TButton', background=self.ACCENT_BG, foreground=self.FG_TEXT,
                        borderwidth=1, focuscolor='none', font=self.btn_font, padding=[8, 4])
        style.map('TButton',
                  background=[('active', self.HIGHLIGHT), ('pressed', self.BTN_BLUE)],
                  foreground=[('active', '#ffffff')])
        style.configure('Green.TButton', background=self.BTN_GREEN, foreground='#ffffff')
        style.map('Green.TButton', background=[('active', '#2ea043')])
        style.configure('Red.TButton', background=self.BTN_RED, foreground='#ffffff')
        style.map('Red.TButton', background=[('active', '#f85149')])
        style.configure('Amber.TButton', background=self.BTN_AMBER, foreground='#ffffff')
        style.map('Amber.TButton', background=[('active', '#bb8009')])
        style.configure('Blue.TButton', background=self.BTN_BLUE, foreground='#ffffff')
        style.map('Blue.TButton', background=[('active', '#388bfd')])
        style.configure('TScale', background=self.BG_DARK, troughcolor=self.ACCENT_BG)

    def _build_menu(self):
        menubar = tk.Menu(self.root, bg=self.BG_PANEL, fg=self.FG_TEXT,
                         activebackground=self.HIGHLIGHT, activeforeground='#fff',
                         borderwidth=0, font=self.label_font)

        # File menu
        file_menu = tk.Menu(menubar, tearoff=0, bg=self.BG_PANEL, fg=self.FG_TEXT,
                           activebackground=self.HIGHLIGHT, activeforeground='#fff',
                           font=self.label_font)
        file_menu.add_command(label="New", command=self._new_file, accelerator="Ctrl+N")
        file_menu.add_command(label="Open...", command=self._open_file, accelerator="Ctrl+O")
        file_menu.add_command(label="Save...", command=self._save_file, accelerator="Ctrl+S")
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        # Sample programs menu
        samples_menu = tk.Menu(menubar, tearoff=0, bg=self.BG_PANEL, fg=self.FG_TEXT,
                              activebackground=self.HIGHLIGHT, activeforeground='#fff',
                              font=self.label_font)
        for name in SAMPLE_PROGRAMS:
            samples_menu.add_command(label=name,
                                    command=lambda n=name: self._load_sample(n))
        menubar.add_cascade(label="Sample Programs", menu=samples_menu)

        # Execute menu
        exec_menu = tk.Menu(menubar, tearoff=0, bg=self.BG_PANEL, fg=self.FG_TEXT,
                           activebackground=self.HIGHLIGHT, activeforeground='#fff',
                           font=self.label_font)
        exec_menu.add_command(label="Assemble", command=self._assemble, accelerator="F8")
        exec_menu.add_command(label="Run", command=self._run_program, accelerator="F5")
        exec_menu.add_command(label="Step", command=self._step_program, accelerator="F6")
        exec_menu.add_command(label="Stop", command=self._stop_program, accelerator="F7")
        exec_menu.add_command(label="Reset CPU", command=self._reset_cpu, accelerator="F9")
        menubar.add_cascade(label="Execute", menu=exec_menu)

        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0, bg=self.BG_PANEL, fg=self.FG_TEXT,
                           activebackground=self.HIGHLIGHT, activeforeground='#fff',
                           font=self.label_font)
        help_menu.add_command(label="Instruction Set Reference", command=self._show_help)
        help_menu.add_command(label="About", command=self._show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.root.config(menu=menubar)

        # Keyboard shortcuts
        self.root.bind('<Control-n>', lambda e: self._new_file())
        self.root.bind('<Control-o>', lambda e: self._open_file())
        self.root.bind('<Control-s>', lambda e: self._save_file())

    def _build_title_bar(self):
        title_frame = tk.Frame(self.root, bg=self.BG_HEADER, height=48)
        title_frame.pack(fill='x', side='top')
        title_frame.pack_propagate(False)

        # Left: Logo and title
        logo_text = "█▀▀ █▀█ █▀█ █▀"
        tk.Label(title_frame, text="⬡", font=("Segoe UI", 18), bg=self.BG_HEADER,
                fg=self.FG_CYAN).pack(side='left', padx=(12, 4))
        tk.Label(title_frame, text="INTEL 8085", font=("Segoe UI", 14, "bold"),
                bg=self.BG_HEADER, fg=self.FG_BRIGHT).pack(side='left')
        tk.Label(title_frame, text="  MICROPROCESSOR SIMULATOR", font=("Segoe UI", 10),
                bg=self.BG_HEADER, fg=self.FG_DIM).pack(side='left')
        tk.Label(title_frame, text="  ─  Lab Trainer Kit Edition", font=("Segoe UI", 9, "italic"),
                bg=self.BG_HEADER, fg=self.FG_AMBER).pack(side='left')

        # Right: Status indicators
        self.status_led = tk.Label(title_frame, text="● READY", font=self.btn_font,
                                  bg=self.BG_HEADER, fg=self.FG_GREEN)
        self.status_led.pack(side='right', padx=12)

    def _build_main_layout(self):
        """Build the main three-panel layout."""
        main = tk.Frame(self.root, bg=self.BG_DARK)
        main.pack(fill='both', expand=True, padx=6, pady=(2, 0))

        # Configure grid: 3 columns
        main.columnconfigure(0, weight=4, minsize=350)  # Editor
        main.columnconfigure(1, weight=3, minsize=300)  # Registers + Memory
        main.columnconfigure(2, weight=3, minsize=300)  # Trainer Kit + IO

        main.rowconfigure(0, weight=1)

        # ── LEFT: Code Editor + Listing ──
        left_frame = tk.Frame(main, bg=self.BG_DARK)
        left_frame.grid(row=0, column=0, sticky='nsew', padx=(0, 3))

        self._build_editor_panel(left_frame)

        # ── CENTER: Registers + Memory Viewer ──
        center_frame = tk.Frame(main, bg=self.BG_DARK)
        center_frame.grid(row=0, column=1, sticky='nsew', padx=3)

        self._build_register_panel(center_frame)
        self._build_memory_panel(center_frame)

        # ── RIGHT: Trainer Kit + IO ──
        right_frame = tk.Frame(main, bg=self.BG_DARK)
        right_frame.grid(row=0, column=2, sticky='nsew', padx=(3, 0))

        self._build_trainer_panel(right_frame)
        self._build_io_panel(right_frame)

    def _build_editor_panel(self, parent):
        """Build the assembly code editor and listing panel."""
        # Notebook for Editor and Listing tabs
        notebook = ttk.Notebook(parent)
        notebook.pack(fill='both', expand=True)

        # ── Tab 1: Assembly Editor ──
        editor_tab = tk.Frame(notebook, bg=self.BG_DARK)
        notebook.add(editor_tab, text="  ✎ Assembly Editor  ")

        # Toolbar
        toolbar = tk.Frame(editor_tab, bg=self.ACCENT_BG, height=36)
        toolbar.pack(fill='x', pady=(0, 2))
        toolbar.pack_propagate(False)

        ttk.Button(toolbar, text="▶ Assemble (F8)", command=self._assemble,
                  style='Green.TButton').pack(side='left', padx=4, pady=4)
        ttk.Button(toolbar, text="⏵ Run (F5)", command=self._run_program,
                  style='Blue.TButton').pack(side='left', padx=2, pady=4)
        ttk.Button(toolbar, text="⏭ Step (F6)", command=self._step_program,
                  style='Amber.TButton').pack(side='left', padx=2, pady=4)
        ttk.Button(toolbar, text="⏹ Stop (F7)", command=self._stop_program,
                  style='Red.TButton').pack(side='left', padx=2, pady=4)
        ttk.Button(toolbar, text="↺ Reset (F9)", command=self._reset_cpu).pack(
            side='left', padx=2, pady=4)

        # Speed control
        tk.Label(toolbar, text="Speed:", bg=self.ACCENT_BG, fg=self.FG_DIM,
                font=self.label_font).pack(side='right', padx=(4, 2))
        self.speed_var = tk.IntVar(value=50)
        speed_scale = tk.Scale(toolbar, from_=1, to=200, orient='horizontal',
                              variable=self.speed_var, bg=self.ACCENT_BG, fg=self.FG_TEXT,
                              troughcolor=self.BG_DARK, highlightthickness=0,
                              sliderrelief='flat', length=100, showvalue=False,
                              command=self._on_speed_change)
        speed_scale.pack(side='right', padx=4, pady=4)
        self.speed_label = tk.Label(toolbar, text="50ms", bg=self.ACCENT_BG,
                                   fg=self.FG_AMBER, font=self.label_font)
        self.speed_label.pack(side='right')

        # Editor with line numbers
        editor_container = tk.Frame(editor_tab, bg=self.BG_DARK)
        editor_container.pack(fill='both', expand=True)

        # Line numbers
        self.line_numbers = tk.Text(editor_container, width=4, padx=4, pady=8,
                                   bg=self.ACCENT_BG, fg=self.FG_DIM,
                                   font=self.mono_font, borderwidth=0, state='disabled',
                                   selectbackground=self.ACCENT_BG, cursor='arrow',
                                   highlightthickness=0, takefocus=0)
        self.line_numbers.pack(side='left', fill='y')

        # Code editor
        self.editor = tk.Text(editor_container, wrap='none', undo=True,
                             bg=self.BG_EDITOR, fg=self.FG_TEXT, insertbackground=self.FG_CYAN,
                             font=self.mono_font, borderwidth=0, padx=8, pady=8,
                             selectbackground=self.HIGHLIGHT, selectforeground='#ffffff',
                             highlightthickness=1, highlightcolor=self.BORDER,
                             highlightbackground=self.BORDER, tabs='4c')
        self.editor.pack(side='left', fill='both', expand=True)

        # Scrollbar
        scrollbar = tk.Scrollbar(editor_container, command=self._sync_scroll,
                                bg=self.ACCENT_BG, troughcolor=self.BG_DARK,
                                activebackground=self.HIGHLIGHT, highlightthickness=0)
        scrollbar.pack(side='right', fill='y')
        self.editor.configure(yscrollcommand=scrollbar.set)

        # Editor tags for syntax highlighting
        self.editor.tag_configure('keyword', foreground=self.FG_CYAN)
        self.editor.tag_configure('register', foreground=self.FG_AMBER)
        self.editor.tag_configure('number', foreground=self.FG_PURPLE)
        self.editor.tag_configure('comment', foreground=self.FG_DIM, font=
                                 tkfont.Font(family="Consolas", size=11, slant="italic"))
        self.editor.tag_configure('label_def', foreground=self.FG_GREEN)
        self.editor.tag_configure('directive', foreground=self.FG_RED)
        self.editor.tag_configure('current_line', background='#1c3a5f')
        self.editor.tag_configure('breakpoint', background='#5c1a1a')

        self.editor.bind('<KeyRelease>', self._on_editor_change)
        self.editor.bind('<ButtonRelease-1>', self._on_editor_change)
        self.editor.bind('<MouseWheel>', lambda e: self._on_editor_change())

        # ── Tab 2: Assembled Listing ──
        listing_tab = tk.Frame(notebook, bg=self.BG_DARK)
        notebook.add(listing_tab, text="  ☰ Assembled Listing  ")

        self.listing_text = tk.Text(listing_tab, wrap='none', state='disabled',
                                   bg=self.BG_EDITOR, fg=self.FG_TEXT, font=self.mono_font,
                                   borderwidth=0, padx=8, pady=8,
                                   selectbackground=self.HIGHLIGHT,
                                   highlightthickness=1, highlightcolor=self.BORDER,
                                   highlightbackground=self.BORDER)
        listing_scroll = tk.Scrollbar(listing_tab, command=self.listing_text.yview,
                                     bg=self.ACCENT_BG, troughcolor=self.BG_DARK)
        self.listing_text.configure(yscrollcommand=listing_scroll.set)
        listing_scroll.pack(side='right', fill='y')
        self.listing_text.pack(fill='both', expand=True)

        self.listing_text.tag_configure('addr', foreground=self.FG_ORANGE)
        self.listing_text.tag_configure('hex', foreground=self.FG_CYAN)
        self.listing_text.tag_configure('mnemonic', foreground=self.FG_TEXT)
        self.listing_text.tag_configure('error', foreground=self.FG_RED)
        self.listing_text.tag_configure('current', background='#1c3a5f')

        # ── Tab 3: Errors / Console ──
        console_tab = tk.Frame(notebook, bg=self.BG_DARK)
        notebook.add(console_tab, text="  ⚠ Console  ")

        self.console_text = tk.Text(console_tab, wrap='word', state='disabled',
                                   bg=self.BG_EDITOR, fg=self.FG_TEXT, font=self.mono_small,
                                   borderwidth=0, padx=8, pady=8,
                                   selectbackground=self.HIGHLIGHT,
                                   highlightthickness=1, highlightcolor=self.BORDER,
                                   highlightbackground=self.BORDER)
        console_scroll = tk.Scrollbar(console_tab, command=self.console_text.yview,
                                     bg=self.ACCENT_BG, troughcolor=self.BG_DARK)
        self.console_text.configure(yscrollcommand=console_scroll.set)
        console_scroll.pack(side='right', fill='y')
        self.console_text.pack(fill='both', expand=True)

        self.console_text.tag_configure('error', foreground=self.FG_RED)
        self.console_text.tag_configure('success', foreground=self.FG_GREEN)
        self.console_text.tag_configure('info', foreground=self.FG_CYAN)
        self.console_text.tag_configure('warning', foreground=self.FG_AMBER)

    def _build_register_panel(self, parent):
        """Build the register and flag display."""
        reg_frame = tk.LabelFrame(parent, text=" ▣ REGISTERS & FLAGS ",
                                 bg=self.BG_PANEL, fg=self.FG_CYAN,
                                 font=self.title_font, borderwidth=2, relief='groove',
                                 labelanchor='n', padx=8, pady=6)
        reg_frame.pack(fill='x', pady=(0, 4))

        # Register display grid
        reg_grid = tk.Frame(reg_frame, bg=self.BG_PANEL)
        reg_grid.pack(fill='x')

        self.reg_labels = {}
        reg_info = [
            ('A', 0, 0), ('B', 0, 2), ('C', 0, 4),
            ('D', 1, 0), ('E', 1, 2), ('H', 1, 4), ('L', 1, 6),
        ]

        for name, row, col in reg_info:
            tk.Label(reg_grid, text=f"{name}:", bg=self.BG_PANEL, fg=self.FG_DIM,
                    font=self.mono_font).grid(row=row, column=col, sticky='e', padx=(8, 2), pady=2)
            lbl = tk.Label(reg_grid, text="00", bg=self.BG_INPUT, fg=self.SEG_GREEN,
                          font=self.mono_large, width=3, anchor='center', relief='sunken',
                          borderwidth=1)
            lbl.grid(row=row, column=col + 1, sticky='w', padx=(0, 8), pady=2)
            self.reg_labels[name] = lbl

        # 16-bit registers on a new row
        r16_frame = tk.Frame(reg_frame, bg=self.BG_PANEL)
        r16_frame.pack(fill='x', pady=(4, 0))

        for name in ['SP', 'PC']:
            f = tk.Frame(r16_frame, bg=self.BG_PANEL)
            f.pack(side='left', expand=True, padx=8)
            tk.Label(f, text=f"{name}:", bg=self.BG_PANEL, fg=self.FG_DIM,
                    font=self.mono_font).pack(side='left', padx=(0, 4))
            lbl = tk.Label(f, text="0000", bg=self.BG_INPUT, fg=self.FG_AMBER,
                          font=self.mono_large, width=5, anchor='center', relief='sunken',
                          borderwidth=1)
            lbl.pack(side='left')
            self.reg_labels[name] = lbl

        # ── Flags ──
        flags_frame = tk.Frame(reg_frame, bg=self.BG_PANEL)
        flags_frame.pack(fill='x', pady=(8, 2))

        tk.Label(flags_frame, text="FLAGS:", bg=self.BG_PANEL, fg=self.FG_DIM,
                font=self.label_font).pack(side='left', padx=(8, 4))

        self.flag_labels = {}
        for flag_name in ['S', 'Z', 'AC', 'P', 'CY']:
            f = tk.Frame(flags_frame, bg=self.BG_PANEL)
            f.pack(side='left', padx=6)
            tk.Label(f, text=flag_name, bg=self.BG_PANEL, fg=self.FG_DIM,
                    font=self.label_font).pack()
            lbl = tk.Label(f, text="0", bg=self.BG_INPUT, fg=self.FG_RED,
                          font=self.mono_large, width=2, anchor='center', relief='sunken',
                          borderwidth=1)
            lbl.pack()
            self.flag_labels[flag_name] = lbl

        # Cycle counter
        cycle_frame = tk.Frame(reg_frame, bg=self.BG_PANEL)
        cycle_frame.pack(fill='x', pady=(4, 0))
        tk.Label(cycle_frame, text="Cycles:", bg=self.BG_PANEL, fg=self.FG_DIM,
                font=self.label_font).pack(side='left', padx=(8, 4))
        self.cycle_label = tk.Label(cycle_frame, text="0", bg=self.BG_PANEL,
                                   fg=self.FG_PURPLE, font=self.mono_font)
        self.cycle_label.pack(side='left')

        # Halted indicator
        self.halt_label = tk.Label(cycle_frame, text="", bg=self.BG_PANEL,
                                  fg=self.FG_RED, font=self.btn_font)
        self.halt_label.pack(side='right', padx=8)

    def _build_memory_panel(self, parent):
        """Build the memory viewer/editor."""
        mem_frame = tk.LabelFrame(parent, text=" ▦ MEMORY VIEWER ",
                                 bg=self.BG_PANEL, fg=self.FG_CYAN,
                                 font=self.title_font, borderwidth=2, relief='groove',
                                 labelanchor='n', padx=8, pady=6)
        mem_frame.pack(fill='both', expand=True, pady=(0, 4))

        # Address navigation
        nav_frame = tk.Frame(mem_frame, bg=self.BG_PANEL)
        nav_frame.pack(fill='x', pady=(0, 4))

        tk.Label(nav_frame, text="Address:", bg=self.BG_PANEL, fg=self.FG_DIM,
                font=self.label_font).pack(side='left')
        self.mem_addr_var = tk.StringVar(value="2000")
        addr_entry = tk.Entry(nav_frame, textvariable=self.mem_addr_var, width=6,
                             bg=self.BG_INPUT, fg=self.FG_AMBER, font=self.mono_font,
                             insertbackground=self.FG_CYAN, borderwidth=1, relief='sunken',
                             highlightthickness=1, highlightcolor=self.HIGHLIGHT,
                             highlightbackground=self.BORDER)
        addr_entry.pack(side='left', padx=4)
        addr_entry.bind('<Return>', lambda e: self._update_memory_view())

        ttk.Button(nav_frame, text="Go", command=self._update_memory_view).pack(
            side='left', padx=2)
        ttk.Button(nav_frame, text="◄", command=lambda: self._mem_page(-1)).pack(
            side='left', padx=1)
        ttk.Button(nav_frame, text="►", command=lambda: self._mem_page(1)).pack(
            side='left', padx=1)

        # Memory display (hex dump style)
        self.mem_text = tk.Text(mem_frame, wrap='none', state='disabled', height=14,
                               bg=self.BG_EDITOR, fg=self.FG_TEXT, font=self.mono_small,
                               borderwidth=0, padx=4, pady=4,
                               selectbackground=self.HIGHLIGHT,
                               highlightthickness=1, highlightcolor=self.BORDER,
                               highlightbackground=self.BORDER)
        mem_scroll = tk.Scrollbar(mem_frame, command=self.mem_text.yview,
                                 bg=self.ACCENT_BG, troughcolor=self.BG_DARK)
        self.mem_text.configure(yscrollcommand=mem_scroll.set)
        mem_scroll.pack(side='right', fill='y')
        self.mem_text.pack(fill='both', expand=True)

        self.mem_text.tag_configure('addr', foreground=self.FG_ORANGE)
        self.mem_text.tag_configure('nonzero', foreground=self.FG_GREEN)
        self.mem_text.tag_configure('zero', foreground=self.FG_DIM)
        self.mem_text.tag_configure('ascii', foreground=self.FG_PURPLE)
        self.mem_text.tag_configure('pc_byte', background='#1c3a5f', foreground=self.FG_CYAN)

        # Memory edit
        edit_frame = tk.Frame(mem_frame, bg=self.BG_PANEL)
        edit_frame.pack(fill='x', pady=(4, 0))

        tk.Label(edit_frame, text="Edit:", bg=self.BG_PANEL, fg=self.FG_DIM,
                font=self.label_font).pack(side='left')
        tk.Label(edit_frame, text="Addr:", bg=self.BG_PANEL, fg=self.FG_DIM,
                font=self.label_font).pack(side='left', padx=(4, 2))
        self.edit_addr_var = tk.StringVar(value="2000")
        tk.Entry(edit_frame, textvariable=self.edit_addr_var, width=5,
                bg=self.BG_INPUT, fg=self.FG_AMBER, font=self.mono_small,
                insertbackground=self.FG_CYAN, borderwidth=1, relief='sunken',
                highlightthickness=0).pack(side='left', padx=2)
        tk.Label(edit_frame, text="Data:", bg=self.BG_PANEL, fg=self.FG_DIM,
                font=self.label_font).pack(side='left', padx=(4, 2))
        self.edit_data_var = tk.StringVar()
        tk.Entry(edit_frame, textvariable=self.edit_data_var, width=3,
                bg=self.BG_INPUT, fg=self.FG_GREEN, font=self.mono_small,
                insertbackground=self.FG_CYAN, borderwidth=1, relief='sunken',
                highlightthickness=0).pack(side='left', padx=2)
        ttk.Button(edit_frame, text="Store", command=self._store_memory).pack(
            side='left', padx=4)
        ttk.Button(edit_frame, text="Store Next", command=self._store_next).pack(
            side='left', padx=2)

    def _build_trainer_panel(self, parent):
        """Build the trainer kit hex keypad and 7-segment display."""
        trainer_frame = tk.LabelFrame(parent, text=" ⌨ TRAINER KIT KEYPAD ",
                                     bg=self.BG_PANEL, fg=self.FG_CYAN,
                                     font=self.title_font, borderwidth=2, relief='groove',
                                     labelanchor='n', padx=8, pady=6)
        trainer_frame.pack(fill='x', pady=(0, 4))

        # Seven-segment style display
        display_frame = tk.Frame(trainer_frame, bg='#000000', relief='sunken',
                                borderwidth=2, padx=8, pady=6)
        display_frame.pack(fill='x', pady=(0, 8))

        # Address display
        addr_display_frame = tk.Frame(display_frame, bg='#000000')
        addr_display_frame.pack(fill='x')

        tk.Label(addr_display_frame, text="ADDR", bg='#000000', fg='#444444',
                font=self.label_font).pack(side='left')
        self.seg_addr = tk.Label(addr_display_frame, text="2000", bg='#000000',
                                fg=self.SEG_GREEN, font=self.seg_font, anchor='e')
        self.seg_addr.pack(side='left', padx=(8, 16))

        tk.Label(addr_display_frame, text="DATA", bg='#000000', fg='#444444',
                font=self.label_font).pack(side='left')
        self.seg_data = tk.Label(addr_display_frame, text="00", bg='#000000',
                                fg=self.SEG_GREEN, font=self.seg_font, anchor='e')
        self.seg_data.pack(side='left', padx=(8, 0))

        # Mode indicator
        self.seg_mode = tk.Label(display_frame, text="▸ ADDRESS MODE", bg='#000000',
                                fg=self.FG_AMBER, font=self.label_font)
        self.seg_mode.pack(anchor='w', pady=(2, 0))

        # Hex keypad (4x4 grid + function keys)
        keypad_frame = tk.Frame(trainer_frame, bg=self.BG_PANEL)
        keypad_frame.pack(fill='x')

        hex_keys = [
            ['C', 'D', 'E', 'F'],
            ['8', '9', 'A', 'B'],
            ['4', '5', '6', '7'],
            ['0', '1', '2', '3'],
        ]

        for r, row in enumerate(hex_keys):
            for c, key in enumerate(row):
                btn = tk.Button(keypad_frame, text=key, width=4, height=1,
                               bg=self.ACCENT_BG, fg=self.FG_BRIGHT,
                               activebackground=self.HIGHLIGHT, activeforeground='#fff',
                               font=self.mono_large, relief='raised', borderwidth=2,
                               command=lambda k=key: self._hex_key_press(k))
                btn.grid(row=r, column=c, padx=2, pady=2, sticky='nsew')
                keypad_frame.columnconfigure(c, weight=1)

        # Function keys row
        func_frame = tk.Frame(trainer_frame, bg=self.BG_PANEL)
        func_frame.pack(fill='x', pady=(6, 0))

        func_buttons = [
            ("EXAM", self._trainer_examine, self.BTN_BLUE),
            ("NEXT", self._trainer_next, self.ACCENT_BG),
            ("PREV", self._trainer_prev, self.ACCENT_BG),
            ("STORE", self._trainer_store, self.BTN_GREEN),
            ("EXEC", self._trainer_exec, self.BTN_AMBER),
            ("RESET", self._trainer_reset, self.BTN_RED),
        ]

        for text, cmd, color in func_buttons:
            btn = tk.Button(func_frame, text=text, bg=color, fg='#ffffff',
                           activebackground=self.HIGHLIGHT, activeforeground='#fff',
                           font=self.btn_font, relief='raised', borderwidth=2,
                           command=cmd, padx=4, pady=2)
            btn.pack(side='left', expand=True, fill='x', padx=1)

    def _build_io_panel(self, parent):
        """Build the I/O ports display."""
        io_frame = tk.LabelFrame(parent, text=" ⇄ I/O PORTS & OUTPUT ",
                                bg=self.BG_PANEL, fg=self.FG_CYAN,
                                font=self.title_font, borderwidth=2, relief='groove',
                                labelanchor='n', padx=8, pady=6)
        io_frame.pack(fill='both', expand=True)

        # I/O port editor
        port_edit = tk.Frame(io_frame, bg=self.BG_PANEL)
        port_edit.pack(fill='x', pady=(0, 4))

        tk.Label(port_edit, text="Set Port:", bg=self.BG_PANEL, fg=self.FG_DIM,
                font=self.label_font).pack(side='left')
        self.port_num_var = tk.StringVar(value="01")
        tk.Entry(port_edit, textvariable=self.port_num_var, width=3,
                bg=self.BG_INPUT, fg=self.FG_AMBER, font=self.mono_small,
                insertbackground=self.FG_CYAN, borderwidth=1,
                highlightthickness=0).pack(side='left', padx=2)
        tk.Label(port_edit, text="Value:", bg=self.BG_PANEL, fg=self.FG_DIM,
                font=self.label_font).pack(side='left', padx=(4, 2))
        self.port_val_var = tk.StringVar(value="00")
        tk.Entry(port_edit, textvariable=self.port_val_var, width=3,
                bg=self.BG_INPUT, fg=self.FG_GREEN, font=self.mono_small,
                insertbackground=self.FG_CYAN, borderwidth=1,
                highlightthickness=0).pack(side='left', padx=2)
        ttk.Button(port_edit, text="Set", command=self._set_io_port).pack(
            side='left', padx=4)

        # I/O log display
        self.io_text = tk.Text(io_frame, wrap='word', state='disabled', height=10,
                              bg=self.BG_EDITOR, fg=self.FG_TEXT, font=self.mono_small,
                              borderwidth=0, padx=4, pady=4,
                              selectbackground=self.HIGHLIGHT,
                              highlightthickness=1, highlightcolor=self.BORDER,
                              highlightbackground=self.BORDER)
        io_scroll = tk.Scrollbar(io_frame, command=self.io_text.yview,
                                bg=self.ACCENT_BG, troughcolor=self.BG_DARK)
        self.io_text.configure(yscrollcommand=io_scroll.set)
        io_scroll.pack(side='right', fill='y')
        self.io_text.pack(fill='both', expand=True)

        self.io_text.tag_configure('output', foreground=self.FG_GREEN)
        self.io_text.tag_configure('input', foreground=self.FG_CYAN)
        self.io_text.tag_configure('info', foreground=self.FG_DIM)

    def _build_status_bar(self):
        """Build the bottom status bar."""
        status = tk.Frame(self.root, bg=self.ACCENT_BG, height=26)
        status.pack(fill='x', side='bottom')
        status.pack_propagate(False)

        self.status_text = tk.Label(status, text="Ready ─ Load a program and press F8 to assemble",
                                   bg=self.ACCENT_BG, fg=self.FG_DIM, font=self.label_font,
                                   anchor='w')
        self.status_text.pack(side='left', padx=8, fill='x', expand=True)

        # Current instruction display
        self.instr_label = tk.Label(status, text="", bg=self.ACCENT_BG,
                                   fg=self.FG_CYAN, font=self.mono_small, anchor='e')
        self.instr_label.pack(side='right', padx=8)

    # ═══════════════════════════════════════════════════════════
    # Editor Operations
    # ═══════════════════════════════════════════════════════════

    def _sync_scroll(self, *args):
        self.editor.yview(*args)
        self.line_numbers.yview(*args)

    def _on_editor_change(self, event=None):
        self._update_line_numbers()
        self._syntax_highlight()

    def _update_line_numbers(self):
        self.line_numbers.configure(state='normal')
        self.line_numbers.delete('1.0', 'end')
        line_count = int(self.editor.index('end-1c').split('.')[0])
        line_nums = '\n'.join(str(i) for i in range(1, line_count + 1))
        self.line_numbers.insert('1.0', line_nums)
        self.line_numbers.configure(state='disabled')

        # Sync scroll position
        self.line_numbers.yview_moveto(self.editor.yview()[0])

    def _syntax_highlight(self):
        """Apply syntax highlighting to the editor."""
        for tag in ('keyword', 'register', 'number', 'comment', 'label_def', 'directive'):
            self.editor.tag_remove(tag, '1.0', 'end')

        text = self.editor.get('1.0', 'end')
        lines = text.split('\n')

        KEYWORDS = {
            'MOV', 'MVI', 'LDA', 'STA', 'LHLD', 'SHLD', 'LXI', 'LDAX', 'STAX', 'XCHG',
            'ADD', 'ADC', 'SUB', 'SBB', 'INR', 'DCR', 'INX', 'DCX', 'DAD', 'DAA',
            'ADI', 'ACI', 'SUI', 'SBI',
            'ANA', 'XRA', 'ORA', 'CMP', 'ANI', 'XRI', 'ORI', 'CPI',
            'RLC', 'RRC', 'RAL', 'RAR', 'CMA', 'CMC', 'STC',
            'JMP', 'JC', 'JNC', 'JZ', 'JNZ', 'JP', 'JM', 'JPE', 'JPO',
            'CALL', 'CC', 'CNC', 'CZ', 'CNZ', 'CP', 'CM', 'CPE', 'CPO',
            'RET', 'RC', 'RNC', 'RZ', 'RNZ', 'RP', 'RM', 'RPE', 'RPO',
            'PUSH', 'POP', 'XTHL', 'SPHL', 'PCHL',
            'IN', 'OUT', 'HLT', 'NOP', 'EI', 'DI', 'RST', 'RIM', 'SIM',
        }
        REGISTERS = {'A', 'B', 'C', 'D', 'E', 'H', 'L', 'M', 'SP', 'PSW', 'BC', 'DE', 'HL'}
        DIRECTIVES = {'ORG', 'DB', 'DW', 'DS', 'EQU', 'END'}

        for line_idx, line in enumerate(lines):
            line_num = line_idx + 1

            # Comments
            comment_pos = line.find(';')
            if comment_pos >= 0:
                start = f"{line_num}.{comment_pos}"
                end = f"{line_num}.{len(line)}"
                self.editor.tag_add('comment', start, end)
                line = line[:comment_pos]  # Only highlight non-comment part

            # Labels
            match = re.match(r'^([A-Za-z_]\w*)\s*:', line)
            if match:
                start = f"{line_num}.0"
                end = f"{line_num}.{match.end()}"
                self.editor.tag_add('label_def', start, end)

            # Tokenize
            tokens = re.finditer(r'[A-Za-z_]\w*|[0-9][0-9A-Fa-fHhBbXx]*', line)
            for token in tokens:
                word = token.group().upper()
                col_start = token.start()
                col_end = token.end()
                start = f"{line_num}.{col_start}"
                end = f"{line_num}.{col_end}"

                if word in KEYWORDS:
                    self.editor.tag_add('keyword', start, end)
                elif word in DIRECTIVES:
                    self.editor.tag_add('directive', start, end)
                elif word in REGISTERS:
                    self.editor.tag_add('register', start, end)

            # Numbers (hex: FFH, 0xFF; decimal; binary: 1010B)
            for match in re.finditer(
                r'\b(?:0[xX][0-9A-Fa-f]+|[0-9][0-9A-Fa-f]*[Hh]|[0-9]+|[01]+[Bb])\b', line):
                start = f"{line_num}.{match.start()}"
                end = f"{line_num}.{match.end()}"
                self.editor.tag_add('number', start, end)

    # ═══════════════════════════════════════════════════════════
    # Assembly & Execution
    # ═══════════════════════════════════════════════════════════

    def _assemble(self):
        """Assemble the source code."""
        self._stop_program()
        source = self.editor.get('1.0', 'end')
        self.asm = Assembler8085()
        success, machine_code, errors, listing = self.asm.assemble(source)

        # Reset CPU and load code
        self.cpu.reset()
        for addr, byte in machine_code.items():
            self.cpu.memory[addr] = byte

        # Set PC to start address
        self.cpu.PC = self.asm.start_addr

        # Build address-to-line mapping
        self.addr_to_line = {}
        self.line_to_addr = {}
        for addr, code_bytes, src, line_num in listing:
            if code_bytes:
                self.addr_to_line[addr] = line_num
                self.line_to_addr[line_num] = addr

        self.assembled = True

        # Update listing display
        self._update_listing(listing)

        # Update console
        self.console_text.configure(state='normal')
        self.console_text.delete('1.0', 'end')

        if success:
            self.console_text.insert('end', f"✓ Assembly successful!\n", 'success')
            self.console_text.insert('end', f"  Code: {self.asm.start_addr:04X}H - "
                                   f"{self.asm.end_addr:04X}H "
                                   f"({len(machine_code)} bytes)\n", 'info')
            self.console_text.insert('end', f"  PC set to {self.asm.start_addr:04X}H\n", 'info')
            self.console_text.insert('end', f"  Labels: {dict(self.asm.labels)}\n", 'info')
            self._set_status(f"Assembled OK ─ {len(machine_code)} bytes at "
                           f"{self.asm.start_addr:04X}H")
        else:
            self.console_text.insert('end', f"✗ Assembly failed with {len(errors)} error(s):\n",
                                    'error')
            for err in errors:
                self.console_text.insert('end', f"  {err}\n", 'error')
            self._set_status(f"Assembly failed ─ {len(errors)} error(s)")

        self.console_text.configure(state='disabled')

        # Update all displays
        self._update_all_displays()

    def _update_listing(self, listing):
        """Update the assembled listing display."""
        self.listing_text.configure(state='normal')
        self.listing_text.delete('1.0', 'end')

        self.listing_text.insert('end', "  ADDR   CODE          SOURCE\n", 'addr')
        self.listing_text.insert('end', "  ─────  ────────────  ──────────────────────────\n",
                                'addr')

        for addr, code_bytes, src, line_num in listing:
            if not src.strip():
                self.listing_text.insert('end', '\n')
                continue

            if code_bytes:
                hex_str = ' '.join(f'{b:02X}' for b in code_bytes)
                addr_str = f"  {addr:04X}   {hex_str:<14s}"
                self.listing_text.insert('end', addr_str, 'hex')
            else:
                self.listing_text.insert('end', f"{'':22s}")

            self.listing_text.insert('end', f"  {src}\n", 'mnemonic')

        self.listing_text.configure(state='disabled')

    def _step_program(self):
        """Execute one instruction."""
        if not self.assembled:
            self._assemble()
            if not self.assembled:
                return

        if self.cpu.halted:
            self._set_status("CPU is halted ─ Reset to continue")
            return

        # Check breakpoint (but allow stepping past it)
        old_pc = self.cpu.execute_one()

        # Update current instruction display
        if old_pc is not None:
            mnemonic, _ = disassemble(self.cpu.memory, old_pc)
            self.instr_label.config(text=f"[{old_pc:04X}H] {mnemonic}")

        self._update_all_displays()
        self._highlight_current_line()

        if self.cpu.halted:
            self._set_status("CPU halted (HLT executed)")
            self.status_led.config(text="● HALTED", fg=self.FG_RED)

    def _run_program(self):
        """Run the program continuously."""
        if not self.assembled:
            self._assemble()
            if not self.assembled:
                return

        if self.cpu.halted:
            self._set_status("CPU is halted ─ Reset to continue")
            return

        self.running = True
        self.status_led.config(text="● RUNNING", fg=self.FG_AMBER)
        self._set_status("Running...")
        self._run_step()

    def _run_step(self):
        """Execute one step in continuous run mode."""
        if not self.running or self.cpu.halted:
            self.running = False
            self._update_all_displays()
            self._highlight_current_line()
            if self.cpu.halted:
                self._set_status("CPU halted (HLT executed)")
                self.status_led.config(text="● HALTED", fg=self.FG_RED)
            else:
                self.status_led.config(text="● READY", fg=self.FG_GREEN)
            return

        # Execute a batch of instructions for performance
        batch_size = max(1, 500 // max(1, self.run_speed))
        for _ in range(batch_size):
            if not self.running or self.cpu.halted:
                break

            old_pc = self.cpu.PC
            # Check breakpoint
            if old_pc in self.breakpoints and old_pc != self.asm.start_addr:
                self.running = False
                self._set_status(f"Breakpoint hit at {old_pc:04X}H")
                self.status_led.config(text="● BREAK", fg=self.FG_AMBER)
                self._update_all_displays()
                self._highlight_current_line()
                return

            self.cpu.execute_one()

            if self.cpu.halted:
                break

        # Update display
        self._update_all_displays()
        if old_pc is not None:
            mnemonic, _ = disassemble(self.cpu.memory, old_pc)
            self.instr_label.config(text=f"[{old_pc:04X}H] {mnemonic}")

        if self.running:
            self.root.after(self.run_speed, self._run_step)

    def _stop_program(self):
        """Stop continuous execution."""
        self.running = False
        self.status_led.config(text="● READY", fg=self.FG_GREEN)
        self._set_status("Stopped")

    def _reset_cpu(self):
        """Reset the CPU and reload assembled program."""
        self._stop_program()
        old_memory = bytes(self.cpu.memory)  # Save memory content
        self.cpu.reset()

        # Restore program in memory if assembled
        if self.assembled:
            for i in range(65536):
                self.cpu.memory[i] = old_memory[i]
            self.cpu.PC = self.asm.start_addr

        self.io_log = []
        self.cpu.output_callback = self._on_output
        self.cpu.input_callback = self._on_input
        self._update_all_displays()
        self._clear_io_log()
        self.halt_label.config(text="")
        self.status_led.config(text="● READY", fg=self.FG_GREEN)
        self._set_status("CPU Reset ─ Ready to execute")
        self.instr_label.config(text="")
        self._highlight_current_line()

    # ═══════════════════════════════════════════════════════════
    # Display Updates
    # ═══════════════════════════════════════════════════════════

    def _update_all_displays(self):
        self._update_register_display()
        self._update_flag_display()
        self._update_memory_view()
        self._update_trainer_display()

    def _update_register_display(self):
        reg_map = {
            'A': self.cpu.reg[7], 'B': self.cpu.reg[0], 'C': self.cpu.reg[1],
            'D': self.cpu.reg[2], 'E': self.cpu.reg[3],
            'H': self.cpu.reg[4], 'L': self.cpu.reg[5],
        }
        for name, val in reg_map.items():
            self.reg_labels[name].config(text=f"{val:02X}")
        self.reg_labels['SP'].config(text=f"{self.cpu.SP:04X}")
        self.reg_labels['PC'].config(text=f"{self.cpu.PC:04X}")
        self.cycle_label.config(text=str(self.cpu.cycles))
        self.halt_label.config(text="⬤ HALTED" if self.cpu.halted else "")

    def _update_flag_display(self):
        for name, val in self.cpu.flags.items():
            lbl = self.flag_labels[name]
            lbl.config(text=str(val))
            lbl.config(fg=self.FG_GREEN if val else self.FG_RED)

    def _update_memory_view(self, event=None):
        try:
            addr_str = self.mem_addr_var.get().strip()
            base_addr = int(addr_str, 16)
        except ValueError:
            base_addr = 0x2000

        base_addr = base_addr & 0xFFF0  # Align to 16

        self.mem_text.configure(state='normal')
        self.mem_text.delete('1.0', 'end')

        # Show 16 rows of 16 bytes
        rows = 16
        for row in range(rows):
            addr = (base_addr + row * 16) & 0xFFFF
            # Address column
            self.mem_text.insert('end', f" {addr:04X}: ", 'addr')

            # Hex bytes
            ascii_str = ""
            for col in range(16):
                byte_addr = (addr + col) & 0xFFFF
                val = self.cpu.memory[byte_addr]

                # Determine tag
                if byte_addr == self.cpu.PC:
                    tag = 'pc_byte'
                elif val != 0:
                    tag = 'nonzero'
                else:
                    tag = 'zero'

                self.mem_text.insert('end', f"{val:02X} ", tag)

                # ASCII representation
                if 32 <= val <= 126:
                    ascii_str += chr(val)
                else:
                    ascii_str += '.'

            self.mem_text.insert('end', f" │{ascii_str}│\n", 'ascii')

        self.mem_text.configure(state='disabled')

    def _update_trainer_display(self):
        self.seg_addr.config(text=f"{self.trainer_addr:04X}")
        val = self.cpu.memory[self.trainer_addr]
        self.seg_data.config(text=f"{val:02X}")

    def _highlight_current_line(self):
        """Highlight the line corresponding to current PC in editor."""
        self.editor.tag_remove('current_line', '1.0', 'end')
        if self.cpu.PC in self.addr_to_line:
            line_num = self.addr_to_line[self.cpu.PC]
            self.editor.tag_add('current_line', f'{line_num}.0', f'{line_num}.end')
            self.editor.see(f'{line_num}.0')

    def _mem_page(self, direction):
        try:
            addr = int(self.mem_addr_var.get(), 16)
        except ValueError:
            addr = 0x2000
        addr = (addr + direction * 256) & 0xFFFF
        self.mem_addr_var.set(f"{addr:04X}")
        self._update_memory_view()

    # ═══════════════════════════════════════════════════════════
    # I/O Operations
    # ═══════════════════════════════════════════════════════════

    def _on_output(self, port, value):
        entry = f"OUT  Port {port:02X}H ← {value:02X}H ({value:3d}) '{chr(value) if 32 <= value <= 126 else '.'}'"
        self.io_log.append(('output', entry))
        self._append_io_log(entry, 'output')

    def _on_input(self, port):
        val = self.cpu.io[port]
        entry = f"IN   Port {port:02X}H → {val:02X}H ({val:3d})"
        self.io_log.append(('input', entry))
        self._append_io_log(entry, 'input')
        return val

    def _append_io_log(self, text, tag):
        self.io_text.configure(state='normal')
        self.io_text.insert('end', text + '\n', tag)
        self.io_text.see('end')
        self.io_text.configure(state='disabled')

    def _clear_io_log(self):
        self.io_text.configure(state='normal')
        self.io_text.delete('1.0', 'end')
        self.io_text.configure(state='disabled')

    def _set_io_port(self):
        try:
            port = int(self.port_num_var.get(), 16) & 0xFF
            val = int(self.port_val_var.get(), 16) & 0xFF
            self.cpu.io[port] = val
            self._append_io_log(f"SET  Port {port:02X}H = {val:02X}H", 'info')
        except ValueError:
            messagebox.showerror("Error", "Invalid port number or value (use hex)")

    # ═══════════════════════════════════════════════════════════
    # Memory Editor
    # ═══════════════════════════════════════════════════════════

    def _store_memory(self):
        try:
            addr = int(self.edit_addr_var.get(), 16) & 0xFFFF
            data = int(self.edit_data_var.get(), 16) & 0xFF
            self.cpu.memory[addr] = data
            self._update_memory_view()
            self._update_trainer_display()
        except ValueError:
            messagebox.showerror("Error", "Invalid address or data (use hex)")

    def _store_next(self):
        try:
            addr = int(self.edit_addr_var.get(), 16) & 0xFFFF
            data = int(self.edit_data_var.get(), 16) & 0xFF
            self.cpu.memory[addr] = data
            addr = (addr + 1) & 0xFFFF
            self.edit_addr_var.set(f"{addr:04X}")
            self.edit_data_var.set(f"{self.cpu.memory[addr]:02X}")
            self._update_memory_view()
            self._update_trainer_display()
        except ValueError:
            messagebox.showerror("Error", "Invalid address or data (use hex)")

    # ═══════════════════════════════════════════════════════════
    # Trainer Kit Operations
    # ═══════════════════════════════════════════════════════════

    def _hex_key_press(self, key):
        """Handle hex keypad button press."""
        val = int(key, 16)

        if self.trainer_mode == 'ADDR':
            # Shift address left and add new digit
            self.trainer_addr = ((self.trainer_addr << 4) | val) & 0xFFFF
        else:
            # Data mode: shift data left and add new digit
            old_data = self.cpu.memory[self.trainer_addr]
            new_data = ((old_data << 4) | val) & 0xFF
            self.cpu.memory[self.trainer_addr] = new_data

        self._update_trainer_display()
        self._update_memory_view()

    def _trainer_examine(self):
        """Examine memory at current address (switch to data mode)."""
        self.trainer_mode = 'DATA'
        self.seg_mode.config(text="▸ DATA MODE ─ Enter data, press STORE")
        self._update_trainer_display()
        self.edit_addr_var.set(f"{self.trainer_addr:04X}")
        self.edit_data_var.set(f"{self.cpu.memory[self.trainer_addr]:02X}")

    def _trainer_next(self):
        """Move to next address."""
        self.trainer_addr = (self.trainer_addr + 1) & 0xFFFF
        self._update_trainer_display()
        self.edit_addr_var.set(f"{self.trainer_addr:04X}")
        self.edit_data_var.set(f"{self.cpu.memory[self.trainer_addr]:02X}")

    def _trainer_prev(self):
        """Move to previous address."""
        self.trainer_addr = (self.trainer_addr - 1) & 0xFFFF
        self._update_trainer_display()
        self.edit_addr_var.set(f"{self.trainer_addr:04X}")
        self.edit_data_var.set(f"{self.cpu.memory[self.trainer_addr]:02X}")

    def _trainer_store(self):
        """Store and move to next (trainer mode)."""
        self.trainer_addr = (self.trainer_addr + 1) & 0xFFFF
        self.trainer_mode = 'DATA'
        self._update_trainer_display()
        self._update_memory_view()

    def _trainer_exec(self):
        """Execute from current trainer address."""
        self.cpu.PC = self.trainer_addr
        self.cpu.halted = False
        self._run_program()

    def _trainer_reset(self):
        """Reset trainer display to address mode."""
        self.trainer_mode = 'ADDR'
        self.trainer_addr = 0x2000
        self.seg_mode.config(text="▸ ADDRESS MODE")
        self._reset_cpu()
        self._update_trainer_display()

    # ═══════════════════════════════════════════════════════════
    # File Operations
    # ═══════════════════════════════════════════════════════════

    def _new_file(self):
        self.editor.delete('1.0', 'end')
        self.editor.insert('1.0', "; New 8085 Assembly Program\n    ORG 2000H\n\n    ; Your code here\n\n    HLT\n")
        self.assembled = False
        self._on_editor_change()

    def _open_file(self):
        filepath = filedialog.askopenfilename(
            title="Open Assembly File",
            filetypes=[("Assembly files", "*.asm *.s *.a85 *.txt"), ("All files", "*.*")])
        if filepath:
            try:
                with open(filepath, 'r') as f:
                    content = f.read()
                self.editor.delete('1.0', 'end')
                self.editor.insert('1.0', content)
                self.assembled = False
                self._on_editor_change()
                self._set_status(f"Loaded: {filepath}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to open file: {e}")

    def _save_file(self):
        filepath = filedialog.asksaveasfilename(
            title="Save Assembly File",
            defaultextension=".asm",
            filetypes=[("Assembly files", "*.asm"), ("Text files", "*.txt"), ("All files", "*.*")])
        if filepath:
            try:
                with open(filepath, 'w') as f:
                    f.write(self.editor.get('1.0', 'end'))
                self._set_status(f"Saved: {filepath}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save file: {e}")

    def _load_sample(self, name):
        if name in SAMPLE_PROGRAMS:
            self.editor.delete('1.0', 'end')
            self.editor.insert('1.0', SAMPLE_PROGRAMS[name])
            self.assembled = False
            self._on_editor_change()
            self._set_status(f"Loaded sample: {name}")

    # ═══════════════════════════════════════════════════════════
    # Misc
    # ═══════════════════════════════════════════════════════════

    def _on_speed_change(self, val):
        self.run_speed = int(float(val))
        self.speed_label.config(text=f"{self.run_speed}ms")

    def _set_status(self, text):
        self.status_text.config(text=text)

    def _show_about(self):
        messagebox.showinfo("About", 
            "Intel 8085 Microprocessor Simulator\n"
            "Lab Trainer Kit Edition\n"
            "GitHub: gojonichan\n\n"
            "Features:\n"
            "• Complete 8085 instruction set (all 246 opcodes)\n"
            "• Two-pass assembler with labels & directives\n"
            "• Step-by-step execution & continuous run\n"
            "• Hex keypad trainer kit interface\n"
            "• Memory viewer/editor (64KB)\n"
            "• I/O port simulation\n"
            "• Syntax-highlighted editor\n"
            "• 12+ sample programs\n\n"
            "Keyboard Shortcuts:\n"
            "  F8 - Assemble\n"
            "  F5 - Run\n"
            "  F6 - Step\n"
            "  F7 - Stop\n"
            "  F9 - Reset\n"
        )

    def _show_help(self):
        """Show instruction set reference."""
        help_win = tk.Toplevel(self.root)
        help_win.title("8085 Instruction Set Reference")
        help_win.geometry("800x600")
        help_win.configure(bg=self.BG_DARK)

        text = tk.Text(help_win, wrap='word', bg=self.BG_EDITOR, fg=self.FG_TEXT,
                      font=self.mono_small, padx=12, pady=12,
                      highlightthickness=0, borderwidth=0)
        scroll = tk.Scrollbar(help_win, command=text.yview)
        text.configure(yscrollcommand=scroll.set)
        scroll.pack(side='right', fill='y')
        text.pack(fill='both', expand=True)

        text.tag_configure('title', foreground=self.FG_CYAN, font=("Consolas", 14, "bold"))
        text.tag_configure('section', foreground=self.FG_AMBER, font=("Consolas", 12, "bold"))
        text.tag_configure('mnemonic', foreground=self.FG_GREEN)

        ref = """INTEL 8085 INSTRUCTION SET REFERENCE
════════════════════════════════════════

DATA TRANSFER INSTRUCTIONS
──────────────────────────
MOV  r1, r2    Copy register r2 to r1
MVI  r, data   Load immediate 8-bit data to register
LDA  addr      Load A from memory address
STA  addr      Store A to memory address
LHLD addr      Load HL from memory (L←[addr], H←[addr+1])
SHLD addr      Store HL to memory
LXI  rp, d16   Load 16-bit immediate to register pair
LDAX rp        Load A from address in rp (B or D only)
STAX rp        Store A to address in rp (B or D only)
XCHG           Exchange DE and HL

ARITHMETIC INSTRUCTIONS
───────────────────────
ADD  r         A ← A + r
ADC  r         A ← A + r + CY
SUB  r         A ← A - r
SBB  r         A ← A - r - CY
INR  r         r ← r + 1
DCR  r         r ← r - 1
INX  rp        rp ← rp + 1
DCX  rp        rp ← rp - 1
DAD  rp        HL ← HL + rp
DAA            Decimal Adjust Accumulator
ADI  data      A ← A + data
ACI  data      A ← A + data + CY
SUI  data      A ← A - data
SBI  data      A ← A - data - CY

LOGICAL INSTRUCTIONS
────────────────────
ANA  r         A ← A AND r
XRA  r         A ← A XOR r
ORA  r         A ← A OR r
CMP  r         Compare A with r (set flags, A unchanged)
ANI  data      A ← A AND data
XRI  data      A ← A XOR data
ORI  data      A ← A OR data
CPI  data      Compare A with data
RLC            Rotate A left through carry
RRC            Rotate A right through carry
RAL            Rotate A left through carry (9-bit)
RAR            Rotate A right through carry (9-bit)
CMA            Complement A (1's complement)
CMC            Complement carry flag
STC            Set carry flag

BRANCH INSTRUCTIONS
───────────────────
JMP  addr      Jump unconditionally
JC   addr      Jump if carry (CY=1)
JNC  addr      Jump if no carry (CY=0)
JZ   addr      Jump if zero (Z=1)
JNZ  addr      Jump if not zero (Z=0)
JP   addr      Jump if positive (S=0)
JM   addr      Jump if minus (S=1)
JPE  addr      Jump if parity even (P=1)
JPO  addr      Jump if parity odd (P=0)
CALL addr      Call subroutine
RET            Return from subroutine
  (Conditional calls/returns: CC,CNC,CZ,CNZ,CP,CM,CPE,CPO)
  (Conditional returns: RC,RNC,RZ,RNZ,RP,RM,RPE,RPO)
PCHL           Jump to address in HL
RST  n         Restart (call address n×8, n=0-7)

STACK & I/O INSTRUCTIONS
─────────────────────────
PUSH rp        Push register pair onto stack
POP  rp        Pop register pair from stack
  (rp can be B, D, H, or PSW)
XTHL           Exchange top of stack with HL
SPHL           SP ← HL
IN   port      Read input port to A
OUT  port      Write A to output port

CONTROL INSTRUCTIONS
────────────────────
NOP            No operation
HLT            Halt processor
EI             Enable interrupts
DI             Disable interrupts
RIM            Read interrupt mask
SIM            Set interrupt mask

ASSEMBLER DIRECTIVES
────────────────────
ORG  addr      Set origin address
DB   data      Define byte(s)
DW   data      Define word(s) (16-bit)
DS   count     Define storage (reserve bytes)
EQU  value     Equate label to value
END            End of source

REGISTER NAMES
──────────────
8-bit:  A, B, C, D, E, H, L, M (M = memory at [HL])
16-bit: B(BC), D(DE), H(HL), SP, PSW(A+Flags)

NUMBER FORMATS
──────────────
Hex:     0FFH, 2000H, 0x2000
Decimal: 255, 100
Binary:  11111111B, 1010B

FLAGS
─────
S  - Sign (bit 7 of result)
Z  - Zero (result is zero)
AC - Auxiliary Carry (carry from bit 3)
P  - Parity (even parity = 1)
CY - Carry (carry/borrow from bit 7)
"""
        text.insert('1.0', ref)
        text.configure(state='disabled')


# ═══════════════════════════════════════════════════════════════════
# SECTION 6: Main Entry Point
# ═══════════════════════════════════════════════════════════════════

def main():
    root = tk.Tk()

    # Set icon if possible
    try:
        root.iconbitmap(default='')
    except:
        pass

    app = SimulatorApp(root)
    root.mainloop()


if __name__ == '__main__':
    main()
