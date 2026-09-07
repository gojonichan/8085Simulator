# Intel 8085 Microprocessor Simulator - Lab Trainer Kit

A comprehensive simulator with a graphical user interface that mimics a real 8085 trainer kit. Features a complete instruction set, a two-pass assembler, step execution, breakpoints, and a memory viewer.

## Features

- **Complete 8085 Instruction Set**: Supports all 246 opcodes.
- **Two-pass Assembler**: Includes support for labels and assembler directives (ORG, EQU, DB, DW, DS, END).
- **Execution Modes**: Step-by-step execution or continuous run with adjustable speed.
- **Lab Trainer Kit Interface**: Features a hex keypad and a 7-segment display for authentic trainer kit experience.
- **Memory Viewer & Editor**: View and edit 64KB of memory directly.
- **I/O Port Simulation**: Interactive I/O port reading and writing.
- **Syntax-highlighted Editor**: Built-in assembly editor with syntax highlighting and line numbers.
- **Sample Programs**: Comes with over 12 built-in sample programs (e.g., Fibonacci, Bubble Sort, BCD Addition).

## Requirements

- Python 3.x
- `tkinter` (usually included with standard Python installations)

## How to Run

Clone the repository and run the script:

```bash
python simulator.py
```

## Usage

1. **Write or Load Assembly Code**: Use the built-in editor to write 8085 assembly code or load a sample program from the "Sample Programs" menu.
2. **Assemble**: Click "Assemble (F8)" or press `F8` to compile your code. Check the Console tab for any errors.
3. **Run or Step**:
   - Click "Run (F5)" to execute the code continuously. Adjust speed using the slider.
   - Click "Step (F6)" to execute instructions one at a time.
4. **Trainer Kit Mode**: Use the keypad to enter addresses and data directly into memory, simulating a hardware trainer kit.

## Keyboard Shortcuts

- **F8** - Assemble
- **F5** - Run
- **F6** - Step
- **F7** - Stop
- **F9** - Reset CPU
- **Ctrl+N** - New File
- **Ctrl+O** - Open File
- **Ctrl+S** - Save File

## Credits

Developed by [gojonichan](https://github.com/gojonichan).
