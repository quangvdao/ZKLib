/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.ConstraintSystem.Constants
import ZKLib.ConstraintSystem.Field
import ZKLib.ConstraintSystem.Trace

/-!
  # I/O and decoding for a RISC-V program

  TODO: the most important thing is to implement the `decode` and `trace` functions.
  This will help us understand the memory layout of a program.
-/
namespace Jolt

variable (F : Type) [JoltField F]

structure ProgramSummary where
  rawTrace : List RVTraceRow
  bytecode : List ELFInstruction
  memoryInit : List (UInt64 × UInt8)
  ioDevice : Device
  processedTrace : List (TraceStep F)
  circuitFlags : List Bool
deriving Inhabited
-- deriving Repr, Inhabited, DecidableEq

def ProgramSummary.traceLen (ps : ProgramSummary F) : Nat :=
  ps.processedTrace.length

-- def ProgramSummary.analyze (ps : ProgramSummary F) : List (RV32IM × Nat) :=
--   let counts := ps.rawTrace.foldl (fun acc row =>
--     let op := row.instruction.opcode
--     match acc.find? op with
--     | some count => acc.insert op (count + 1)
--     | none => acc.insert op 1
--   ) (HashMap.empty)
--   let countsList := counts.toList
--   countsList.qsort (fun a b => b.2 < a.2)

-- def ProgramSummary.writeToFile (ps : ProgramSummary F) (path : System.FilePath) : IO Unit := do
--   let data := toString ps -- Assuming a toString instance for ProgramSummary
--   IO.FS.writeFile path data

structure Program where
  guest : String
  func : Option String
  input : List UInt8
  memorySize : UInt64
  stackSize : UInt64
  maxInputSize : UInt64
  maxOutputSize : UInt64
  std : Bool
  elf : Option (List String)
  deriving Repr

def Program.new (guest : String) : Program := {
  guest := guest,
  func := none,
  input := [],
  memorySize := DEFAULT_MEMORY_SIZE,
  stackSize := DEFAULT_STACK_SIZE,
  maxInputSize := DEFAULT_MAX_INPUT_SIZE,
  maxOutputSize := DEFAULT_MAX_OUTPUT_SIZE,
  std := false,
  elf := none
}

def Program.setStd (p : Program) (std : Bool) : Program :=
  { p with std := std }

def Program.setFunc (p : Program) (func : String) : Program :=
  { p with func := some func }

def Program.setInput (p : Program) (input : List UInt8) : Program :=
  { p with input := p.input ++ input }

def Program.setMemorySize (p : Program) (len : UInt64) : Program :=
  { p with memorySize := len }

def Program.setStackSize (p : Program) (len : UInt64) : Program :=
  { p with stackSize := len }

def Program.setMaxInputSize (p : Program) (size : UInt64) : Program :=
  { p with maxInputSize := size }

def Program.setMaxOutputSize (p : Program) (size : UInt64) : Program :=
  { p with maxOutputSize := size }

def Program.build (p : Program) : Program :=
  -- Implementation to be added
  p

def Program.decode (p : Program) : Program × (List ELFInstruction) × (List (UInt64 × UInt8)) :=
  -- Implementation to be added
  (p, [], [])

def Program.trace (p : Program) (F : Type) [JoltField F] :
    Program × Device × (List (TraceStep F)) × (List F) :=
  -- Implementation to be added
  (p, default, [], [])

def Program.traceAnalyze (p : Program) : ProgramSummary F :=
  -- Implementation to be added
  default

def Program.saveLinker (p : Program) : IO Unit :=
  -- Implementation to be added
  pure ()

def Program.linkerPath (p : Program) : String :=
  s!"/tmp/jolt-guest-linkers/{p.guest}.ld"
/-
const LINKER_SCRIPT_TEMPLATE: &str = r#"
MEMORY {
  program (rwx) : ORIGIN = 0x80000000, LENGTH = {MEMORY_SIZE}
}

SECTIONS {
  .text.boot : {
    *(.text.boot)
  } > program

  .text : {
    *(.text)
  } > program

  .data : {
    *(.data)
  } > program

  .bss : {
    *(.bss)
  } > program

  . = ALIGN(8);
  . = . + {STACK_SIZE};
  _STACK_PTR = .;
  . = ALIGN(8);
  _HEAP_PTR = .;
}
"#;

-/

end Jolt