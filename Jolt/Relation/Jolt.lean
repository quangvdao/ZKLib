import Mathlib.FieldTheory.Finite.Basic
import Jolt.Relation.Basic
import Jolt.RiscV.ISA

/-!
  # The Jolt Relation

  This file contains the specification for the Jolt relation, which is a combination of R1CS, lookups, and memory-checking (both read-only and read-write).

  We will show that the Jolt relation is exactly equal to the execution of RISC-V programs.

  Many of our specification draws directly from the main [Rust codebase](https://github.com/a16z/jolt).
-/


namespace Jolt

open RiscV

notation "MEMORY_OPS_PER_INSTRUCTION" => (7 : ℕ)
notation "NUM_INSTR_FIELDS" => (6 : ℕ)
notation "NUM_BYTES_IN_WORD" => (4 : ℕ)
notation "RAM_START_ADDRESS" => (2147483648 : UInt64)
notation "REGISTER_COUNT" => (64 : UInt64)


section Model

structure ELFInstruction where
  address : UInt64
  opcode : RV32IM.Instr
  rs1 : Option UInt64
  rs2 : Option UInt64
  rd : Option UInt64
  imm : Option UInt32
  -- Technically the below is `usize` in Rust
  virtualSequenceIndex : Option UInt64

structure RegisterState where
  rs1Value : Option UInt64
  rs2Value : Option UInt64
  rdValue : Option UInt64

section Memory

inductive MemoryState where
  | Read (address : UInt64) (value : UInt64)
  | Write (address : UInt64) (value : UInt64)

inductive MemoryOp where
  | Read (address : UInt64)
  | Write (address : UInt64) (value : UInt64)

structure MemoryLayout where
  maxInputSize : UInt64
  maxOutputSize : UInt64

def MemoryLayout.ramWitnessOffset (m : MemoryLayout) : UInt64 :=
  (REGISTER_COUNT + m.maxInputSize + m.maxOutputSize + 1).nextPowerOfTwo

def MemoryLayout.inputStart (m : MemoryLayout) : UInt64 :=
  RAM_START_ADDRESS - m.ramWitnessOffset + REGISTER_COUNT

def MemoryLayout.inputEnd (m : MemoryLayout) : UInt64 :=
  m.inputStart + m.maxInputSize

def MemoryLayout.outputStart (m : MemoryLayout) : UInt64 :=
  m.inputEnd + 1

def MemoryLayout.outputEnd (m : MemoryLayout) : UInt64 :=
  m.outputStart + m.maxOutputSize

def MemoryLayout.panic (m : MemoryLayout) : UInt64 :=
  m.outputEnd + 1

end Memory

structure RVTraceRow where
  instruction : ELFInstruction
  registerState : RegisterState
  memoryState : Option MemoryState
  adviceValue : Option UInt64

structure BytecodeRow where
  -- Technically `usize` in Rust
  address : UInt64
  bitflags : UInt64
  rs1 : UInt64
  rs2 : UInt64
  rd : UInt64
  imm : UInt64

structure JoltTraceStep where
  instructionLookup : Option ISA
  bytecodeRow : BytecodeRow
  memoryOps : Fin MEMORY_OPS_PER_INSTRUCTION → MemoryOp

structure JoltDevice where
  inputs : Array UInt8
  outputs : Array UInt8
  panic : Bool
  memoryLayout : MemoryLayout

end Model

variable (F : Type) [Field F] [Fintype F] [Inhabited F]

section Witness

-- TODO: define a class that says you can embed `UInt64` into `F`

structure BytecodeWitness where
  readWriteAddress : Array F
  readWriteValue : Fin NUM_INSTR_FIELDS → Array F
  readTimestamp : Array F
  finalTimestamp : Array F

structure ReadWriteMemoryWitness where
  memorySize : UInt64
  initialMemValue : Array F
  ramAddress : Array F
  readValue : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  writeRdValue : Array F
  writeRamValue : Fin NUM_BYTES_IN_WORD → Array F
  finalMemValue : Array F
  readMemTimestamps : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  writeTimestamps : Fin NUM_BYTES_IN_WORD → Array F
  finalTimestamp : Array F

structure RangeCheckWitness where
  readTimestamps : Fin MEMORY_OPS_PER_INSTRUCTION → Array UInt64
  readCtsReadTimestamp : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  readCtsGlobalMinusRead : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  finalCtsReadTimestamp : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  finalCtsGlobalMinusRead : Fin MEMORY_OPS_PER_INSTRUCTION → Array F

structure InstructionWitness where
  dim : Array (Array F)
  readCts : Array (Array F)
  finalCts : Array (Array F)
  EPolys : Array (Array F)
  instructionFlagPolys : Array (Array F)
  instructionFlagBitvectors : Array (Array UInt64)
  lookupOutputs : Array F

-- TODO: add instruction flags (it's just an array / vector of `UInt64`?)

structure JoltWitness extends BytecodeWitness F, ReadWriteMemoryWitness F, RangeCheckWitness F, InstructionWitness F

end Witness

section Preprocessing

-- Is `HashMap` the right type?
open Lean in
structure BytecodePreprocessing where
  codeSize : UInt64
  vInitFinal : Fin NUM_INSTR_FIELDS → Array F
  virtualAddressMap : HashMap UInt64 UInt64

structure ReadWriteMemoryPreprocessing where
  minBytecodeAddress : UInt64
  bytecodeBytes : Array UInt8
  programIo : Option JoltDevice

structure InstructionLookupsPreprocessing where
  subtableToMemoryIndices : Array (Array UInt64)
  instructionToMemoryIndices : Array (Array UInt64)
  memoryToSubtableIndex : Array UInt64
  memoryToDimensionIndex : Array UInt64
  materializedSubtables : Array (Array F)
  numMemories : UInt64

structure JoltPreprocessing extends
  BytecodePreprocessing F,
  ReadWriteMemoryPreprocessing,
  InstructionLookupsPreprocessing F

end Preprocessing

section Generation

-- Generate preprocessing data from `Array ELFInstruction` and `Array (UInt64 × UInt8)`


-- Generate witness from `Array ELFInstruction` and `Array (UInt64 × UInt8)`


end Generation

section R1CS

-- TODO: figure out how `JoltWitness` is transformed into `R1CSWitness`

structure R1CSWitness where
  paddedTraceLength : UInt64
  programCounter : Array F
  bytecodeAddress : Array F
  bytecodeValue : Array F
  memoryAddressReadWrite : Array F
  memoryValueReads : Array F
  memoryValueWrites : Array F
  chunksX : Array F
  chunksY : Array F
  chunksQuery : Array F
  lookupOutputs : Array F
  circuitFlagsBits : Array F
  instructionFlagsBits : Array F


end R1CS


end Jolt
