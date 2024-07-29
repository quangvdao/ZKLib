import Mathlib.FieldTheory.Finite.Basic
import Batteries.Data.UInt
import Jolt.Relation.Basic
import Jolt.RiscV.ISA

/-!
  # The Jolt Relation

  This file contains the specification for the Jolt relation, which is a combination of R1CS,
  lookups, and memory-checking (both read-only and read-write).

  We will show that the Jolt relation is exactly equal to the execution of RISC-V programs.

  Many of our specification draws directly from the main [Rust codebase](https://github.com/a16z/jolt).
-/


namespace Jolt

open RiscV

notation "RAM_START_ADDRESS" => (2147483648 : UInt64)
notation "REGISTER_COUNT" => (64 : UInt64)
notation "MEMORY_OPS_PER_INSTRUCTION" => (7 : ℕ)
notation "NUM_INSTR_FIELDS" => (6 : ℕ)
notation "NUM_BYTES_IN_WORD" => (4 : ℕ)
notation "BYTES_PER_INSTRUCTION" => (4 : UInt64)


section Model

structure ELFInstruction where
  address : UInt64
  opcode : RV32IM.Instr
  rs1 : Option UInt64
  rs2 : Option UInt64
  rd : Option UInt64
  imm : Option UInt32
  virtualSequenceIndex : Option USize
deriving Repr, Inhabited

structure RegisterState where
  rs1Value : Option UInt64
  rs2Value : Option UInt64
  rdValue : Option UInt64
deriving Repr, Inhabited

section Memory

inductive MemoryState where
  | Read (address : UInt64) (value : UInt64)
  | Write (address : UInt64) (value : UInt64)
deriving Repr, Inhabited

inductive MemoryOp where
  | Read (address : UInt64)
  | Write (address : UInt64) (value : UInt64)
deriving Repr, Inhabited

structure MemoryLayout where
  maxInputSize : UInt64
  maxOutputSize : UInt64
deriving Repr, Inhabited

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
deriving Repr, Inhabited

structure BytecodeRow where
  address : USize
  bitflags : UInt64
  rs1 : UInt64
  rs2 : UInt64
  rd : UInt64
  imm : UInt64
deriving Repr, Inhabited

-- TODO: Define `InstructionSet` and `SubtableSet`

structure JoltTraceStep (InstructionSet : Type) where
  instructionLookup : Option InstructionSet
  bytecodeRow : BytecodeRow
  memoryOps : Fin MEMORY_OPS_PER_INSTRUCTION → MemoryOp
deriving Repr, Inhabited

structure JoltDevice where
  inputs : Array UInt8
  outputs : Array UInt8
  panic : Bool
  memoryLayout : MemoryLayout
deriving Repr, Inhabited

end Model

class FromUInt64 (F : Type u) where
  embedding : UInt64 ↪ F

variable (F : Type) [Field F] [Fintype F] [Inhabited F] [FromUInt64 F]

section Witness

-- TODO: define a class that says you can embed `UInt64` into `F`

structure BytecodeWitness where
  readWriteAddress : Array F
  readWriteValue : Fin NUM_INSTR_FIELDS → Array F
  readTimestamp : Array F
  finalTimestamp : Array F
deriving Repr, Inhabited

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
deriving Repr, Inhabited

structure RangeCheckWitness where
  readTimestamps : Fin MEMORY_OPS_PER_INSTRUCTION → Array UInt64
  readCtsReadTimestamp : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  readCtsGlobalMinusRead : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  finalCtsReadTimestamp : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  finalCtsGlobalMinusRead : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
deriving Repr, Inhabited

structure InstructionLookupsWitness where
  dim : Array (Array F)
  readCts : Array (Array F)
  finalCts : Array (Array F)
  EPolys : Array (Array F)
  instructionFlagPolys : Array (Array F)
  instructionFlagBitvectors : Array (Array UInt64)
  lookupOutputs : Array F
deriving Repr, Inhabited

-- TODO: rename variables in different witness types to have no overlap
-- TODO: add instruction flags (it's just an array / vector of `UInt64`?)

structure JoltWitness extends BytecodeWitness F, ReadWriteMemoryWitness F,
    RangeCheckWitness F, InstructionLookupsWitness F
  --   where
  -- circuitFlags : Array F

end Witness

section Preprocessing

-- TODO: derive `Repr` for `HashMap`?
-- We can prove that the keys are distinct, assuming we do preprocessing on a valid `ELF` file
open Lean in
structure BytecodePreprocessing where
  codeSize : UInt64
  vInitFinal : Fin NUM_INSTR_FIELDS → Array F
  virtualAddressMap : HashMap UInt64 UInt64
deriving Inhabited

structure ReadWriteMemoryPreprocessing where
  minBytecodeAddress : UInt64
  bytecodeBytes : Array UInt8
  programIo : Option JoltDevice
deriving Repr, Inhabited

structure InstructionLookupsPreprocessing where
  subtableToMemoryIndices : Array (Array UInt64)
  instructionToMemoryIndices : Array (Array UInt64)
  memoryToSubtableIndex : Array UInt64
  memoryToDimensionIndex : Array UInt64
  materializedSubtables : Array (Array F)
  numMemories : UInt64
deriving Repr, Inhabited

structure JoltPreprocessing extends
  BytecodePreprocessing F,
  ReadWriteMemoryPreprocessing,
  InstructionLookupsPreprocessing F
deriving Inhabited


-- TODO: will need to add R1CS constraints as part of `JoltPreprocessing`.
-- Will do this after the changes are made to the Rust codebase

end Preprocessing

section Generation

-- Generate preprocessing data from `Array ELFInstruction` and `Array (UInt64 × UInt8)`

open Lean in
def BytecodePreprocessing.new (bytecode : Array BytecodeRow) : BytecodePreprocessing F := Id.run do
  assert! bytecode.size > 0
  let codeSize := bytecode.size
  let vInitFinal := Array.range NUM_INSTR_FIELDS |> Array.map (fun _ => Array.range codeSize |> Array.map (fun _ => 0 : F))
  let virtualAddressMap := HashMap.empty
  { codeSize := codeSize, vInitFinal := vInitFinal, virtualAddressMap := virtualAddressMap }

def ReadWriteMemoryPreprocessing.new (memoryInit : Array (UInt64 × UInt8)) :
    ReadWriteMemoryPreprocessing :=
  let minBytecodeAddress := memoryInit.map Prod.fst |> Array.min? |> Option.get!
  let maxBytecodeAddress := memoryInit.map Prod.fst |> Array.max? |> Option.get!
  let size := (maxBytecodeAddress - minBytecodeAddress + 1).toNat
  let emptyArray := mkArray size 0
  let bytecodeBytes := memoryInit.foldl (init := emptyArray)
    (fun acc (addr, byte) =>
      let remappedIndex := (addr - minBytecodeAddress).toNat
      acc.set! remappedIndex byte)
  { minBytecodeAddress := minBytecodeAddress,
    bytecodeBytes := bytecodeBytes,
    programIo := none }


-- TODO: this definition depends on the `InstructionSet` and `SubtableSet`
-- for a given architecture (i.e. RV32IM)
def InstructionLookupsPreprocessing.new : InstructionLookupsPreprocessing F := sorry

def JoltPreprocessing.new (bytecode : Array BytecodeRow) (memoryInit : Array (UInt64 × UInt8)) :
    JoltPreprocessing F :=
  let bytecodePrep := BytecodePreprocessing.new F bytecode
  let memoryPrep := ReadWriteMemoryPreprocessing.new memoryInit
  let instructionLookupsPrep := InstructionLookupsPreprocessing.new F
  { toBytecodePreprocessing := bytecodePrep,
    toReadWriteMemoryPreprocessing := memoryPrep,
    toInstructionLookupsPreprocessing := instructionLookupsPrep }



-- Generate witness from `Array ELFInstruction` and `Array (UInt64 × UInt8)`


-- TODO: this depends on the `InstructionSet` and `SubtableSet`
def InstructionLookupsWitness.new
    (preprocessedInstructionLookups : InstructionLookupsPreprocessing F)
    (trace : Array (JoltTraceStep InstructionSet)) : InstructionLookupsWitness F := sorry

def InstructionLookupsWitness.getFlags (w : InstructionLookupsWitness F) : Array F := sorry

-- Also supposed to return `readTimestamp`
def ReadWriteMemoryWitness.new (programIo : JoltDevice)
    (loadStoreFlags : Array F)
    (preprocessedRWMemory : ReadWriteMemoryPreprocessing)
    (trace : Array (JoltTraceStep InstructionSet)) : ReadWriteMemoryWitness F := sorry

def ReadWriteMemoryWitness.getReadTimestamps (w : ReadWriteMemoryWitness F) : Array F := sorry

def BytecodeWitness.new (preprocessedBytecode : BytecodePreprocessing F)
    (trace : Array (JoltTraceStep InstructionSet)) : BytecodeWitness F := sorry

def RangeCheckWitness.new (readTimestamps : Array F) : RangeCheckWitness F := sorry

-- Combine the witness generation from the previous functions
def JoltWitness.new (programIo : JoltDevice)
    (preprocessing : JoltPreprocessing F)
    (trace : Array (JoltTraceStep InstructionSet)) : JoltWitness F :=
  let instructionLookupsWitness := InstructionLookupsWitness.new F preprocessing.toInstructionLookupsPreprocessing trace
  let loadStoreFlags := instructionLookupsWitness.getFlags
  let bytecodeWitness := BytecodeWitness.new F preprocessing.toBytecodePreprocessing trace
  let rwMemoryWitness := ReadWriteMemoryWitness.new F programIo loadStoreFlags preprocessing.toReadWriteMemoryPreprocessing trace
  let rangeCheckWitness := RangeCheckWitness.new F rwMemoryWitness.getReadTimestamps
  { toBytecodeWitness := bytecodeWitness,
    toReadWriteMemoryWitness := sorry,
    toRangeCheckWitness := rangeCheckWitness,
    toInstructionLookupsWitness := instructionLookupsWitness }


end Generation

section MemoryChecking




section ReadOnly





end ReadOnly


section ReadWrite




end ReadWrite


section Lookup



end Lookup


section RangeCheck




end RangeCheck



end MemoryChecking

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

def R1CSWitness.isValid (w : R1CSWitness F) : Bool :=
  w.programCounter.size % w.paddedTraceLength.toNat = 0 &&
  w.bytecodeAddress.size % w.paddedTraceLength.toNat = 0 &&
  w.bytecodeValue.size % w.paddedTraceLength.toNat = 0 &&
  w.memoryAddressReadWrite.size % w.paddedTraceLength.toNat = 0 &&
  w.memoryValueReads.size % w.paddedTraceLength.toNat = 0 &&
  w.memoryValueWrites.size % w.paddedTraceLength.toNat = 0 &&
  w.chunksX.size % w.paddedTraceLength.toNat = 0 &&
  w.chunksY.size % w.paddedTraceLength.toNat = 0 &&
  w.chunksQuery.size % w.paddedTraceLength.toNat = 0 &&
  w.lookupOutputs.size % w.paddedTraceLength.toNat = 0 &&
  w.circuitFlagsBits.size % w.paddedTraceLength.toNat = 0 &&
  w.instructionFlagsBits.size % w.paddedTraceLength.toNat = 0


end R1CS


end Jolt
