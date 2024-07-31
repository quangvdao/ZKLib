import Jolt.ConstraintSystem.Constants
import Jolt.ConstraintSystem.Field
import Jolt.ConstraintSystem.Trace
import Jolt.ConstraintSystem.Preprocessing
import Jolt.ConstraintSystem.R1CS
import Jolt.ConstraintSystem.InstructionLookup
import Jolt.ConstraintSystem.MemoryChecking

/-!
  # The Jolt Relation

  This file contains the specification for the Jolt relation, which is a combination of R1CS,
  lookups, and memory-checking (both read-only and read-write).

  We will show that the Jolt relation is exactly equal to the execution of RISC-V programs.

  Many of our specification draws directly from the main [Rust codebase](https://github.com/a16z/jolt).
-/


namespace Jolt

variable (F : Type) [Field F] [Fintype F] [Inhabited F] [FromUInt64 F]

section Witness

-- TODO: define a class that says you can embed `UInt64` into `F`

structure BytecodeWitness where
  readWriteAddress : Array F
  readWriteValue : Fin NUM_BYTECODE_VALUE_FIELDS → Array F
  readTimestamp : Array F
  finalBytecodeTimestamp : Array F
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


end Witness


end Jolt
