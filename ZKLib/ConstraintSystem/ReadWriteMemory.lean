import ZKLib.ConstraintSystem.Constants
import ZKLib.ConstraintSystem.Field
import ZKLib.ConstraintSystem.Trace

/-!
  # Read-Write Memory Checking in Jolt

  We cover the read-write memory checking argument in Jolt.

  First, we model the memory as consisting of read/write operations. We then prove that the argument system for proving this in Jolt, once their guarantees (i.e. multiset equality, range checks) are satisfied, form a refinement of the memory model.
-/


namespace Jolt

variable (F : Type) [JoltField F]


-- TODO: define an abstract memory model with reads/writes operations, and state the guarantees with respect to this model
-- We should use `MemoryOp` from `Trace.lean`

namespace ReadWriteMemory

/--
  Preprocessing for the read-write memory checking argument.
  Consists of the bytecode and the program IO.
 -/
structure Preprocessing where
  minBytecodeAddress : UInt64
  bytecodeBytes : Array UInt8
  programIo : Option Device
deriving Repr, Inhabited, DecidableEq

def Preprocessing.new (memoryInit : Array (UInt64 × UInt8)) : Preprocessing :=
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


structure Witness where
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
deriving Repr, Inhabited, DecidableEq

structure WitnessRangeCheck where
  readTimestamps : Fin MEMORY_OPS_PER_INSTRUCTION → Array UInt64
  readCtsReadTimestamp : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  readCtsGlobalMinusRead : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  finalCtsReadTimestamp : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
  finalCtsGlobalMinusRead : Fin MEMORY_OPS_PER_INSTRUCTION → Array F
deriving Repr, Inhabited, DecidableEq

-- Multiset equality of the vectors of field elements
def isValid (preprocessing : Preprocessing) (wit : Witness F) : Prop := sorry

-- Each field element is in a small range
-- Alternatively, there exists small `Fin n` elements that map to the field elements
def WitnessRangeCheck.isValid (wit : WitnessRangeCheck F) : Prop := sorry

end ReadWriteMemory

end Jolt
