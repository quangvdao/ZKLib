import Jolt.ConstraintSystem.Constants
import Jolt.ConstraintSystem.Field
import Jolt.ConstraintSystem.Subtable.Basic
import Jolt.ConstraintSystem.Instruction.Basic
import Jolt.Relation.Lookup

/-!
  # Lookup Relations in Jolt
-/

namespace Jolt

variable (F : Type) [JoltField F]


namespace InstructionLookup

structure Preprocessing where
  subtableToMemoryIndices : Array (Array UInt64)
  instructionToMemoryIndices : Array (Array UInt64)
  memoryToSubtableIndex : Array UInt64
  memoryToDimensionIndex : Array UInt64
  materializedSubtables : Array (Array F)
  numMemories : UInt64
deriving Repr, Inhabited


-- TODO: this definition depends on the `InstructionSet` and `SubtableSet`
-- for a given architecture (i.e. RV32IM)
def Preprocessing.new (instructionSet : InstructionSet F C logM) (subtableSet : SubtableSet F logM) : Preprocessing F := sorry


structure Witness (C : Nat) (logM : Nat) where
  /- The number of various operations -/
  numMemories : Nat
  numLookups : Nat
  numInstructions : Nat

  dim : Fin C → Fin numLookups → F
  readCts : Fin numMemories → Fin numLookups → F
  finalCts : Fin numMemories → Fin numLookups → F
  evalMemories : Fin numMemories → Fin numLookups → F
  instructionFlags : Fin numInstructions → Fin numLookups → F
  lookupOutputs : Fin numLookups → F
deriving Repr, Inhabited

-- TODO: define the relation that this is supposed to satisfy (i.e. all lookups are correct)


end InstructionLookup

end Jolt
