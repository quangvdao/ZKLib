/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.ConstraintSystem.Constants
import ZKLib.ConstraintSystem.Field
import ZKLib.ConstraintSystem.Subtable.Basic
import ZKLib.ConstraintSystem.Instruction.Basic
import ZKLib.Relation.Lookup

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

def isValid (preprocessing : Preprocessing F) (witness : Witness F C logM) : Prop := sorry

end InstructionLookup

end Jolt