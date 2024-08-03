import Jolt.ConstraintSystem.Subtable.Basic

/-!
  # Interface for Instructions in Jolt
-/

namespace Jolt

variable (F : Type) [JoltField F]

-- `F` must be big enough

/--
  Interface for an instruction in Jolt.

  Here, `C` is the "dimension" of the decomposition, i.e. the number of values read from each subtable, and `logM` is the number of bits for the subtable.
-/
class Instruction (C : Nat) (logM : Nat) where
  -- The first operand of the instruction. Should be `C * (logM / 2)` bits.
  firstOperand : Fin (C * 2 ^ (logM / 2))

  -- The second operand of the instruction
  secondOperand : Fin (C * 2 ^ (logM / 2))

  -- The number of subtables used by the instruction
  numSubtables : Nat

  -- The subtables used by the instruction
  subtables : Fin numSubtables → LassoSubtable F logM

  -- Combine table lookups into final value
  -- Here, `vals` is modeled as a list of `C`-length vectors of the subtables.
  combineLookups : (vals : Fin numSubtables → Fin C → LassoSubtable F logM) → F

  -- The degree of the `g` polynomial described by `combineLookups`
  combineDegree : Nat

  -- The lookup entry of the instruction
  lookupEntry : UInt64
-- deriving Repr, Inhabited, DecidableEq

class InstructionSet (C : Nat) (logM : Nat) where
  numInstructions : Nat
  instructions : Fin numInstructions → Instruction F C logM
-- deriving Repr, Inhabited, DecidableEq

end Jolt
