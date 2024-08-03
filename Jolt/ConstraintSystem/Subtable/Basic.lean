import Jolt.ConstraintSystem.Field
import Jolt.ConstraintSystem.Constants
import Jolt.Data.ComputablePolynomial.Multilinear

/-!
  # Interface for Lasso Subtables in Jolt

  This fine defines the basic interface for Lasso subtables.
-/


namespace Jolt

variable (F : Type) [JoltField F]

/- Represents a subtable in the Jolt system. This is essentially a wrapper around a `MlPoly`. -/
class LassoSubtable (logM : Nat) where
  /-- Returns the `Id` of this subtable. -/
  subtableId : Nat

  /-- The multilinear polynomial that represents this subtable.
  TODO: This should be a `MlPoly` of length `2 ^ logM`. -/
  poly : MlPoly F
deriving Repr, Inhabited, DecidableEq


/- Represents a set of Jolt subtables. -/
class SubtableSet (logM : Nat) where
  numSubtables : Nat
  subtables : Fin numSubtables → LassoSubtable F logM
deriving Repr, Inhabited, DecidableEq



/- Which subtables to cover?

`And`
`DivByZero`
`Eq`
`EqAbs`
`Identity`
`LeftIsZero`
`LeftMsb`
`LtAbs`
`Ltu`
`Mod`
`Or`
`RightIsZero`
`RightMsb`
`SignExtend`
`Sll`
`SraSign`
`Srl`
`Test`
`TruncateOverflow`
`Xor`
`ZeroLsb`

-/

end Jolt
