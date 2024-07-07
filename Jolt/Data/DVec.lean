import Mathlib.Data.Matrix.DMatrix
import Mathlib.Data.Fin.Tuple.Curry

/-!
  # Dependent vectors
-/

def addUnitApp (m : Type v) (α : m → Type u) : m → Unit → Type (max u v) :=
  fun i _ => α i

/--
  A dependent vector of length `n`, indexed by `Fin n`,
  that is, a function `Fin n → α`.
-/
def DVec (m : Type v) (α : m → Type u) : Type (max u v) := ∀ i, α i

def DVec' (m : Type v) (α : m → Unit → Type u) : Type (max u v) := DMatrix m Unit α
