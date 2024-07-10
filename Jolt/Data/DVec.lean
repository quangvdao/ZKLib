import Mathlib.Data.Matrix.DMatrix
import Mathlib.Data.Fin.Tuple.Curry
import Mathlib.Tactic

/-!
  # Dependent vectors
-/

def addUnitApp (m : Type v) (α : m → Type u) : m → Unit → Type (max u v) :=
  fun i _ => ULift (α i)

/--
  A dependent vector of length `n`, indexed by `Fin n`,
  that is, a function `Fin n → α`.
-/
def DVec (m : Type v) (α : m → Type u) : Type (max u v) := ∀ i, α i

def DVec' (m : Type v) (α : m → Unit → Type u) : Type (max u v) := DMatrix m Unit α


-- inductive HList : List (Type u) → Type (u + 1) where
--   | nil : HList []
--   | cons {α : Type u} (x : α) {αs : List (Type u)} (xs : HList αs) : HList (α :: αs)

-- inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
--   | nil  : HList β []
--   | cons : β i → HList β is → HList β (i::is)
