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

-- inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
--   | nil  : HList β []
--   | cons : β i → HList β is → HList β (i::is)


-- TODO: port over stuff from [Soup](https://github.com/crabbo-rave/Soup/tree/master)

inductive HList : List (Type u) → Type (u + 1) where
  | nil : HList []
  | cons {α : Type u} (x : α) {αs : List (Type u)} (xs : HList αs) : HList (α :: αs)

syntax (name := hlist) "[" term,* "]" : term
macro_rules (kind := hlist)
  | `([]) => `(HList.nil)
  | `([$x]) => `(HList.cons $x HList.nil)
  | `([$x, $xs,*]) => `(HList.cons $x [$xs,*])

/- HList.cons notation -/
infixr:67 " :: " => HList.cons


namespace HList

/-- Returns the first element of a HList -/
def head {α : Type u} {αs : List (Type u)} : HList (α :: αs) → α
  | x :: _ => x

/-- Returns a HList of all the elements besides the first -/
def tail {α : Type u} {αs : List (Type u)} : HList (α :: αs) → HList αs
  | _ :: xs => xs

/-- Returns the length of a HList -/
def length {αs : List (Type u)} (_ : HList αs) := αs.length

/-- Returns the nth element of a HList -/
-- @[reducible] def nth {αs : List (Type u)} : HList αs → (n : Fin αs.length) → αs.get' n
--   | x::_, ⟨0, _⟩ => x
--   | _::xs, ⟨n+1, h⟩ => xs.nth ⟨n, Nat.lt_of_succ_lt_succ h⟩

-- /- Getting the nth index -/
-- def getOp {αs : List Type} (self : HList αs) (idx : Fin' αs.length) :=
--   self.nth idx

-- def getTypes {αs : List Type} (_ : HList αs) : List Type :=
--   αs

-- def mapNthNoMetaEval : (n : Fin' αs.length) → ((αs.get' n) → β) → HList αs → HList (αs.replaceAt n β)
--   | ⟨0, _⟩, f, a::as => (f a)::as
--   | ⟨n+1, h⟩, f, a::as => a::(as.mapNthNoMetaEval ⟨n, Nat.lt_of_succ_lt_succ h⟩ f)

private def the (α : Type u) (a : α) := a

-- def mapNth (n : Fin' αs.length) (f : (αs.get' n) → β) (h : HList αs) : HList (αs.replaceAt n β) :=
--   let typeSig : List Type := αs.replaceAt n β
--   the (HList typeSig) (h.mapNthNoMetaEval n f)

end HList
