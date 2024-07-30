import Mathlib.Data.Matrix.DMatrix
import Mathlib.Data.Fin.Tuple.Curry
import Mathlib.Tactic

/-!
  # Heterogeneous Lists
-/


structure Bundled where
  α : Type
  a : α

instance : Inhabited Bundled where
  default := Bundled.mk Nat 0

def test : List Bundled := [Bundled.mk Nat 1, Bundled.mk String "bad", Bundled.mk Int 3]

@[simp]
theorem test_length : test.length = 3 := rfl

#eval (test.getD 5 default).a


-- This is a port from [Soup](https://github.com/crabbo-rave/Soup/tree/master)

inductive HList : List (Type u) → Type (u + 1) where
  | nil : HList []
  | cons {α : Type u} (x : α) {αs : List (Type u)} (xs : HList αs) : HList (α :: αs)

syntax (name := hlist) "[" term,* "]ₕ" : term
macro_rules (kind := hlist)
  | `([]ₕ) => `(HList.nil)
  | `([$x]ₕ) => `(HList.cons $x HList.nil)
  | `([$x, $xs,*]ₕ) => `(HList.cons $x [$xs,*]ₕ)

/- HList.cons notation -/
infixr:67 " ::ₕ " => HList.cons


namespace HList

/-- Returns the first element of a HList -/
def head {α : Type u} {αs : List (Type u)} : HList (α :: αs) → α
  | x ::ₕ _ => x

/-- Returns a HList of all the elements besides the first -/
def tail {α : Type u} {αs : List (Type u)} : HList (α :: αs) → HList αs
  | _ ::ₕ xs => xs

/-- Returns the length of a HList -/
def length {αs : List (Type u)} (_ : HList αs) := αs.length

/-- Returns the nth element of a HList -/
@[reducible]
def get {αs : List (Type u)} : HList αs → (n : Fin αs.length) → αs.get n
  | x ::ₕ _, ⟨0, _⟩ => x
  | _ ::ₕ xs, ⟨n+1, h⟩ => xs.get ⟨n, Nat.lt_of_succ_lt_succ h⟩

def getTypes {αs : List Type} (_ : HList αs) : List Type := αs

/--
`O(|join L|)`. `join L` concatenates all the lists in `L` into one list.
* `join [[a], [], [b, c], [d, e, f]] = [a, b, c, d, e, f]`
-/
-- def join {αs : List (Type u)} {βs : αs → List (Type v)} : HList (List (HList βs)) → HList αs
--   | []      => []
--   | a :: as => a ++ join as

@[simp] theorem join_nil : List.join ([] : List (List α)) = [] := rfl
@[simp] theorem join_cons : (l :: ls).join = l ++ ls.join := rfl


section Repr

class HListRepr (α : Type _) where
  repr: α → Std.Format

instance : HListRepr (HList []) where
  repr := fun _ => ""

instance [Repr α] (αs : List Type) [HListRepr (HList αs)] : HListRepr (HList (α :: αs)) where
  repr
  | HList.cons x xs =>
    match xs with
    | HList.nil => reprPrec x 0
    | HList.cons _ _ => reprPrec x 0 ++ ", " ++ HListRepr.repr xs

/-- Repr instance for HLists -/
instance (αs : List Type) [HListRepr (HList αs)] : Repr (HList αs) where
  reprPrec
  | v, _ => "[" ++ HListRepr.repr v ++ "]"

class HListString (α : Type _) where
  toString : α → String

instance : HListString (HList []) where
  toString
  | HList.nil => ""

instance [ToString α] (αs : List Type) [HListString (HList αs)] : HListString (HList (α :: αs)) where
  toString
  | HList.cons x xs =>
    match xs with
    | HList.nil => toString x
    | HList.cons _ _ => toString x ++ ", " ++ HListString.toString xs

/-- ToString instance for HLists -/
instance (αs : List Type) [HListString (HList αs)] : ToString (HList αs) where
  toString : HList αs → String
  | t => "[" ++ HListString.toString t ++ "]"

end Repr

def test : HList [Nat, String, Nat] :=
  HList.cons 1 (HList.cons "bad" (HList.cons 3 HList.nil))

#eval test

-- Okay, what do I need to define?
-- `Monad` and `LawfulMonad` instances for `HList`
-- `ForInStep` instance for `HList`

@[inline]
def pure {α : Type u} (a : α) : HList [α] := [a]ₕ

-- @[inline]
-- def bind {α : Type u} {β : Type v} (a : HList [α]) (f : α → HList [β]) : HList [β] :=
--   match a with
--   | [a]ₕ => f a
--   | _ => HList.nil

-- instance (αs : List (Type u)) : Monad (HList αs) where
--   pure := fun a => [a]ₕ
--   @bind := fun _ _ _ hla f _ => HList.nil

-- instance : LawfulMonad HList := {}


-- def mapNthNoMetaEval : (n : Fin αs.length) → ((αs.get n) → β) → HList αs → HList (αs.repla n β)
--   | ⟨0, _⟩, f, a::as => (f a)::as
--   | ⟨n+1, h⟩, f, a::as => a::(as.mapNthNoMetaEval ⟨n, Nat.lt_of_succ_lt_succ h⟩ f)

-- def mapNth (n : Fin' αs.length) (f : (αs.get' n) → β) (h : HList αs) : HList (αs.replaceAt n β) :=
--   let typeSig : List Type := αs.replaceAt n β
--   the (HList typeSig) (h.mapNthNoMetaEval n f)

end HList


/--
  A dependent vector of length `n`, indexed by `Fin n`,
  that is, a function `Fin n → α`.
-/
def DVec (m : Type v) (α : m → Type u) : Type (max u v) := ∀ i, α i

def DVec' (m : Type v) (α : m → Unit → Type u) : Type (max u v) := DMatrix m Unit α




inductive HList' {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList' β []
  | cons : β i → HList' β is → HList' β (i :: is)

namespace HList'

variable {α : Type v} (β : α → Type u)

inductive member (a : α) : List α → Type v where
  | first : member a (a :: is)
  | next : member a is → member a (b :: is)

def length : HList' β ls → Nat
  | nil => 0
  | cons _ xs => xs.length + 1


def get (mls : HList' β ls) : member a ls → β a := match mls with
  | nil => fun h => nomatch h
  | cons x xs => fun h => match h with
    | member.first => x
    | member.next h => get xs h

#check HList'.get

def someTypes : List Type := [Nat, String, Nat]

def someValues : HList' (fun x => x) someTypes :=
  HList'.cons 1 (HList'.cons "bad" (HList'.cons 3 HList'.nil))

#eval HList'.get (fun x => x) someValues HList'.member.first

def somePairs : HList' (fun x => x × x) someTypes :=
  HList'.cons (1, 1) (HList'.cons ("good", "bad") (HList'.cons (5, 3) HList'.nil))

#eval HList'.get (fun x => x × x) somePairs (HList'.member.next HList'.member.first)

end HList'
