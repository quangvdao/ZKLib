import Mathlib.Data.Nat.Basic

def first (xs : List α) : Option α := xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third => some (first, third)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def firstThird' (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
    andThen xs[2]? fun third =>
      some (first, third)

def firstThird'' (xs : List α) : Option (α × α) :=
  andThen (first xs) (λ x => andThen (xs[2]?) (λ y => some (x, y)))

#eval firstThird [1, 2, 3]
#eval firstThird' [1, 2, 3]
#eval firstThird'' [1, 2, 3]

inductive Except' (ε : Type) (α : Type) : Type
  | ok : α → Except' ε α
  | err : ε → Except' ε α
deriving BEq, Hashable, Repr

def get (xs : List α) (i : Nat) : Except' String α :=
  match xs[i]? with
  | none => Except'.err s!"Index {i} out of bounds (maximum is {xs.length - 1})"
  | some x => Except'.ok x

def plants : List String := ["🌱", "🌷", "🌸", "🌹", "🌻", "🌼", "🌾", "🌿"]

#eval get plants 0
#eval get plants 10

def first' (xs : List α) : Except' String α := get xs 0

def ok' (x : α) : Except' ε α := Except'.ok x

def fail' (e : ε) : Except' ε α := Except'.err e

def andThen' (opt : Except' ε α) (next : α → Except' ε β) : Except' ε β :=
  match opt with
  | Except'.ok x => next x
  | Except'.err e => Except'.err e

infixl:55 " ~~> " => andThen'

def firstThird''' (xs : List α) : Except' String (α × α) :=
  first' xs ~~> fun x =>
    get xs 2 ~~> fun y =>
      ok' (x, y)

class Monad' (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β

instance : Monad' Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad' (Except' ε) where
  pure x := Except'.ok x
  bind attempt next :=
    match attempt with
    | Except'.ok x => next x
    | Except'.err e => Except'.err e

def pure' [Monad' m] (x : α) : m α := Monad'.pure x

infixl:55 " >>=' " => Monad'.bind

def firstThirdFifth [Monad' m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α) :=
  lookup xs 0 >>=' fun first =>
    lookup xs 2 >>=' fun third =>
      lookup xs 4 >>=' fun fifth =>
        pure' (first, third, fifth)

def firstThirdFifth' [Monad' m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α) :=
  Monad'.bind (lookup xs 0) (fun first =>
    Monad'.bind (lookup xs 2) (fun third =>
      Monad'.bind (lookup xs 4) (fun fifth =>
        Monad'.pure (first, third, fifth))))

#eval firstThirdFifth get plants
#eval firstThirdFifth' get plants

theorem triv (a b : Nat) (h : a < b) (h' : a ≥ b) : False :=
  Nat.not_lt_of_ge h' h

#eval triv 1 2 (by decide) (by decide)
