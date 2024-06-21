import Mathlib.Data.Nat.Basic

/- Motivation for Monads -/

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

def State (σ : Type) (α : Type) : Type := σ → (σ × α)

def State.ok (x : α) : State σ α := fun s => (s, x)

def State.get : State σ σ := fun s => (s, s)

def State.put (s : σ) : State σ Unit := fun _ => (s, ())

def State.andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', a) := first s
    next a s'

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

def WithLog.ok (x : α) : WithLog logged α :=
  { log := [], val := x }

def WithLog.save (data : logged) : WithLog logged Unit :=
  { log := [data], val := () }

def WithLog.andThen (result : WithLog logged α) (next : α → WithLog logged β) : WithLog logged β :=
  let { log := log, val := val } := result
  let { log := logNext, val := valNext } := next val
  { log := log ++ logNext, val := valNext }

/- Introducing Monads -/

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

instance : Monad' (State σ) where
  pure x := State.ok x
  bind first next :=
    fun s =>
      let (s', a) := first s
      next a s'

instance : Monad' (WithLog logged) where
  pure x := WithLog.ok x
  bind result next :=
    WithLog.andThen result (fun x => next x)

instance : Monad' Id where
  pure x := x
  bind x next := next x

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

def mapM [Monad' m] (f : α → m β) : List α → m (List β)
  | [] => pure' []
  | x :: xs =>
    f x >>=' fun hd =>
    mapM f xs >>=' fun tl =>
    pure' (hd :: tl)

def increment (howMuch : Int) : State Int Int :=
  fun s => (s + howMuch, s)

def increment' (howMuch : Int) : State Int Int :=
  State.get >>=' fun s =>
    State.put (s + howMuch) >>=' fun _ =>
      State.ok s

#eval increment' 2 3

-- Start at 0, increment by the list of numbers
#eval mapM increment [1, 2, 3] 0

def saveIfOdd (i : Int) : WithLog Int Int :=
  (if i % 2 == 1 then WithLog.save i else WithLog.ok ()) >>=' fun _ =>
    WithLog.ok i

#eval mapM saveIfOdd [1, 2, 3, 4, 5]

-- When it's the Identity Monad, mapM reduces to map
#eval mapM (m := Id) (fun x => x + 1) [1, 4, 7, 10]


/- Laws that Monad should satisfy (see LawfulMonad):
- `pure` should be a right identity of `bind`, e.g. `bind (pure v) f = pure (f v)`
- `pure` should be a left identity of `bind`, e.g. `bind v pure = v`
- `bind` should be associative, e.g. `bind (bind v f) g  = bind v (fun x => bind (f x) g)`
-/


/- Example : Arithmetic in Monads -/

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special


def applyPrim [Monad' m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure' (x + y)
  | Prim.minus, x, y => pure' (x - y)
  | Prim.times, x, y => pure' (x * y)
  | Prim.other f, x, y => applySpecial f x y


def evalM [Monad' m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const n => pure' n
  | Expr.prim f x y =>
    evalM applySpecial x >>=' fun x' =>
    evalM applySpecial y >>=' fun y' =>
    applyPrim applySpecial f x' y'

def applyEmpty [Monad' m] : Empty → Int → Int → m Int :=
  fun op _ _ => nomatch op

#eval evalM (m := Id) applyEmpty (Expr.prim Prim.plus (Expr.const 4) (Expr.const 2))

-- TODO: add stuff about Many


def Reader (ρ : Type) (α : Type) : Type := ρ → α

def Reader.read : Reader ρ ρ := fun env => env

def Reader.pure (result : α) : Reader ρ α := fun _ => result

def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β := fun env => next (result env) env

instance : Monad' (Reader ρ) where
  pure result := Reader.pure result
  bind result next := Reader.bind result next

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", fun x y => x % y)]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  Reader.read >>=' fun env =>
    match env.lookup op with
    | none => Reader.pure 0
    | some f => Reader.pure (f x y)

open Expr Prim in
#eval evalM (m := Reader Env) applyPrimReader (prim (other "max") (const 3) (const 5)) exampleEnv

open Expr Prim in
#eval evalM (m := Reader Env) applyPrimReader (prim (other "mod") (const 9) (const 5)) exampleEnv

-- TODO: add tracing evaluator



/- do-Notation for Monads -/

#print IO.getStdout
