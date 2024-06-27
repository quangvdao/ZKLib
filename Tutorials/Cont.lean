def Cont (r : Type u) (α : Type w) := (α → r) → r

namespace Cont

variable {r : Type u} {α : Type v}

def pure (x' : α) : Cont r α := fun f => f x'

def bind (x : Cont r α) (f : α → Cont r β) : Cont r β := fun g => x (fun a => f a g)

instance : Monad (Cont r) where
  pure := pure
  bind := bind

-- Example functions
def double (x : Nat) : Cont r Nat :=
  pure (x * 2)

def addThree (x : Nat) : Cont r Nat :=
  pure (x + 3)

def earlyReturn (x : r) : Cont r a :=
  fun _ => x

-- Example usage
def computation : Cont r Nat :=
  do
    let x ← pure 5
    let y ← double x
    let z ← addThree y
    double z

def computationWithEarlyReturn : Cont Nat Nat :=
  do
    let x ← pure 5
    let y ← double x
    if y > 8 then
      earlyReturn 100
    else
      addThree y

-- Run the computations
def runCont {a : Type} (c : Cont a a) : a :=
  c (fun x => x)

#eval runCont computation  -- Expected: 26
#eval runCont computationWithEarlyReturn  -- Expected: 100

#check Id.run

end Cont
