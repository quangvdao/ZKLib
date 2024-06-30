
import Mathlib.Control.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sups

/-!
  # The basic resumption monad

  This is an attempted port of the resumption monad from the corresponding [Haskell library](https://hackage.haskell.org/package/monad-resumption-0.1.4.0/docs/Control-Monad-Resumption.html).
-/

universe u v w

inductive Free (F : Type u → Type v) (α : Type w) : Type (max u v w + 1) where
  | pure : α → Free F α
  | free : ∀ (β : Type u), F β → (β → Free F α) → Free F α

-- Attempted definition using Haskell-like syntax
-- def ResM' (α : Type u) : Type _ := Sum α (ResM' α)

inductive ResM (α : Type u) : Type u where
  | done : α → ResM α
  | pause : ResM α → ResM α

def ResM.size : ResM α → Nat
  | done _ => 1
  | pause r => r.size + 1

instance : SizeOf (ResM α) where
  sizeOf := ResM.size

/-- Helper function for bind of `ResM` -/
def ResM.bindAux {α β : Type u} (f : α → ResM β) : ResM α → ResM β
  | done a => f a
  | pause r => pause (bindAux f r)
termination_by r => r.size
decreasing_by
  apply Nat.lt_succ_self

instance : Monad ResM where
  pure := ResM.done
  bind := fun r f => ResM.bindAux f r


def StateResM (σ α : Type u) := StateT σ ResM α


-- Attempted translation from Haskell, does not work
-- def ResT (m : Type u → Type v) (α : Type w) : Type (max u v w) := m (Sum α (ResT m α))

-- This seems to be more difficult to show well-founded recursion
-- inductive ResT (m : Type u → Type v) (α : Type u) : Type (max u v) where
--   | done : α → ResT m α
--   | pause : (ULift m) (ResT m α) → ResT m α

-- instance MonadLift m (ResT m) := sorry


/-- Reactive resumption monad -/
inductive ReacM (input : Type u) (output : Type v) (α : Type w) : Type (max u v w) where
  | done : α → ReacM input output α
  | pause : output × (input → ReacM input output α) → ReacM input output α


/- I don't think this size function necessarily terminates
  What if you have something like `input = {0, 1}`, and `1 ↦ pause^n done` for arbitrarily large `n`?
-/
-- def ReacM.size [Fintype input] : ReacM input output α → Nat
--   | done _ => 1
--   | pause ⟨_, f⟩ => 1 + Finset.sup Finset.univ (fun i => (f i).size)
-- termination_by r => r.size
-- decreasing_by
--   apply Nat.lt_succ_self


instance [Fintype input] : SizeOf (ReacM input output α) where
  sizeOf := ReacM.size

/-- Helper function for bind of `ReacM` -/
-- def ReacM.bindAux {α β : Type u} (f : α → ReacM input output β) : ReacM input output α → ReacM input output β
--   | done a => f a
--   | pause r => pause (bindAux f r)
-- termination_by r => r.size
-- decreasing_by
--   apply Nat.lt_succ_self

instance : Monad ResM where
  pure := ResM.done
  bind := fun r f => ResM.bindAux f r
