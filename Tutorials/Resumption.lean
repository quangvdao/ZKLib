
import Mathlib.Control.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sups

/-!
  # The basic resumption monad

  This is an attempted port of the resumption monad from the corresponding [Haskell library](https://hackage.haskell.org/package/monad-resumption-0.1.4.0/docs/Control-Monad-Resumption.html).
-/

universe u v w

inductive Free (F : Type u → Type v) (α : Type w) : Type (max (max (u + 1) v) w) where
  | pure : α → Free F α
  | free : ∀ {β : Type u}, F β → (β → Free F α) → Free F α

inductive CoFree (F : Type u → Type v) (α : Type w) : Type (max (max (u + 1) v) w) where
  | cofree : ∀ {β : Type u}, α → F β → (β → CoFree F α) → CoFree F α


namespace Free

protected def bind : Free F α → (α → Free F β) → Free F β
| .pure a, f => f a
| free fc g, f =>
  free fc (fun c => g c |>.bind f)

instance instMonad : Monad (Free f) where
  pure := Free.pure
  bind := Free.bind

instance instMonadLift : MonadLift M (Free M) where
  monadLift m := free m .pure



/-! ## Now I can write `Pause` -/

inductive Pause.Op (σ : Type u) (α : Type u)
| mutate : (σ → σ) → α → Op σ α
| yield : α → Op σ α

abbrev Pause (σ : Type u) :=
  Free (Pause.Op σ)

namespace Pause

def mutate (f : σ → σ) (next : α) : Pause σ α :=
  liftM (Pause.Op.mutate f next)

def yield (a : α) : Pause σ α :=
  liftM (Pause.Op.yield (σ := σ) a)

def done (a : α) : Pause σ α :=
  .pure a

def step (code : Pause σ Unit) (state : σ) : σ × Option (Pause σ Unit) :=
  match code with
  | .pure () => (state, none)
  | .free (.mutate f next) k =>
    let code := k next
    step code $ f state
  | .free (.yield next) k => (state, k next)

def test : Pause Nat Unit := do
  mutate Nat.succ ()
  yield ()
  mutate Nat.succ ()
  yield ()
  mutate Nat.succ ()
  yield ()
  done ()

end Pause

/- A concrete example of a monad that can be seen as a `Free` monad -/

inductive PreGroup (α : Type u) : Type u where
  | ret : α → PreGroup α
  | id : PreGroup α
  | mul : PreGroup α → PreGroup α → PreGroup α
  | inv : PreGroup α → PreGroup α

def PreGroup.bindAux {α β : Type u} (f : α → PreGroup β) : PreGroup α → PreGroup β
  | PreGroup.ret a => f a
  | PreGroup.id => (PreGroup.id : PreGroup β)
  | PreGroup.mul s t => PreGroup.mul (bindAux f s) (bindAux f t)
  | PreGroup.inv s => PreGroup.inv (bindAux f s)

instance preGroupMonad : Monad PreGroup where
  pure := PreGroup.ret
  bind := fun r f => PreGroup.bindAux f r

/- Showing that `PreGroup` is an instance of a `Free` monad -/

inductive GroupF (α : Type u) : Type u where
  | id : GroupF α
  | mul : α → α → GroupF α
  | inv : α → GroupF α


-- def preGroupToFree {α : Type u} {GroupF : Type u → Type u} : PreGroup α → Free GroupF α
--   | PreGroup.ret a => Free.pure a
--   | PreGroup.id => Free.free GroupF.id (fun _ => Free.pure GroupF.id)
--   | PreGroup.mul x y => Free.free (GroupF.mul (preGroupToFree x) (preGroupToFree y)) (fun _ => Free.pure GroupF.id)
--   | PreGroup.inv x => Free.free (GroupF.inv (preGroupToFree x)) (fun _ => Free.pure GroupF.id)


-- def freeToPreGroup {α : Type u} {GroupF : Type u → Type u} : Free GroupF α → PreGroup α
--   | Free.pure a => PreGroup.ret a
--   | Free.free _ GroupF.id k => PreGroup.mul PreGroup.id (freeToPreGroup (k ()))
--   | Free.free _ (GroupF.mul x y) k => PreGroup.mul (freeToPreGroup x) (PreGroup.mul (freeToPreGroup y) (freeToPreGroup (k ())))
--   | Free.free _ (GroupF.inv x) k => PreGroup.mul (PreGroup.inv (freeToPreGroup x)) (freeToPreGroup (k ()))


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

/- The resumption monad transformer? -/
-- inductive ResT (m : Type (max u v) → Type v) (α : Type u) : Type (max u v) where
--   | deResT : m (Sum α (ResT m α)) → ResT m α

-- inductive ResT' (m : Type (max u v) → Type v) (α : Type u) : Type (max u v) where
--   | done : m (ULift α) → ResT' m α
--   | pause : m (ResT' m α) → ResT' m α

-- inductive ResM' (α : Type u) : Type u where
--   | deResM : Sum α (ResM' α) → ResM' α


-- instance MonadLift m (ResT m) := sorry


/-- Reactive resumption monad -/
inductive ReacM (input : Type u) (output : Type u) (α : Type u) : Type u where
  | done : α → ReacM input output α
  | pause : output → (input → ReacM input output α) → ReacM input output α

/-- Helper function for bind of `ReacM` -/
def ReacM.bindAux {α β : Type u} (f : α → ReacM input output β) : ReacM input output α → ReacM input output β
  | done a => f a
  | pause q r => pause q (fun i => bindAux f (r i))

instance reacMonad : Monad (ReacM input output) where
  pure := ReacM.done
  bind := fun r f => ReacM.bindAux f r

/- Reactive resumption monad transformer -/
-- inductive ReacT (input : Type u) (output : Type u) (m : Type u → Type u) (α : Type u) : Type u where
--   | deReacT : m (Sum α (ReacT input output m α)) → ReacT input output m α
