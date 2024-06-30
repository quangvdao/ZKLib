import Mathlib.Tactic.Common
import Mathlib.Control.Random

open scoped Classical

variable {α : Type*} {β : α → Type*}

inductive Comp : Type _ → Type _ :=
| ret {A : Type _} [DecidableEq A] : A → Comp A
| bind {A : Type _} {B : Type _} : Comp B → (B → Comp A) → Comp A
| repeat {A : Type _} : Comp A → (A → Bool) → Comp A → (A → Bool) → Comp A
| rnd : ∀ n, Comp (BitVec n)

inductive OracleComp : Type _ → Type _ → Type _ → Type _ where
| query (A B : Type _) : A → OracleComp A B B
| run (A B C A' B' S : Type _) : OracleComp A B C → S → (S → A → OracleComp A' B' (B × S)) → OracleComp A' B' (C × S)
| ret (A B C : Type _) : Comp C → OracleComp A B C
| bind (A B C C' : Type _) : OracleComp A B C → (C → OracleComp A B C') → OracleComp A B C'

-- def oneTimePad (n : ℕ) (x : BitVec n) : Comp (BitVec n) :=
--   Comp.ret (Comp.rnd n)

-- def double (x : ℕ) := x * 2

class Fix (α : Type*) where
  fix : (α → α) → α

-- instance (α : Type*) : Fix α where
--   fix f := f (fix f)
