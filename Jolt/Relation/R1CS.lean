import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Hadamard
import Jolt.Relation.Basic

/-!
# R1CS

This file defines the R1CS (Rank-1 Constraint System) relation.

-/

namespace R1CS

open Matrix

variable {R : Type _} [CommSemiring R]

structure IndexType (R : Type _) [CommSemiring R] where
  m : ℕ -- number of columns
  inputSize : ℕ
  witnessSize : ℕ
  A : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
  B : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
  C : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R

@[simp]
def IndexType.n (index : IndexType R) : ℕ := 1 + index.inputSize + index.witnessSize

structure StmtType (R : Type _) [CommSemiring R] (index : IndexType R) where
  x : Fin index.inputSize → R

structure WitType (R : Type _) [CommSemiring R] (index : IndexType R) where
  w : Fin index.witnessSize → R

-- structure R1CS (R : Type) [Inhabited R] [Ring R] where
--   m : Nat -- number of columns
--   inputSize : Nat
--   witnessSize : Nat
--   -- TODO: define n to be this sum
--   A : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
--   B : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
--   C : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
--   x : Fin inputSize → R
--   w : Fin witnessSize → R

instance R1CSRelation (R : Type _) [CommSemiring R] : Relation R where
  Index := IndexType R
  Stmt := StmtType R
  Wit := WitType R
  isValid := fun index stmt wit =>
    let z : Fin index.n → R := Fin.append (Fin.append (λ _ => 1) stmt.x) wit.w
    (index.A *ᵥ z) * (index.B *ᵥ z) = (index.C *ᵥ z)

end R1CS
