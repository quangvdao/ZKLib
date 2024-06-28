import Mathlib.Data.Matrix.Hadamard
import Jolt.Relation.Basic

/-!
# R1CS

This file defines the R1CS (Rank-1 Constraint System) relation.

-/

namespace R1CS

open Matrix

-- Bundle R and its CommSemiring instance
structure RingParams where
  R : Type _
  [commSemiring : CommSemiring R]

-- Make the CommSemiring instance accessible
attribute [instance] RingParams.commSemiring

structure Index (pp : RingParams) where
  m : ℕ -- number of columns
  inputSize : ℕ
  witnessSize : ℕ
  A : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) pp.R
  B : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) pp.R
  C : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) pp.R

@[simp]
def Index.n (index : Index pp) : ℕ := 1 + index.inputSize + index.witnessSize

structure Statement (pp : RingParams) (index : Index pp) where
  x : Fin index.inputSize → pp.R

structure Witness (pp : RingParams) (index : Index pp) where
  w : Fin index.witnessSize → pp.R


-- Relation instance for R1CS
instance relation (pp : RingParams) (index : Index pp) : Relation RingParams Index where
  Statement := Statement pp index
  Witness := Witness pp index
  isValid := fun stmt wit =>
    let z : Fin index.n → pp.R := Fin.append (Fin.append (λ _ => 1) stmt.x) wit.w
    (index.A *ᵥ z) * (index.B *ᵥ z) = (index.C *ᵥ z)

instance relationFamily (pp : RingParams) : RelationFamily RingParams where
  Index := Index
  Relation := relation pp

end R1CS
