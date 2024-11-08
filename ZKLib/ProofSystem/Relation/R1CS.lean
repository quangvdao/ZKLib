/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Matrix.Hadamard
/-!
# R1CS

This file defines the R1CS (Rank-1 Constraint System) relation.

-/

namespace R1CS

open Matrix

-- Note: we can define separately instances of `R`

variable (R : Type) [CommSemiring R]

structure Index where
  m : ℕ -- number of columns
  inputSize : ℕ
  witnessSize : ℕ
  A : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
  B : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
  C : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R

abbrev Index.n (index : Index R) : ℕ := 1 + index.inputSize + index.witnessSize

structure Statement (index : Index R) where
  x : Fin index.inputSize → R

structure Witness (index : Index R) where
  w : Fin index.witnessSize → R

-- Relation structure for R1CS
def R1CSRel (index : Index R) : (Statement R index) → (Witness R index) → Prop :=
  fun stmt wit =>
    let z : Fin index.n → R := Fin.append (Fin.append (fun _ => 1) stmt.x) wit.w
    (index.A *ᵥ z) * (index.B *ᵥ z) = (index.C *ᵥ z)

-- instance relation (index : Index R) : Relation (Statement index) (Witness index) where
--   isValid := fun stmt wit =>
--     let z : Fin index.n → R := Fin.append (Fin.append (λ _ => 1) stmt.x) wit.w
--     (index.A *ᵥ z) * (index.B *ᵥ z) = (index.C *ᵥ z)
  -- Statement := fun pp index => Statement pp index
  -- Witness := fun pp index => Witness pp index

end R1CS
