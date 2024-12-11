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
  A : Matrix (Fin m) (Fin (inputSize + witnessSize)) R
  B : Matrix (Fin m) (Fin (inputSize + witnessSize)) R
  C : Matrix (Fin m) (Fin (inputSize + witnessSize)) R

abbrev Index.n (index : Index R) : ℕ := index.inputSize + index.witnessSize

structure Statement (index : Index R) where
  x : Fin index.inputSize → R

structure Witness (index : Index R) where
  w : Fin index.witnessSize → R

-- The R1CS relation
def rel (index : Index R) : (Statement R index) → (Witness R index) → Prop :=
  fun stmt wit =>
    let z : Fin index.n → R := Fin.append stmt.x wit.w
    (index.A *ᵥ z) * (index.B *ᵥ z) = (index.C *ᵥ z)

#print rel

end R1CS
