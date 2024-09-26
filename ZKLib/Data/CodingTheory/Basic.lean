/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange

/-!
  # Basic Definitions for Codes

  An error-correcting code `C` over a field `F` is a subset of `F^n` for some `n ∈ ℕ+`. It is a linear code if `C` is a linear subspace of `F^n`.

  We define the block length, rate, and distance of `C`. We prove simple properties of linear codes such as the singleton bound.
-/


section CodingTheory

open Finset Function

variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]

-- A linear code is a linear map from `R ^ k` to `R ^ n`

#check FiniteDimensional.finrank

end CodingTheory
