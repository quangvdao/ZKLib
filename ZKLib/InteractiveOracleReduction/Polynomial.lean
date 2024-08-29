/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
-- import ZKLib.InteractiveOracleProof.Basic


variable {R : Type _} [CommSemiring R]

def InfiniteVariablesMvPolynomial := MvPolynomial ℕ R


/-!
  # Polynomial IOPs

  This file defines polynomial IOPs as an instance of IOPs with polynomial queries.

  There will be two flavors? One using noncomputable types (Polynomial and MvPolynomial) and one using computable types (UniPoly and MlPoly)?
-/