/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Basic
import ZKLib.Data.MvPolynomial.Notation
import ZKLib.Data.MlPoly.Basic

/-!
  # Instances for `ToOracle`

  We define `ToOracle` instances for the following:

  - Univariate and multivariate polynomials. These instances turn polynomials into oracles for which
    one can query at a point, and the response is the evaluation of the polynomial on that point.

  - Vectors. This instance turns vectors into oracles for which one can query specific positions.
-/

section Polynomial

open Polynomial MvPolynomial

variable {R : Type} [CommSemiring R] {d : ℕ} {σ : Type}

/-- Univariate polynomials can be accessed via evaluation queries. -/
instance instToOraclePolynomial : ToOracle R[X] where
  Query := R
  Response := R
  oracle := fun poly point => poly.eval point

/-- Univariate polynomials with degree at most `d` can be accessed via evaluation queries. -/
instance instToOraclePolynomialDegreeLE : ToOracle (R⦃≤ d⦄[X]) where
  Query := R
  Response := R
  oracle := fun ⟨poly, _⟩ point => poly.eval point

/-- Univariate polynomials with degree less than `d` can be accessed via evaluation queries. -/
instance instToOraclePolynomialDegreeLT : ToOracle (R⦃< d⦄[X]) where
  Query := R
  Response := R
  oracle := fun ⟨poly, _⟩ point => poly.eval point

/-- Multivariate polynomials can be accessed via evaluation queries. -/
instance instToOracleMvPolynomial : ToOracle (R[X σ]) where
  Query := σ → R
  Response := R
  oracle := fun poly point => eval point poly

/-- Multivariate polynomials with individual degree at most `d` can be accessed via evaluation
queries. -/
instance instToOracleMvPolynomialDegreeLE : ToOracle (R⦃≤ d⦄[X σ]) where
  Query := σ → R
  Response := R
  oracle := fun ⟨poly, _⟩ point => eval point poly

end Polynomial

section Vector

variable {n : ℕ} {α : Type}

/-- Vectors of the form `Fin n → α` can be accessed via queries on their indices. -/
instance instToOracleForallFin : ToOracle (Fin n → α) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec i

/-- Vectors of the form `Mathlib.Vector α n` can be accessed via queries on their indices. -/
instance instToOracleMathlibVector : ToOracle (Mathlib.Vector α n) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec[i]

/-- Vectors of the form `Vector α n` can be accessed via queries on their indices. -/
instance instToOracleBatteriesVector : ToOracle (Vector α n) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec[i]

end Vector
