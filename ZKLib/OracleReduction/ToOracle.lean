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

/-- Defining oracle access to univariate polynomials -/
instance instToOraclePolynomial : ToOracle R[X] where
  Query := R
  Response := R
  oracle := fun poly point => poly.eval point

instance instToOraclePolynomialDegreeLE : ToOracle (R⦃≤ d⦄[X]) where
  Query := R
  Response := R
  oracle := fun ⟨poly, _⟩ point => poly.eval point

instance instToOraclePolynomialDegreeLT : ToOracle (R⦃< d⦄[X]) where
  Query := R
  Response := R
  oracle := fun ⟨poly, _⟩ point => poly.eval point

instance instToOracleMvPolynomial : ToOracle (R[X σ]) where
  Query := σ → R
  Response := R
  oracle := fun poly point => eval point poly

instance instToOracleMvPolynomialDegreeLE : ToOracle (R⦃≤ d⦄[X σ]) where
  Query := σ → R
  Response := R
  oracle := fun ⟨poly, _⟩ point => eval point poly

end Polynomial

section Vector

variable {n : ℕ} {α : Type}

instance instToOracleForallFin : ToOracle (Fin n → α) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec i

instance instToOracleMathlibVector : ToOracle (Mathlib.Vector α n) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec[i]

instance instToOracleBatteriesVector : ToOracle (Batteries.Vector α n) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec[i]

end Vector
