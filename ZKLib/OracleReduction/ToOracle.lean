/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ZKLib.Data.MvPolynomial.Notation
-- import ZKLib.Data.MlPoly.Basic

/-!
  # Definitions and Instances for `ToOracle`

  We define `ToOracle` and give instances for the following:

  - Univariate and multivariate polynomials. These instances turn polynomials into oracles for which
    one can query at a point, and the response is the evaluation of the polynomial on that point.

  - Vectors. This instance turns vectors into oracles for which one can query specific positions.
-/

/-- `ToOracleData` is a type class that provides an oracle interface for a type `Message`. It
    consists of a query type `Query`, a response type `Response`, and a function `oracle` that
    transforms a message `m : Message` into a function `Query → Response`.

  In order to fit into VCV's `OracleSpec` definition, we need type classes on `Query` and
  `Response`. Thus, we define a base class `ToOracleData` without any type class information, and
  a full class `ToOracle` with type classes. -/
@[ext]
class ToOracleData (Message : Type) where
  Query : Type
  Response : Type
  oracle : Message → Query → Response

/-- `ToOracle` is a type class that provides an oracle interface for a type `Message`. It consists
    of a query type `Query`, a response type `Response`, and a function `oracle` that transforms a
    message `m : Message` into a function `Query → Response`.

  In order to fit into VCV's `OracleSpec` definition, we need type classes on `Query` and
  `Response`. Thus, we define a base class `ToOracleData` without any type class information, and
  a full class `ToOracle` with type classes. -/
@[ext]
class ToOracle (Message : Type) extends ToOracleData Message where
  [query_decidableEq' : DecidableEq Query]
  [response_decidableEq' : DecidableEq Response]
  [response_inhabited' : Inhabited Response]
  [response_fintype' : Fintype Response]

section ToOracle

variable {Message : Type} [O : ToOracle Message]

instance query_decidableEq : DecidableEq O.Query := O.query_decidableEq'
instance response_decidableEq : DecidableEq O.Response := O.response_decidableEq'
instance response_inhabited : Inhabited O.Response := O.response_inhabited'
instance response_fintype : Fintype O.Response := O.response_fintype'

end ToOracle

@[simps]
def ToOracle.toOracleSpec {ι : Type} (v : ι → Type) [O : ∀ i, ToOracle (v i)] :
    OracleSpec ι where
  domain := fun i => (O i).Query
  range := fun i => (O i).Response
  domain_decidableEq' := fun i => (O i).query_decidableEq'
  range_decidableEq' := fun i => (O i).response_decidableEq'
  range_inhabited' := fun i => (O i).response_inhabited'
  range_fintype' := fun i => (O i).response_fintype'

notation "[" term "]ₒ" => ToOracle.toOracleSpec term

section Polynomial

open Polynomial MvPolynomial

variable {R : Type} [CommSemiring R] [DecidableEq R] [Fintype R] [Inhabited R] {d : ℕ}
  {σ : Type} [DecidableEq σ] [Fintype σ]

/-- Univariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instToOraclePolynomial : ToOracle R[X] where
  Query := R
  Response := R
  oracle := fun poly point => poly.eval point

/-- Univariate polynomials with degree at most `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instToOraclePolynomialDegreeLE : ToOracle (R⦃≤ d⦄[X]) where
  Query := R
  Response := R
  oracle := fun ⟨poly, _⟩ point => poly.eval point

/-- Univariate polynomials with degree less than `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instToOraclePolynomialDegreeLT : ToOracle (R⦃< d⦄[X]) where
  Query := R
  Response := R
  oracle := fun ⟨poly, _⟩ point => poly.eval point

/-- Multivariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instToOracleMvPolynomial : ToOracle (R[X σ]) where
  Query := σ → R
  Response := R
  oracle := fun poly point => eval point poly
  query_decidableEq' := by simp!; infer_instance

/-- Multivariate polynomials with individual degree at most `d` can be accessed via evaluation
queries. -/
@[reducible, inline]
instance instToOracleMvPolynomialDegreeLE : ToOracle (R⦃≤ d⦄[X σ]) where
  Query := σ → R
  Response := R
  oracle := fun ⟨poly, _⟩ point => eval point poly
  query_decidableEq' := by simp!; infer_instance

end Polynomial

section Vector

variable {n : ℕ} {α : Type} [DecidableEq α] [Fintype α] [Inhabited α]

/-- Vectors of the form `Fin n → α` can be accessed via queries on their indices. -/
instance instToOracleForallFin : ToOracle (Fin n → α) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec i
  query_decidableEq' := by simp!; infer_instance

/-- Vectors of the form `Mathlib.Vector α n` can be accessed via queries on their indices. -/
instance instToOracleMathlibVector : ToOracle (Mathlib.Vector α n) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec[i]
  query_decidableEq' := by simp!; infer_instance

/-- Vectors of the form `Vector α n` can be accessed via queries on their indices. -/
instance instToOracleBatteriesVector : ToOracle (Vector α n) where
  Query := Fin n
  Response := α
  oracle := fun vec i => vec[i]
  query_decidableEq' := by simp!; infer_instance

end Vector
