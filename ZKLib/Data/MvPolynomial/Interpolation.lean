/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Common
import ZKLib.Data.MvPolynomial.Degrees

/-!
  # Interpolation of multivariate polynomials

  Theory of interpolation for `MvPolynomial` with individual bounds on `degreeOf`. Follows from a
  combination of the univariate case (see `Lagrange.lean`) and the tensor structure of
  `MvPolynomial`.

  ## Main definitions

  ### Notation

  ## Tags
  multivariate polynomial, interpolation, multivariate Lagrange
-/

noncomputable section

namespace MvPolynomial

section MvPolynomialDetermination

universe u v

#check Polynomial.degreeLE

variable {σ : Type u} [Fintype σ] {R : Type v} [CommRing R] [IsDomain R] {f g : MvPolynomial σ R}

section Finset

open Function Fintype

variable (s : σ → Finset R)

@[reducible]
def prodSet : Set (σ → R) := { f : σ → R | ∀ i : σ, f i ∈ s i }

theorem eq_zero_of_degreeOf_lt_of_eval_prod_finset_eq_zero
    (degreeOf_f_lt : ∀ i : σ, f.degreeOf i < (s i).card)
    (eval_f : ∀ x ∈ prodSet s, eval x f = 0) : f = 0 := by
  let d := f.support

  -- Restrict this to f.support, which is finite, then reduce further to univariate case
  sorry

#check MvPolynomial.restrictDegree

end Finset


end MvPolynomialDetermination

section Interpolation

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} {i j : ι}

/-- Define basis polynomials for interpolation -/
protected def basis : F := sorry

end Interpolation


end MvPolynomial

end
