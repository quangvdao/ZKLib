import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Common
import Jolt.Data.MvPolynomial.Degrees

/-!
  # Interpolation of multivariate polynomials

  Theory of interpolation for `MvPolynomial` with individual bounds on `degreeOf`. Follows from a combination of the univariate case (see `Lagrange.lean`) and the tensor structure of `MvPolynomial`.

  ## Main definitions

  ### Notation

  ## Tags
  multivariate polynomial, interpolation, multivariate Lagrange
-/

noncomputable section

namespace MvPolynomial

section MvPolynomialDetermination

universe u v

variable {σ : Type u} [Fintype σ] {R : Type v} [CommRing R] [IsDomain R] {f g : MvPolynomial σ R}

section Finset

open Function Fintype

variable (s : σ → Finset R)

@[reducible]
def prodSet : Set (σ → R) := { f : σ → R | ∀ i : σ, f i ∈ s i }

theorem eq_zero_of_degreeOf_lt_of_eval_prod_finset_eq_zero (degreeOf_f_lt : ∀ i : σ, f.degreeOf i < (s i).card) (eval_f : ∀ x ∈ prodSet s, eval x f = 0) : f = 0 := by
  let d := f.support

  -- Restrict this to f.support, which is finite, then reduce further to univariate case
  sorry


end Finset


end MvPolynomialDetermination


end MvPolynomial

end
