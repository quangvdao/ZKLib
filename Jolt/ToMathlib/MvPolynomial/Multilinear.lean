import Mathlib.Data.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Polynomial.Basic

/-!
  # Multilinear Polynomials as instantiations of `MvPolynomial`

  Define multilinear extensions, prove their uniqueness, etc.
-/

noncomputable section

open MvPolynomial BigOperators

universe u v

variable {σ : Type u} {R : Type v} [CommRing R] [Nontrivial R]

def isMultilinear (p : MvPolynomial σ R) : Prop := ∀ n : σ, p.degreeOf n ≤ 1

def zeroOnePred : R → Prop := fun r => r = 0 ∨ r = 1

def zeroOneSet : Set R := {r : R | zeroOnePred r}

instance zeroOneSetFinset : Finset R where
  val := {0, 1}
  nodup := by simp

-- def sumOverHyperCube (n : ℕ) (p : MvPolynomial (Fin n) R) : R :=
--   sumFinset n zeroOneSetFinset p


-- def MlPolynomial (σ : Type u) (R : Type v) := {p : MvPolynomial σ R // isMultilinear p}

-- instance [CommSemiring R] : CommMonoid (MlPolynomial σ R) := inferInstance

/- Note: it's not immediate that this is a multilinear polynomial -/
def EqPolynomial (n : ℕ) (r : Fin n → R) : MvPolynomial (Fin n) R :=
  ∏ i : Fin n,
    ((1 - r i) • (1 - X i) + C (r i) • X i)


theorem EqPolynomial_isMultilinear (n : ℕ) (r : Fin n → R) : isMultilinear (EqPolynomial n r) := sorry


def MlExtension (n : ℕ) (evals : List R) (evals.length = 2 ^ n) : MvPolynomial (Fin n) R := sorry


end
