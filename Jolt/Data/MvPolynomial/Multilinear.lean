import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Common
import Jolt.Data.MvPolynomial.Degrees


/-!
  # Multilinear Polynomials as instantiations of `MvPolynomial`

  Define multilinear extensions, prove their uniqueness, etc.
-/

noncomputable section

open MvPolynomial BigOperators

universe u v

variable {σ : Type u} {R : Type v} [CommRing R] [Nontrivial R]

variable {n : ℕ}


def zeroOnePred : R → Prop := fun r => r = 0 ∨ r = 1

def zeroOneSet : Set R := {r : R | zeroOnePred r}

instance zeroOneSetFinset : Finset R where
  val := {0, 1}
  nodup := by simp

def finPowToFinset (n : ℕ) : Fin (2 ^ n) → (Fin n → R) := sorry

def isMultilinear (p : MvPolynomial σ R) : Prop := ∀ n : σ, p.degreeOf n ≤ 1

-- def sumOverHyperCube (n : ℕ) (p : MvPolynomial (Fin n) R) : R :=
--   sumFinset n zeroOneSetFinset p

-- def MlPolynomial (σ : Type u) (R : Type v) := {p : MvPolynomial σ R // isMultilinear p}

-- instance [CommSemiring R] : CommMonoid (MlPolynomial σ R) := inferInstance


def singleEqPolynomial (r : R) (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R := (1 - C r) * (1 - x) + C r * x

def eqPolynomial (r : Fin n → R) : MvPolynomial (Fin n) R :=
  ∏ i : Fin n, singleEqPolynomial (r i) (X i)

/-- Multilinear extension of evaluations on the hypercube -/
def MLE (evals : Fin (2 ^ n) → R) : MvPolynomial (Fin n) R := sorry

theorem singleEqPolynomial_rewrite (r : R) : singleEqPolynomial r (X i : MvPolynomial (Fin n) R) = (2 * C r - 1) * X i + (1 - C r) := by
  unfold singleEqPolynomial
  ring_nf


section DegreeOf

lemma degrees_one_minus_X (n : ℕ) (i : Fin n) : degrees (1 - X i : MvPolynomial (Fin n) R) = {i} := by
  rw [sub_eq_add_neg]
  have h1 : degrees (1 : MvPolynomial (Fin n) R) = ∅ := degrees_one
  have h2 : degrees (- X i : MvPolynomial (Fin n) R) = {i} := degrees_monomial_eq (Finsupp.single i 1) (-1) _
  have h3 : Multiset.Disjoint ∅ {i} := by simp
  rw [degrees_add_of_disjoint h3]
  simp [h1, h2]


theorem singleEqPolynomial_degreeOf (r : R) (i : Fin n) :
    degreeOf i (singleEqPolynomial r (X i)) ≤ 1 := by
  unfold singleEqPolynomial
  apply le_trans (degreeOf_add_le i _ _) _
  have h_one_minus_X : degreeOf i (1 - X i : MvPolynomial (Fin n) R) = 1 := by
    rw [sub_eq_add_neg]

  have h_left : degreeOf i ((1 - C r) * (1 - X i)) ≤ 1 := by
    apply degreeOf_linear_le
  have h_right : degreeOf i (C r * X i) ≤ 1 := by
    apply degreeOf_linear_le
  apply max_le_max h_left h_right
  -- rw [max_def]
  -- split_ifs
  -- . simp only [smul_eq_C_mul]
  --   apply le_trans (degreeOf_C_mul_le (X i ) i r) _
  --   simp [degreeOf_X]
  -- . simp only [smul_eq_C_mul]
  --   apply le_trans (degreeOf_C_mul_le _ _ _) _
  --   apply

theorem eqPolynomial_isMultilinear (r : Fin n → R) : isMultilinear (eqPolynomial r) := by
  simp [isMultilinear, eqPolynomial, degreeOf]
  intro i
  have hi : degreeOf i (singleEqPolynomial (r i) (X i)) ≤ 1 := by
    unfold singleEqPolynomial
    let f : MvPolynomial (Fin n) R := (1 - r i) • (1 - X i)
    let g : MvPolynomial (Fin n) R := (r i) • X i
    calc
    degreeOf i ((1 - r i) • (1 - X i) + (r i) • X i) = degreeOf i (f + g) := rfl
    _ ≤ max (degreeOf i f) (degreeOf i g) := degreeOf_add_le i f g
    _ ≤ max (degreeOf i f) 1 := by sorry

theorem MLE_isMultilinear (evals : Fin (2 ^ n) → R) : isMultilinear (MLE evals) := sorry

end DegreeOf

end
