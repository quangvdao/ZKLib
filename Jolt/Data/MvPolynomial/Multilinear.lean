import Jolt.Data.MvPolynomial.Interpolation


/-!
  # Multilinear Polynomials

  This is the special case of polynomial interpolation, when we consider multilinear polynomials and evaluation on the hypercube `{0, 1}^n`.
-/

-- TODO: define custom Fin tactic for `Fin 2`
@[elab_as_elim] def Fin.two_cases {motive : Fin 2 → Sort _} (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i := by
  refine' Fin.cases _ _ i
  . exact zero
  . intro i ; simp [Fin.succ] ; exact one

@[simp]
theorem Fin.two_cases_eq_ite (x : Fin 2) (u : Type _) (v : Type _) :
    (match x with
    | 0 => u
    | 1 => v)
    = if x = 0 then u else v := by
  refine' Fin.cases _ _ x <;> simp [Fin.succ]


theorem Fin.vec_fin2_ite_eq_prod_ite {n : ℕ} {x y : Fin n → Fin 2} : (if x = y then 1 else 0) = ∏ i : Fin n, if x i = y i then 1 else 0 := by
  induction n with
  | zero => simp [Fin.prod_univ_zero] ; funext i ; apply Fin.elim0 i
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simp [ih]



noncomputable section

open MvPolynomial BigOperators

universe u

variable {F : Type u} [Field F]


instance coeVecFin2 : Coe (Fin n → Fin 2) (Fin n → R) where
  coe := fun vec => fun i => vec i


-- Should this be made into a type class?
def isMultilinear (p : MvPolynomial σ F) : Prop := ∀ n : σ, p.degreeOf n ≤ 1

class IsMultilinear (p : MvPolynomial σ F) : Prop where
  protected is_multilinear : ∀ n : σ, p.degreeOf n ≤ 1


def singleEqPolynomial (r : F) (x : MvPolynomial σ F) : MvPolynomial σ F := (1 - C r) * (1 - x) + C r * x


def eqPolynomial (r : Fin n → F) : MvPolynomial (Fin n) F :=
    ∏ i : Fin n, singleEqPolynomial (r i) (X i)


theorem eqPolynomial_expanded (r : Fin n → F) : eqPolynomial r = ∏ i : Fin n, ((1 - C (r i)) * (1 - X i) + C (r i) * X i) := by
  unfold eqPolynomial singleEqPolynomial ; congr


theorem singleEqPolynomial_symm (r : F) (s : F) : (singleEqPolynomial r (C s) : MvPolynomial σ F) = singleEqPolynomial s (C r) := by
  unfold singleEqPolynomial ; ring_nf


theorem eqPolynomial_symm (x : Fin n → F) (y : Fin n → F) : MvPolynomial.eval y (eqPolynomial x) = MvPolynomial.eval x (eqPolynomial y) := by
  simp [eqPolynomial_expanded] ; congr ; funext ; ring_nf

@[simp]
theorem singleEqPolynomial_zero (x : MvPolynomial σ F) : singleEqPolynomial (0 : F) x = 1 - x := by
  unfold singleEqPolynomial ; simp

@[simp]
theorem singleEqPolynomial_one (x : MvPolynomial σ F) : singleEqPolynomial (1 : F) x = x := by
  unfold singleEqPolynomial ; simp

@[simp]
theorem singleEqPolynomial_zeroOne_eq_ite (r : Fin 2) (x : MvPolynomial σ F) : singleEqPolynomial (r : F) x = if r = 0 then 1 - x else x := by
  refine' Fin.two_cases _ _ r <;> simp

@[simp]
theorem singleEqPolynomial_zeroOne_eq_ite' (r : Fin 2) (x : Fin 2) : (singleEqPolynomial (r : F) (C x) : MvPolynomial σ F) = if x = r then 1 else 0 := by
  refine' Fin.two_cases _ _ r <;> refine' Fin.two_cases _ _ x <;> simp

@[simp]
theorem singleEqPolynomial_eval_zeroOne (x : Fin n → Fin 2) (r : Fin n → Fin 2) (i : Fin n) : (eval fun i => ↑↑(x i))
    (match r i with
    | 0 => 1 - X i
    | 1 => X i) = 1 := by


-- @[simp]
theorem eqPolynomial_zeroOne (r : Fin n → Fin 2) : (eqPolynomial r : MvPolynomial (Fin n) F) =
    ∏ i : Fin n, match r i with
        | 0 => 1 - X i
        | 1 => X i := by
  unfold eqPolynomial ; congr ; funext i ; simp
  refine' Fin.two_cases _ _ (r i) <;> simp

@[simp]
theorem eqPolynomial_eval_zeroOne_eq_ite (r : Fin n → Fin 2) (x : Fin n → Fin 2) : MvPolynomial.eval (x : Fin n → F) (eqPolynomial r) = if x = r then 1 else 0 := by
  unfold eqPolynomial ; simp
  split_ifs
  .
  -- refine' Fin.two_cases _ _ (r i)






/-- Multilinear extension of evaluations on the hypercube -/
def multilinearExtension (evals : (Fin n → Fin 2) → F) : MvPolynomial (Fin n) F :=
    ∑ x : Fin n → Fin 2, (eqPolynomial (x : Fin n → F)) * C (evals x)

theorem multilinearExtension_expanded (evals : (Fin n → Fin 2) → F) : multilinearExtension evals =
    ∑ x : Fin n → Fin 2, (∏ i : Fin n, ((1 - C (x i : F)) * (1 - X i) + C (x i : F) * X i)) * C (evals x) := by
  unfold multilinearExtension ; congr

@[simp]
theorem multilinearExtension_eval_zeroOne (x : Fin n → Fin 2) (evals : (Fin n → Fin 2) → F) : MvPolynomial.eval (x : Fin n → F) (multilinearExtension evals) = evals x := by
  unfold multilinearExtension
  simp


section DegreeOf

lemma degrees_one_minus_X (n : ℕ) (i : Fin n) : degrees (1 - X i : MvPolynomial (Fin n) F) = {i} := by
  rw [sub_eq_add_neg]
  have h1 : degrees (1 : MvPolynomial (Fin n) F) = ∅ := degrees_one
  have h2 : degrees (- X i : MvPolynomial (Fin n) F) = {i} := degrees_monomial_eq (Finsupp.single i 1) (-1) _
  have h3 : Multiset.Disjoint ∅ {i} := by simp
  rw [degrees_add_of_disjoint h3]
  simp [h1, h2]


theorem singleEqPolynomial_degreeOf (r : F) (i : Fin n) :
    degreeOf i (singleEqPolynomial r (X i)) ≤ 1 := by
  unfold singleEqPolynomial
  apply le_trans (degreeOf_add_le i _ _) _
  have h_one_minus_X : degreeOf i (1 - X i : MvPolynomial (Fin n) F) = 1 := degrees_one_minus_X n i
  have h_left : degreeOf i ((1 - C r) * (1 - X i)) ≤ 1 := by

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

instance eqPolynomial_is_multilinear (r : Fin n → F) : IsMultilinear (eqPolynomial r) where
  is_multilinear := by
    simp [eqPolynomial, degreeOf]
    intro i
    have hi : degreeOf i (singleEqPolynomial (r i) (X i)) ≤ 1 := by
      unfold singleEqPolynomial
      let f : MvPolynomial (Fin n) F := (1 - r i) • (1 - X i)
      let g : MvPolynomial (Fin n) F := (r i) • X i
      calc
      degreeOf i ((1 - r i) • (1 - X i) + (r i) • X i) = degreeOf i (f + g) := rfl
      _ ≤ max (degreeOf i f) (degreeOf i g) := degreeOf_add_le i f g
      _ ≤ max (degreeOf i f) 1 := by sorry

instance multilinearExtension_is_multilinear (evals : (Fin n → Fin 2) → F) : IsMultilinear (multilinearExtension evals) where
  is_multilinear := by
    simp [multilinearExtension, eqPolynomial, degreeOf]
    sorry

end DegreeOf

-- TODO: add lemmas about the uniqueness of multilinear polynomials up to evaluations on hypercube

namespace MvPolynomial

def toEvalsZeroOne (p : MvPolynomial (Fin n) F) : (Fin n → Fin 2) → F :=
  fun x => MvPolynomial.eval (x : Fin n → F) p

-- instance : Function.Injective toEvalsZeroOne where
--   injective := by
--     intro x y h
--     rw [toEvalsZeroOne, toEvalsZeroOne] at h
--     sorry



theorem eq_evals_zeroOne_if_is_multilinear (p : MvPolynomial (Fin n) F) [IsMultilinear p] : p = multilinearExtension p.toEvalsZeroOne := by
  sorry

theorem iff_is_multilinear_eq_evals_zeroOne : IsMultilinear p ↔ p = multilinearExtension p.toEvalsZeroOne := by
  sorry

theorem is_multilinear_eq_iff_eq_evals_zeroOne (p : MvPolynomial (Fin n) F) (q : MvPolynomial (Fin n) F) [IsMultilinear p] [IsMultilinear q] : p = q ↔ p.toEvalsZeroOne = q.toEvalsZeroOne := by
  sorry

end MvPolynomial

end
