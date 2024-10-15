/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.Data.MvPolynomial.Notation
import ZKLib.Data.MvPolynomial.Interpolation

/-!
  # Multilinear Polynomials

  This is the special case of polynomial interpolation, when we consider multilinear polynomials and
  evaluation on the hypercube `{0, 1}^n`.
-/

noncomputable section

open MvPolynomial BigOperators

universe u

variable {σ : Type*} {R : Type*} [CommRing R] {n : ℕ}


instance coeVecFin2 : Coe (Fin n → Fin 2) (Fin n → R) where
  coe := fun vec => fun i => vec i

-- Multilinear polynomials defined in Mathlib
abbrev MultilinearPolynomial := MvPolynomial.restrictDegree σ R 1

abbrev singleEqPolynomial (r : R) (x : MvPolynomial σ R) : MvPolynomial σ R :=
  (1 - C r) * (1 - x) + C r * x

abbrev eqPolynomial (r : Fin n → R) : MvPolynomial (Fin n) R :=
  ∏ i : Fin n, singleEqPolynomial (r i) (X i)

theorem eqPolynomial_expanded (r : Fin n → R) :
    eqPolynomial r = ∏ i : Fin n, ((1 - C (r i)) * (1 - X i) + C (r i) * X i) := rfl

theorem singleEqPolynomial_symm (r : R) (s : R) :
    (singleEqPolynomial r (C s) : MvPolynomial σ R) = singleEqPolynomial s (C r) := by ring_nf

theorem eqPolynomial_symm (x : Fin n → R) (y : Fin n → R) :
    MvPolynomial.eval y (eqPolynomial x) = MvPolynomial.eval x (eqPolynomial y) := by
  simp [eqPolynomial_expanded] ; congr ; funext ; ring_nf

@[simp]
theorem singleEqPolynomial_zero (x : MvPolynomial σ R) : singleEqPolynomial (0 : R) x = 1 - x := by
  unfold singleEqPolynomial ; simp

@[simp]
theorem singleEqPolynomial_one (x : MvPolynomial σ R) : singleEqPolynomial (1 : R) x = x := by
  unfold singleEqPolynomial ; simp

@[simp]
theorem singleEqPolynomial_zeroOne_eq_ite (r : Fin 2) (x : MvPolynomial σ R) :
    singleEqPolynomial (r : R) x = if r = 0 then 1 - x else x := by
  fin_cases r <;> simp

@[simp]
theorem singleEqPolynomial_zeroOne_eq_ite' (r : Fin 2) (x : Fin 2) :
    (singleEqPolynomial (r : R) (C x) : MvPolynomial σ R) = if x = r then 1 else 0 := by
  fin_cases r <;> fin_cases x <;> simp

-- @[simp]
-- theorem singleEqPolynomial_eval_zeroOne (x : Fin n → Fin 2) (r : Fin n → Fin 2) (i : Fin n) :
--     (eval fun i => ↑↑(x i))
--     (match r i with
--     | 0 => 1 - X i
--     | 1 => X i) = 1 := by

-- @[simp]
theorem eqPolynomial_zeroOne (r : Fin n → Fin 2) : (eqPolynomial r : MvPolynomial (Fin n) R) =
    ∏ i : Fin n, if r i = 0 then 1 - X i else X i := by
  unfold eqPolynomial ; congr ; funext i ; simp

@[simp]
theorem eqPolynomial_eval_zeroOne_eq_ite (r : Fin n → Fin 2) (x : Fin n → Fin 2) :
    MvPolynomial.eval (x : Fin n → R) (eqPolynomial r) = if x = r then 1 else 0 := by
  unfold eqPolynomial ; simp
  sorry
  -- split_ifs
  -- refine' Fin.two_cases _ _ (r i)

/-- Multilinear extension of evaluations on the hypercube -/
def MLE (evals : (Fin n → Fin 2) → R) : MvPolynomial (Fin n) R :=
    ∑ x : Fin n → Fin 2, (eqPolynomial (x : Fin n → R)) * C (evals x)

theorem MLE_expanded (evals : (Fin n → Fin 2) → R) : MLE evals =
    ∑ x : Fin n → Fin 2, (∏ i : Fin n, ((1 - C (x i : R)) * (1 - X i) + C (x i : R) * X i))
     * C (evals x) := by
  unfold MLE ; congr

@[simp]
theorem MLE_eval_zeroOne (x : Fin n → Fin 2) (evals : (Fin n → Fin 2) → R) :
    MvPolynomial.eval (x : Fin n → R) (MLE evals) = evals x := by
  unfold MLE
  sorry


section DegreeOf

lemma degrees_one_minus_X (i : Fin n) :
    degrees (1 - X i : MvPolynomial (Fin n) R) = {i} := by
  rw [sub_eq_add_neg]
  have h1 : degrees (1 : MvPolynomial (Fin n) R) = ∅ := degrees_one
  have h2 : degrees (- X i : MvPolynomial (Fin n) R) = {i} := sorry
  have h3 : Multiset.Disjoint ∅ {i} := by simp
  rw [degrees_add_of_disjoint (h1 ▸ (h2 ▸ h3))]
  simp [h1, h2]

theorem singleEqPolynomial_degreeOf (r : R) (i : Fin n) :
    degreeOf i (singleEqPolynomial r (X i)) ≤ 1 := by
  unfold singleEqPolynomial
  apply le_trans (degreeOf_add_le i _ _) _
  have h_one_minus_X : degreeOf i (1 - X i : MvPolynomial (Fin n) R) = 1 := sorry
  have h_left : degreeOf i ((1 - C r) * (1 - X i)) ≤ 1 := by
    sorry
  have h_right : degreeOf i (C r * X i) ≤ 1 := by
    -- apply degreeOf_linear_le
    sorry
  apply max_le_max h_left h_right

instance eqPolynomial_is_multilinear (r : Fin n → R) :
    (eqPolynomial r) ∈ MultilinearPolynomial := by
  simp [mem_restrictDegree_iff_sup]
  -- simp [eqPolynomial]
  intro i
  have hi : degreeOf i (singleEqPolynomial (r i) (X i)) ≤ 1 := by
    unfold singleEqPolynomial
    let f : MvPolynomial (Fin n) R := (1 - r i) • (1 - X i)
    let g : MvPolynomial (Fin n) R := (r i) • X i
    sorry
    -- calc
    -- degreeOf i ((1 - r i) • (1 - X i) + (r i) • X i) = degreeOf i (f + g) := rfl
    -- _ ≤ max (degreeOf i f) (degreeOf i g) := degreeOf_add_le i f g
    -- _ ≤ max (degreeOf i f) 1 := by sorry
  sorry

instance MLE_is_multilinear (evals : (Fin n → Fin 2) → R) :
    (MLE evals) ∈ MultilinearPolynomial := by
  simp [MLE, eqPolynomial, degreeOf]
  sorry

end DegreeOf

-- TODO: add lemmas about the uniqueness of multilinear polynomials up to evaluations on hypercube

namespace MvPolynomial

def toEvalsZeroOne (p : MvPolynomial (Fin n) R) : (Fin n → Fin 2) → R :=
  fun x => MvPolynomial.eval (x : Fin n → R) p

-- instance : Function.Injective toEvalsZeroOne where
--   injective := by
--     intro x y h
--     rw [toEvalsZeroOne, toEvalsZeroOne] at h
--     sorry


-- theorem eq_evals_zeroOne_if_is_multilinear (p : @MultilinearPolynomial σ R _) :
--     p.1 = MLE p.1.toEvalsZeroOne := by
--   sorry

theorem iff_is_multilinear_eq_evals_zeroOne (p : MvPolynomial (Fin n) R) :
    p ∈ MultilinearPolynomial ↔ p = MLE p.toEvalsZeroOne := by
  sorry

theorem is_multilinear_eq_iff_eq_evals_zeroOne (p : MvPolynomial (Fin n) R)
    (q : MvPolynomial (Fin n) R) : p ∈ MultilinearPolynomial → q ∈ MultilinearPolynomial
    → (p = q ↔ p.toEvalsZeroOne = q.toEvalsZeroOne) := by
  sorry

end MvPolynomial

end
