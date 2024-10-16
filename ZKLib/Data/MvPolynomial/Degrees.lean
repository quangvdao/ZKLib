/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import ZKLib.Data.MvPolynomial.Notation

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

universe u v w

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ τ ι : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R}

section Support

theorem support_C {r : R} [h : Decidable (r = 0)] :
    (@C R σ _ r).support = if r = 0 then ∅ else { 0 } := by
  rw [←monomial_zero', support_monomial]

theorem support_C_subset {r : R} : (@C R σ _ r).support ⊆ { 0 } := by
  rw [←monomial_zero']
  exact support_monomial_subset

theorem support_C_mul_le (p : MvPolynomial σ R) (r : R) : (C r * p).support ⊆ p.support := by
  classical
  refine le_trans (support_mul _ _) ?_
  rw [support_C]
  by_cases h : r = 0
  · simp [h]
  · simp [h, Finset.singleton_add]

theorem support_mul_C_le (p : MvPolynomial σ R) (r : R) : (p * C r).support ⊆ p.support := by
  rw [mul_comm]
  exact support_C_mul_le p r

theorem support_eval [DecidableEq σ] {τ : Type*} {f : τ → R} {p : R[X σ][X τ]} :
    (eval (C ∘ f) p).support ⊆ p.support.biUnion (fun c => (coeff c p).support) := by
  classical
  rw [eval_eq]
  refine le_trans support_sum (Finset.biUnion_mono (fun c _ => ?_))
  conv =>
    enter [1, 1, 2, 2]
    intro x
    rw [comp_apply, ←C_pow (f x)]
  rw [←map_prod]
  exact support_mul_C_le _ _

end Support

section Degrees

theorem degrees_C_mul_le (p : MvPolynomial σ R) (c : R) : (C c * p).degrees ≤ p.degrees := by
  refine le_trans (degrees_mul _ _) ?_
  simp [degrees_C]

theorem degrees_mul_C_le (p : MvPolynomial σ R) (c : R) : (p * C c).degrees ≤ p.degrees := by
  rw [mul_comm]
  exact degrees_C_mul_le p c

theorem degrees_eval [DecidableEq σ] {τ : Type*} {f : τ → R} {p : R[X σ][X τ]} :
    (eval (C ∘ f) p).degrees ≤ p.support.sup (fun c => (coeff c p).degrees)  := by
  classical
  rw [eval_eq]
  refine le_trans (degrees_sum _ _) (Finset.sup_mono_fun (fun b _ => ?_))
  conv =>
    enter [1, 1, 2, 2]
    intro x
    rw [comp_apply, ←C_pow (f x)]
  rw [←map_prod]
  exact degrees_mul_C_le _ _

end Degrees

section DegreeOf

-- TODO we can prove equality here if R is a domain
-- theorem degreeOf_mul_eq' [IsDomain R] (i : σ) (f g : MvPolynomial σ R) :
--     degreeOf i (f * g) = degreeOf i f + degreeOf i g := by
--   classical
--   repeat' rw [degreeOf]
--   simp [degreeOf]

-- TODO in the following we have equality iff f ≠ 0
-- theorem degreeOf_mul_X_eq' (j : σ) (f : MvPolynomial σ R) (h : f ≠ 0) :
--     degreeOf j (f * X j) = degreeOf j f + 1 := by
--   classical
--   repeat' rw [degreeOf]
--   apply (Multiset.count_add j (degrees_mul f (X j))).trans
--   simp only [Multiset.count_add, add_le_add_iff_left]
--   convert Multiset.count_le_of_le j (degrees_X' (R := R) j)
--   rw [Multiset.count_singleton_self]

theorem degreeOf_linear_le {a b : R} : degreeOf n (C a + C b * p) ≤ degreeOf n p := by
  apply le_trans (degreeOf_add_le _ _ _) _
  rw [max_def]
  split_ifs <;> simp [degreeOf_C_mul_le]

theorem degreeOf_sum_le (n : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    degreeOf n (∑ i in s, f i) ≤ s.sup fun i => degreeOf n (f i) := by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_sum_le

theorem degreeOf_prod_le (n : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    degreeOf n (∏ i in s, f i) ≤ ∑ i in s, degreeOf n (f i) := by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_prod_le (by simp) (by intro a1 a2 ; simp)

end DegreeOf

end CommSemiring

end MvPolynomial
