/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Degrees

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

universe u v w

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R}

section DegreeOf


/-
-- TODO we can prove equality here if R is a domain
theorem degreeOf_mul_eq' [IsDomain R] (i : σ) (f g : MvPolynomial σ R) :
    degreeOf i (f * g) = degreeOf i f + degreeOf i g := by
  classical
  repeat' rw [degreeOf]
  convert Multiset.count_le_of_le i (degrees_mul f g)
  rw [Multiset.count_add]
-/

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


theorem degreeOf_sum_le {ι : Type*} [DecidableEq σ] (n : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    degreeOf n (∑ i in s, f i) ≤ s.sup fun i => degreeOf n (f i) := by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_sum_le


theorem degreeOf_prod_le {ι : Type*} [DecidableEq σ] (n : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    degreeOf n (∏ i in s, f i) ≤ ∑ i in s, degreeOf n (f i) := by
  simp_rw [degreeOf_eq_sup]
  classical exact supDegree_prod_le (A := σ →₀ ℕ) (B := ℕ) (D := fun fsupp => fsupp n) (by simp) (by intro a1 a2 ; simp)