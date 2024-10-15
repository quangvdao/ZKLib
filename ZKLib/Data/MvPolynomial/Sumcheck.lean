/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import ZKLib.Data.MvPolynomial.Notation

/-!
  # Auxiliary functions for sum-check over multivariate polynomials
-/

noncomputable section

open BigOperators Finset Fintype

/-- Equivalence that splits `Fin (m + n)` to `Fin m` and `Fin n`, then swaps the two -/
def Fin.sumCommEquiv (m : ℕ) (n : ℕ) : Fin (m + n) ≃ Sum (Fin n) (Fin m) :=
  (@finSumFinEquiv m n).symm.trans (Equiv.sumComm (Fin m) (Fin n))

namespace MvPolynomial

open scoped Polynomial

variable {R : Type _} [CommSemiring R] {σ : Type*} {m n : ℕ}

/-- Evaluate the first variable of a multivariate polynomial -/
def evalFirstVar (p : MvPolynomial (Fin n) R) (r : R) (pos : n > 0) :
    MvPolynomial (Fin (n - 1)) R := by
  have : n = n - 1 + 1 := by omega
  rw [this] at p
  exact (finSuccEquiv R (n - 1) p).eval (C r)

/-- `C : R →+* MvPolynomial σ R` as an embedding -/
def CEmbedding : R ↪ MvPolynomial σ R := ⟨C, C_injective σ R⟩

/-- Equivalence between `MvPolynomial (Fin 1) R` and `Polynomial R` -/
def finOneEquiv : MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R :=
  (finSuccEquiv R 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv R (Fin 0)))

def test (p : ℕ[X Fin 2]) := ∑ x ∈ {0, 1}, evalFirstVar p x (by norm_num)

def testTuple (p : ℕ[X Fin 2]) := ∑ x ∈ {0, 1} ^ᶠ 2, eval x p

example : testTuple (X 0 + X 1) = (0 + 0) + (0 + 1) + (1 + 0) + (1 + 1) := by
  simp [testTuple]
  exact rfl

section PartialEval

variable {σ σ₁ σ₂ : Type*}

/-- Partial evaluation of multivariate polynomials given a mapping to a sum type `σ → σ₁ ⊕ σ₂`
and a partial evaluation point `x : σ₁ → R` -/
def peval (x : σ₁ → R) (f : σ → σ₁ ⊕ σ₂) :
    MvPolynomial σ R →+* MvPolynomial σ₂ R where
  toFun := fun p => eval (C ∘ x) ((sumAlgEquiv R σ₁ σ₂).toFun (rename f p))
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp

-- theorem peval_support_of_injective {x : σ₁ → R} {f : σ → σ₁ ⊕ σ₂} {p : MvPolynomial σ R} :
--     (peval x f p).support ⊆ p.support.image (sumAlgEquiv R σ₁ σ₂).toFun := by
--   sorry

#check MvPolynomial.support_rename_of_injective

#check MvPolynomial.degrees

end PartialEval

/--
  A `R`-linear mapping that sends

  `p(X_0,\dots,X_{m-1},X_m,\dots,X_{m+n-1})` to

  `\sum_{x_m ∈ D 0, ..., x_{m+n-1} ∈ D (n-1)} p(X_0,\dots,X_{m-1},x_m,\dots,x_{m+n-1})`
-/
def sumPartial (m : ℕ) (n : ℕ) (D : Fin n → Finset R) :
    MvPolynomial (Fin (m + n)) R →ₗ[R] MvPolynomial (Fin m) R where
  toFun := fun p => ∑ x ∈ Fintype.piFinset D, peval x (Fin.sumCommEquiv m n) p
  map_add' := fun p q => by simp only [map_add, sum_add_distrib]
  map_smul' := fun r p => by simp [peval, smul_eq_C_mul, mul_sum]

/-- Special case of `sumPartialFinset` when `m = 0`. Directly returns `R` -/
def sumAll (n : ℕ) (D : Fin n → Finset R) : MvPolynomial (Fin n) R →ₗ[R] R := by
  rw [← Nat.zero_add n]
  exact (isEmptyAlgEquiv R (Fin 0)).toLinearMap.comp (sumPartial 0 n D)

/-- Special case of `sumPartialFinset` when `m = 1`. Directly returns `R[X]` -/
def sumExceptFirst (n : ℕ) (D : Fin n → Finset R) :
    MvPolynomial (Fin (n + 1)) R →ₗ[R] Polynomial R := by
  rw [Nat.add_comm n 1]
  exact finOneEquiv.toLinearMap.comp (sumPartial 1 n D)

/-- Variant of `sumFinsetExceptFirst` where we replace `n` with `n - 1` -/
def sumExceptFirst' (n : ℕ) (h : n > 0) (D : Fin (n - 1) → Finset R) :
    MvPolynomial (Fin n) R →ₗ[R] Polynomial R := by
  have : n - 1 + 1 = n := @Nat.sub_add_cancel n 1 (gt_iff_lt.mp h)
  exact this ▸ sumExceptFirst (n - 1) D

@[simp]
theorem sumExceptFirst'_degree_le (n : ℕ) (h : n > 0) (D : Fin (n - 1) → Finset R)
    (p : MvPolynomial (Fin n) R) : (sumExceptFirst' n h D p).degree ≤ p.degreeOf ⟨0, h⟩ := by
  sorry

-- @[simp]
-- theorem sum_of_sumExceptFirst'_eval_eq_sumAll (n : ℕ+) (D : Finset R)
    -- (p : MvPolynomial (Fin n) R) (i : ℕ) :
    -- (sumExceptFirst' n D p).coeff i = p.coeff (Fin.castSucc i) := by
--   sorry

end MvPolynomial

end
