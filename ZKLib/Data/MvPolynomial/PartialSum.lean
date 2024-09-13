/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Equiv

/-!
  # Sum of `MvPolynomial` over some variables taking values in a finite set
-/

noncomputable section

open BigOperators Finset Fintype

/-- Equivalence that splits `Fin (m + n)` to `Fin m` and `Fin n`, then swaps the two -/
def Fin.sumCommEquiv (m : ℕ) (n : ℕ) : Fin (m + n) ≃ Sum (Fin n) (Fin m) := (@finSumFinEquiv m n).symm.trans (Equiv.sumComm (Fin m) (Fin n))


namespace MvPolynomial

variable {R : Type _} [CommSemiring R] {σ : Type*}

/-- Embedding of `R` to `MvPolynomial (Fin m) R` -/
def CEmbedding : R ↪ MvPolynomial (Fin m) R := ⟨C, C_injective (Fin m) R⟩

/-- Equivalence between `MvPolynomial (Fin 1) R` and `Polynomial R` -/
def finOneEquiv : MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R :=
  (finSuccEquiv R 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv R (Fin 0)))

/--
  An `R`-linear mapping that sends

  `p(X_0,\dots,X_{m-1},X_m,\dots,X_{m+n-1})` to

  `\sum_{x_m,\dots,x_{m+n-1} \in D} p(X_0,\dots,X_{m-1},x_m,\dots,x_{m+n-1})`
-/
def sumPartial (m : ℕ) (n : ℕ) (D : Finset R) : MvPolynomial (Fin (m + n)) R →ₗ[R] MvPolynomial (Fin m) R where
  toFun := fun p =>
    -- Swap the last `n` variables and the first `m` variables
    let p1 := rename (Fin.sumCommEquiv m n) p
    -- Split into a polynomial over `n` variables, with coefficients in `MvPolynomial (Fin m) R`
    let p2 := sumAlgEquiv R (Fin n) (Fin m) p1
    -- Product domain `D ^ n`
    let prod_D := Fintype.piFinset (fun _ => Finset.map CEmbedding D)
    -- Perform the partial sum via summing the evaluations
    ∑ x in prod_D, eval x p2

  map_add' := fun p q => by simp [sum_add_distrib]
  map_smul' := fun r p => by simp [smul_eq_C_mul, mul_sum]

/-- Special case of `sumPartialFinset` when `m = 0`. Directly returns `R` -/
def sumAll (n : ℕ) (D : Finset R) : MvPolynomial (Fin n) R →ₗ[R] R := by
  rw [← Nat.zero_add n]
  exact (isEmptyAlgEquiv R (Fin 0)).toLinearMap.comp (sumPartial 0 n D)

/-- Special case of `sumPartialFinset` when `m = 1`. Directly returns `R[X]` -/
def sumExceptFirst (n : ℕ) (D : Finset R) : MvPolynomial (Fin (n + 1)) R →ₗ[R] Polynomial R := by
  rw [Nat.add_comm n 1]
  exact finOneEquiv.toLinearMap.comp (sumPartial 1 n D)

/-- Change `sumFinsetExceptFirst` to handle `n : ℕ+`-/
def sumExceptFirst' (n : ℕ+) (D : Finset R) : MvPolynomial (Fin n) R →ₗ[R] Polynomial R := by
  have : n.1 - 1 + 1 = (n : ℕ) := @Nat.sub_add_cancel n.1 1 (n.2)
  exact this ▸ sumExceptFirst (n.1 - 1) D

@[simp]
theorem sumExceptFirst'_degree (n : ℕ+) (D : Finset R) (p : MvPolynomial (Fin n) R) : (sumExceptFirst' n D p).degree ≤ p.degreeOf 0 := by
  sorry

-- @[simp]
-- theorem sum_of_sumExceptFirst'_eval_eq_sumAll (n : ℕ+) (D : Finset R) (p : MvPolynomial (Fin n) R) (i : ℕ) : (sumExceptFirst' n D p).coeff i = p.coeff (Fin.castSucc i) := by
--   sorry

end MvPolynomial

end
