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

def CEmbedding : R ↪ MvPolynomial (Fin m) R := ⟨C, C_injective (Fin m) R⟩

def productFinset (n : ℕ) (D : Finset R) : Finset (Fin n → R) := Fintype.piFinset (fun _ => D)
  -- @Fintype.piFinset (Fin n) _ _ (fun _ => R) (fun _ => D)

def finOneEquiv : MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R :=
  (finSuccEquiv R 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv R (Fin 0)))

/--
  An `R`-linear mapping that sends

  `p(X_0,\dots,X_{m-1},X_m,\dots,X_{m+n-1})` to

  `\sum_{x_m,\dots,x_{m+n-1} \in D} p(X_0,\dots,X_{m-1},x_m,\dots,x_{m+n-1})`
-/
def sumFinsetPartial (m : ℕ) (n : ℕ) (D : Finset R) : MvPolynomial (Fin (m + n)) R →ₗ[R] MvPolynomial (Fin m) R where
  toFun := fun p =>
    let q := rename (Fin.sumCommEquiv m n) p
    let q' := sumAlgEquiv R (Fin n) (Fin m) q
    let D' := Finset.map CEmbedding D
    let prod_D' := Fintype.piFinset (fun _ => D')
    ∑ x in prod_D', eval x q'
  map_add' := fun p q => by simp [sum_add_distrib]
  map_smul' := fun r p => by simp [smul_eq_C_mul, mul_sum]

/-- Special case of `sumPartialFinset` when `m = 0`. Directly returns `R` -/
def sumFinsetAll (n : ℕ) (D : Finset R) : MvPolynomial (Fin n) R →ₗ[R] R := by
  rw [← Nat.zero_add n]
  exact (isEmptyAlgEquiv R (Fin 0)).toLinearMap.comp (sumFinsetPartial 0 n D)

/-- Special case of `sumPartialFinset` when `m = 1`. Directly returns `R[X]` -/
def sumFinsetExceptFirst (n : ℕ) (D : Finset R) : MvPolynomial (Fin (n + 1)) R →ₗ[R] Polynomial R := by
  rw [Nat.add_comm n 1]
  exact finOneEquiv.toLinearMap.comp (sumFinsetPartial 1 n D)

end MvPolynomial

end