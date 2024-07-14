import Mathlib.Algebra.MvPolynomial.Equiv

/-!
  # Sum of `MvPolynomial` over some variables taking values in a finite set
-/

noncomputable section

open BigOperators Finset Fintype


/-- Equivalence that splits `Fin (m + n)` to `Fin m` and `Fin n`, then swaps the two -/
def Fin.sumCommEquiv (m : ℕ) (n : ℕ) : Fin (m + n) ≃ Sum (Fin n) (Fin m) := (@finSumFinEquiv m n).symm.trans (Equiv.sumComm (Fin m) (Fin n))


namespace Polynomial

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R]
[Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- `Polynomial.map` as an `AlgHom` for noncommutative algebras.

  This is the algebra version of `Polynomial.mapRingHom`. -/
def mapAlgHom (f : A →ₐ[R] B) : Polynomial A →ₐ[R] Polynomial B where
  toRingHom := mapRingHom f.toRingHom
  commutes' := by simp

@[simp]
theorem coe_mapAlgHom (f : A →ₐ[R] B) : ⇑(mapAlgHom f) = map f :=
  rfl

@[simp]
theorem mapAlgHom_id : mapAlgHom (AlgHom.id R A) = AlgHom.id R (Polynomial A) :=
  AlgHom.ext fun _x => map_id

@[simp]
theorem mapAlgHom_coe_ringHom (f : A →ₐ[R] B) :
    ↑(mapAlgHom f : _ →ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A →+* Polynomial B) :=
  rfl

@[simp]
theorem mapAlgHom_comp (C : Type z) [Semiring C] [Algebra R C] (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (mapAlgHom f).comp (mapAlgHom g) = mapAlgHom (f.comp g) := by
  apply AlgHom.ext
  intro x
  simp [AlgHom.comp_algebraMap, map_map]
  congr

def mapAlgEquiv (f : A ≃ₐ[R] B) : Polynomial A ≃ₐ[R] Polynomial B :=
  AlgEquiv.ofAlgHom (mapAlgHom f.toAlgHom) (mapAlgHom f.symm.toAlgHom) (by simp) (by simp)

theorem mapAlgHom_eq_eval₂AlgHom'_CAlgHom (f : A →ₐ[R] B) : mapAlgHom f = eval₂AlgHom'
    (CAlgHom.comp f) X (fun a => (commute_X (C (f a))).symm) := by
  apply AlgHom.ext ; intro x ; congr


end Polynomial


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
