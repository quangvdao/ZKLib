/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange

/-!
  # Basics of Coding Theory

  We define a general code `C` to be a subset of `n → R` for some finite index set `n` and some target type `R`.

  We can then specialize this notion to various settings. For `[CommSemiring R]`, we define a linear code to be a linear subspace of `n → R`. We also define the notion of generator matrix and (parity) check matrix.

  ## Main Definitions

  - `codeDist C`: The Hamming distance of a code `C`, defined as the infimum (in `ℕ∞`) of the Hamming distances between any two distinct elements of `C`. This is noncomputable.

  - `codeDist' C`: A computable version of `codeDist C`, assuming `C` is a `Fintype`.

  We define the block length, rate, and distance of `C`. We prove simple properties of linear codes such as the singleton bound.
-/


section CodingTheory

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

section Distance

/-- The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct elements of the code.

We formalize this as the infimum `sInf` over all `d : ℕ` such that there exist `u v : n → R` in the code with `u ≠ v` and `hammingDist u v ≤ d`. If none exists, then we define the distance to be `0`. -/
noncomputable def codeDist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}

@[simp]
theorem codeDist_empty : codeDist (∅ : Set (n → R)) = 0 := by simp [codeDist]

@[simp]
theorem codeDist_subsingleton {C : Set (n → R)} [Subsingleton C] : codeDist C = 0 := by
  simp only [codeDist]
  have {d : ℕ} : (∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d) = False := by
    have h := @Subsingleton.allEq C _
    simp_all; intro a ha b hb hab
    have hEq : a = b := h a ha b hb
    simp_all
  have : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d} = (∅ : Set ℕ) := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    simp [this]
  simp [this]

@[simp]
theorem codeDist_le_card (C : Set (n → R)) : codeDist C ≤ Fintype.card n := by
  by_cases h : Subsingleton C
  · simp
  · simp at h
    unfold Set.Nontrivial at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    refine Nat.sInf_le ?_
    simp
    refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, hammingDist_le_card_fintype⟩⟩⟩

/-- If `u` and `v` are two codewords of `C` with distance at most `codeDist C / 2`, then they are the same. -/
theorem eq_of_le_half_codeDist {C : Set (n → R)} {u v : n → R} (hu : u ∈ C) (hv : v ∈ C)
    (huv : hammingDist u v ≤ codeDist C / 2) : u = v := by sorry

section Computable

/-- Computable version of the Hamming distance of a code `C`, assuming `C` is a `Fintype`.

The return type is `ℕ∞` since we use `Finset.min`. -/
def codeDist' (C : Set (n → R)) [Fintype C] : ℕ∞ :=
  Finset.min <| ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)).image
    (fun ⟨u, v⟩ => hammingDist u.1 v.1)

variable {C : Set (n → R)} [Fintype C]

@[simp]
theorem codeDist'_empty : codeDist' (∅ : Set (n → R)) = ⊤ := by
  simp [codeDist']

@[simp]
theorem codeDist'_subsingleton [Subsingleton C] : codeDist' C = ⊤ := by
  simp [codeDist']
  apply Finset.min_eq_top.mpr
  simp [Finset.filter_eq_empty_iff]
  have h := @Subsingleton.elim C _
  simp_all
  exact h

theorem codeDist_eq_codeDist' : codeDist C = (codeDist' C).toNat:= by
  by_cases h : Subsingleton C
  · simp
  · simp [codeDist, codeDist']
    have : codeDist' C ≠ ⊤ := by sorry
    sorry
    -- apply (ENat.toNat_eq_iff this).mp
    -- apply Finset.min_eq_top.mp
    -- simp [this]

end Computable

end Distance

section Linear

variable {k : Type*} [Fintype k] [CommSemiring R]

/-- Define a linear code from its generator matrix -/
def codeByGenMatrix (G : Matrix k n R) : Submodule R (n → R) :=
  LinearMap.range G.vecMulLinear
  -- Submodule.span R (Set.range G)

/-- Define a linear code from its (parity) check matrix -/
def codeByCheckMatrix (H : Matrix k n R) : Submodule R (n → R) :=
  LinearMap.ker H.mulVecLin

/-- The Hamming distance of a linear code can also be defined as the minimum Hamming norm of a non-zero vector in the code -/
noncomputable def linearCodeDist (C : Submodule R (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, u ≠ 0 ∧ hammingNorm u ≤ d}

-- Require `[CommRing R]`
theorem codeDist_eq_linearCodeDist (C : Submodule R (n → R)) :
    codeDist C.carrier = linearCodeDist C := by
  simp [codeDist, linearCodeDist]
  congr; unfold setOf; funext d
  apply Eq.propIntro <;> intro h
  · obtain ⟨u, hu, v, hv, huv, hDist⟩ := h
    -- let w := u - v
    -- have hw : w ∈ C := by simp [Submodule.add_mem]
    -- refine ⟨w, And.intro hw ⟨v, And.intro hv ⟨huv, ?_⟩⟩⟩
    sorry
  · obtain ⟨u, hu, hNorm, hDist⟩ := h
    -- refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, ?_⟩⟩⟩
    sorry

/-- A computable version of the Hamming distance of a linear code `C`. -/
def linearCodeDist' (C : Submodule R (n → R)) [Fintype C] : ℕ∞ :=
  Finset.min <| ((Finset.univ (α := C)).filter (fun v => v ≠ 0)).image (fun v => hammingNorm v.1)

instance [Finite R] (C : Submodule R (n → R)) : Finite C := inferInstance

instance [DecidableEq n] [Fintype R] : Fintype (n → R) := inferInstance

-- instance [DecidableEq n] [Fintype R] (C : Submodule R (n → R)) : Fintype C := inferInstance

-- The interleaving of a code `C` over index set `ι` is the submodule spanned by `ι × n`-matrices whose rows are elements of `C`
def codeInterleave (C : Submodule R (n → R)) (ι : Type*) : Submodule R ((ι × n) → R) :=
  Submodule.span R {v | ∀ i, ∃ c ∈ C, c = fun j => v (i, j)}



end Linear

end CodingTheory
