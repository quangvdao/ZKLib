-- Minimum working example (MWE) to post on Zulip

import Mathlib.Algebra.MvPolynomial.Equiv

-- The key lemma of quorum intersection:
-- Fix f. Let n=3f+1. Let L, L' be two subsets of {1,...,n} such that |L| ≥ 2f+1 and |L'| ≥ 2f+1.
-- Then |L ∩ L'| ≥ 1f+1.
theorem quorum_intersection
 (f n : Nat)
 (L L' : Finset Nat)
 (h1 : n = 3 * f + 1)
 (h2 : L.card ≥ 2 * f + 1)
 (h3 : L'.card ≥ 2 * f + 1)
 (h4 : L ⊆ Finset.range n)
 (h5 : L' ⊆ Finset.range n)
 : (L ∩ L').card ≥ f + 1
 := by
  calc (L ∩ L').card = L.card + L'.card - (L ∪ L').card := Finset.card_inter L L'
  _ ≥ (2 * f + 1) + (2 * f + 1) - (L ∪ L').card := by gcongr
  _ ≥ (2 * f + 1) + (2 * f + 1) - (3 * f + 1) := by
    gcongr
    rw [←h1, ←Finset.card_range n]
    exact Finset.card_le_card (Finset.union_subset h4 h5)
  _ ≥ f + 1 := by omega

  -- first, we show that L ∪ L' ⊆ {0,...,n-1}
  --  have h_union : L ∪ L' ⊆ Finset.range n := Finset.union_subset h4 h5
  --  -- as a result of h_union, |L ∪ L'| ≤ n
  --  have h_union_card : (L ∪ L').card ≤ n := by
  --    rw [←Finset.card_range n]
  --    exact Finset.card_le_card h_union
  --  -- then we use that |L ∩ L'| = |L| + |L'| - |L ∪ L'|
  --  have h_inter : (L ∩ L').card = L.card + L'.card - (L ∪ L').card := Finset.card_inter L L'
  --  -- and then we use our hyptheses about |L|, |L'| and the knowledge that
  --  -- |L ∪ L'| ≤ n to conclude the proof
  --  have h_card : f + 1 ≤ (L ∩ L').card := by
  --    rw [h_inter]
  --    simp at *
  --    omega
  --  exact h_card



noncomputable section

open Polynomial
open MvPolynomial

def testPoly : MvPolynomial (Fin 2) ℕ := X 0 * X 0 + X 1

def testPoly2 : Polynomial (MvPolynomial (Fin 1) ℕ) := finSuccEquiv ℕ 1 testPoly

-- theorem testPoly2_eval : testPoly2.eval 2 = 4 + X 0 := by
--   simp only [testPoly2, testPoly]
--   simp only [ map_add, map_mul]
--   simp only [MvPolynomial.finSuccEquiv_X_zero]
--   have : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by rfl
--   rw [this]
--   simp only [MvPolynomial.finSuccEquiv_X_succ]
--   simp
--   congr
--   . norm_num

theorem testPoly2_eval : testPoly2.eval 2 = 4 + X 0 := by
  simp [testPoly2, testPoly]
  congr
  · norm_num
  · have : (1 : Fin 2) = Fin.succ 0 := by rfl
    rw [this]
    rw [Fin.cases_succ]
    simp

end

-- def IteratedPolynomial (n : ℕ) : (F : Type _) × (CommSemiring F) × List F :=
--   match n with
--   | 0 => ⟨ ℕ, inferInstance, [(1 : ℕ)] ⟩
--   | n + 1 =>
--     let ⟨ Fn, _, elts ⟩ := IteratedPolynomial n
--     ⟨ Polynomial Fn, inferInstance, [(X : Polynomial Fn)] ++ elts.map (fun x => C x) ⟩

-- def iterZero : Type _ := (IteratedPolynomial 0).1
-- def iterOne : Type _ := (IteratedPolynomial 1).1


-- @[simp]
-- theorem iterZero_is_nat : iterZero = ℕ := rfl

-- @[simp]
-- theorem iterOne_is_poly : iterOne = Polynomial ℕ := rfl

-- theorem iterPoly_is_mvPoly (n : ℕ) : (IteratedPolynomial n).1 =
