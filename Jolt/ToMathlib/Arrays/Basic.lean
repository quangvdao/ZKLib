import Mathlib.Data.Array.Basic

/-!
  ## Some proofs for Array.zipWith
  No longer needed, just import `batteries`
-/


theorem length_eq_zipWith_length (x : List α) (y : List β) (f : α → β → γ) (h : x.length ≤ y.length) : (List.zipWith f x y).length = x.length := by
  revert y
  induction x with
  | nil => aesop
  | cons a x' _ => aesop



lemma zipWithAux_at_size (a : Array α) (b : Array β) (f : α → β → γ) (h : n ≥ b.size) :
  Array.zipWithAux f a b n c = c :=
by
  unfold Array.zipWithAux
  split; split; simp_rw
  sorry
  -- . cases Nat.not_le_of_gt ‹_› h
  -- . simp
  -- . simp


theorem zipWith_eq_zipWith_data (x : Array α) (y : Array β) (f : α → β → γ) : (Array.zipWith x y f).data = List.zipWith f x.data y.data := by
  unfold Array.zipWith
  unfold Array.zipWithAux
  split; split
  sorry
  -- . sorry


theorem size_eq_zipWith_size (x : Array α) (y : Array β) (f : α → β → γ) (h : x.size = y.size) : (x.zipWith y f).size = x.size := by
  revert y
  induction x.data with
  | nil =>
