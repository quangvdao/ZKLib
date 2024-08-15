import Mathlib.Probability.ProbabilityMassFunction.Basic

instance [IsEmpty α] : IsEmpty (PMF α) := by
  refine' Subtype.isEmpty_of_false _
  intro f h
  have : Fintype α := Fintype.ofIsEmpty
  obtain h' := hasSum_fintype f ; simp at h'
  have one_eq_zero := HasSum.unique h h'
  simp_all
