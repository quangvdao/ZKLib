import Mathlib.Probability.ProbabilityMassFunction.Monad


noncomputable section

variable {α β γ : Type*}

open scoped Classical
open NNReal ENNReal

open MeasureTheory

namespace PMF

section LawfulMonad



instance : LawfulMonad PMF where
  map_const := sorry
  id_map := sorry
  seqLeft_eq := sorry
  seqRight_eq := sorry
  pure_seq := sorry
  bind_pure_comp := sorry
  bind_map := sorry
  pure_bind := sorry
  bind_assoc := sorry

end LawfulMonad

end PMF
