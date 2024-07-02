import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UnitInterval

-- Test out the probability library

noncomputable section


open PMF

open scoped ProbabilityTheory

def pmfExample : PMF ℕ := PMF.pure 3

#check pmfExample

-- PMF as a monad
def coin_flip : PMF Bool :=
  PMF.bernoulli (1/2) (by norm_num)

def two_flips : PMF (Bool × Bool) :=
  coin_flip.bind (fun b₁ =>
    coin_flip.map (fun b₂ => (b₁, b₂)))

def two_flips_do : PMF (Bool × Bool) := do
  let b₁ ← coin_flip
  let b₂ ← coin_flip
  return (b₁, b₂)

theorem two_flips_defs_eq : two_flips = two_flips_do := by
  unfold two_flips two_flips_do PMF.bind
  simp [PMF.bind_apply, PMF.map_apply]

theorem coin_flip_prob_true : coin_flip true = 1/2 := by
  -- Unfold the definition of coin_flip and bernoulli
  unfold coin_flip PMF.bernoulli
  -- Simplify
  simp

theorem two_flips_one_quarter_prob : two_flips_do.toMeasure (fun (b₁, b₂) => b₁ ∧ b₂) = 1/4 := by
  unfold two_flips_do
  simp [PMF.toMeasure_bind_apply]
  have h1 : (do
            let b₁ ← coin_flip
            let b₂ ← coin_flip
            Pure.pure (b₁, b₂))
        (true, true) = 1/4 := by
    simp [PMF.bind_pure_comp, Pure.pure, PMF.pure]
    simp [coin_flip]
    simp [PMF.bind_apply]
  norm_num

-- Uniform distribution
-- def uniform_on_list {α : Type} (l : List α) : PMF α :=
--   PMF.ofList l

-- #eval (uniform_on_list [1, 2, 3, 4, 5]).prob (· = 3)

end
