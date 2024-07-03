import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UnitInterval

-- Test out the probability library

noncomputable section


open PMF

open scoped ProbabilityTheory

-- PMF as a monad
def coin_flip : PMF Bool := PMF.bernoulli (1/2) (by norm_num)

theorem coin_flip_uniform : coin_flip = PMF.uniformOfFintype Bool := by
  simp [coin_flip, PMF.bernoulli, PMF.uniformOfFintype, PMF.uniformOfFinset, PMF.ofFintype]



def two_flips : PMF (Bool × Bool) :=
  coin_flip.bind (fun b₁ =>
    coin_flip.map (fun b₂ => (b₁, b₂)))

def two_flips_do : PMF (Bool × Bool) := do
  let b₁ ← coin_flip
  let b₂ ← coin_flip
  return (b₁, b₂)

theorem two_flips_defs_eq : two_flips = two_flips_do := by congr

-- instance : ForIn PMF (List Bool) (Fin n) where
--   forIn := _

-- def n_flips (n : ℕ+) : PMF (List Bool) := do
--   let mut bs : List Bool := []
--   for i in Fin n do {
--     let b ← coin_flip
--     bs := bs.cons b
--   }
--   return bs

  -- Finset.univ.powerset.map (fun s => s.map (fun i => i.val))

theorem two_flips_one_quarter_prob : ∀ a b : Bool, two_flips (a, b) = 1/4 := by
  intro a b
  cases a <;> cases b <;> simp [two_flips, coin_flip, tsum_fintype, ← ENNReal.mul_inv] <;> norm_num

theorem two_flips_one_quarter_prob : two_flips = uniformOfFintype (Bool × Bool) := by
  simp [two_flips, coin_flip, uniformOfFintype, uniformOfFinset, bernoulli]
  simp [two_flips, coin_flip]
  calc
    _ = ∑' (a_1 : Bool), 2⁻¹ * if a = a_1 then 2⁻¹ else 0 := by
      congr ; funext a_1 ; cases b <;> norm_num
    _ = (2⁻¹ : ENNReal) * (2⁻¹ : ENNReal) := by norm_num
    _ = (4⁻¹ : ENNReal) := by rw [← ENNReal.mul_inv] <;> norm_num


theorem two_flips_one_quarter_prob' : two_flips_do.toMeasure (fun (b₁, b₂) => b₁ ∧ b₂) = 1/4 := by
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
  sorry

-- Uniform distribution
-- def uniform_on_list {α : Type} (l : List α) : PMF α :=
--   PMF.ofList l

-- #eval (uniform_on_list [1, 2, 3, 4, 5]).prob (· = 3)

end
