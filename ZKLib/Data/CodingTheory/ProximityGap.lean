import ZKLib.Data.CodingTheory.Basic

/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  ## Main Definitions

-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : Type*} [Fintype n] [DecidableEq n]

variable {C : Submodule F (n → F)} [DecidablePred (· ∈ C)]

def proximityTupleCard (u v : n → F) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀'(r • u + (1 - r) • v, C) < d}
