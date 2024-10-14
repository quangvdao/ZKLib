import ZKLib.Data.CodingTheory.Basic

/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  ## Main Definitions

-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : Type*} [Fintype n] [DecidableEq n]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]

def proximityTupleCard (u v : n → F) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀'(r • u + (1 - r) • v, C) ≤ d}

def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : n → F, (proximityTupleCard C u v d > bound)
  → (Δ₀( (fun ⟨a, b⟩ => if a = 0 then u b else v b : Fin 2 × n → F) ,
          (interleaveCode C (Fin 2) : Set (Fin 2 × n → F)) ) ≤ d)
