/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ZKLib.OracleReduction.Security

/-!
  # Commitment Schemes with Oracle Openings

  A commitment scheme, relative to an oracle `oSpec : OracleSpec ι`, and for a given function
  `oracle : Data → Query → Response` transforming underlying data `Data` into an oracle `Query →
  Response`, is a tuple of two operations:

  - Commit, which is a function `commit : Data → Randomness → OracleComp oSpec Commitment`
  - Open, which is (roughly) an interactive proof (relative to `oSpec`) for the following relation:
    - `StmtIn := (cm : Commitment) × (x : Query) × (y : Response)`
    - `WitIn := (d : Data) × (r : Randomness)`
    - `rel : StmtIn → WitIn → Prop := fun ⟨cm, x, y⟩ ⟨d, r⟩ => commit d r = cm ∧ oracle d x = y`

  There is one inaccuracy about the relation above: `commit` is an oracle computation, and not a
  deterministic function; hence the relation is not literally true as described. This is why
  security definitions for commitment schemes have to be stated differently than those for IOPs.
-/

namespace Commitment

open OracleSpec OracleComp SubSpec

variable {n : ℕ} {ι : Type}

structure Commit (oSpec : OracleSpec ι) (Data Randomness Commitment : Type) where
  commit : Data → Randomness → OracleComp oSpec Commitment

structure Opening (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Data : Type)
    [O : ToOracle Data] (Randomness Commitment : Type) where
  opening : Proof pSpec oSpec (Commitment × O.Query × O.Response) (Data × Randomness)

-- abbrev Statement (Data Commitment : Type) [O : ToOracle Data] :=
--  Commitment × O.Query × O.Response

-- abbrev Witness (Data Randomness : Type) := Data × Randomness

structure Scheme (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Data : Type) [O : ToOracle Data]
    (Randomness Commitment : Type) extends
    Commit oSpec Data Randomness Commitment,
    Opening pSpec oSpec Data Randomness Commitment

section Security

noncomputable section

open scoped NNReal

variable [DecidableEq ι] {pSpec : ProtocolSpec n} [∀ i, Sampleable (pSpec.Challenge i)]
  {oSpec : OracleSpec ι} {Data : Type} [O : ToOracle Data] {Randomness : Type} [Fintype Randomness]
  {Commitment : Type}

/-- A commitment scheme satisfies **correctness** with error `correctnessError` if for all
  `data : Data`, `randomness : Randomness`, and `query : O.Query`, the probability of accepting
  upon executing commitment and opening procedures honestly is at least `1 - correctnessError`. -/
def correctness (scheme : Scheme pSpec oSpec Data Randomness Commitment)
    (correctnessError : ℝ≥0) : Prop :=
  ∀ data : Data,
  ∀ randomness : Randomness,
  ∀ query : O.Query,
    let commitment := scheme.commit data randomness
    let result := evalDist (liftComp commitment >>=
      fun cm => scheme.opening.run ⟨cm, query, O.oracle data query⟩ ⟨data, randomness⟩)
    let probAccept := Prod.fst <$> Prod.snd <$> Prod.snd <$> result
    probAccept True ≥ 1 - correctnessError

/-- A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
  -/
def perfectCorrectness (scheme : Scheme pSpec oSpec Data Randomness Commitment) : Prop :=
  correctness scheme 0

/-- An adversary in the binding game returns a commitment `cm` and two purported openings `(d₁,r₁)`,
  `(d₂,r₂)` for that commitment. -/
def BindingAdversary := OracleComp oSpec (Commitment × (Data × Randomness) × (Data × Randomness))

/-- A commitment scheme satisfies **binding** with error `bindingError` if for all -/
def binding (scheme : Scheme pSpec oSpec Data Randomness Commitment)
    (bindingError : ℝ≥0): Prop :=
  ∀ adversary : OracleComp oSpec (Commitment × (Data × Randomness) × (Data × Randomness)),
  ∀ prover : Prover pSpec oSpec (Commitment × O.Query × O.Response) (Data × Randomness) Bool Unit,
    False

def extractability (scheme : Scheme pSpec oSpec Data Randomness Commitment) : Prop := sorry

/-- Have to put it as `hiding'` because `hiding` is already used somewhere else. -/
def hiding' (scheme : Scheme pSpec oSpec Data Randomness Commitment) : Prop := sorry

end

end Security

end Commitment
