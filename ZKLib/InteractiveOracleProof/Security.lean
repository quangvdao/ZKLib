import ZKLib.InteractiveOracleProof.Basic

/-!
  # Security Definitions for IOR

  We define the following security properties for IOR:

  - Completeness.

  - (Knowledge) Soundness: We define many variants of soundness and knowledge soundness, including
    - (Standard) soundness
    - State-restoration soundness
    - Round-by-round soundness
  All definitions are in the adaptive prover setting.

  - Zero-knowledge: This will be defined in the future
-/

-- We first define security notions for interactive (non-oracle) protocols, and then for oracle protocols?

-- For completeness and soundness, it doesn't matter whether the verifier is oracle or not

namespace Protocol

open OracleComp OracleSpec

noncomputable section

open scoped NNReal

-- open unitInterval

-- /- Unit interval embedded into `NNReal` -/
-- instance unitInterval.toNNReal : Coe unitInterval NNReal where
--   coe := fun ⟨x, h⟩ => ⟨x, (Set.mem_Icc.mp h).left⟩

variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, Sampleable (pSpec.Challenge i)] {PrvState : Type} {Statement Witness : Type}

section Completeness

/--
  For all valid statement-witness pair for the input relation `relIn`,
  the execution between the honest prover and the honest verifier will result in a valid pair for
  the output relation `relOut`,
  except with probability `completenessError`
-/
def completeness (protocol : Protocol pSpec oSpec PrvState Statement Witness)
    [RelIn : Relation Statement Witness]
    -- (RelOut : Transcript pSpec → Relation Statement' Witness')
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : Statement,
  ∀ witIn : Witness,
    RelIn.isValid stmtIn witIn = true →
      let decision := evalDist (Prod.fst <$> runProtocol protocol stmtIn witIn)
      decision True ≥ 1 - completenessError


/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (protocol : Protocol pSpec oSpec PrvState Statement Witness)
    [Relation Statement Witness] : Prop :=
  completeness protocol 0

end Completeness

section Soundness


/- We define 3 variants each of soundness and knowledge soundness, all in the adaptive setting: (our definitions are automatically in the adaptive setting, since there is no `crs`?)

  1. (Plain) soundness
  2. Knowledge soundness
  3. State-restoration soundness
  4. State-restoration knowledge soundness
  5. Round-by-round soundness
  6. Round-by-round knowledge soundness
-/

/-- Don't really need this? -/
structure AdaptiveProver extends Prover pSpec oSpec PrvState Statement Witness where
  chooseStatementIn : OracleComp oSpec Statement

/--
  For all initial statement `stmtIn` not in the language, all (malicious) provers with initial
  witness `witIn`, the execution will result in an invalid statement-witness pair for `relOut`
  except with probability `soundnessBound`.
-/
def soundness (verifier : Verifier pSpec oSpec Statement)
    [RelIn : Relation Statement Witness]
    (soundnessBound : ENNReal) : Prop :=
  ∀ stmtIn ∉ RelIn.language,
  /-
    Need to quantify over the witness because of the way we defined
    the type signature of the prover, which always takes in some witness.
    Think of this as the initializing the state of the prover.
  -/
  ∀ witIn : Witness,
  ∀ prover : Prover pSpec oSpec PrvState Statement Witness,
    let protocol := Protocol.mk prover verifier
    let decision := evalDist (Prod.fst <$> runProtocol protocol stmtIn witIn)
    decision true ≤ soundnessBound

/--
  An extractor is defined to be a deterministic function that takes in the initial statement and the
  IOR transcript, and returns a corresponding initial witness.

  TODO: when we generalize IOR to the ROM, how do we model the extractor's ability to observe the
  prover's queries?
-/
def Extractor := Statement → Transcript pSpec → Witness

/--
  There exists an extractor such that for all

  This is the black-box, deterministic, straightline version of knowledge soundness.
-/
def knowledgeSoundness (verifier : Verifier pSpec oSpec Statement)
    [RelIn : Relation Statement Witness]
    (knowledgeBound : ENNReal) : Prop :=
  ∃ extractor : Extractor,
  ∀ stmtIn : Statement,
  ∀ witIn : Witness,
  ∀ prover : Prover pSpec oSpec PrvState Statement Witness,
    let protocol := Protocol.mk prover verifier
    let result := evalDist (runProtocol protocol stmtIn witIn)
    let decision := Prod.fst <$> result
    let transcript := Prod.fst <$> Prod.snd <$> result
    let queryLog := Prod.snd <$> Prod.snd <$> result
    if decision true > knowledgeBound then
      let extractedWitIn := (fun tr _ => extractor stmtIn tr) <$> transcript <*> queryLog
      let validWit := RelIn.isValid stmtIn <$> extractedWitIn
      validWit true ≥ 1 - knowledgeBound
    else
      True


/-- Version of `challengeOracle` that requires querying with the statement and prior messages.

This is a stepping stone toward the Fiat-Shamir transform. -/
@[simps]
def challengeOracle' (pSpec : ProtocolSpec n) (Statement : Type) [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Sampleable (pSpec.Challenge i)] : OracleSpec (Fin n) where
  domain := fun i => Statement × (∀ j : Fin i, (pSpec.take i (by omega)).Message j)
  range := fun i => pSpec.Challenge i
  domain_decidableEq' := fun _ => decEq
  range_decidableEq' := fun _ => Sampleable.toDecidableEq
  range_inhabited' := fun _ => Sampleable.toInhabited
  range_fintype' := fun _ => Sampleable.toFintype

-- def StateRestorationProver extends Prover pSpec oSpec PrvState Statement Witness where

def stateRestorationSoundness (verifier : Verifier pSpec oSpec Statement)
    [RelIn : Relation Statement Witness]
    (SRSoundnessBound : ENNReal) : Prop :=
  ∀ stmtIn ∉ RelIn.language,
  ∀ witIn : Witness,
  ∀ adaptiveProver : AdaptiveProver (PrvState := PrvState),
    let protocol := Protocol.mk (Witness := Witness) adaptiveProver.toProver verifier
    sorry


def BadFunction := (i : ℕ) → (h : i ≤ n) → Statement →  Transcript (pSpec.take i h) → Prop

/--
  Round-by-round soundness should be defined for each round
-/
def roundByRoundSoundness (verifier : Verifier pSpec oSpec Statement)
    [RelIn : Relation Statement Witness]
    (badFunction : BadFunction (pSpec := pSpec) (Statement := Statement))
    (rbrSoundnessBound : Fin n → ℝ≥0) : Prop :=
  ∀ stmtIn ∉ RelIn.language,
  ∀ witIn : Witness,
  ∀ adaptiveProver : AdaptiveProver (PrvState := PrvState),
  ∀ i : Fin n,
    let protocol := Protocol.mk adaptiveProver.toProver verifier
    let result := evalDist (runProtocol protocol stmtIn witIn)
    let decision := Prod.fst <$> result
    let transcript := Prod.fst <$> Prod.snd <$> result
    -- decision true ≤ (rbrSoundnessBound i)
    sorry
    -- let partialTranscript : PartialTranscript spec i := ⟨transcript.messages,
    -- transcript.challenges⟩
    -- prob true ≤ soundnessBound


end Soundness


section ZeroKnowledge

-- The simulator should have programming access to the shared oracles `oSpec`
def Simulator : Type := sorry
  -- Statement → PMF (Verifier oSpec)


/-
  We define honest-verifier zero-knowledge as follows:
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts
  generated by the simulator and the interaction between the verifier and the prover are
  (statistically) indistinguishable.
-/
-- def zeroKnowledge (prover : Prover pSpec oSpec) : Prop :=
--   ∃ simulator : Simulator,
--   ∀ verifier : Verifier pSpec oSpec,
--   ∀ stmtIn : Statement,
--   ∀ witIn : Witness,
--   relIn.isValid stmtIn witIn = true →
--     let result := runProtocolAux (Protocol.mk prover verifier) stmtIn witIn
--     let transcript := Prod.fst <$> Prod.snd <$> result
--     let simTranscript := simulator
--     -- let prob := spec.relOut.isValid' <$> output
--     sorry

end ZeroKnowledge

-- End noncomputable section
end

end Protocol


namespace OracleProtocol

noncomputable section

open OracleComp OracleSpec
open scoped NNReal

variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} {pSpec : ProtocolSpec n} [∀ i, ToOracle (pSpec.Message i)] [∀ i, Sampleable (pSpec.Challenge i)] {PrvState : Type} {Statement : Type} {Witness : Type}

def completeness (oracleProtocol : OracleProtocol pSpec oSpec PrvState Statement Witness)
    [Relation Statement Witness] (completenessError : ℝ≥0) : Prop :=
  Protocol.completeness oracleProtocol.toProtocol completenessError

def perfectCompleteness (oracleProtocol : OracleProtocol pSpec oSpec PrvState Statement Witness)
    [Relation Statement Witness] : Prop :=
  Protocol.perfectCompleteness oracleProtocol.toProtocol

def soundness (verifier : OracleVerifier pSpec oSpec Statement)
    [RelIn : Relation Statement Witness] (soundnessBound : ENNReal) : Prop :=
  Protocol.soundness verifier.toVerifier (PrvState := PrvState) (RelIn := RelIn) soundnessBound

-- def knowledgeSoundness (oracleProtocol : OracleProtocol OpSpec oSpec Statement Witness)
--     [Relation Statement Witness] (knowledgeBound : ENNReal) : Prop :=
--   Protocol.knowledgeSoundness oracleProtocol.toProtocol knowledgeBound


end

end OracleProtocol
