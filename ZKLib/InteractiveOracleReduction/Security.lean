import ZKLib.InteractiveOracleReduction.Basic

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

variable {ι : Type} [DecidableEq ι] {OSpec : OracleSpec ι} {n : ℕ} {PSpec : ProtocolSpec n} [∀ i, Sampleable (PSpec.Challenge i)] {PrvState : Type} {Statement Witness : Type}

section Completeness

/--
  For all valid statement-witness pair for the input relation `relIn`,
  the execution between the honest prover and the honest verifier will result in a valid pair for
  the output relation `relOut`,
  except with probability `completenessError`
-/
def completeness (protocol : Protocol PSpec OSpec PrvState Statement Witness)
    [RelIn : Relation Statement Witness]
    -- (RelOut : Transcript PSpec → Relation Statement' Witness')
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : Statement,
  ∀ witIn : Witness,
    RelIn.isValid stmtIn witIn = true →
      let decision := evalDist (Prod.fst <$> runProtocol protocol stmtIn witIn)
      decision True ≥ 1 - completenessError


/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (protocol : Protocol PSpec OSpec PrvState Statement Witness)
    [Relation Statement Witness] : Prop :=
  completeness protocol 0

end Completeness

section Soundness


/- We define 3 variants each of soundness and knowledge soundness, all in the adaptive setting:

  1. (Plain) soundness
  2. Knowledge soundness
  3. State-restoration soundness
  4. State-restoration knowledge soundness
  5. Round-by-round soundness
  6. Round-by-round knowledge soundness
-/

structure AdaptiveProver extends Prover PSpec OSpec PrvState Statement Witness where
  chooseStatementIn : OracleComp OSpec (Statement × PrvState)

/--
  For all initial statement `stmtIn` not in the language, all (malicious) provers with initial
  witness `witIn`, the execution will result in an invalid statement-witness pair for `relOut`
  except with probability `soundnessBound`.
-/
def soundness (verifier : Verifier PSpec OSpec Statement)
    [RelIn : Relation Statement Witness]
    (soundnessBound : ENNReal) : Prop :=
  ∀ stmtIn ∉ RelIn.language,
  /-
    Need to quantify over the witness because of the way we defined
    the type signature of the prover, which always takes in some witness.
    Think of this as the initializing the state of the prover.
  -/
  ∀ witIn : Witness,
  ∀ adaptiveProver : AdaptiveProver (PrvState := PrvState),
    let protocol := Protocol.mk adaptiveProver.toProver verifier
    let decision := evalDist (Prod.fst <$> runProtocol protocol stmtIn witIn)
    decision true ≤ soundnessBound

/--
  An extractor is defined to be a deterministic function that takes in the initial statement and the
  IOR transcript, and returns a corresponding initial witness.

  TODO: when we generalize IOR to the ROM, how do we model the extractor's ability to observe the
  prover's queries?
-/
def Extractor := Statement → Transcript PSpec → Witness

/--
  There exists an extractor such that for all

  This is the black-box, deterministic, straightline version of knowledge soundness.
-/
def knowledgeSoundness (verifier : Verifier PSpec OSpec Statement)
    [RelIn : Relation Statement Witness]
    (knowledgeBound : ENNReal) : Prop :=
  ∃ extractor : Extractor,
  ∀ stmtIn : Statement,
  ∀ witIn : Witness,
  ∀ adaptiveProver : AdaptiveProver (PrvState := PrvState),
    let protocol := Protocol.mk adaptiveProver.toProver verifier
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

def stateRestorationSoundness (verifier : Verifier PSpec OSpec Statement)
    [RelIn : Relation Statement Witness]
    (SRSoundnessBound : ENNReal) : Prop :=
  ∀ stmtIn ∉ RelIn.language,
  ∀ witIn : Witness,
  ∀ adaptiveProver : AdaptiveProver (PrvState := PrvState),
    let protocol := Protocol.mk (Witness := Witness) adaptiveProver.toProver verifier
    sorry


def BadFunction :=
  (i : Fin n) → Statement →  PartialTranscript PSpec i → Prop

/--
  Round-by-round soundness should be defined for each round
-/
def roundByRoundSoundness (verifier : Verifier PSpec OSpec Statement)
    [RelIn : Relation Statement Witness]
    (badFunction : BadFunction (PSpec := PSpec) (Statement := Statement))
    (rbrSoundnessBound : Fin n → ℝ≥0) : Prop :=
  ∀ stmtIn ∉ RelIn.language,
  ∀ witIn : Witness,
  ∀ adaptiveProver : AdaptiveProver (PrvState := PrvState),
  ∀ i : Fin n,
    let protocol := Protocol.mk adaptiveProver.toProver verifier
    let result := evalDist (runProtocol protocol stmtIn witIn)
    let decision := Prod.fst <$> result
    let transcript := Prod.fst <$> Prod.snd <$> result
    let partialTranscript := (fun tr => tr.toPartial i) <$> transcript
    -- decision true ≤ (rbrSoundnessBound i)
    sorry
    -- let partialTranscript : PartialTranscript spec i := ⟨transcript.messages,
    -- transcript.challenges⟩
    -- prob true ≤ soundnessBound


end Soundness


section ZeroKnowledge

-- The simulator should have programming access to the shared oracles `OSpec`
def Simulator : Type := sorry
  -- Statement → PMF (Verifier OSpec)


/-
  We define honest-verifier zero-knowledge as follows:
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts
  generated by the simulator and the interaction between the verifier and the prover are
  (statistically) indistinguishable.
-/
-- def zeroKnowledge (prover : Prover PSpec OSpec) : Prop :=
--   ∃ simulator : Simulator,
--   ∀ verifier : Verifier PSpec OSpec,
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

variable {ι : Type} [DecidableEq ι] {OSpec : OracleSpec ι} {oraclePSpec : OracleProtocolSpec n} [∀ i, Sampleable (oraclePSpec.Challenge i)] {PrvState : Type} {Statement : Type} {Witness : Type}

def completeness (oracleProtocol : OracleProtocol oraclePSpec OSpec PrvState Statement Witness)
    [Relation Statement Witness] (completenessError : ℝ≥0) : Prop :=
  Protocol.completeness oracleProtocol.toProtocol completenessError

def perfectCompleteness (oracleProtocol : OracleProtocol oraclePSpec OSpec PrvState Statement Witness)
    [Relation Statement Witness] : Prop :=
  Protocol.perfectCompleteness oracleProtocol.toProtocol

def soundness (verifier : OracleVerifier oraclePSpec OSpec Statement)
    [RelIn : Relation Statement Witness] (soundnessBound : ENNReal) : Prop :=
  Protocol.soundness verifier.toVerifier (PrvState := PrvState) (RelIn := RelIn) soundnessBound

-- def knowledgeSoundness (oracleProtocol : OracleProtocol OPSpec OSpec Statement Witness)
--     [Relation Statement Witness] (knowledgeBound : ENNReal) : Prop :=
--   Protocol.knowledgeSoundness oracleProtocol.toProtocol knowledgeBound


end

end OracleProtocol
