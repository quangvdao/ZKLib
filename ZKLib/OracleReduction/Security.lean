import ZKLib.OracleReduction.Basic

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

-- We first define security notions for interactive (non-oracle) protocols, and then for oracle
-- protocols?

-- For completeness and soundness, it doesn't matter whether the verifier is oracle or not

def Function.language {α β} (rel : α → β → Prop) : Set α :=
  {stmt | ∃ wit, rel stmt wit}

namespace Protocol

open OracleComp OracleSpec

noncomputable section

open scoped NNReal

-- open unitInterval

-- /- Unit interval embedded into `NNReal` -/
-- instance unitInterval.toNNReal : Coe unitInterval NNReal where
--   coe := fun ⟨x, h⟩ => ⟨x, (Set.mem_Icc.mp h).left⟩

variable {n : ℕ} (pSpec : ProtocolSpec n) {ι : Type} [DecidableEq ι] (oSpec : OracleSpec ι)
    [∀ i, Sampleable (pSpec.Challenge i)] {PrvState StmtIn WitIn StmtOut WitOut : Type}

section Completeness

/--
  For all valid statement-witness pair for the input relation `relIn`,
  the execution between the honest prover and the honest verifier will result in a valid pair for
  the output relation `relOut`,
  except with probability `completenessError`
-/
def completeness (protocol : Protocol pSpec oSpec PrvState StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop)
    (relOut : StmtOut → WitOut → Prop)
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
    relIn stmtIn witIn = true →
      letI newPair := evalDist (Prod.snd <$> Prod.snd <$> protocol.run stmtIn witIn)
      (relOut.uncurry <$> newPair) True ≥ 1 - completenessError

/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (protocol : Protocol pSpec oSpec PrvState StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop) : Prop :=
  completeness pSpec oSpec protocol relIn relOut 0

end Completeness

section Soundness


/- We define 3 variants each of soundness and knowledge soundness, all in the adaptive setting: (our
  definitions are automatically in the adaptive setting, since there is no `crs`?)

  1. (Plain) soundness
  2. Knowledge soundness
  3. State-restoration soundness
  4. State-restoration knowledge soundness
  5. Round-by-round soundness
  6. Round-by-round knowledge soundness
-/

/-- Don't really need this? -/
structure AdaptiveProver extends Prover pSpec oSpec PrvState StmtIn WitIn StmtOut WitOut where
  chooseStatementIn : OracleComp oSpec StmtIn

/--
  For all initial statement `stmtIn` not in the language, all (malicious) provers with initial
  witness `witIn`, the execution will result in an invalid statement-witness pair for `relOut`
  except with probability `soundnessBound`.
-/
def soundness (verifier : Verifier pSpec oSpec StmtIn StmtOut) (relIn : StmtIn → WitIn → Prop)
    (relOut : StmtOut → WitOut → Prop) (soundnessBound : ℝ≥0) : Prop :=
  ∀ stmtIn ∉ relIn.language,
  ∀ witIn : WitIn,
  ∀ prover : Prover pSpec oSpec PrvState StmtIn WitIn StmtOut WitOut,
    letI protocol := Protocol.mk prover verifier
    letI newPair := evalDist (Prod.snd <$> Prod.snd <$> protocol.run stmtIn witIn)
    (relOut.uncurry <$> newPair) True ≤ soundnessBound

/--
  A straightline, deterministic, non-oracle-querying extractor takes in the initial statement, the
  output statement, the output witness, the IOR transcript, and the query log, and returns a
  corresponding initial witness.

  This form of extractor suffices for proving knowledge soundness of most hash-based IOPs.
-/
def Extractor := StmtIn → StmtOut → WitOut → Transcript pSpec → QueryLog oSpec → WitIn

/--
  There exists an extractor such that for all

  This is the black-box, deterministic, straightline version of knowledge soundness.
-/
def knowledgeSoundness (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (knowledgeBound : ℝ≥0) : Prop :=
  ∃ extractor : Extractor pSpec oSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover pSpec oSpec PrvState StmtIn WitIn StmtOut WitOut,
    letI protocol := Protocol.mk prover verifier
    letI result := evalDist (protocol.run stmtIn witIn)
    letI transcript := Prod.fst <$> result
    letI queryLog := Prod.fst <$> Prod.snd <$> result
    letI newPair := Prod.snd <$> Prod.snd <$> result
    letI stmtOut := Prod.fst <$> newPair
    letI witOut := Prod.snd <$> newPair
    if (relOut.uncurry <$> newPair) True > knowledgeBound then
      letI extractedWitIn := (fun tr ql sOut wOut => extractor stmtIn sOut wOut tr ql)
        <$> transcript <*> queryLog <*> stmtOut <*> witOut
      letI validWit := relIn stmtIn <$> extractedWitIn
      validWit True ≥ 1 - knowledgeBound
    else
      True

section StateRestoration

variable [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Sampleable (pSpec.Challenge i)]

-- /-- Version of `challengeOracle` that requires querying with the statement and prior messages.

-- This is a stepping stone toward the Fiat-Shamir transform. -/
-- def challengeOracle' : OracleSpec (Fin n) where
--   domain := fun i => Statement × (∀ j : Fin i, (pSpec.take i (by omega) j)
--   range := fun i => pSpec.Challenge i
--   domain_decidableEq' := fun _ => decEq
--   range_decidableEq' := fun _ => Sampleable.toDecidableEq
--   range_inhabited' := fun _ => Sampleable.toInhabited
--   range_fintype' := fun _ => Sampleable.toFintype

-- class StateRestorationProver extends Prover pSpec oSpec PrvState Statement Witness where
--   stateRestorationQuery : OracleComp (oSpec ++ₒ challengeOracle' pSpec (Statement := Statement))
--     (PrvState × Statement × Transcript pSpec)

-- def runStateRestorationProver (prover : StateRestorationProver pSpec oSpec PrvState
--     Statement Witness) (stmtIn : Statement) (witIn : Witness) :
--     OracleComp (oSpec ++ₒ challengeOracle' pSpec (Statement := Statement))
--     (Transcript pSpec × QueryLog (oSpec ++ₒ challengeOracle' pSpec (Statement := Statement)))
-- := do
--   let ⟨state, stmt, transcript⟩ ← prover.stateRestorationQuery stmtIn
--   return ⟨transcript, state⟩


-- def stateRestorationSoundness (verifier : Verifier pSpec oSpec Statement)
--     [RelIn : Relation Statement Witness] (SRSoundnessBound : ENNReal) : Prop :=
--   ∀ stmtIn ∉ RelIn.language,
--   ∀ witIn : Witness,
--   ∀ SRProver : StateRestorationProver pSpec oSpec,
--     let protocol := Protocol.mk (PrvState := PrvState) (Witness := Witness)
--       SRProver.toProver verifier
--     sorry

end StateRestoration

structure StateFunction (verifier : Verifier pSpec oSpec StmtIn StmtOut) (language : Set StmtOut)
    where
  fn : (m : ℕ) → StmtIn → PartialTranscript pSpec m → Prop
  -- Just for `stmt` not in language?
  fn_empty : ∀ stmt, fn 0 stmt emptyPartialTranscript = False
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  fn_next : ∀ m stmt tr, (h : m < n) →
      fn m stmt tr = False ∧ pSpec.getDir ⟨m, h⟩ = .P_to_V →
        ∀ msg, fn (m + 1) stmt (tr.snoc h msg) = False
  /-- If the state function is false for a full transcript, the verifier will output false / a new
    statement not in the language (for all choice of randomness) -/
  fn_full : ∀ stmt tr, fn n stmt tr = False →
      ((· ∈ language) <$> evalDist (verifier.run stmt (tr.toFull (by simp)))) False = 1

/--
  A protocol with `verifier` satisfies round-by-round soundness with error `rbrSoundnessBound` and
  state function `stateFunction` if for all initial statement `stmtIn` not in the language of
  `relIn`, for all initial witness `witIn`, for all provers `prover`, for all `i : Fin n` that is a
  round corresponding to a challenge, the probability that the state function is false for the
  partial transcript output by the prover and the state function is true for the partial transcript
  appended by next challenge (chosen randomly) is at most `rbrSoundnessBound i`.
-/
def roundByRoundSoundness (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (relIn : StmtIn → WitIn → Prop) (language : Set StmtOut)
    (stateFunction : StateFunction pSpec oSpec verifier language)
    (rbrSoundnessBound : Fin n → ℝ≥0) : Prop :=
  ∀ stmtIn ∉ relIn.language,
  ∀ witIn : WitIn,
  ∀ prover : Prover pSpec oSpec PrvState StmtIn WitIn StmtOut WitOut,
  ∀ i : ChallengeIndex pSpec,
    letI partialTranscript := Prod.fst <$> evalDist (prover.runAux stmtIn witIn i.1.castSucc)
    letI challenge := PMF.uniformOfFintype (pSpec.Challenge i)
    letI nextTranscript := PartialTranscript.snoc i.1.isLt <$> challenge <*> partialTranscript
    letI firstProb := stateFunction.fn i.1 stmtIn <$> partialTranscript
    letI secondProb := stateFunction.fn (i.1 + 1) stmtIn <$> nextTranscript
    ((· = False ∧ · = True) <$> firstProb <*> secondProb) True ≤ rbrSoundnessBound i.1

/--
  A protocol with `verifier` satisfies round-by-round knowledge soundness with error
  `rbrKnowledgeBound` and state function `stateFunction` and extractor `extractor` if for all
  initial statement `stmtIn` not in the language of `relIn`, for all initial witness `witIn`, for
  all provers `prover`, for all `i : Fin n` that is a round corresponding to a challenge, the
  probability that the state function is false for the partial transcript output by the prover and
  the state function is true for the partial transcript appended by next challenge (chosen randomly)
  is at most `rbrKnowledgeBound i`.
-/
def roundByRoundKnowledgeSoundness (verifier : Verifier pSpec oSpec StmtIn StmtOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (stateFunction : StateFunction pSpec oSpec verifier relOut.language)
    (extractor : @Extractor _ pSpec _ oSpec StmtIn StmtOut WitIn WitOut)
    (rbrKnowledgeBound : Fin n → ℝ≥0) : Prop :=
  sorry

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

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} [DecidableEq ι] (oSpec : OracleSpec ι)
    [∀ i, ToOracle (pSpec.Message i)] [∀ i, Sampleable (pSpec.Challenge i)] {PrvState : Type}
    {StmtIn WitIn StmtOut WitOut : Type}

def completeness (oracleProtocol : OracleProtocol pSpec oSpec PrvState StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (completenessError : ℝ≥0) : Prop :=
  Protocol.completeness pSpec oSpec oracleProtocol.toProtocol relIn relOut completenessError

def perfectCompleteness
    (oracleProtocol : OracleProtocol pSpec oSpec PrvState StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop) : Prop :=
  Protocol.perfectCompleteness pSpec oSpec oracleProtocol.toProtocol relIn relOut

def soundness (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (soundnessBound : ℝ≥0) : Prop :=
  Protocol.soundness (PrvState := PrvState) pSpec oSpec verifier.toVerifier
    relIn relOut soundnessBound

def knowledgeSoundness (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut)
    (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
    (knowledgeBound : ℝ≥0) : Prop :=
  Protocol.knowledgeSoundness (PrvState := PrvState) pSpec oSpec verifier.toVerifier
    relIn relOut knowledgeBound

end

end OracleProtocol
