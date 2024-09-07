/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UnitInterval
import VCVio
import ZKLib.Data.Misc.HList
import ZKLib.Relation.Basic
import ZKLib.ToVCVio.Oracle

/-!
# Formalism of Interactive Oracle Reductions

We define (public-coin) interactive oracle reductions (IORs). This is an interactive protocol
between a prover and a verifier with the following format:

  - At the beginning, the prover and verifier both hold a public statement x (and potentially have
    access to some public parameters pp). The prover may also hold some private state which in
    particular may contain a witness w to the statement x.

  - In each round, the verifier sends some random challenges, and the prover sends back responses to
    the challenges. The responses are received as oracles by the verifier. The verifier only sees
    some abstract representation of the responses, and is only allowed to query these oracles in
    specific ways (i.e. point queries, polynomial evaluation queries, tensor queries).

  - At each step, the verifier may make oracle queries and perform some checks on the responses so
    far. At the end of the interaction, the verifier outputs a new statement, and the prover outputs
    a new witness.

Note: the definition of IORs as defined above generalizes those found in the literature. When the
output relation is the Boolean relation (where `StatementOut = Bool`), then we recover a generalized
version of Interactive Oracle Proofs (IOPs) [BCS16]. The particular IOP considered in [BCS16] may be
called "point IOP" due to its query structure. We also get "polynomial IOP" [BCG+19] and "tensor
IOP" [BCG20] (and other kinds of IOPs) from our definition.

-/

instance instDecidableEqOption [DecidableEq α] : DecidableEq (Option α) := inferInstance

namespace IOR

open OracleComp
section Format

/--
  Structure that turns messages of an IOR into oracles.
-/
structure Oracleize (n : ℕ+) (Message : Fin n → Type) where
  Query : Fin n → Type -- Query type for oracle in each round
  Response : Fin n → Type -- Response type for oracle in each round
  oracle : ∀ i, Message i → Query i → Response i -- Transforming messages to oracles that take queries and return responses

/--
  A class to ensure that the oracle queries and responses are finite, decidable, and inhabited. This can then be plugged into the `VCVio` framework.
-/
class ValidOracleize (O : Oracleize n Message) where
  domain_decidableEq : ∀ i, DecidableEq (O.Query i)
  range_decidableEq : ∀ i, DecidableEq (O.Response i)
  range_inhabited : ∀ i, Inhabited (O.Response i)
  range_fintype : ∀ i, Fintype (O.Response i)

class ValidChallenge (C : Fin n → Type) where
  fintype : ∀ i, Fintype (C i)
  decidableEq : ∀ i, DecidableEq (C i)
  inhabited : ∀ i, Inhabited (C i)
  selectable : ∀ i, SelectableType (C i)

/-- The specification of an Interactive Oracle Reduction -/
structure ProtocolSpec where
  numRounds : ℕ+
  Message : Fin numRounds → Type -- Message type for each round
  Challenge : Fin numRounds → Type -- Challenge type for each round
  Oracle : Oracleize numRounds Message -- Oracle for each round, derived from the message
  validChallenge : ValidChallenge Challenge -- Challenges can be sampled from
  validOracle : ValidOracleize Oracle -- Oracles satisfy the `ValidOracleize` conditions

def ChallengePMF (spec : ProtocolSpec) := ∀ i, PMF (spec.Challenge i)

/-- Vector of messages -/
def Messages (spec : ProtocolSpec) := ∀ i, spec.Message i

/-- Vector of challenges -/
def Challenges (spec : ProtocolSpec) := ∀ i, spec.Challenge i

/--
  The transcript of the IOR, including all messages and challenges
-/
def Transcript (spec : ProtocolSpec) := ∀ i, spec.Message i × spec.Challenge i

def Transcript.mk (msgs : Messages spec) (chals : Challenges spec) : Transcript spec := fun i => ⟨ msgs i, chals i ⟩

def Transcript.toMessages (transcript : Transcript spec) : Messages spec := fun i => (transcript i).1

def Transcript.toChallenges (transcript : Transcript spec) : Challenges spec := fun i => (transcript i).2

-- TODO: re-org this structure
structure ProverSpec (spec : ProtocolSpec)

/-- Oracle for the prover to query the verifier's challenge in round `i`.
The prover may query only once, after which the challenge oracle returns `none`. -/
def oracleChallengeSpec (spec : ProtocolSpec) (i : Fin spec.numRounds) : OracleSpec Unit where
  domain := fun _ => Unit
  range := fun _ => Option (spec.Challenge i)
  domain_decidableEq' := fun _ => decEq
  range_decidableEq' := fun _ => @instDecidableEqOption _ (spec.validChallenge.decidableEq i)
  range_inhabited' := fun _ => inferInstance
  range_fintype' := fun _ => @instFintypeOption _ (spec.validChallenge.fintype i)

/--
  The prover function for each round of the IOR, disregarding the witness input and output.
-/
structure ProverRound (spec : ProtocolSpec) (relIn : Relation) where
  PrvState : Fin (spec.numRounds + 1) → Type
  PrvRand : Fin spec.numRounds → Type
  sampleRand : ∀ i, PMF (PrvRand i)
  prove : ∀ (i : Fin spec.numRounds), relIn.Statement → PrvState i → PrvRand i
    → spec.Challenge i → spec.Message i × (PrvState (i + 1))

-- TODO: re-org this structure
structure ProverWithOracle (spec : ProtocolSpec) (oSpec : OracleSpec ι) (relIn : Relation) where
  PrvState : Fin (spec.numRounds + 1) → Type
  PrvRand : Fin spec.numRounds → Type
  sampleRand : ∀ i, PMF (PrvRand i)
  prove : ∀ (i : Fin spec.numRounds), relIn.Statement → PrvState i → PrvRand i
    → spec.Challenge i → OracleComp oSpec (spec.Message i × (PrvState (i + 1)))


/-- The full prover, including the witness input and output -/
structure Prover (spec : ProtocolSpec) (relIn : Relation) extends ProverRound spec relIn where
  fromWitnessIn : relIn.Witness → PrvState 0

def oracleMessageSpec (spec : ProtocolSpec) : OracleSpec (Fin spec.numRounds) where
  domain := fun i => spec.Oracle.Query i
  range := fun i => spec.Oracle.Response i
  domain_decidableEq' := spec.validOracle.domain_decidableEq
  range_decidableEq' := spec.validOracle.range_decidableEq
  range_inhabited' := spec.validOracle.range_inhabited
  range_fintype' := spec.validOracle.range_fintype

/-- The public-coin verifier of an IOR, which returns a boolean indicating whether the reduction is
  valid. It is itself an oracle computation that may query any of the oracles sent by the prover. -/
structure Verifier (spec : ProtocolSpec) (relIn : Relation) where
  verify : relIn.Statement → OracleComp (oracleMessageSpec spec) Bool


/-- An IOR protocol consists of an honest prover and an honest verifier, to reduce a relation
  `RelIn` to relation `RelOut` -/
structure Protocol (spec : ProtocolSpec) (relIn : Relation) (relOut : Relation) extends Prover spec relIn, Verifier spec relIn


/-- Define family of IOR specifications parameterized by `Index` -/
structure ProtocolSpecFamily where
  Index : Type
  spec : Index → ProtocolSpec

-- /-- Define family of IOR protocols parameterized by `Index` -/
structure ProtocolFamily extends ProtocolSpecFamily where
  relIn : Index → Relation
  relOut : Index → Relation
  protocol : (index : Index) → Protocol (spec index) (relIn index) (relOut index)


section Transcript

-- More stuff about transcript

/-- A partial transcript of the IOR consists of all the messages and challenges up to a certain
  round `i ≤ spec.numRounds` -/
def PartialTranscript (spec : ProtocolSpec) (i : Fin (spec.numRounds + 1)) := ∀ j : Fin spec.numRounds, (j.val < i.val) → (spec.Message j × spec.Challenge j)

/-- The empty (partial) transcript, which is the unique element of `PartialTranscript spec 0` -/
def emptyTranscript : PartialTranscript spec 0 := fun j h => by contradiction

/-- Add a new message and challenge for round `i` to a partial transcript up to round `i - 1` -/
def PartialTranscript.cons (partialTranscript : PartialTranscript spec i) (hLt : i.val < spec.numRounds) (msg : spec.Message i) (challenge : spec.Challenge i) : PartialTranscript spec (i + 1) := fun j h => by
    -- TODO: try `Fin.addCases` instead
    if h' : j.val < i.val then
      exact partialTranscript j h'
    else
      have : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt (by aesop)
      rw [this] at h
      simp at *
      have : j = i := by
        refine Fin.eq_of_val_eq ?_
        rw [Fin.val_cast_of_lt (n := spec.numRounds) hLt]
        exact Nat.eq_of_le_of_lt_succ h' h
      exact this ▸ ⟨msg, challenge⟩


-- def PartialTranscript.cons (partialTranscript : PartialTranscript spec i) (hNe : i ≠ Fin.last spec.numRounds) (msg : spec.Message <| i.castPred hNe) (challenge : spec.Challenge <| i.castPred hNe) : PartialTranscript spec (i + 1) := fun j h => by
--     -- TODO: try `Fin.addCases` instead
--     if h' : j.val < i.val then
--       exact partialTranscript j h'
--     else
--       have hLt : i.val < spec.numRounds := Fin.val_lt_last hNe
--       have : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt hLt
--       rw [this] at h
--       simp at *
--       have : j = i.castPred hNe := by
--         refine Fin.eq_of_val_eq ?_
--         exact Nat.eq_of_le_of_lt_succ h' h
--       exact this ▸ ⟨msg, challenge⟩

def Messages.toHList (messages : Messages spec) : HList := HList.ofDVec messages

def Challenges.toHList (challenges : Challenges spec) : HList := HList.ofDVec challenges

/-- Return two `HList`s, one for the messages and one for the challenges -/
def Transcript.toHList (transcript : Transcript spec) : HList × HList := ⟨ transcript.toMessages.toHList, transcript.toChallenges.toHList ⟩

def Messages.fromHList {spec : ProtocolSpec} (lMessages : HList) (hLen : lMessages.length = spec.numRounds) (h : ∀ i, lMessages[i].1 = spec.Message i) : DVec spec.Message := fun j => ((h j) ▸ lMessages[j].2)

def Challenges.fromHList {spec : ProtocolSpec} (lChallenges : HList) (hLen : lChallenges.length = spec.numRounds) (h : ∀ i, lChallenges[i].1 = spec.Challenge i) : DVec spec.Challenge := fun j => ((h j) ▸ lChallenges[j].2)

-- To get `Transcript` from two `HList`s, first convert them to `Messages` and `Challenges` and then make a transcript from that

def Transcript.toPartial (transcript : Transcript spec) (i : Fin (spec.numRounds + 1)) :
    PartialTranscript spec i := fun j _ => transcript j

def PartialTranscript.toFull (spec : ProtocolSpec)
    (partialTranscript : PartialTranscript spec spec.numRounds) : Transcript spec := fun j => partialTranscript j (by simp)

@[simp]
theorem Transcript.toPartial_toFull (spec : ProtocolSpec) (transcript : Transcript spec) :
  (transcript.toPartial spec.numRounds).toFull spec = transcript := rfl

@[simp]
theorem PartialTranscript.toFull_toPartial (spec : ProtocolSpec) (partialTranscript : PartialTranscript spec spec.numRounds) :
  (partialTranscript.toFull spec).toPartial spec.numRounds = partialTranscript := rfl

end Transcript

end Format

-- Since we are using `PMF`, this section is marked as noncomputable
noncomputable section

section Execution

-- def runFirstRound (prover : Prover spec relIn) (stmtIn : relIn.Statement) (witIn : relIn.Witness) (sampleCh : ChallengePMF spec) : PMF (PartialTranscript spec 1 × prover.PrvState 1) := do
--   let newRand ← prover.sampleRand 0
--   let challenge ← sampleCh 0
--   let state := prover.fromWitnessIn witIn
--   let (msg, newState) := prover.prove 0 stmtIn state newRand challenge
--   let newState' : prover.PrvState 1 := by
--     simp at newState
--     exact newState
--   let partialTrans := fun j h => by
--     simp [Nat.mod_eq_of_lt] at h
--     have : j = 0 := by aesop
--     exact this ▸ ⟨msg, challenge⟩
--   return ⟨partialTrans, newState'⟩


def runProverAux (prover : Prover spec relIn)
    (stmtIn : relIn.Statement) (witIn : relIn.Witness)
    (sampleCh : ChallengePMF spec) (i : Fin (spec.numRounds + 1)) :
    PMF (PartialTranscript spec i × prover.PrvState i) := do
  if h : i = 0 then
    -- Simply return the empty transcript and the initial state
    let state := prover.fromWitnessIn witIn
    return ⟨h ▸ emptyTranscript, h ▸ state⟩
  else
    -- Run the prover up to the `i - 2`-th round
    let j := Fin.pred i h
    let ⟨partialTrans, state⟩ ← runProverAux prover stmtIn witIn sampleCh j
    -- Sample new randomness and challenge for round `i - 1`
    let newRand ← prover.sampleRand j
    let challenge ← sampleCh j
    -- Run the prover for round `i - 1`
    let (msg, newState) := prover.prove j stmtIn state newRand challenge
    have newState' : prover.PrvState i := by
      simp at newState
      rw [Fin.succ_pred] at newState
      exact newState
    -- Compute new partial transcript
    let partialTransAux := partialTrans.cons (by simp)
    have partialTransAux' : spec.Message j → spec.Challenge j → PartialTranscript spec i := by
      simp at partialTransAux
      rw [Fin.succ_pred] at partialTransAux
      exact partialTransAux
    let partialTrans' := partialTransAux' msg challenge
    return ⟨partialTrans', newState'⟩
termination_by i.val
decreasing_by
  simp_wf
  refine Fin.lt_iff_val_lt_val.mpr ?_
  simp
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Nat.sub_lt_self (by decide) ((Fin.pos_iff_ne_zero' i).mpr h)

/--
  Running the IOR prover in the protocol; returns the transcript along with the final prover's state
-/
def runProver (prover : Prover spec relIn) (sampleCh : ChallengePMF spec)
    (stmtIn : relIn.Statement) (witIn : relIn.Witness) :
    PMF (Transcript spec × prover.PrvState spec.numRounds) := do
  let ⟨transcript, state⟩ ← runProverAux prover stmtIn witIn sampleCh spec.numRounds
  return ⟨transcript.toFull, state⟩

def runVerifier (verifier : Verifier spec relIn)
    (stmtIn : relIn.Statement) (transcript : Transcript spec) :
    PMF Bool := do
  -- TODO: implement this
  -- First run the prover to get oracles, then run the verifier as an oracle computation, answering each query with the corresponding oracle
  let oracles := oracleMessageSpec spec
  let oracleComp := verifier.verify stmtIn
  let decision := oracleComp.simulate' transcript.toMessages.toOracles
  return decision

/--
  An IOR execution between an arbitrary prover and an arbitrary verifier, on a given initial statement and witness.

  Returns a probability distribution over the prover's end private state and a verifier's output statement.
-/
def runProtocolWithTranscript (prover : Prover spec relIn) (verifier : Verifier spec relIn)
    (sampleCh : ChallengePMF spec) (stmtIn : relIn.Statement) (witIn : relIn.Witness) :
    PMF (Output spec × Transcript spec) := do
  let (transcript, state) ← runProver prover sampleCh stmtIn witIn
  let stmtOut ← verifier.verify stmtIn (transcript.toOracles)
  return ⟨⟨stmtOut, prover.toWitnessOut state⟩, transcript⟩


def runProtocol (prover : Prover spec relIn) (verifier : Verifier spec relIn)
    (sampleCh : ChallengePMF spec) (stmtIn : relIn.Statement) (witIn : relIn.Witness) : PMF (Output spec) := do
  let result ← runProtocolWithTranscript prover verifier sampleCh stmtIn witIn
  return result.fst

end Execution

section SecurityDefinitions

open unitInterval

/- Unit interval embedded into `NNReal` -/
instance unitInterval.toNNReal : Coe unitInterval NNReal where
  coe := fun ⟨x, h⟩ => ⟨x, (Set.mem_Icc.mp h).left⟩

section Completeness

/--
  For all valid statement-witness pair for the input relation `relIn`,
  the execution between the honest prover and the honest verifier will result in a valid pair for
  the output relation `relOut`,
  except with probability `completenessError`
-/
def completeness (spec : ProtocolSpec) (protocol : Protocol spec) (completenessError : I) : Prop :=
    ∀ stmtIn : spec.relIn.Statement,
    ∀ witIn : spec.relIn.Witness,
    spec.relIn.isValid stmtIn witIn = true →
        let output := run spec protocol.toProver protocol.toVerifier stmtIn witIn
        let prob := spec.relOut.isValid' <$> output
        prob true ≥ 1 - completenessError


/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (spec : ProtocolSpec) (protocol : Protocol spec) : Prop :=
  completeness spec protocol 0

end Completeness


section Soundness


/- We have 6 variants of soundness:

  1. (Regular) soundness
  2. Knowledge soundness
  3. State-restoration soundness
  4. State-restoration knowledge soundness
  5. Round-by-round soundness
  6. Round-by-round knowledge soundness

This does not cover other variants such as adaptive versions of the above (seems to have negligible
difference compared to non-adaptive version in the interactive setting?), or special soundness.
-/

/--
  For all initial statement `stmtIn` not in the language, all (malicious) provers with initial
  witness `witIn`, the execution will result in an invalid statement-witness pair for `relOut`
  except with probability `soundnessBound`.
-/
def soundness (spec : ProtocolSpec) (verifier : Verifier spec) (soundnessBound : ENNReal) : Prop :=
  ∀ stmtIn ∉ spec.relIn.language,
  /-
    Need to quantify over the witness because of the way we defined
    the type signature of the prover, which always takes in some witness.
    Think of this as the initializing the state of the prover.
  -/
  ∀ witIn : spec.relIn.Witness,
  ∀ prover : Prover spec,
    let output := run spec prover verifier stmtIn witIn
    let prob := spec.relOut.isValid' <$> output
    prob true ≤ soundnessBound


-- Adaptive soundness? Makes no sense in interactive setting... the most the prover will do is to
-- send the initial statement together with the first message (but this gives no extra power?) The
-- more important question is that is this property necessary for proving adaptive soundness after
-- (strong) Fiat-Shamir?

structure AdaptiveProver (spec : ProtocolSpec) extends Prover spec where
  chooseStatementIn : PrvState 0 × PrvRand 0 → spec.relIn.Statement

/--
  An extractor is defined to be a deterministic function that takes in the initial statement and the
  IOR transcript, and returns a corresponding initial witness.

  TODO: when we generalize IOR to the ROM, how do we model the extractor's ability to observe the
  prover's queries?
-/
def Extractor (spec : ProtocolSpec) :=
  spec.relIn.Statement → Transcript spec → Output spec → spec.relIn.Witness

/--
  There exists an extractor such that for all

  This is the black-box, deterministic, straightline version of knowledge soundness.
-/
def knowledgeSoundness (spec : ProtocolSpec) (verifier : Verifier spec) (knowledgeBound : ENNReal) : Prop :=
  ∃ extractor : Extractor spec,
  ∀ stmtIn : spec.relIn.Statement,
  ∀ witIn : spec.relIn.Witness,
  ∀ prover : Prover spec,
    let result := runWithTranscript spec prover verifier stmtIn witIn
    let output := Prod.fst <$> result
    let transcript := Prod.snd <$> result
    let prob := spec.relOut.isValid' <$> output
    -- TODO: fix this definition
    if prob true > knowledgeBound then
      let extractedWitIn := (fun tr out => extractor stmtIn tr out) <$> transcript <*> output
      let prob' := spec.relIn.isValid stmtIn <$> extractedWitIn
      prob' true ≥ 1 - knowledgeBound
    else
      True


def BadFunction (spec : ProtocolSpec) (relIn : Relation) :=
  (i : Fin spec.numRounds) → relIn.Statement →  PartialTranscript spec i → Prop

/--
  Round-by-round soundness should be defined for each round
-/
def roundByRoundSoundness (spec : ProtocolSpec) [ValidOracleize spec.Oracle] (relIn : Relation) (relOut : Relation) (verifier : Verifier spec relIn)
    (badFunction : BadFunction spec) (rbrSoundnessBound : Fin spec.numRounds → I) : Prop :=
  ∀ stmtIn ∉ relIn.language,
  ∀ witIn : relIn.Witness,
  ∀ prover : Prover spec relIn,
  ∀ i : Fin spec.numRounds,
    let result := runWithTranscript spec prover verifier stmtIn witIn
    let output := Prod.fst <$> result
    let transcript := Prod.snd <$> result
    let prob := relOut.isValid' <$> output
    let partialTranscript := (fun tr => tr.toPartial i) <$> transcript
    -- prob true ≤ rbrSoundnessBound i
    sorry
    -- let partialTranscript : PartialTranscript spec i := ⟨transcript.messages,
    -- transcript.challenges⟩
    -- prob true ≤ soundnessBound


end Soundness


section ZeroKnowledge


def Simulator (spec : ProtocolSpec) := spec.relIn.Statement → PMF (VerifierView spec)


/--
  We define honest-verifier zero-knowledge as follows:
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts
  generated by the simulator and the interaction between the verifier and the prover are
  (statistically) indistinguishable.
-/
def zeroKnowledge (spec : ProtocolSpec) (prover : Prover spec) : Prop :=
  ∃ simulator : Simulator spec,
  ∀ verifier : Verifier spec,
  ∀ stmtIn : spec.relIn.Statement,
  ∀ witIn : spec.relIn.Witness,
  spec.relIn.isValid stmtIn witIn = true →
    let result := runWithTranscript spec prover verifier stmtIn witIn
    let transcript := Prod.snd <$> result
    let simTranscript := simulator stmtIn
    -- let prob := spec.relOut.isValid' <$> output
    sorry

end ZeroKnowledge

end SecurityDefinitions



section Composition

def Oracleize.append (O1 : Oracleize n1 Message1) (O2 : Oracleize n2 Message2) : Oracleize (n1 + n2) (Fin.addCases Message1 Message2) where
  Query := Fin.addCases O1.Query O2.Query
  Response := Fin.addCases O1.Response O2.Response
  oracle := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j msg q
    · simp [Fin.addCases_left j] at msg
      simp [Fin.addCases_left j] at q
      simp
      exact O1.oracle j msg q
    · simp [Fin.addCases_right j] at msg
      simp [Fin.addCases_right j] at q
      simp
      exact O2.oracle j msg q


/-- Sequential composition of two protocols -/
def ProtocolSpec.append (spec1 spec2 : ProtocolSpec) : ProtocolSpec where
  numRounds := spec1.numRounds + spec2.numRounds
  Message := Fin.addCases spec1.Message spec2.Message
  Challenge := Fin.addCases spec1.Challenge spec2.Challenge
  Oracle := Oracleize.append spec1.Oracle spec2.Oracle



/-- Parallel repetition of two protocols

When proving theorems, need to add the condition that `spec1.numRounds = spec2.numRounds` -/
def ProtocolSpec.composeParallel (spec1 spec2 : ProtocolSpec) : ProtocolSpec where
  numRounds := spec1.numRounds
  Message := fun i => spec1.Message i × spec2.Message i
  Challenge := fun i => spec1.Challenge i × spec2.Challenge i
  Oracle := sorry
  -- spec1.Oracle × spec2.Oracle
  -- OracleQuery := fun i => spec1.OracleQuery i × spec2.OracleQuery i
  -- OracleResponse := fun i => spec1.OracleResponse i × spec2.OracleResponse i
  -- oracleFromMessage := fun i msg q => (spec1.oracleFromMessage i msg.1 q.1, spec2.oracleFromMessage i msg.2 q.2)


end Composition

end

end IOR
