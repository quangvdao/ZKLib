/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

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

-- Figure out where to put this instance
instance instDecidableEqOption [DecidableEq α] : DecidableEq (Option α) := inferInstance

open OracleComp OracleSpec SubSpec

section Format

/--
  A class to ensure that the verifier's challenges are finite, decidable, inhabited, and sampleable.
-/
class ValidChallenge (C : Fin n → Type) where
  fintype : ∀ i, Fintype (C i)
  decidableEq : ∀ i, DecidableEq (C i)
  inhabited : ∀ i, Inhabited (C i)
  selectable : ∀ i, SelectableType (C i)

/-- Specification of a public-coin interactive protocol -/
class ProtocolSpec where
  numRounds : ℕ+ -- Number of rounds
  Message : Fin numRounds → Type -- Message type for each round
  Challenge : Fin numRounds → Type -- Challenge type for each round
  validChallenge : ValidChallenge Challenge -- Challenges can be sampled from


/-- Specification of a public-coin interactive oracle protocol.

  The only difference is that the verifier can only access the prover's messages via oracle queries.
-/
class OracleProtocolSpec extends ProtocolSpec where
  Query : Fin numRounds → Type -- Query type for oracle in each round
  Response : Fin numRounds → Type -- Response type for oracle in each round
  -- Transforming messages to oracles that take queries and return responses
  oracle : ∀ i, Message i → Query i → Response i

instance : Coe OracleProtocolSpec ProtocolSpec where
  coe := fun PSpec => PSpec.toProtocolSpec

/-- Spec for the verifier's challenges, invoked in the process of running the protocol -/
def challengeOSpec (PSpec : ProtocolSpec) : OracleSpec (Fin PSpec.numRounds) where
  domain := fun _ => Unit
  range := fun i => PSpec.Challenge i
  domain_decidableEq' := fun _ => decEq
  range_decidableEq' := fun i => PSpec.validChallenge.decidableEq i
  range_inhabited' := fun i => PSpec.validChallenge.inhabited i
  range_fintype' := fun i => PSpec.validChallenge.fintype i

/-- Vector of message types -/
@[inline, reducible] def Messages (PSpec : ProtocolSpec) := ∀ i, PSpec.Message i

/-- Vector of challenge types -/
@[inline, reducible] def Challenges (PSpec : ProtocolSpec) := ∀ i, PSpec.Challenge i

/--
  The type for the IOR transcript, including all message and challenge types
-/
structure Transcript (PSpec : ProtocolSpec) where
  messages : Messages PSpec
  challenges : Challenges PSpec

set_option pp.universes true

/-- The prover of an interactive protocol
(it doesn't matter whether the protocol has oracles to messages or not) -/
class Prover (PSpec : ProtocolSpec) (OSpec : OracleSpec ι) where
  PrvState : Type
  loadState {Statement Witness : Type} : Statement → Witness → PrvState
  prove : (i : Fin PSpec.numRounds) → PSpec.Challenge i → StateT PrvState (OracleComp OSpec) (PSpec.Message i)

/-- The verifier of an interactive protocol (that may read messages in full) -/
class Verifier (PSpec : ProtocolSpec) (OSpec : OracleSpec ι) where
  verify : Statement → Transcript PSpec → OracleComp OSpec Bool

/-- A list of queries to the prover's messages -/
@[inline, reducible] def QueryList (PSpec : OracleProtocolSpec) := List ((i : Fin PSpec.numRounds) × (PSpec.Query i))

/-- A list of responses to queries, computed from the prover's messages -/
@[inline, reducible] def ResponseList (PSpec : OracleProtocolSpec) := List ((i : Fin PSpec.numRounds) × (PSpec.Query i) × (PSpec.Response i))

/-- The verifier of an interactive oracle protocol (that may only make queries to the prover's messages) -/
class OracleVerifier (PSpec : OracleProtocolSpec) (OSpec : OracleSpec ι) where
  -- Generate a list of queries of the form `(i, query)`,
  -- where `i` is the round index and `query` is the query to the oracle
  genQueries : Statement → Challenges PSpec →
    OracleComp OSpec (QueryList PSpec)
  -- Verify the proof based on the list of responses
  verify : Statement → Challenges PSpec → ResponseList PSpec →
    OracleComp OSpec Bool

class Protocol (PSpec : ProtocolSpec) (OSpec : OracleSpec ι)
    extends Prover PSpec OSpec, Verifier PSpec OSpec

class OracleProtocol (PSpec : OracleProtocolSpec) (OSpec : OracleSpec ι)
    extends Prover PSpec OSpec, OracleVerifier PSpec OSpec

section Transcript

-- More stuff about transcript

/-- A partial transcript of the IOR consists of all the messages and challenges
up to a certain round `i ≤ spec.numRounds` -/
structure PartialTranscript (PSpec : ProtocolSpec) (i : Fin (PSpec.numRounds + 1)) where
  messages : ∀ j : Fin PSpec.numRounds, (j.val < i.val) → (PSpec.Message j)
  challenges : ∀ j : Fin PSpec.numRounds, (j.val < i.val) → (PSpec.Challenge j)

/-- The empty (partial) transcript, which is the unique element of `PartialTranscript spec 0` -/
def emptyTranscript : PartialTranscript PSpec 0 where
  messages := fun j h => by contradiction
  challenges := fun j h => by contradiction

/-- Add a new message and challenge for round `i` to a partial transcript up to round `i - 1` -/
def PartialTranscript.cons (partialTranscript : PartialTranscript PSpec i)
    (hLt : i.val < PSpec.numRounds) (msg : PSpec.Message i)
    (challenge : PSpec.Challenge i) : PartialTranscript PSpec (i + 1) where
  messages := fun j h => by
    if h' : j.val < i.val then
      exact partialTranscript.messages j h'
    else
      have : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt (by aesop)
      rw [this] at h
      simp at *
      have : j = i := by
        refine Fin.eq_of_val_eq ?_
        rw [Fin.val_cast_of_lt (n := PSpec.numRounds) hLt]
        exact Nat.eq_of_le_of_lt_succ h' h
      exact this ▸ msg
  challenges := fun j h => by
    if h' : j.val < i.val then
      exact partialTranscript.challenges j h'
    else
      have : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt (by aesop)
      rw [this] at h
      simp at *
      have : j = i := by
        refine Fin.eq_of_val_eq ?_
        rw [Fin.val_cast_of_lt (n := PSpec.numRounds) hLt]
        exact Nat.eq_of_le_of_lt_succ h' h
      exact this ▸ challenge

def Transcript.toPartial (transcript : Transcript spec) (i : Fin (spec.numRounds + 1)) :
    PartialTranscript spec i where
  messages := fun j _ => transcript.messages j
  challenges := fun j _ => transcript.challenges j

def PartialTranscript.toFull (spec : ProtocolSpec)
    (partialTranscript : PartialTranscript spec spec.numRounds) : Transcript spec where
  messages := fun j => partialTranscript.messages j (by simp)
  challenges := fun j => partialTranscript.challenges j (by simp)

@[simp]
theorem Transcript.toPartial_toFull (spec : ProtocolSpec) (transcript : Transcript spec) :
  (transcript.toPartial spec.numRounds).toFull spec = transcript := rfl

@[simp]
theorem PartialTranscript.toFull_toPartial (spec : ProtocolSpec) (partialTranscript : PartialTranscript spec spec.numRounds) :
  (partialTranscript.toFull spec).toPartial spec.numRounds = partialTranscript := rfl

end Transcript

end Format

section Execution

variable {ι : Type} [DecidableEq ι] {OSpec : OracleSpec ι}

/--
  Auxiliary function for running the prover in an interactive protocol.

  Given round index `i`, returns the partial transcript up to that round and the prover's state at that round
-/
def runProverAux (prover : Prover PSpec OSpec) (stmt : Statement)
    (wit : Witness) (i : Fin (PSpec.numRounds + 1)) :
    OracleComp (OSpec ++ₒ challengeOSpec PSpec)
        (PartialTranscript PSpec i × prover.PrvState) := do
  if h : i = 0 then
    -- If `i = 0`, simply load the statement and the witness
    let state := prover.loadState stmt wit
    -- Return the empty transcript and the state
    return ⟨h ▸ emptyTranscript, state⟩
  else
    let j := Fin.pred i h
    -- Run the prover up to the `i - 2`-th round
    let ⟨partialTrans, state⟩ ← runProverAux prover stmt wit j
    -- Query the verifier's challenge for round `i - 1`
    let challenge : PSpec.Challenge j ← query (Sum.inr j) ()
    -- Run the prover for round `i - 1`
    let proverRun := fun state => liftComp (prover.prove j challenge state)
    let ⟨msg, newState⟩ ← StateT.run proverRun state
    -- Massage the partial transcript to match the expected type
    let partialTransAux := partialTrans.cons (by simp)
    have partialTransAux : PSpec.Message j → PSpec.Challenge j → PartialTranscript PSpec i := by
      rwa [Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.cast_val_eq_self,
        Fin.coeSucc_eq_succ, Fin.succ_pred] at partialTransAux
    let partialTrans := partialTransAux msg challenge
    -- Return the new partial transcript and state
    return ⟨partialTrans, newState⟩
termination_by i.val
decreasing_by
  -- Can we make this simpler?
  simp_wf
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Nat.sub_lt_self (by decide) ((Fin.pos_iff_ne_zero' i).mpr h)

/--
  Run the prover in the interactive protocol

  Returns the transcript along with the final prover's state
-/
def runProver (prover : Prover PSpec OSpec) (stmt : Statement)
    (wit : Witness) : OracleComp (OSpec ++ₒ challengeOSpec PSpec)
    (Transcript PSpec × prover.PrvState) := do
  let ⟨transcript, state⟩ ← runProverAux prover stmt wit PSpec.numRounds
  return ⟨transcript.toFull, state⟩

/-- Run the (non-oracle) verifier in the interactive protocol

Simply reads the statement and the transcript, and outputs a decision
-/
def runVerifier (verifier : Verifier PSpec OSpec)
    (stmt : Statement) (transcript : Transcript PSpec) :
    OracleComp OSpec Bool := do
  let decision ← verifier.verify stmt transcript
  return decision

/-- Run the oracle verifier in the interactive protocol

Returns the verifier's output and the log of queries made by the verifier.
-/
def runOracleVerifier (verifier : OracleVerifier PSpec OSpec)
    (stmt : Statement) (transcript : Transcript PSpec) :
    OracleComp OSpec (Bool × ResponseList PSpec) := do
  let queries ← verifier.genQueries stmt transcript.challenges
  let oracles := fun i => PSpec.oracle i (transcript.messages i)
  let responses ← List.mapM (fun ⟨j, q⟩ => pure ⟨j, q, oracles j q⟩ ) queries
  let decision ← verifier.verify stmt transcript.challenges responses
  return ⟨decision, responses⟩

/--
  An execution between an arbitrary prover and an arbitrary verifier, on a given initial statement and witness.

  Returns the verifier's decision, the transcript, and the prover's final state
-/
def runProtocol (protocol : Protocol PSpec OSpec)
    (stmt : Statement) (wit : Witness) : OracleComp
    (OSpec ++ₒ challengeOSpec PSpec)
    (Bool × Transcript PSpec × protocol.PrvState) := do
  let (transcript, state) ← runProver protocol.toProver stmt wit
  let decision ← liftComp (runVerifier protocol.toVerifier stmt transcript)
  return (decision, transcript, state)

/-- Run an interactive oracle protocol

Returns the verifier's decision, the transcript, and the log of all oracle queries to the prover's messages, and the prover's final state
-/
def runOracleProtocol (protocol : OracleProtocol PSpec OSpec)
    (stmt : Statement) (wit : Witness) : OracleComp
    (OSpec ++ₒ challengeOSpec PSpec)
    (Bool × Transcript PSpec × ResponseList PSpec × protocol.PrvState) := do
  let (transcript, state) ← runProver protocol.toProver stmt wit
  let ⟨decision, queries⟩ ←
    liftComp (runOracleVerifier protocol.toOracleVerifier stmt transcript)
  return (decision, transcript, queries, state)

end Execution
