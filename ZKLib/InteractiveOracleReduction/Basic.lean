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

/-- `Sampleable` is a type class for types that can be sampled uniformly at random (via the VCV framework).

This is mostly used for uniform sampling from challenges in an interactive protocol. -/
class Sampleable (α : Type) extends Fintype α, Inhabited α, SelectableType α where
  [toDecidableEq : DecidableEq α]

section Format

/-- Type signature of a public-coin interactive protocol.
`ProtocolSpec` is parameterized by the number of rounds `numRounds`. -/
@[ext]
structure ProtocolSpec (numRounds : ℕ) where
  Message : Fin numRounds → Type -- Message type for each round
  Challenge : Fin numRounds → Type -- Challenge type for each round

/-- The empty protocol, with no rounds -/
@[inline, reducible, simps]
def emptyPSpec : ProtocolSpec 0 where
  Message := isEmptyElim
  Challenge := isEmptyElim

/-- The empty protocol is the unique protocol with 0 rounds -/
instance : Unique (ProtocolSpec 0) where
  default := emptyPSpec
  uniq := fun spec => by ext i <;> exact Fin.elim0 i

/-- Type signature of a public-coin interactive oracle protocol `OracleProtocolSpec`,
parameterized by the number of rounds `numRounds`.

The only difference to `ProtocolSpec` is that the verifier can only access
the prover's messages via oracle queries.
-/
@[ext]
structure OracleProtocolSpec (numRounds : ℕ) extends ProtocolSpec numRounds where
  Query : Fin numRounds → Type -- Query type for oracle in each round
  Response : Fin numRounds → Type -- Response type for oracle in each round
  -- Transforming messages to oracles that take queries and return responses
  oracleize : ∀ i, Message i → Query i → Response i

@[inline, reducible, simps]
def emptyOraclePSpec : OracleProtocolSpec 0 where
  toProtocolSpec := emptyPSpec
  Query := isEmptyElim
  Response := isEmptyElim
  oracleize := isEmptyElim

instance : Unique (OracleProtocolSpec 0) where
  default := emptyOraclePSpec
  uniq := fun spec => by
    ext i <;> try { exact Fin.elim0 i }
    exact Function.hfunext rfl (fun i _ _ => Fin.elim0 i)

@[simps]
instance {n : ℕ} : Coe (OracleProtocolSpec n) (ProtocolSpec n) where
  coe := fun oraclePSpec => oraclePSpec.toProtocolSpec

/-- Spec for the verifier's challenges, invoked in the process of running the protocol -/
@[simps!]
def challengeOracle (PSpec : ProtocolSpec n) [∀ i, Sampleable (PSpec.Challenge i)] : OracleSpec (Fin n) where
  domain := fun _ => Unit
  range := fun i => PSpec.Challenge i
  domain_decidableEq' := fun _ => decEq
  range_decidableEq' := fun _ => Sampleable.toDecidableEq
  range_inhabited' := fun _ => Sampleable.toInhabited
  range_fintype' := fun _ => Sampleable.toFintype

/-- Vector of message types -/
@[inline, reducible, simp] def Messages (PSpec : ProtocolSpec n) := ∀ i, PSpec.Message i

/-- Vector of challenge types -/
@[inline, reducible, simp] def Challenges (PSpec : ProtocolSpec n) := ∀ i, PSpec.Challenge i

/--
  The transcript of an interactive protocol, which is a list of messages and challenges according to their type signatures
-/
structure Transcript (PSpec : ProtocolSpec n) where
  messages : Messages PSpec
  challenges : Challenges PSpec

/-- The prover of an interactive protocol.

Defined by a proving function `prove` for each round `i` that takes in
the challenge for that round and performs an oracle stateful computation,
returning the next message in the protocol.-/
structure ProverRound (PSpec : ProtocolSpec n) (OSpec : OracleSpec ι) (PrvState : Type) where
  prove : (i : Fin n) → PSpec.Challenge i →
    StateT PrvState (OracleComp OSpec) (PSpec.Message i)

/-- We decouple the "loading" of the statement and witness into
the prover's internal state, from the proving process in each round -/
structure Prover (PSpec : ProtocolSpec n) (OSpec : OracleSpec ι) (PrvState : Type)
    (Statement Witness : Type) extends ProverRound PSpec OSpec PrvState where
  loadState : Statement → Witness → OracleComp OSpec PrvState

/-- The verifier of an interactive protocol (that may read messages in full) -/
structure Verifier (PSpec : ProtocolSpec n) (OSpec : OracleSpec ι) (Statement : Type) where
  verify : Statement → Transcript PSpec → OracleComp OSpec Bool

/-- A list of queries to the prover's messages -/
@[inline, reducible] def QueryList (oraclePSpec : OracleProtocolSpec n) :=
  List ((i : Fin n) × (oraclePSpec.Query i))

/-- A list of responses to queries, computed from the prover's messages -/
@[inline, reducible] def ResponseList (oraclePSpec : OracleProtocolSpec n) :=
  List ((i : Fin n) × (oraclePSpec.Query i) × (oraclePSpec.Response i))

/-- The verifier of an interactive oracle protocol
(that may only make queries to the prover's messages) -/
structure OracleVerifier (oraclePSpec : OracleProtocolSpec n) (OSpec : OracleSpec ι)
    (Statement : Type) where
  -- Generate a list of queries of the form `(i, query)`,
  -- where `i` is the round index and `query` is the query to the oracle
  genQueries : Statement → @Challenges n oraclePSpec →
    OracleComp OSpec (QueryList oraclePSpec)
  -- Verify the proof based on the list of responses
  verify : Statement → @Challenges n oraclePSpec → ResponseList oraclePSpec →
    OracleComp OSpec Bool

/-- We can always turn an oracle verifier into a (non-oracle) verifier -/
def OracleVerifier.toVerifier {n : ℕ} {oraclePSpec : OracleProtocolSpec n} (verifier : OracleVerifier oraclePSpec OSpec Statement) :
    Verifier (n := n) oraclePSpec OSpec Statement where
  verify := fun stmt transcript => do
    let queries ← verifier.genQueries stmt transcript.challenges
    let responses ← queries.mapM (fun ⟨j, q⟩ =>
      pure ⟨j, q, oraclePSpec.oracleize j (transcript.messages j) q⟩ )
    verifier.verify stmt transcript.challenges responses

instance : Coe (OracleVerifier oraclePSpec OSpec Statement)
    (Verifier oraclePSpec.toProtocolSpec OSpec Statement) :=
  ⟨OracleVerifier.toVerifier⟩

structure Protocol (PSpec : ProtocolSpec n) (OSpec : OracleSpec ι)
    (PrvState : Type) (Statement Witness : Type) where
  prover : Prover PSpec OSpec PrvState Statement Witness
  verifier : Verifier PSpec OSpec Statement

structure OracleProtocol (oraclePSpec : OracleProtocolSpec n) (OSpec : OracleSpec ι)
    (PrvState : Type) (Statement Witness : Type) where
  prover : Prover (n := n) oraclePSpec OSpec PrvState Statement Witness
  verifier : OracleVerifier oraclePSpec OSpec Statement

def OracleProtocol.toProtocol (oracleProtocol : OracleProtocol oraclePSpec OSpec PrvState Statement Witness) :
    Protocol oraclePSpec.toProtocolSpec OSpec PrvState Statement Witness :=
  ⟨oracleProtocol.prover, oracleProtocol.verifier⟩

instance : Coe (OracleProtocol OPSpec OSpec PrvState Statement Witness)
    (Protocol OPSpec.toProtocolSpec OSpec PrvState Statement Witness) :=
  ⟨OracleProtocol.toProtocol⟩

section Transcript

@[simps]
def emptyTranscript : Transcript emptyPSpec where
  messages := isEmptyElim
  challenges := isEmptyElim

-- More stuff about transcript

/-- A partial transcript of the IOR consists of all the messages and challenges
up to a certain round `i ≤ spec.numRounds` -/
structure PartialTranscript (PSpec : ProtocolSpec n) (i : Fin (n + 1)) where
  messages : ∀ j : Fin n, (j.val < i.val) → (PSpec.Message j)
  challenges : ∀ j : Fin n, (j.val < i.val) → (PSpec.Challenge j)

/-- The empty (partial) transcript, which is the unique element of `PartialTranscript spec 0` -/
def emptyPartialTranscript : PartialTranscript PSpec 0 where
  messages := fun j h => by contradiction
  challenges := fun j h => by contradiction

/-- Add a new message and challenge for round `i` to a partial transcript up to round `i - 1` -/
def PartialTranscript.cons {spec : ProtocolSpec n} (partialTranscript : PartialTranscript spec i)
    (hLt : i.val < n) (hPos : i ≠ Fin.last n) (msg : spec.Message (i.castPred hPos))
    (challenge : spec.Challenge (i.castPred hPos)) : PartialTranscript spec (i + 1) where
  messages := fun j h => by
    if h' : j.val < i.val then
      exact partialTranscript.messages j h'
    else
      have : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt (by aesop)
      rw [this] at h
      simp at *
      have : NeZero n := ⟨by omega⟩
      have : j = i.castPred hPos := by
        refine Fin.eq_of_val_eq ?_
        simp
        exact Nat.eq_of_le_of_lt_succ h' h
      exact this ▸ msg
  challenges := fun j h => by
    if h' : j.val < i.val then
      exact partialTranscript.challenges j h'
    else
      have : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt (by aesop)
      rw [this] at h
      simp at *
      have : j = i.castPred hPos := by
        refine Fin.eq_of_val_eq ?_
        simp
        exact Nat.eq_of_le_of_lt_succ h' h
      exact this ▸ challenge

def Transcript.toPartial {spec : ProtocolSpec n} (transcript : Transcript spec) (i : Fin (n + 1)) :
    PartialTranscript spec i where
  messages := fun j _ => transcript.messages j
  challenges := fun j _ => transcript.challenges j

def PartialTranscript.toFull {spec : ProtocolSpec n}
    (partialTranscript : PartialTranscript spec n) : Transcript spec where
  messages := fun j => partialTranscript.messages j (by simp)
  challenges := fun j => partialTranscript.challenges j (by simp)

@[simp]
theorem Transcript.toPartial_toFull {spec : ProtocolSpec n} (transcript : Transcript spec) :
  (transcript.toPartial n).toFull = transcript := rfl

@[simp]
theorem PartialTranscript.toFull_toPartial {spec : ProtocolSpec n} (partialTranscript : PartialTranscript spec n) :
  (partialTranscript.toFull).toPartial n = partialTranscript := rfl

end Transcript

end Format

section Execution

variable {ι : Type} [DecidableEq ι] {OSpec : OracleSpec ι} {n : ℕ} {PSpec : ProtocolSpec n} {OPSpec : OracleProtocolSpec n} {PrvState : Type} {Statement Witness : Type}

/--
  Auxiliary function for running the prover in an interactive protocol.

  Given round index `i`, returns the partial transcript up to that round and the prover's state at that round
-/
def runProverAux [∀ i, Sampleable (PSpec.Challenge i)]
    (prover : Prover PSpec OSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) (i : Fin (n + 1)) :
    OracleComp (OSpec ++ₒ challengeOracle PSpec)
        (PartialTranscript PSpec i × PrvState) := do
  if h : i = 0 then
    -- If `i = 0`, simply load the statement and the witness
    let state ← liftComp (prover.loadState stmt wit)
    -- Return the empty transcript and the state
    return ⟨h ▸ emptyPartialTranscript, state⟩
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
      simp at partialTransAux; sorry
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
def runProver [∀ i, Sampleable (PSpec.Challenge i)]
    (prover : Prover PSpec OSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) : OracleComp
    (OSpec ++ₒ challengeOracle PSpec)
    (Transcript PSpec × PrvState) := do
  let ⟨transcript, state⟩ ← runProverAux prover stmt wit n
  return ⟨transcript.toFull, state⟩

/-- Run the (non-oracle) verifier in the interactive protocol

Simply reads the statement and the transcript, and outputs a decision
-/
def runVerifier (verifier : Verifier PSpec OSpec Statement)
    (stmt : Statement) (transcript : Transcript PSpec) :
    OracleComp OSpec Bool := do
  let decision ← verifier.verify stmt transcript
  return decision

/-- Run the oracle verifier in the interactive protocol

Returns the verifier's output and the log of queries made by the verifier.
-/
def runOracleVerifier (verifier : OracleVerifier OPSpec OSpec Statement)
    (stmt : Statement) (transcript : Transcript OPSpec.toProtocolSpec) :
    OracleComp OSpec (Bool × ResponseList OPSpec) := do
  let queries ← verifier.genQueries stmt transcript.challenges
  let oracles := fun i => OPSpec.oracleize i (transcript.messages i)
  let responses ← List.mapM (fun ⟨j, q⟩ => pure ⟨j, q, oracles j q⟩ ) queries
  let decision ← verifier.verify stmt transcript.challenges responses
  return ⟨decision, responses⟩

/--
  An execution between an arbitrary prover and an arbitrary verifier, on a given initial statement and witness.

  Returns the verifier's decision, the transcript, and the prover's final state
-/
def runProtocol [∀ i, Sampleable (PSpec.Challenge i)]
(protocol : Protocol PSpec OSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) : OracleComp
    (OSpec ++ₒ challengeOracle PSpec)
    (Bool × Transcript PSpec × PrvState) := do
  let (transcript, state) ← runProver protocol.prover stmt wit
  let decision ← liftComp (runVerifier protocol.verifier stmt transcript)
  return (decision, transcript, state)

/-- Run an interactive oracle protocol

Returns the verifier's decision, the transcript, and the log of all oracle queries to the prover's messages, and the prover's final state
-/
def runOracleProtocol [∀ i, Sampleable (OPSpec.Challenge i)]
    (protocol : OracleProtocol OPSpec OSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) : OracleComp
    (OSpec ++ₒ challengeOracle OPSpec.toProtocolSpec)
    (Bool × Transcript OPSpec.toProtocolSpec × ResponseList OPSpec × PrvState) := do
  let (transcript, state) ← runProver protocol.prover stmt wit
  let ⟨decision, queries⟩ ←
    liftComp (runOracleVerifier protocol.verifier stmt transcript)
  return (decision, transcript, queries, state)

end Execution
