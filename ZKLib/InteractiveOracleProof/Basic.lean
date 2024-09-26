/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.Relation.Basic
import ZKLib.ToVCVio.Oracle
import ZKLib.Data.Math.Fin

/-!
# Interactive Oracle Proofs

We define (public-coin) interactive oracle proofs (IOPs). This is an interactive protocol
between a prover and a verifier with the following format:

  - At the beginning, the prover and verifier both hold a public statement `x` (and potentially have
    access to some public parameters `pp`). The prover may also hold some private state which in
    particular may contain a witness `w` to the statement `x`.

  - In each round, the verifier sends some random challenges, and the prover sends back responses to
    the challenges. The responses are received as oracles by the verifier. The verifier is only
    allowed to query these oracles in specific ways.

  - At the end of the interaction, the verifier outputs a decision.

Along the way, we also define Interactive Proofs (IPs) as a special kind of IOPs where
the verifier can see the full messages. Our formalization also allows both prover and verifier
to have access to some shared oracle.

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

/-- `ToOracle` provides an oracle interface for a type `Message`.
It defines the query type `Query`, the response type `Response`, and the transformation `toOracle` that transforms a message into an oracle. -/
@[ext]
class ToOracle (Message : Type) where
  Query : Type
  Response : Type
  respond : Message → Query → Response

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

instance : Inhabited (ProtocolSpec 0) where
  default := emptyPSpec

/-- The empty protocol is the unique protocol with 0 rounds -/
instance : Unique (ProtocolSpec 0) where
  default := default
  uniq := fun spec => by ext i <;> exact Fin.elim0 i

/-- A protocol with only one round, and with the given message and challenge types -/
@[inline, reducible, simps]
def ProtocolSpec.mkSingle (Message : Type) (Challenge : Type) : ProtocolSpec 1 where
  Message := fun _ => Message
  Challenge := fun _ => Challenge

/-- Spec for the verifier's challenges, invoked in the process of running the protocol -/
@[simps]
def challengeOracle (pSpec : ProtocolSpec n) [∀ i, Sampleable (pSpec.Challenge i)] : OracleSpec (Fin n) where
  domain := fun _ => Unit
  range := fun i => pSpec.Challenge i
  domain_decidableEq' := fun _ => decEq
  range_decidableEq' := fun _ => Sampleable.toDecidableEq
  range_inhabited' := fun _ => Sampleable.toInhabited
  range_fintype' := fun _ => Sampleable.toFintype

/--
  The transcript of an interactive protocol, which is a list of messages and challenges according to their type signatures
-/
@[ext]
structure Transcript (pSpec : ProtocolSpec n) where
  messages : ∀ i, pSpec.Message i
  challenges : ∀ i, pSpec.Challenge i

@[inline, reducible]
def emptyTranscript : Transcript emptyPSpec where
  messages := isEmptyElim
  challenges := isEmptyElim

/-- The prover of an interactive protocol.

Defined by a proving function `prove` for each round `i` that takes in
the challenge for that round and performs an oracle stateful computation,
returning the next message in the protocol.-/
structure ProverRound (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (PrvState : Type) where
  prove : (i : Fin n) → pSpec.Challenge i →
    StateT PrvState (OracleComp oSpec) (pSpec.Message i)

structure ProverRound' {ι : Type} {n : ℕ} {Message : Fin n → Type} {Challenge : Fin n → Type} {oSpec : OracleSpec ι} (PrvState : Type) where
  prove : (i : Fin n) → Challenge i →
    StateT PrvState (OracleComp oSpec) (Message i)

/-- We decouple the "loading" of the statement and witness into
the prover's internal state, from the proving process in each round -/
class Prover (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (PrvState : Type)
    (Statement Witness : Type) extends ProverRound pSpec oSpec PrvState where
  load : Statement → Witness → OracleComp oSpec PrvState

/-- The verifier of an interactive protocol (that may read messages in full) -/
class Verifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement : Type) where
  verify : Statement → Transcript pSpec → OracleComp oSpec Bool

/-- A list of queries to the prover's messages -/
@[inline, reducible]
def QueryList (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)] :=
  List ((i : Fin n) × (O i).Query)

/-- A list of responses to queries, computed from the prover's messages -/
@[inline, reducible]
def ResponseList (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)] :=
  List ((i : Fin n) × (O i).Query × (O i).Response)

/-- The verifier of an interactive oracle protocol
(that may only make queries to the prover's messages) -/
structure OracleVerifier (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)]
    (oSpec : OracleSpec ι) (Statement : Type) where
  -- Generate a list of queries of the form `(i, query)`,
  -- where `i` is the round index and `query` is the query to the oracle
  genQueries : Statement → (∀ i, pSpec.Challenge i) → OracleComp oSpec (QueryList pSpec)
  -- Verify the proof based on the list of responses
  verify : Statement → (∀ i, pSpec.Challenge i) → ResponseList pSpec → OracleComp oSpec Bool

/-- We can always turn an oracle verifier into a (non-oracle) verifier -/
def OracleVerifier.toVerifier {pSpec : ProtocolSpec n} [O : ∀ i, ToOracle (pSpec.Message i)] (verifier : OracleVerifier pSpec oSpec Statement) :
    Verifier pSpec oSpec Statement where
  verify := fun stmt transcript => do
    let queries ← verifier.genQueries stmt transcript.challenges
    let responses ← queries.mapM (fun ⟨j, q⟩ =>
      pure ⟨j, q, (O j).respond (transcript.messages j) q⟩ )
    verifier.verify stmt transcript.challenges responses

instance {pSpec : ProtocolSpec n} [∀ i, ToOracle (pSpec.Message i)] : Coe (OracleVerifier pSpec oSpec Statement)
    (Verifier pSpec oSpec Statement) :=
  ⟨OracleVerifier.toVerifier⟩

structure Protocol (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (PrvState : Type) (Statement Witness : Type) where
  prover : Prover pSpec oSpec PrvState Statement Witness
  verifier : Verifier pSpec oSpec Statement

structure OracleProtocol (pSpec : ProtocolSpec n) [∀ i, ToOracle (pSpec.Message i)] (oSpec : OracleSpec ι)
    (PrvState : Type) (Statement Witness : Type) where
  prover : Prover pSpec oSpec PrvState Statement Witness
  verifier : OracleVerifier pSpec oSpec Statement

def OracleProtocol.toProtocol {pSpec : ProtocolSpec n} [∀ i, ToOracle (pSpec.Message i)] (oracleProtocol : OracleProtocol pSpec oSpec PrvState Statement Witness) :
    Protocol pSpec oSpec PrvState Statement Witness :=
  ⟨oracleProtocol.prover, oracleProtocol.verifier⟩

instance {pSpec : ProtocolSpec n} [∀ i, ToOracle (pSpec.Message i)] : Coe (OracleProtocol pSpec oSpec PrvState Statement Witness)
    (Protocol pSpec oSpec PrvState Statement Witness) :=
  ⟨OracleProtocol.toProtocol⟩

end Format

section Restrict

/-- For a protocol specification `pSpec` with `n` rounds, restrict `pSpec` to the first `cutoff` rounds. -/
@[inline, reducible, simps]
def ProtocolSpec.take (pSpec : ProtocolSpec n) (cutoff : ℕ) (h : cutoff ≤ n) : ProtocolSpec cutoff where
  Message := Fin.take pSpec.Message cutoff h
  Challenge := Fin.take pSpec.Challenge cutoff h

/-- For a protocol specification `pSpec` with `n` rounds, restrict `pSpec` to the last `cutoff` rounds. -/
@[inline, reducible, simps]
def ProtocolSpec.rtake (pSpec : ProtocolSpec n) (cutoff : ℕ) (h : cutoff ≤ n) : ProtocolSpec cutoff where
  Message := Fin.rtake pSpec.Message cutoff h
  Challenge := Fin.rtake pSpec.Challenge cutoff h

@[simp]
theorem ProtocolSpec.take_nil (pSpec : ProtocolSpec n) :
    ProtocolSpec.take pSpec 0 (by omega) = default := by
  ext i <;> exact Fin.elim0 i

@[simp]
theorem ProtocolSpec.take_self (pSpec : ProtocolSpec n) :
    ProtocolSpec.take pSpec n (by omega) = pSpec := by
  ext i <;> simp [ProtocolSpec.take]

@[simp]
theorem ProtocolSpec.rtake_nil (pSpec : ProtocolSpec n) :
    ProtocolSpec.rtake pSpec 0 (by omega) = default := by
  ext i <;> exact Fin.elim0 i

@[simp]
theorem ProtocolSpec.rtake_self (pSpec : ProtocolSpec n) :
    ProtocolSpec.rtake pSpec n (by omega) = pSpec := by
  ext i <;> simp [ProtocolSpec.rtake, Fin.natAdd]

def Transcript.take {pSpec : ProtocolSpec n} (transcript : Transcript pSpec) (cutoff : ℕ) (h : cutoff ≤ n) : Transcript (pSpec.take cutoff h) where
  messages := Fin.take transcript.messages cutoff h
  challenges := Fin.take transcript.challenges cutoff h

def Transcript.rtake {pSpec : ProtocolSpec n} (transcript : Transcript pSpec) (cutoff : ℕ) (h : cutoff ≤ n) : Transcript (pSpec.rtake cutoff h) where
  messages := Fin.rtake transcript.messages cutoff h
  challenges := Fin.rtake transcript.challenges cutoff h

end Restrict

section Composition

/-- Adding a round with type `Message` and `Challenge` to the beginning of a `ProtocolSpec` -/
def ProtocolSpec.cons (pSpec : ProtocolSpec n) (Message : Type) (Challenge : Type) :
    ProtocolSpec (n + 1) where
  Message := Fin.cons Message pSpec.Message
  Challenge := Fin.cons Challenge pSpec.Challenge

/-- Adding a round with type `Message` and `Challenge` to the end of a `ProtocolSpec` -/
def ProtocolSpec.snoc (pSpec : ProtocolSpec n) (Message : Type) (Challenge : Type) :
    ProtocolSpec (n + 1) where
  Message := Fin.snoc pSpec.Message Message
  Challenge := Fin.snoc pSpec.Challenge Challenge

/-- Appending two `ProtocolSpec`s via appending their `Message` and `Challenge` types -/
def ProtocolSpec.append (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) :
    ProtocolSpec (m + n) where
  Message := Fin.append pSpec.Message pSpec'.Message
  Challenge := Fin.append pSpec.Challenge pSpec'.Challenge

infixl : 65 " ++ₚ " => ProtocolSpec.append

@[simp]
theorem ProtocolSpec.snoc_eq_append {Message Challenge : Type} {pSpec : ProtocolSpec m} :
    pSpec.snoc Message Challenge = pSpec ++ₚ .mkSingle Message Challenge := by
  ext i <;> simp [ProtocolSpec.append, ProtocolSpec.snoc, Fin.snoc_eq_append] <;>
  congr <;> unfold Fin.cons <;> ext j
  · have h : j = 0 := by aesop
    subst h ; simp
  · have h : j = 0 := by aesop
    subst h ; simp

@[simp]
theorem ProtocolSpec.append_take {pSpec : ProtocolSpec n} (m : Fin n) :
    (pSpec.take m (by omega) ++ₚ .mkSingle (pSpec.Message m) (pSpec.Challenge m)) = pSpec.take (m + 1) (by omega) := by
  ext i <;> simp only [append] <;> rw [Fin.take_succ] <;>
  simp [Fin.snoc_eq_append] <;> congr <;> unfold Fin.cons <;> ext j
  · have : j = 0 := by aesop
    subst this ; simp
  · have : j = 0 := by aesop
    subst this ; simp

/-- Appending two `ToOracle`s for two `ProtocolSpec`s -/
def ToOracle.append {pSpec : ProtocolSpec m} {pSpec' : ProtocolSpec n}
    [O : ∀ i, ToOracle (pSpec.Message i)] [O' : ∀ i, ToOracle (pSpec'.Message i)] :
        ∀ i, ToOracle ((pSpec ++ₚ pSpec').Message i) :=
  Fin.addCases' O O'

/-- Appending two transcripts for two `ProtocolSpec`s -/
def Transcript.append {pSpec : ProtocolSpec m} {pSpec' : ProtocolSpec n}
    (T : Transcript pSpec) (T' : Transcript pSpec') :
    Transcript (pSpec ++ₚ pSpec') where
  messages := Fin.addCases' (φ := id) T.messages T'.messages
  challenges := Fin.addCases' (φ := id) T.challenges T'.challenges

/-- Adding a message and challenge to the end of a `Transcript` -/
def Transcript.snoc {pSpec : ProtocolSpec n} (T : Transcript pSpec) (msg : NextMessage) (challenge : NextChallenge) :
    Transcript (pSpec ++ₚ .mkSingle NextMessage NextChallenge) :=
  Transcript.append T ⟨fun _ => msg, fun _ => challenge⟩

end Composition

section Execution

variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n} {PrvState : Type} {Statement Witness : Type}

def simulateSwap {α : Type} (so : spec →[σ]ₛₒ specₜ) (s : σ) :
    (oa : OracleComp spec α) → OracleComp specₜ (σ × α) :=
  fun oa => Prod.swap <$> simulate so s oa

/--
  Auxiliary function for running the prover in an interactive protocol.

  Given round index `i`, returns the transcript up to that round, the log of oracle queries made by the prover to `oSpec` up to that round, and the prover's state after that round.
-/
def runProverAux [∀ i, Sampleable (pSpec.Challenge i)]
    (prover : Prover pSpec oSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) (i : Fin (n + 1)) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (Transcript (pSpec.take i (by omega)) × QueryLog oSpec × PrvState) := by
  induction i using Fin.induction with
  | zero => simp; exact
    (do
      let ⟨state, queryLog⟩ ← liftComp (simulate loggingOracle ∅ (prover.load stmt wit))
      return ⟨emptyTranscript, queryLog, state⟩)
  | succ j ih => simp at ih ⊢; exact
    (do
      let ⟨transcript, queryLog, state⟩ ← ih
      let challenge : pSpec.Challenge j ← query (Sum.inr j) ()
      let ⟨⟨msg, newState⟩, newQueryLog⟩ ← liftComp
        (simulate loggingOracle queryLog ((prover.prove j challenge) state))
      let newTranscript := transcript.snoc msg challenge
      let newTranscript : Transcript (pSpec.take (j + 1) (by omega)) := by
        simp only [ProtocolSpec.append_take] at newTranscript
        exact newTranscript
      return ⟨newTranscript, newQueryLog, newState⟩)

/--
  Run the prover in the interactive protocol

  Returns the transcript along with the final prover's state
-/
def runProver [∀ i, Sampleable (pSpec.Challenge i)]
    (prover : Prover pSpec oSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) : OracleComp
    (oSpec ++ₒ challengeOracle pSpec)
    (Transcript pSpec × QueryLog oSpec × PrvState) := do
  return ← runProverAux prover stmt wit ⟨n, by omega⟩

/-- Run the (non-oracle) verifier in the interactive protocol

Simply reads the statement and the transcript, and outputs a decision
-/
def runVerifier (verifier : Verifier pSpec oSpec Statement)
    (stmt : Statement) (transcript : Transcript pSpec) :
    OracleComp oSpec Bool := do
  let decision ← verifier.verify stmt transcript
  return decision

/-- Run the oracle verifier in the interactive protocol

Returns the verifier's output and the log of queries made by the verifier.
-/
def runOracleVerifier [O : ∀ i, ToOracle (pSpec.Message i)]
    (verifier : OracleVerifier pSpec oSpec Statement)
    (stmt : Statement) (transcript : Transcript pSpec) :
    OracleComp oSpec (Bool × ResponseList pSpec) := do
  let queries ← verifier.genQueries stmt transcript.challenges
  let oracles := fun i => (O i).respond (transcript.messages i)
  let responses ← List.mapM (fun ⟨j, q⟩ => pure ⟨j, q, oracles j q⟩ ) queries
  let decision ← verifier.verify stmt transcript.challenges responses
  return ⟨decision, responses⟩

/--
  An execution of an interactive protocol on a given initial statement and witness.

  Returns the verifier's decision, the protocol transcript, the log of prover's queries to `oSpec`,
  and the prover's final state
-/
def runProtocol [∀ i, Sampleable (pSpec.Challenge i)]
(protocol : Protocol pSpec oSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) : OracleComp
    (oSpec ++ₒ challengeOracle pSpec)
    (Bool × Transcript pSpec × QueryLog oSpec × PrvState) := do
  let (transcript, queryLog, state) ← runProver protocol.prover stmt wit
  let decision ← liftComp (runVerifier protocol.verifier stmt transcript)
  return (decision, transcript, queryLog, state)

/-- Run an interactive oracle protocol

Returns the verifier's decision, the transcript, the log of all verifier's oracle queries
to the prover's messages, the log of all prover's queries to `oSpec`, and the prover's final state
-/
def runOracleProtocol [∀ i, Sampleable (pSpec.Challenge i)]
    [∀ i, ToOracle (pSpec.Message i)]
    (protocol : OracleProtocol pSpec oSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) : OracleComp
    (oSpec ++ₒ challengeOracle pSpec)
    (Bool × Transcript pSpec × ResponseList pSpec × QueryLog oSpec × PrvState) := do
  let (transcript, queryLog, state) ← runProver protocol.prover stmt wit
  let ⟨decision, queries⟩ ←
    liftComp (runOracleVerifier protocol.verifier stmt transcript)
  return (decision, transcript, queries, queryLog, state)

end Execution
