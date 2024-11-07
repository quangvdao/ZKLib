/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ZKLib.Relation.Basic
import ZKLib.Data.Math.Fin
import ZKLib.Data.Math.HList
import Mathlib.Data.Fin.Fin2

/-!
# (Interactive) Oracle Reductions

We define (public-coin) interactive oracle reductions (IORs). This is an interactive protocol
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

set_option linter.docPrime false

open OracleComp OracleSpec SubSpec

section Prelude

-- Figure out where to put this instance
instance instDecidableEqOption {α : Type*} [DecidableEq α] : DecidableEq (Option α) := inferInstance

/-- `Sampleable` is a type class for types that can be sampled uniformly at random (via the VCV
    framework). This is mostly used for uniform sampling from challenges in an interactive protocol.
-/
class Sampleable (α : Type) extends Fintype α, Inhabited α, SelectableType α where
  [toDecidableEq : DecidableEq α]

instance {α : Type} [Sampleable α] : DecidableEq α := Sampleable.toDecidableEq

/-- Enum type for the direction of a round in a protocol specification -/
inductive Direction where
  | P_to_V -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr

/-- Equivalence between `Direction` and `Fin 2`, sending `V_to_P` to `0` and `P_to_V` to `1`
(the choice is essentially arbitrary). -/
def DirectionEquivFin2 : Direction ≃ Fin 2 where
  toFun := fun dir => match dir with
    | .V_to_P => ⟨0, by decide⟩
    | .P_to_V => ⟨1, by decide⟩
  invFun := fun n => match n with
    | ⟨0, _⟩ => .V_to_P
    | ⟨1, _⟩ => .P_to_V
  left_inv := fun dir => match dir with
    | .P_to_V => rfl
    | .V_to_P => rfl
  right_inv := fun n => match n with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

/-- This allows us to write `0` for `.V_to_P` and `1` for `.P_to_V`. -/
instance : Coe (Fin 2) Direction := ⟨DirectionEquivFin2.invFun⟩

end Prelude

section Format

/-- Type signature for an interactive protocol, with `n` messages exchanged. -/
@[reducible]
def ProtocolSpec (n : ℕ) := Fin n → Direction × Type

variable {n : ℕ}

abbrev ProtocolSpec.getDir (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.1

abbrev ProtocolSpec.getType (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.2

/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
def MessageIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.getDir i = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
def ChallengeIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.getDir i = Direction.V_to_P}

/-- The type of the `i`-th message in a protocol specification -/
@[inline, reducible]
def ProtocolSpec.Message (pSpec : ProtocolSpec n) (i : MessageIndex pSpec) :=
  pSpec.getType i.val

/-- The type of the `i`-th challenge in a protocol specification -/
@[inline, reducible]
def ProtocolSpec.Challenge (pSpec : ProtocolSpec n) (i : ChallengeIndex pSpec) :=
  pSpec.getType i.val

/-- The transcript of an interactive protocol, which is a list of messages and challenges -/
@[inline, reducible]
def Transcript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.getType i

variable {ι : Type}

variable {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} {State : Type}

@[inline, reducible]
def Transcript.messages (transcript : Transcript pSpec) (i : MessageIndex pSpec) :=
  transcript i.val

@[inline, reducible]
def Transcript.challenges (transcript : Transcript pSpec) (i : ChallengeIndex pSpec) :=
  transcript i.val

/-- `ToOracle` provides an oracle interface for a type `Message`. It defines the query type `Query`,
  the response type `Response`, and the transformation `toOracle` that transforms a message into an
  oracle. -/
@[ext]
class ToOracle (Message : Type) where
  Query : Type
  Response : Type
  respond : Message → Query → Response

-- TODO: Notation for the type signature of an interactive protocol

#eval "𝒫 ——⟦ 𝔽⦃≤ d⦄[X] ⟧⟶ 𝒱"

#eval "𝒫  ⟵⟦ 𝔽 ⟧—— 𝒱"

-- TODO: Notation for the objects / elements sent during the protocol

#eval "𝒫  ——[ ∑ x ∈ D ^ᶠ (n - i), peval x (Fin.injOnRight i n) p ]⟶  𝒱"

#eval "𝒫  ⟵[ r i ←$ 𝔽 ]—— 𝒱"

/-- Spec for the verifier's challenges, invoked in the process of running the protocol -/
@[simps]
def challengeOracle (pSpec : ProtocolSpec n) [S : ∀ i, Sampleable (pSpec.Challenge i)] :
    OracleSpec (ChallengeIndex pSpec) where
  domain := fun _ => Unit
  range := fun i => pSpec.Challenge i
  domain_decidableEq' := fun _ => decEq
  range_decidableEq' := fun i => @Sampleable.toDecidableEq _ (S i)
  range_inhabited' := fun i => @Sampleable.toInhabited _ (S i)
  range_fintype' := fun i => @Sampleable.toFintype _ (S i)


-- Add an indexer?
structure Indexer (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Index : Type)
    (Encoding : Type) where
  encode : Index → OracleComp oSpec Encoding
  [toOracle : ToOracle Encoding]

-- The prover should be divided into two parts:
-- Its interaction during the protocol
-- Its initialization and output

/-- Initialization of prover's state via loading the statement and witness -/
structure ProverInit (pSpec : ProtocolSpec n) (PrvState : Type) (Statement Witness : Type) where
  load : Statement → Witness → PrvState

/-- Represents the interactive prover for a given protocol specification -/
structure ProverRound (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (PrvState : Type) where
  -- Receive a challenge and update the prover's state
  receiveChallenge (i : ChallengeIndex pSpec) : PrvState → (pSpec.Challenge i) → PrvState
  -- Send a message and update the prover's state
  sendMessage (i : MessageIndex pSpec) : PrvState → OracleComp oSpec (pSpec.Message i × PrvState)

structure Prover (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (PrvState : Type)
    (Statement Witness : Type) extends ProverInit pSpec PrvState Statement Witness,
    ProverRound pSpec oSpec PrvState

/-- The verifier of an interactive protocol (that may read messages in full) -/
class Verifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement : Type) where
  verify : Statement → Transcript pSpec → OracleComp oSpec Bool

/-- A list of queries to the prover's messages -/
@[inline, reducible]
def QueryList (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)] :=
  List ((i : MessageIndex pSpec) × (O i).Query)

/-- A list of responses to queries, computed from the prover's messages -/
@[inline, reducible]
def ResponseList (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)] :=
  List ((i : MessageIndex pSpec) × (O i).Query × (O i).Response)

/-- The verifier of an interactive oracle protocol
(that may only make queries to the prover's messages) -/
structure OracleVerifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [O : ∀ i, ToOracle (pSpec.Message i)] (Statement : Type) where
  -- Generate a list of queries of the form `(i, query)`,
  -- where `i` is the round index and `query` is the query to the oracle
  genQueries : Statement → (∀ i, pSpec.Challenge i) →
      OracleComp oSpec (QueryList pSpec)
  -- Verify the proof based on the list of responses
  verify : Statement → (∀ i, pSpec.Challenge i) → ResponseList pSpec →
      OracleComp oSpec Bool

/-- We can always turn an oracle verifier into a (non-oracle) verifier -/
def OracleVerifier.toVerifier {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} {Statement : Type}
    [O : ∀ i, ToOracle (pSpec.Message i)] (verifier : OracleVerifier pSpec oSpec Statement) :
    Verifier pSpec oSpec Statement where
  verify := fun stmt transcript => do
    let queries ← verifier.genQueries stmt transcript.challenges
    let responses ← queries.mapM (fun ⟨j, q⟩ =>
      pure ⟨j, q, (O j).respond (transcript.messages j) q⟩ )
    verifier.verify stmt transcript.challenges responses

instance {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} {Statement : Type}
    [∀ i, ToOracle (pSpec.Message i)] : Coe (OracleVerifier pSpec oSpec Statement)
    (Verifier pSpec oSpec Statement) :=
  ⟨OracleVerifier.toVerifier⟩

structure Protocol (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (PrvState : Type) (Statement Witness : Type) where
  prover : Prover pSpec oSpec PrvState Statement Witness
  verifier : Verifier pSpec oSpec Statement

structure OracleProtocol (pSpec : ProtocolSpec n) [∀ i, ToOracle (pSpec.Message i)]
    (oSpec : OracleSpec ι) (PrvState : Type) (Statement Witness : Type) where
  prover : Prover pSpec oSpec PrvState Statement Witness
  verifier : OracleVerifier pSpec oSpec Statement

def OracleProtocol.toProtocol {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} {PrvState : Type}
    {Statement Witness : Type} [∀ i, ToOracle (pSpec.Message i)]
    (oracleProtocol : OracleProtocol pSpec oSpec PrvState Statement Witness) :
    Protocol pSpec oSpec PrvState Statement Witness :=
  ⟨oracleProtocol.prover, oracleProtocol.verifier⟩

instance {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} {PrvState : Type}
    {Statement Witness : Type} [∀ i, ToOracle (pSpec.Message i)] :
    Coe (OracleProtocol pSpec oSpec PrvState Statement Witness)
    (Protocol pSpec oSpec PrvState Statement Witness) :=
  ⟨OracleProtocol.toProtocol⟩

end Format

section Restrict

variable {n : ℕ}

abbrev ProtocolSpec.take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) :=
  Fin.take m h pSpec

abbrev ProtocolSpec.rtake (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) :=
  Fin.rtake m h pSpec

abbrev Transcript.take {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : Transcript pSpec) : Transcript (pSpec.take m h) :=
  Fin.take m h transcript

abbrev Transcript.rtake {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : Transcript pSpec) : Transcript (pSpec.rtake m h) :=
  Fin.rtake m h transcript

end Restrict

section Composition

variable {n m : ℕ}

/-- Adding a round with direction `dir` and type `Message` to the beginning of a `ProtocolSpec` -/
abbrev ProtocolSpec.cons (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  Fin.cons ⟨dir, Message⟩ pSpec

/-- Adding a round with direction `dir` and type `Message` to the end of a `ProtocolSpec` -/
abbrev ProtocolSpec.snoc (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  Fin.snoc pSpec ⟨dir, Message⟩

/-- Appending two `ProtocolSpec`s -/
abbrev ProtocolSpec.append (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) :
    ProtocolSpec (n + m) :=
  Fin.append pSpec pSpec'

def ProtocolSpec.mkSingle (dir : Direction) (Message : Type) : ProtocolSpec 1 :=
  fun _ => ⟨dir, Message⟩

infixl : 65 " ++ₚ " => ProtocolSpec.append

@[simp]
theorem ProtocolSpec.snoc_take {pSpec : ProtocolSpec n} (m : ℕ) (h : m < n) :
    (pSpec.take m (by omega) ++ₚ (fun (_ : Fin 1) => pSpec ⟨m, h⟩))
        = pSpec.take (m + 1) (by omega) := by
  simp only [append, take, Fin.append_right_eq_snoc, Fin.take_succ_eq_snoc]

/-- Appending two `ToOracle`s for two `ProtocolSpec`s -/
def ToOracle.append {pSpec₁ : ProtocolSpec n} {pSpec₂ : ProtocolSpec m}
    [O₁ : ∀ i, ToOracle (pSpec₁.Message i)] [O₂ : ∀ i, ToOracle (pSpec₂.Message i)] :
        ∀ i, ToOracle ((pSpec₁ ++ₚ pSpec₂).Message i) := fun ⟨i, h⟩ => by
  dsimp [ProtocolSpec.append, ProtocolSpec.getDir] at h ⊢
  dsimp [ProtocolSpec.Message, ProtocolSpec.getType]
  by_cases h' : i < n
  · rw [← Fin.castAdd_castLT m i h', Fin.append_left] at h ⊢
    exact O₁ ⟨i.castLT h', h⟩
  · rw [← @Fin.natAdd_subNat_cast n m i (not_lt.mp h'), Fin.append_right] at h ⊢
    exact O₂ ⟨Fin.subNat n (Fin.cast (add_comm n m) i) (not_lt.mp h'), h⟩

/-- Appending two transcripts for two `ProtocolSpec`s -/
def Transcript.append {pSpec₁ : ProtocolSpec n} {pSpec₂ : ProtocolSpec m}
    (T₁ : Transcript pSpec₁) (T₂ : Transcript pSpec₂) : Transcript (pSpec₁ ++ₚ pSpec₂) := by
  dsimp [ProtocolSpec.append, ProtocolSpec.getDir]
  dsimp [Transcript, ProtocolSpec.getType] at T₁ T₂ ⊢
  exact fun i => (Fin.append_comp Prod.snd i) ▸ (Fin.addCases' T₁ T₂ i)

infixl : 65 " ++ₜ " => Transcript.append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def Transcript.snoc {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : Transcript pSpec) (dir : Direction) (msg : NextMessage) :
        Transcript (pSpec ++ₚ .mkSingle dir NextMessage) :=
  Transcript.append T fun _ => msg

end Composition

section Execution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
{PrvState : Type} {Statement Witness : Type}

/-- Run the prover in the interactive protocol. Returns the final prover's state.
TODO: Return the transcript as well -/
def Prover.run (prover : Prover pSpec oSpec PrvState Statement Witness)
    (chals : ∀ i, pSpec.Challenge i) (state : PrvState) :
        OracleComp oSpec PrvState :=
  let rec loop (i : ℕ) (state : PrvState) (chals : ∀ i, pSpec.Challenge i) :
      OracleComp oSpec PrvState :=
    if h : i < n then
      letI i' : Fin n := ⟨i, h⟩
      match hDir : pSpec.getDir i' with
      | .V_to_P => loop (i + 1) (prover.receiveChallenge ⟨i', hDir⟩ state (chals ⟨i', hDir⟩)) chals
      | .P_to_V => do
        let ⟨ msg, state' ⟩ ← prover.sendMessage ⟨i', hDir⟩ state
        loop (i + 1) state' chals
    else
      pure state
  loop 0 state chals

/--
  Auxiliary function for running the prover in an interactive protocol. Given round index `i`,
  returns the transcript up to that round, the log of oracle queries made by the prover to `oSpec`
  up to that round, and the prover's state after that round.
-/
def runProverAux [DecidableEq ι] [∀ i, Sampleable (pSpec.Challenge i)]
    (prover : Prover pSpec oSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) (i : Fin (n + 1)) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (Transcript (pSpec.take i (by omega)) × QueryLog oSpec × PrvState) := by
  induction i using Fin.induction with
  | zero => simp; exact
    (do
      let ⟨state, queryLog⟩ ← liftComp (simulate loggingOracle ∅ <| pure (prover.load stmt wit))
      return ⟨fun i => Fin.elim0 i, queryLog, state⟩)
  | succ j ih => simp [ProtocolSpec.take] at ih ⊢; exact
    (do
      let ⟨transcript, queryLog, state⟩ ← ih
      match hDir : pSpec.getDir j with
      | .V_to_P => do
        let challenge ← query (Sum.inr ⟨j, hDir⟩) ()
        haveI challenge : pSpec.Challenge ⟨j, hDir⟩ := by simpa only
        let newState := prover.receiveChallenge ⟨j, hDir⟩ state challenge
        let newTranscript := transcript.snoc .V_to_P challenge
        let newTranscript : Transcript (pSpec.take (j + 1) (by omega)) := by
          sorry
          -- simp [ProtocolSpec.snoc_take] at newTranscript
          -- exact newTranscript
        return ⟨newTranscript, queryLog, newState⟩
      | .P_to_V => do
        let ⟨⟨msg, newState⟩, newQueryLog⟩ ← liftComp
          (simulate loggingOracle queryLog (prover.sendMessage ⟨j, hDir⟩ state))
        let newTranscript := transcript.snoc .P_to_V msg
        let newTranscript : Transcript (pSpec.take (j + 1) (by omega)) := by
          sorry
          -- simp only [ProtocolSpec.snoc_take] at newTranscript
          -- exact newTranscript
        return ⟨newTranscript, newQueryLog, newState⟩
      )

/--
  Run the prover in the interactive protocol. Returns the transcript along with the final prover's
  state
-/
def runProver [DecidableEq ι] [∀ i, Sampleable (pSpec.Challenge i)]
    (prover : Prover pSpec oSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) : OracleComp
    (oSpec ++ₒ challengeOracle pSpec)
    (Transcript pSpec × QueryLog oSpec × PrvState) := do
  return ← runProverAux prover stmt wit ⟨n, by omega⟩

/-- Run the (non-oracle) verifier in the interactive protocol. Simply reads the statement and the
  transcript, and outputs a decision.
-/
def runVerifier (verifier : Verifier pSpec oSpec Statement)
    (stmt : Statement) (transcript : Transcript pSpec) :
    OracleComp oSpec Bool := do
  let decision ← verifier.verify stmt transcript
  return decision

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output and the log
  of queries made by the verifier.
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

/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem runOracleVerifier_eq_runVerifier [∀ i, ToOracle (pSpec.Message i)]
    (verifier : OracleVerifier pSpec oSpec Statement)
    (stmt : Statement) (transcript : Transcript pSpec) :
        Prod.fst <$> runOracleVerifier verifier stmt transcript =
            runVerifier verifier.toVerifier stmt transcript := by
  simp only [runOracleVerifier, map_bind, map_pure, bind_pure,
    runVerifier, OracleVerifier.toVerifier]

/--
  An execution of an interactive protocol on a given initial statement and witness.

  Returns the verifier's decision, the protocol transcript, the log of prover's queries to `oSpec`,
  and the prover's final state
-/
def runProtocol [DecidableEq ι] [∀ i, Sampleable (pSpec.Challenge i)]
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

Note: we put `ResponseList pSpec` first so that the rest can be `Prod.snd`, which
we will show is the same result as doing `runProtocol`.
-/
def runOracleProtocol [DecidableEq ι] [∀ i, Sampleable (pSpec.Challenge i)]
    [∀ i, ToOracle (pSpec.Message i)]
    (protocol : OracleProtocol pSpec oSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) : OracleComp
    (oSpec ++ₒ challengeOracle pSpec)
    (ResponseList pSpec × Bool × Transcript pSpec × QueryLog oSpec × PrvState) := do
  let ⟨transcript, queryLog, state⟩ ← runProver protocol.prover stmt wit
  let ⟨decision, messageQueries⟩ ←
    liftComp (runOracleVerifier protocol.verifier stmt transcript)
  return (messageQueries, decision, transcript, queryLog, state)

/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem runOracleProtocol_eq_runProtocol [DecidableEq ι] [∀ i, Sampleable (pSpec.Challenge i)]
    [∀ i, ToOracle (pSpec.Message i)]
    (protocol : OracleProtocol pSpec oSpec PrvState Statement Witness)
    (stmt : Statement) (wit : Witness) :
        Prod.snd <$> runOracleProtocol protocol stmt wit =
            runProtocol protocol.toProtocol stmt wit := by
  simp only [runOracleProtocol, runOracleVerifier, liftComp_bind, liftComp_pure, Prod.mk.eta,
    bind_assoc, pure_bind, map_bind, map_pure, runProtocol, OracleProtocol.toProtocol,
    OracleVerifier.toVerifier, runVerifier, bind_pure]

end Execution
