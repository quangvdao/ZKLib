/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ZKLib.Data.Math.Fin

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
output relation is the Boolean relation (where `StmtOut = Bool`), then we recover a generalized
version of Interactive Oracle Proofs (IOPs) [BCS16]. The particular IOP considered in [BCS16] may be
called "point IOP" due to its query structure. We also get "polynomial IOP" [BCG+19] and "tensor
IOP" [BCG20] (and other kinds of IOPs) from our definition.

-/

open OracleComp OracleSpec SubSpec

section Prelude

-- Figure out where to put this instance
instance instDecidableEqOption {α : Type*} [DecidableEq α] :
    DecidableEq (Option α) := inferInstance

class VCVCompatible (α : Type) extends Fintype α, Inhabited α where
  [toDecidableEq : DecidableEq α]

instance {α : Type} [VCVCompatible α] : DecidableEq α := VCVCompatible.toDecidableEq

/-- `Sampleable` is a type class for types that can be sampled uniformly at random (via the VCV
    framework). This is mostly used for uniform sampling from challenges in an interactive protocol.
-/
class Sampleable (α : Type) extends VCVCompatible α, SelectableType α

instance {α : Type} [Sampleable α] : DecidableEq α := inferInstance

/-- Enum type for the direction of a round in a protocol specification -/
inductive Direction where
  | P_to_V -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr

/-- Equivalence between `Direction` and `Fin 2`, sending `V_to_P` to `0` and `P_to_V` to `1`
(the choice is essentially arbitrary). -/
def directionEquivFin2 : Direction ≃ Fin 2 where
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
instance : Coe (Fin 2) Direction := ⟨directionEquivFin2.invFun⟩

/-- `ToOracle` is a type class that provides an oracle interface for a type `Message`. It consists
  of a query type `Query`, a response type `Response`, and a function `oracle` that transforms
  a message `m : Message` into a function `Query → Response`. -/
@[ext]
class ToOracle (Message : Type) where
  Query : Type
  Response : Type
  oracle : Message → Query → Response

end Prelude

section Format

/-- Type signature for an interactive protocol, with `n` messages exchanged. -/
@[reducible]
def ProtocolSpec (n : ℕ) := Fin n → Direction × Type

variable {n : ℕ}

namespace ProtocolSpec

abbrev getDir (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.1

abbrev getType (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.2

/-- We set the rewrite to follow `getDir` instead of `Prod.fst`? -/
@[simp]
theorem getDir_apply (pSpec : ProtocolSpec n) (i : Fin n) : pSpec.getDir i = (pSpec i).1 := rfl

@[simp]
theorem getType_apply (pSpec : ProtocolSpec n) (i : Fin n) : pSpec.getType i = (pSpec i).2 := rfl

/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
def MessageIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.getDir i = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
def ChallengeIndex (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.getDir i = Direction.V_to_P}

instance {pSpec : ProtocolSpec n} : CoeHead (MessageIndex pSpec) (Fin n) where
  coe := fun i => i.1

instance {pSpec : ProtocolSpec n} : CoeHead (ChallengeIndex pSpec) (Fin n) where
  coe := fun i => i.1

/-- The type of the `i`-th message in a protocol specification -/
@[inline, reducible]
def Message (pSpec : ProtocolSpec n) (i : MessageIndex pSpec) :=
  pSpec.getType i.val

/-- The type of the `i`-th challenge in a protocol specification -/
@[inline, reducible]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIndex pSpec) :=
  pSpec.getType i.val

/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) := inferInstance

/-- A (partial) transcript of a protocol specification, indexed by some `k : Fin (n + 1)`, is a
    list of messages from the protocol for all indices `i` less than `k`. -/
@[inline, reducible]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  (i : Fin k) → pSpec.getType (Fin.castLE (by omega) i)

instance {k : Fin 1} : Unique (Transcript k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim

instance {pSpec : ProtocolSpec n} : Unique (Transcript 0 pSpec) where
  default := fun i => Fin.elim0 i
  uniq := fun T => by ext i; exact Fin.elim0 i

/-- The full transcript of an interactive protocol, which is a list of messages and challenges -/
@[inline, reducible]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.getType i

/-- There is only one full transcript (the empty one) for an empty protocol -/
instance : Unique (FullTranscript (default : ProtocolSpec 0)) := inferInstance

variable {pSpec : ProtocolSpec n}

/-- Nicely, a transcript up to the last round of the protocol is definitionally equivalent to a full
    transcript. -/
abbrev Transcript.toFull (T : Transcript (Fin.last n) pSpec) : FullTranscript pSpec := T

/-- Add a message to the end of a partial transcript. This is definitionally equivalent to
    `Fin.snoc`. -/
abbrev Transcript.snoc {m : Fin n} (msg : pSpec.getType m)
    (T : Transcript m.castSucc pSpec) : Transcript m.succ pSpec := Fin.snoc T msg

@[inline, reducible]
def FullTranscript.messages (transcript : FullTranscript pSpec) (i : MessageIndex pSpec) :=
  transcript i.val

@[inline, reducible]
def FullTranscript.challenges (transcript : FullTranscript pSpec) (i : ChallengeIndex pSpec) :=
  transcript i.val

/-- Spec for the verifier's challenges, invoked in the process of running the protocol -/
@[simps]
def challengeOracle (pSpec : ProtocolSpec n) [S : ∀ i, Sampleable (pSpec.Challenge i)] :
    OracleSpec (ChallengeIndex pSpec) where
  domain := fun _ => Unit
  range := fun i => pSpec.Challenge i
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_inhabited' := inferInstance
  range_fintype' := inferInstance

@[simps]
def messageOracle (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)]
    [∀ i, DecidableEq (O i).Query] [∀ i, VCVCompatible (O i).Response] :
    OracleSpec (MessageIndex pSpec) where
  domain := fun i => (O i).Query
  range := fun i => (O i).Response
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_inhabited' := inferInstance
  range_fintype' := inferInstance

-- def statementOracle (oStmt : OracleStatementType) [S : ∀ i, Sampleable (pSpec.Message i)] :
--     OracleSpec (MessageIndex pSpec) where
--   domain := fun _ => Unit
--   range := fun i => pSpec.Message i
--   domain_decidableEq' := fun _ => decEq
--   range_decidableEq' := fun i => @Sampleable.toDecidableEq _ (S i)
--   range_inhabited' := fun i => @Sampleable.toInhabited _ (S i)
--   range_fintype' := fun i => @Sampleable.toFintype _ (S i)

end ProtocolSpec

open ProtocolSpec

-- TODO: Notation for the type signature of an interactive protocol?

#eval "𝒫 ——⟦ 𝔽⦃≤ d⦄[X] ⟧⟶ 𝒱"

#eval "𝒫  ⟵⟦ 𝔽 ⟧—— 𝒱"

-- TODO: Notation for the objects / elements sent during the protocol?

#eval "𝒫  ——[ ∑ x ∈ D ^ᶠ (n - i), p ⸨X⦃i⦄, r, x⸩ ]⟶  𝒱"

#eval "𝒫  ⟵[ rᵢ ←$ 𝔽 ]—— 𝒱"

variable {ι : Type}

-- Add an indexer?
structure Indexer (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Index : Type)
    (Encoding : Type) where
  encode : Index → OracleComp oSpec Encoding
  [toOracle : ToOracle Encoding]

/-- The type signature for the prover's state at each round. For a protocol with `n` messages
  exchanged, there will be `(n + 1)` prover states, with the first state before the first message
  and the last state after the last message. -/
structure ProverState (n : ℕ) where
  PrvState : Fin (n + 1) → Type

/-- Initialization of prover's state via inputting the statement and witness -/
structure ProverIn (StmtIn WitIn PrvState : Type) where
  input : StmtIn → WitIn → PrvState

/-- Represents the interaction of a prover for a given protocol specification.

In each step, the prover gets access to the current state, then depending on the direction of the
step, the prover either sends a message or receives a challenge, and updates its state accordingly.

For maximum simplicity, we only define the `sendMessage` function as an oracle computation. All
other functions are pure. We may revisit this decision in the future.
-/
structure ProverRound (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement : Type)
    extends ProverState n where
  /-- Send a message and update the prover's state -/
  sendMessage (i : MessageIndex pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)
  /-- Receive a challenge and update the prover's state -/
  receiveChallenge (i : ChallengeIndex pSpec) :
    PrvState i.1.castSucc → (pSpec.Challenge i) → PrvState i.1.succ

/-- The output of the prover, which is a function from the prover's state to the output witness -/
structure ProverOut (StmtOut WitOut PrvState : Type) where
  output : PrvState → StmtOut × WitOut

/-- A prover for an interactive protocol with `n` messages consists of a sequence of internal states
    and a tuple of four functions:
  - `PrvState 0`, ..., `PrvState n` are the types for the prover's state at each round
  - `input` initializes the prover's state by taking in the input statement and witness
  - `receiveChallenge` updates the prover's state given a challenge
  - `sendMessage` sends a message and updates the prover's state
  - `output` returns the output statement and witness from the prover's state

Note that the output statement by the prover is present only to facilitate composing two provers
together. For security purposes, we will only use the output statement generated by the verifier. -/
structure Prover (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) extends
      ProverState n,
      ProverIn StmtIn WitIn (PrvState 0),
      ProverRound pSpec oSpec StmtIn,
      ProverOut StmtOut WitOut (PrvState (Fin.last n))

-- structure Prover (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
--     (StmtIn WitIn StmtOut WitOut : Type) where
--   PrvState : Fin (n + 1) → Type

--   input : StmtIn → WitIn → PrvState 0

--   sendMessage : ∀ i, PrvState i.1.castSucc →
--     OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)

--   receiveChallenge : ∀ i, PrvState i.1.castSucc →
--     (pSpec.Challenge i) → PrvState i.1.succ

--   output : PrvState (Fin.last n) → StmtOut × WitOut

-- /-- A verifier of an interactive protocol is a function that takes in the input statement and the
--   transcript, and performs an oracle computation that outputs a new statement -/

structure Verifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) where
  verify : StmtIn → FullTranscript pSpec → OracleComp oSpec StmtOut

/-- A list of queries to the prover's messages -/
@[inline, reducible]
def QueryList (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)] :=
  List ((i : MessageIndex pSpec) × (O i).Query)

/-- A list of responses to queries, computed from the prover's messages -/
@[inline, reducible]
def ResponseList (pSpec : ProtocolSpec n) [O : ∀ i, ToOracle (pSpec.Message i)] :=
  List ((i : MessageIndex pSpec) × (O i).Query × (O i).Response)

/-- An **oracle** verifier of an interactive oracle protocol may only make queries to the prover's
      messages (according to a specified interface defined by `ToOracle` instances).

    We only consider _non-adaptive_ oracle verifiers, where the queries can be determined just based
    on the challenges. Thus, an oracle verifier consists of two subroutines: `genQueries` and
    `verify` -/
-- structure OracleVerifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
--     [O : ∀ i, ToOracle (pSpec.Message i)] (StmtIn StmtOut : Type) where
--   /-- `genQueries` takes in the statement and the challenges, and generates a list of queries of
--     the form `(i, query)` to the prover's messages, where `i` is the round index and `query` is
--     the query to the prover's message as an oracle -/
--   genQueries : StmtIn → (∀ i, pSpec.Challenge i) → QueryList pSpec
--   /-- `verify` takes in the statement, the challenges, and the list of responses, and performs an
--     oracle computation that outputs a new statement -/
--   verify : StmtIn → (∀ i, pSpec.Challenge i) → ResponseList pSpec → OracleComp oSpec StmtOut


structure OracleVerifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [O : ∀ i, ToOracle (pSpec.Message i)] (StmtIn StmtOut : Type) where
  genQueries : StmtIn → (∀ i, pSpec.Challenge i) →
    List ((i : pSpec.MessageIndex) × (O i).Query)
  verify : StmtIn → (∀ i, pSpec.Challenge i) →
    List ((i : pSpec.MessageIndex) × (O i).Query × (O i).Response)
      → OracleComp oSpec StmtOut

/-- An oracle verifier can be seen as a (non-oracle) verifier in the natural way -/
def OracleVerifier.toVerifier {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} [O : ∀ i, ToOracle (pSpec.Message i)]
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut) :
    Verifier pSpec oSpec StmtIn StmtOut where
  verify := fun stmt transcript => do
    letI queries := verifier.genQueries stmt transcript.challenges
    letI responses := queries.map
      (fun q => ⟨q.1, q.2, (O q.1).oracle (transcript.messages q.1) q.2⟩)
    verifier.verify stmt transcript.challenges responses

/-- Make `OracleVerifier.toVerifier` a coercion -/
instance {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    [∀ i, ToOracle (pSpec.Message i)] : Coe (OracleVerifier pSpec oSpec StmtIn StmtOut)
    (Verifier pSpec oSpec StmtIn StmtOut) :=
  ⟨OracleVerifier.toVerifier⟩

/-- An (interactive) reduction for a given protocol specification `pSpec`, and relative to oracles
  defined by `oSpec`, consists of a prover and a verifier. -/
structure Reduction (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) where
  prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut
  verifier : Verifier pSpec oSpec StmtIn StmtOut

/-- An (interactive) oracle reduction for a given protocol specification `pSpec`, and relative to
  oracles defined by `oSpec`, consists of a prover and an **oracle** verifier. -/
structure OracleReduction (pSpec : ProtocolSpec n) [∀ i, ToOracle (pSpec.Message i)]
    (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut : Type) where
  prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut
  verifier : OracleVerifier pSpec oSpec StmtIn StmtOut

/-- An interactive oracle reduction can be seen as an interactive reduction, via coercing the oracle
  verifier to a (normal) verifier -/
def OracleReduction.toReduction {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} [∀ i, ToOracle (pSpec.Message i)]
    (oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut :=
  ⟨oracleReduction.prover, oracleReduction.verifier⟩

/-- Make `OracleReduction.toReduction` a coercion -/
instance {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι} [∀ i, ToOracle (pSpec.Message i)]
    {StmtIn WitIn StmtOut WitOut : Type} :
    Coe (OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut)
    (Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :=
  ⟨OracleReduction.toReduction⟩

/-- An interactive proof is an interactive reduction where the output statement is a boolean, the
  output witness can be arbitrary, and the relation checks whether the output statement is true. -/
abbrev Proof (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement Witness : Type) :=
  Reduction pSpec oSpec Statement Witness Bool Unit

/-- An interactive oracle proof is an interactive oracle reduction where the output statement is a
  boolean, the output witness can be arbitrary, and the relation checks whether the output statement
  is true. -/
abbrev OracleProof (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) [∀ i, ToOracle (pSpec.Message i)]
    (Statement Witness : Type) :=
  OracleReduction pSpec oSpec Statement Witness Bool Unit

end Format

section Execution

open ProtocolSpec

variable {n : ℕ} {ι : Type} [DecidableEq ι] {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}

/--
  Auxiliary function for running the prover in an interactive protocol. Given round index `i`,
  returns the transcript up to that round, the log of oracle queries made by the prover to `oSpec`
  up to that round, and the prover's state after that round.
-/
def Prover.runAux [∀ i, Sampleable (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (i : Fin (n + 1)) (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (pSpec.Transcript i × QueryLog oSpec × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, ∅, prover.input stmt wit⟩)
    (fun j ih => do
      let ⟨transcript, queryLog, state⟩ ← ih
      match hDir : pSpec.getDir j with
      | .V_to_P => do
        let challenge ← query (Sum.inr ⟨j, hDir⟩) ()
        have challenge : pSpec.Challenge ⟨j, hDir⟩ := by simpa only
        let newState := prover.receiveChallenge ⟨j, hDir⟩ state challenge
        return ⟨transcript.snoc challenge, queryLog, newState⟩
      | .P_to_V => do
        let ⟨⟨msg, newState⟩, newQueryLog⟩ ← liftComp
          (simulate loggingOracle queryLog (prover.sendMessage ⟨j, hDir⟩ state))
        return ⟨transcript.snoc msg, newQueryLog, newState⟩)
    i

/--
  Run the prover in an interactive protocol. Returns the full transcript, the log of oracle queries
  made by the prover, and the output witness
-/
def Prover.run [∀ i, Sampleable (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (FullTranscript pSpec × QueryLog oSpec × StmtOut × WitOut) := do
  let ⟨transcript, queryLog, state⟩ ← prover.runAux stmt wit (Fin.last n)
  let ⟨stmtOut, witOut⟩ := prover.output state
  return ⟨transcript, queryLog, stmtOut, witOut⟩

/-- Run the (non-oracle) verifier in the interactive protocol. Simply reads the statement and the
  transcript, and outputs a decision.
-/
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut) : OracleComp oSpec StmtOut :=
  verifier.verify stmt transcript

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output and the log
  of queries made by the verifier.
-/
def OracleVerifier.run [O : ∀ i, ToOracle (pSpec.Message i)] (stmt : StmtIn)
    (transcript : FullTranscript pSpec) (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut) :
      OracleComp oSpec (ResponseList pSpec × StmtOut) := do
  let queries := verifier.genQueries stmt transcript.challenges
  let oracles := fun i => (O i).oracle (transcript.messages i)
  let responses := queries.map (fun q => ⟨q.1, q.2, oracles q.1 q.2⟩)
  let newStmt ← verifier.verify stmt transcript.challenges responses
  return ⟨responses, newStmt⟩

omit [DecidableEq ι] in
/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn}
    {transcript : FullTranscript pSpec} {verifier : OracleVerifier pSpec oSpec StmtIn StmtOut} :
      Prod.snd <$> verifier.run stmt transcript = verifier.toVerifier.run stmt transcript := by
  simp only [OracleVerifier.run, map_bind, map_pure, bind_pure,
    Verifier.run, OracleVerifier.toVerifier]

/--
  An execution of an interactive reduction on a given initial statement and witness.

  Returns the verifier's decision, the transcript, the log of prover's queries to `oSpec`,
  and the prover's final state
-/

def Reduction.run [∀ i, Sampleable (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (FullTranscript pSpec × QueryLog oSpec × StmtOut × WitOut) := do
  let (transcript, queryLog, _, witOut) ← reduction.prover.run stmt wit
  let stmtOut ← liftComp (reduction.verifier.run stmt transcript)
  return (transcript, queryLog, stmtOut, witOut)

/-- Run an interactive oracle reduction

Returns the verifier's decision, the transcript, the log of all verifier's oracle queries
to the prover's messages, the log of all prover's queries to `oSpec`, and the prover's final state

Note: we put `ResponseList pSpec` first so that the rest can be `Prod.snd`, which
we will show is the same result as doing `Protocol.run`.
-/
def OracleReduction.run [∀ i, Sampleable (pSpec.Challenge i)] [∀ i, ToOracle (pSpec.Message i)]
    (stmt : StmtIn) (wit : WitIn)
    (reduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ challengeOracle pSpec)
        (ResponseList pSpec × FullTranscript pSpec × QueryLog oSpec × StmtOut × WitOut) := do
  let ⟨transcript, queryLog, _, witOut⟩ ← reduction.prover.run stmt wit
  let ⟨messageQueries, stmtOut⟩ ← liftComp (reduction.verifier.run stmt transcript)
  return (messageQueries, transcript, queryLog, stmtOut, witOut)

omit [DecidableEq ι] in
/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem OracleReduction.run_eq_run_reduction [DecidableEq ι] [∀ i, Sampleable (pSpec.Challenge i)]
    [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn} {wit : WitIn}
    {oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut} :
      Prod.snd <$> oracleReduction.run stmt wit = oracleReduction.toReduction.run stmt wit := by
  simp [OracleReduction.run, Reduction.run, OracleReduction.toReduction, OracleVerifier.run,
    Verifier.run, OracleVerifier.toVerifier, liftComp]

end Execution

section Classes

namespace ProtocolSpec

variable {n : ℕ}

/-- A protocol specification with the prover speaking first -/
class ProverFirst (pSpec : ProtocolSpec n) [NeZero n] where
  prover_first' : (pSpec 0).1 = .P_to_V

/-- A protocol specification with the verifier speaking last -/
class VerifierLast (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_last' : (pSpec (n - 1)).1 = .V_to_P

@[simp]
theorem prover_first (pSpec : ProtocolSpec n) [NeZero n] [h : ProverFirst pSpec] :
    (pSpec 0).1 = .P_to_V := h.prover_first'

@[simp]
theorem verifier_last (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierLast pSpec] :
    (pSpec (n - 1)).1 = .V_to_P := h.verifier_last'

@[simp]
theorem verifier_last_of_two (pSpec : ProtocolSpec 2) [VerifierLast pSpec] :
    pSpec.getDir 1 = .V_to_P := verifier_last pSpec

/-- A protocol specification with a single round of interaction consisting of two messages, with the
  prover speaking first and the verifier speaking last

This notation is currently somewhat ambiguous, given that there are other valid ways of defining a
"single-round" protocol, such as letting the verifier speaks first, letting the prover speaks
multiple times, etc. -/
class IsSingleRound (pSpec : ProtocolSpec 2) extends ProverFirst pSpec, VerifierLast pSpec

variable {pSpec : ProtocolSpec 2}

/-- The first message is the only message from the prover to the verifier -/
instance [IsSingleRound pSpec] : Unique (pSpec.MessageIndex) where
  default := ⟨0, by simp [pSpec.prover_first]⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 1 := by omega
    subst this
    simp only [verifier_last_of_two, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The second message is the only challenge from the verifier to the prover -/
instance [IsSingleRound pSpec] : Unique (pSpec.ChallengeIndex) where
  default := ⟨1, by simp [pSpec.verifier_last]⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 0 := by omega
    subst this
    simp only [prover_first, ne_eq, reduceCtorEq, not_false_eq_true]

instance [IsSingleRound pSpec] [h : ToOracle (pSpec.Message default)] :
    (i : pSpec.MessageIndex) → ToOracle (pSpec.Message i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

instance [IsSingleRound pSpec] [h : Sampleable (pSpec.Challenge default)] :
    (i : pSpec.ChallengeIndex) → Sampleable (pSpec.Challenge i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

@[inline, reducible]
def FullTranscript.mk2 {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0) (msg1 : pSpec.getType 1) :
    FullTranscript pSpec := fun | ⟨0, _⟩ => msg0 | ⟨1, _⟩ => msg1

theorem FullTranscript.mk2_eq_snoc_snoc {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0)
    (msg1 : pSpec.getType 1) : FullTranscript.mk2 msg0 msg1 =
      ((default : pSpec.Transcript 0).snoc msg0).snoc msg1 := by
  unfold FullTranscript.mk2 Transcript.snoc
  simp only [default, getType_apply, Nat.mod_succ, Nat.lt_one_iff,
    not_lt_zero', ↓reduceDIte, Fin.zero_eta, Fin.isValue, Nat.reduceMod, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.mk_one]
  funext i
  by_cases hi : i = 0
  · subst hi; simp [Fin.snoc]
  · have : i = 1 := by omega
    subst this; simp [Fin.snoc]

variable [∀ i, Sampleable (pSpec.Challenge i)] {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut PrvState : Type}

-- /-- Simplification of the prover's execution in a single-round, two-message protocol where the
--   prover speaks first -/
-- theorem Prover.run_of_isSingleRound [IsSingleRound pSpec] (stmt : StmtIn) (wit : WitIn)
--     (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
--       prover.run stmt wit = (do
--         let state ← liftComp (prover.load stmt wit)
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp
--           (simulate loggingOracle ∅ (prover.sendMessage default state emptyTranscript))
--         let challenge ← query (Sum.inr default) ()
--         let state ← liftComp (prover.receiveChallenge default state transcript challenge)
--         let transcript := Transcript.mk2 msg challenge
--         let witOut := prover.output state
--         return (transcript, queryLog, witOut)) := by
--   simp [Prover.run, Prover.runAux, Fin.reduceFinMk, Fin.val_two,
--     Fin.val_zero, Fin.coe_castSucc, Fin.val_succ, getDir_apply, bind_pure_comp, getType_apply,
--     Fin.induction_two, Fin.val_one, pure_bind, map_bind, liftComp]
--   split <;> rename_i hDir0
--   · exfalso; simp only [prover_first, reduceCtorEq] at hDir0
--   split <;> rename_i hDir1
--   swap
--   · exfalso; simp only [verifier_last_of_two, reduceCtorEq] at hDir1
--   simp only [Functor.map_map, bind_map_left, default]
--   congr; funext x; congr; funext y;
--   simp only [Fin.isValue, map_bind, Functor.map_map, getDir_apply, Fin.succ_one_eq_two,
--     Fin.succ_zero_eq_one, queryBind_inj', true_and, exists_const]
--   funext chal; simp [OracleSpec.append] at chal
--   congr; funext state; congr
--   rw [← Transcript.mk2_eq_toFull_snoc_snoc _ _]

-- theorem Reduction.run_of_isSingleRound [IsSingleRound pSpec]
--     (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState)
--     (stmt : StmtIn) (wit : WitIn) :
--       reduction.run stmt wit = do
--         let state := reduction.prover.load stmt wit
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp (simulate loggingOracle ∅
--           (reduction.prover.sendMessage default state))
--         let challenge := reduction.prover.receiveChallenge default state
--         let stmtOut ← reduction.verifier.verify stmt transcript
--         return (transcript, queryLog, stmtOut, reduction.prover.output state) := by sorry

end ProtocolSpec

end Classes
