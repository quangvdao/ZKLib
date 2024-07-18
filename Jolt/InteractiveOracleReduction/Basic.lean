import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UnitInterval
import Jolt.Data.HList
import Jolt.Relation.Basic

/-!
# Formalism of Interactive Oracle Reductions

We define (public-coin) interactive oracle reductions (IORs). This is an interactive protocol between a prover and a verifier with the following format:

  - At the beginning, the prover and verifier both hold a public statement x (and potentially have access to some public parameters pp). The prover may also hold some private state which in particular may contain a witness w to the statement x.

  - In each round, the verifier sends some random challenges, and the prover sends back responses to the challenges. The responses are received as oracles by the verifier. The verifier only sees some abstract representation of the responses, and is only allowed to query these oracles in specific ways (i.e. point queries, polynomial evaluation queries, tensor queries).

  - At each step, the verifier may make oracle queries and perform some checks on the responses so far. At the end of the interaction, the verifier outputs a new statement, and the prover outputs a new witness.

Note: the definition of IORs as defined above generalizes those found in the literature. When the output relation is the Boolean relation (where `StatementOut = Bool`), then we recover a generalized version of Interactive Oracle Proofs (IOPs) [BCS16]. The particular IOP considered in [BCS16] may be called "point IOP" due to its query structure. We also get "polynomial IOP" [BCG+19] and "tensor IOP" [BCG20] (and other kinds of IOPs) from our definition.

-/


namespace IOR

-- TODO: IORs where both parties have access to some oracle?

/-- Define the format of an Interactive Oracle Reduction -/
structure Spec where
  relIn : Relation
  relOut : Relation
  numRounds : ℕ+
  Message : Fin numRounds → Type _ -- Message type for each round
  Challenge : Fin numRounds → Type _ -- Challenge type for each round
  sampleChallenge : ∀ i, PMF (Challenge i) -- Sampling challenges for the honest verifier
  OQuery : Fin numRounds → Type _ -- Query type for each oracle
  OResponse : Fin numRounds → Type _ -- Response type for each oracle
  oracleFromMessage : ∀ i, Message i → OQuery i → OResponse i -- Transforming messages to oracles that take queries and return responses


/-- A partial transcript of the IOR consists of all the messages and challenges up to a certain round `i ≤ spec.numRounds` -/
structure PartialTranscript (spec : Spec) (i : Fin (spec.numRounds + 1)) where
  messages : ∀ j : Fin i, spec.Message j
  challenges : ∀ j : Fin i, spec.Challenge j

/--
  The final transcript of the IOR, including all messages and challenges
-/
structure Transcript (spec : Spec) where
  messages : ∀ i, spec.Message i
  challenges : ∀ i, spec.Challenge i


def Transcript.toPartial (transcript : Transcript spec) (i : Fin (spec.numRounds + 1)) : PartialTranscript spec i where
  messages := fun j => transcript.messages j
  challenges := fun j => transcript.challenges j


def PartialTranscript.toFull (spec : Spec) (partialTranscript : PartialTranscript spec spec.numRounds) : Transcript spec where
  messages := fun i => partialTranscript.messages ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt_succ i.2)⟩
  challenges := fun i => partialTranscript.challenges ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt_succ i.2)⟩


/-- The output statement and witness pair of an IOR execution -/
def Output (spec : Spec) := spec.relOut.Statement × spec.relOut.Witness


/-- The verifier's view of an IOR (before returning the output statement) -/
structure VerifierView (spec : Spec) where
  oracles : ∀ i : Fin spec.numRounds, spec.OQuery i → spec.OResponse i
  challenges : ∀ i : Fin spec.numRounds, spec.Challenge i

/--
  Convert the messages in a transcript to their oracle forms
-/
def Transcript.toOracles (transcript : Transcript spec) : VerifierView spec where
  oracles := fun i => fun q => spec.oracleFromMessage i (transcript.messages i) q
  challenges := transcript.challenges

-- TODO: for HVZK, the verifier's view only consists of the responses to the queries by the verifier, not the whole oracle (which is hard to simulate).
-- The problem right now is that we have no way of recording queries / counting the number of queries that the verifier makes to the oracles.


/--
  The prover function for each round of the IOR, disregarding the witness input and output.

  Note: we let `PrvState` and `PrvRand` to be `Type` instead of a general `Type u` to avoid universe issues when defining soundness (it can be fixed, but with a more verbose definition involving explicit universes). This does not affect downstream protocols since all objects we care about are finite anyway.
-/
structure ProverRound (spec : Spec) where
  PrvState : Fin (spec.numRounds + 1) → Type
  PrvRand : Fin spec.numRounds → Type
  samplePrvRand : ∀ i, PMF (PrvRand i)
  prove : ∀ (i : Fin spec.numRounds), spec.relIn.Statement → PrvState i → PrvRand i → spec.Challenge i → spec.Message i × (PrvState (i + 1))

-- zero-knowledge in EasyCrypt
--  parametrize the game / program by a function that's an oracle
--  how to encode this?
--  oracle has type ??
--  oracle needs state
--  FCF: `OracleComp` monad
--  CryptHOL:


/-- The full prover, including the witness input and output -/
structure Prover (spec : Spec) extends ProverRound spec where
  fromWitnessIn : spec.relIn.Witness → PrvState 0
  toWitnessOut : PrvState spec.numRounds → spec.relOut.Witness


/-- The public-coin verifier of an IOR -/
structure Verifier (spec : Spec) where
  verify : spec.relIn.Statement → VerifierView spec → spec.relOut.Statement


/-- An IOR protocol consists of an honest prover and an honest verifier, to reduce a relation `RelIn` to relation `RelOut` -/
structure Protocol (spec : Spec) extends Prover spec, Verifier spec


/-- Define family of IOR specifications parameterized by `Index` -/
structure SpecFamily where
  Index : Type _
  Spec : Index → Spec

/-- Define family of IOR protocols parameterized by `Index` -/
structure ProtocolFamily where
  SpecFamily : SpecFamily
  Protocol : (index : SpecFamily.Index) → Protocol (SpecFamily.Spec index)


-- Since we are using `PMF`, this section is marked as noncomputable
noncomputable section


def runProverAux (spec : Spec) (prover : Prover spec) (stmtIn : spec.relIn.Statement) (witIn : spec.relIn.Witness) (i : Fin spec.numRounds) : PMF (PartialTranscript spec i × prover.PrvState i) := do
  let newRand ← prover.samplePrvRand i
  let challenge ← spec.sampleChallenge i
  let (msg, newState) ← prover.prove i stmtIn (prover.fromWitnessIn witIn) newRand challenge
  return ⟨⟨msg, newState⟩, newState⟩

/--
  Running the IOR prover in the protocol; returns the transcript along with the final prover's state
-/
def runProver (spec : Spec) (prover : Prover spec) (stmtIn : spec.relIn.Statement) (witIn : spec.relIn.Witness) : PMF (Transcript spec × prover.PrvState spec.numRounds) := do
  -- TODO: once we have `HList`, we go back and define this function
  let mut state := prover.fromWitnessIn witIn
  -- let mut oracles := HList.nil ;
  -- let mut challenges := HList.nil ;
  for h : i in [0:spec.numRounds] do {
      let newRand ← prover.samplePrvRand i
      let challenge ← spec.sampleChallenge i
    -- let output := (prover.prove i) stmt newState newRand challenge
    -- oracles.append (spec.oracle i msg);
    -- challenges.append (challenge);
    -- newState := state
  }
  sorry

def runVerifier (spec : Spec) (verifier : Verifier spec) (stmtIn : spec.relIn.Statement) (view : VerifierView spec) : PMF (spec.relOut.Statement) := do
  let stmtOut := verifier.verify stmtIn view
  return stmtOut

/--
  An IOR execution between an arbitrary prover and an arbitrary verifier, on a given initial statement and witness.

  Returns a probability distribution over the prover's end private state and a verifier's output statement.
-/
def runWithTranscript (spec : Spec) (prover : Prover spec) (verifier : Verifier spec) (stmtIn : spec.relIn.Statement) (witIn : spec.relIn.Witness) : PMF (Output spec × Transcript spec) := do
  let (transcript, state) ← runProver spec prover stmtIn witIn
  let stmtOut ← runVerifier spec verifier stmtIn (transcript.toOracles)
  return ⟨⟨stmtOut, prover.toWitnessOut state⟩, transcript⟩


def run (spec : Spec) (prover : Prover spec) (verifier : Verifier spec) (stmtIn : spec.relIn.Statement) (witIn : spec.relIn.Witness) : PMF (Output spec) := do
  let result ← runWithTranscript spec prover verifier stmtIn witIn
  return result.fst



open unitInterval

/- Unit interval embedded into `NNReal` -/
instance unitInterval.toNNReal : Coe unitInterval NNReal where
  coe := fun ⟨x, h⟩ => ⟨x, (Set.mem_Icc.mp h).left⟩

section Completeness

/--
  For all valid statement-witness pair for the input relation `relIn`,
  the execution between the honest prover and the honest verifier will result in a valid pair for the output relation `relOut`,
  except with probability `completenessError`
-/
def completeness (spec : Spec) (protocol : Protocol spec) (completenessError : I) : Prop :=
    ∀ stmtIn : spec.relIn.Statement,
    ∀ witIn : spec.relIn.Witness,
    spec.relIn.isValid stmtIn witIn = true →
        let output := run spec protocol.toProver protocol.toVerifier stmtIn witIn
        let prob := spec.relOut.isValid' <$> output
        prob true ≥ 1 - completenessError


/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (spec : Spec) (protocol : Protocol spec) : Prop :=
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

This does not cover other variants such as adaptive versions of the above (seems to have negligible difference compared to non-adaptive version in the interactive setting?), or special soundness.
-/

/--
  For all initial statement `stmtIn` not in the language, all (malicious) provers with initial witness `witIn`, the execution will result in an invalid statement-witness pair for `relOut` except with probability `soundnessBound`.
-/
def soundness (spec : Spec) (verifier : Verifier spec) (soundnessBound : ENNReal) : Prop :=
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


-- Adaptive soundness? Makes no sense in interactive setting... the most the prover will do is to send the initial statement together with the first message (but this gives no extra power?)
-- The more important question is that is this property necessary for proving adaptive soundness after (strong) Fiat-Shamir?

structure AdaptiveProver (spec : Spec) extends Prover spec where
  chooseStatementIn : PrvState 0 × PrvRand 0 → spec.relIn.Statement

/--
  An extractor is defined to be a deterministic function that takes in the initial statement and the IOR transcript, and returns a corresponding initial witness.

  TODO: when we generalize IOR to the ROM, how do we model the extractor's ability to observe the prover's queries?
-/
def Extractor (spec : Spec) := spec.relIn.Statement → Transcript spec → Output spec → spec.relIn.Witness

/--
  There exists an extractor such that for all

  This is the black-box, deterministic, straightline version of knowledge soundness.
-/
def knowledgeSoundness (spec : Spec) (verifier : Verifier spec) (knowledgeBound : ENNReal) : Prop :=
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


def BadFunction (spec : Spec) := (i : Fin spec.numRounds) → spec.relIn.Statement →  PartialTranscript spec i → Prop

/--
  Round-by-round soundness should be defined for each round
-/
def roundByRoundSoundness (spec : Spec) (verifier : Verifier spec) (badFunction : BadFunction spec) (rbrSoundnessBound : Fin spec.numRounds → ENNReal) : Prop :=
  ∀ stmtIn ∉ spec.relIn.language,
  ∀ witIn : spec.relIn.Witness,
  ∀ prover : Prover spec,
  ∀ i : Fin spec.numRounds,
    let result := runWithTranscript spec prover verifier stmtIn witIn
    let output := Prod.fst <$> result
    let transcript := Prod.snd <$> result
    let prob := spec.relOut.isValid' <$> output
    let partialTranscript := (fun tr => tr.toPartial i) <$> transcript
    -- prob true ≤ rbrSoundnessBound i
    sorry
    -- let partialTranscript : PartialTranscript spec i := ⟨transcript.messages, transcript.challenges⟩
    -- prob true ≤ soundnessBound


end Soundness


section ZeroKnowledge


def Simulator (spec : Spec) := spec.relIn.Statement → PMF (VerifierView spec)


/--
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts generated by the simulator and the interaction between the verifier and the prover are (statistically) indistinguishable.

  Since we are in the public-coin case anyway, the verifier can't do anything...
-/
def zeroKnowledge (spec : Spec) (prover : Prover spec) : Prop :=
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




/--
  Zero-knowledge with respect to the honest verifier
-/
def honestVerifierZeroKnowledge (spec : Spec) (protocol : Protocol spec) : Prop :=
  sorry

end ZeroKnowledge

end

end IOR


-- TODO: IOP as a special case of IOR, where `relOut = boolRel PEmpty` (i.e. the output statement is `Bool`, and the output witness is empty)
namespace IOP

structure Spec extends IOR.Spec where
  relOut := boolRel PEmpty

-- Need to look more into structure inheritance

-- structure Prover (spec : Spec) extends IOR.Prover spec

-- structure Verifier (spec : Spec) extends IOR.Verifier spec

-- structure Protocol (spec : Spec) extends Prover spec, Verifier spec

-- structure Transcript (spec : Spec) extends IOR.Transcript spec

-- structure VerifierView (spec : Spec) extends IOR.VerifierView spec



end IOP
