import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UnitInterval
import VCVio
import ZKLib.Data.HList
import ZKLib.Relation.Basic

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

namespace IOR_new


-- What should a relation be? Dependent on a commitment scheme?
structure OracleRelation [DecidableEq ι] (spec : OracleSpec ι) where
  Statement : Type
  Witness : Type
  isValid : Statement → Witness → OracleComp spec Bool

end IOR_new




namespace IOR

-- TODO: IORs where both parties have access to some oracle? commit-and-prove IOR?

/- These relations don't need to be bundled with the protocol specification; this separation is
  helpful when defining composition.
  relIn : Relation
  relOut : Relation
-/

section Format

/-- Define the format of an Interactive Oracle Reduction -/
structure ProtocolSpec where
  numRounds : ℕ+
  Message : Fin numRounds → Type -- Message type for each round
  Challenge : Fin numRounds → Type -- Challenge type for each round
  OracleQuery : Fin numRounds → Type -- Query type for oracle in each round
  OracleResponse : Fin numRounds → Type -- Response type for oracle in each round
  -- Transforming messages to oracles that take queries and return responses
  oracleFromMessage : ∀ i, Message i → OracleQuery i → OracleResponse i

def ChallengePMF (spec : ProtocolSpec) := ∀ i, PMF (spec.Challenge i)

/--
  The transcript of the IOR, including all messages and challenges
-/
structure Transcript (spec : ProtocolSpec) where
  messages : ∀ i, spec.Message i
  challenges : ∀ i, spec.Challenge i








-- TODO: re-org this structure
structure ProverSpec (spec : ProtocolSpec)

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
structure Prover (spec : ProtocolSpec) (relIn : Relation) (relOut : Relation) extends ProverRound spec relIn where
  fromWitnessIn : relIn.Witness → PrvState 0
  toWitnessOut : PrvState spec.numRounds → Transcript spec → relOut.Witness

-- TODO: define `OraclePreSpec` or something that has no instances
-- def verifierView (spec : ProtocolSpec) : OracleSpec (Fin spec.numRounds) where
--   domain := fun i => spec.OracleQuery i
--   range := fun i => spec.OracleResponse i
--   domain_decidableEq' := fun i => inferInstance
--   range_decidableEq' := fun i => inferInstance
--   range_inhabited' := fun i => inferInstance
--   range_fintype' := fun i => inferInstance

/-- The public-coin verifier of an IOR -/
structure Verifier (spec : ProtocolSpec) (relIn : Relation) (relOut : Relation) where
  -- verify : relIn.Statement → OracleComp (verifierView spec) relOut.Statement
  verify : relIn.Statement → Transcript spec → relOut.Statement


/-- An IOR protocol consists of an honest prover and an honest verifier, to reduce a relation
  `RelIn` to relation `RelOut` -/
structure Protocol (spec : ProtocolSpec) (relIn : Relation) (relOut : Relation) extends Prover spec relIn relOut, Verifier spec relIn relOut


/-- Define family of IOR specifications parameterized by `Index` -/
structure ProtocolSpecFamily where
  Index : Type
  spec : Index → ProtocolSpec

/-- Define family of IOR protocols parameterized by `Index` -/
structure ProtocolFamily extends ProtocolSpecFamily where
  relIn : Index → Relation
  relOut : Index → Relation
  protocol : (index : Index) → Protocol (spec index) (relIn index) (relOut index)


end Format

section Transcript

-- More stuff about transcript

/-- A partial transcript of the IOR consists of all the messages and challenges up to a certain
  round `i ≤ spec.numRounds` -/
structure PartialTranscript (spec : ProtocolSpec) (i : Fin (spec.numRounds + 1)) where
  messages : ∀ j : Fin i, spec.Message j
  challenges : ∀ j : Fin i, spec.Challenge j

def Transcript.toBundledList (transcript : Transcript spec) : List Bundled := (List.finRange spec.numRounds).map fun i => Bundled.mk (spec.Message i) (transcript.messages i)

def Transcript.fromBundledList (l : List Bundled) (hLen : l.length = spec.numRounds) (h : ∀ i, (l.get i).α = (spec.Message i × spec.Challenge i)) : Transcript spec where
  messages := sorry
  challenges := by
    intro i
    conv at i => {rw [←hLen]}
    rename_i i1
    let bundled := l.get i
    have hi := h i
    have hEq : i1 = i := sorry
    sorry


def Transcript.toPartial (transcript : Transcript spec) (i : Fin (spec.numRounds + 1)) :
    PartialTranscript spec i where
  messages := fun j => transcript.messages j
  challenges := fun j => transcript.challenges j

-- TODO: is there a better way?
def PartialTranscript.toFull (spec : ProtocolSpec)
    (partialTranscript : PartialTranscript spec spec.numRounds) : Transcript spec where
  messages := fun j => (Fin.cast_val_eq_self j) ▸ ((Fin.val_cast_of_lt (n := spec.numRounds + 1) (a := spec.numRounds) (by simp)) ▸ partialTranscript.messages) j
  challenges := fun j => (Fin.cast_val_eq_self j) ▸ ((Fin.val_cast_of_lt (n := spec.numRounds + 1) (a := spec.numRounds) (by simp)) ▸ partialTranscript.challenges) j


/- The output statement and witness pair of an IOR execution -/
-- def Output (spec : ProtocolSpec) := spec.relOut.Statement × spec.relOut.Witness


/-- The verifier's view of an IOR (before returning the output statement) -/
structure VerifierView (spec : ProtocolSpec) where
  oracles : ∀ i : Fin spec.numRounds, spec.OracleQuery i → spec.OracleResponse i
  challenges : ∀ i : Fin spec.numRounds, spec.Challenge i

/--
  Convert the messages in a transcript to their oracle forms.

  TODO: replace this with the `OracleComp` definitions
-/
def Transcript.toOracles (transcript : Transcript spec) : VerifierView spec where
  oracles := fun i => fun q => spec.oracleFromMessage i (transcript.messages i) q
  challenges := transcript.challenges

end Transcript


-- Since we are using `PMF`, this section is marked as noncomputable
noncomputable section

section Execution

def runProverAux (prover : Prover spec relIn relOut)
    (stmtIn : relIn.Statement) (witIn : relIn.Witness)
    (sampleCh : ChallengePMF spec) (i : Fin spec.numRounds) :
    PMF (PartialTranscript spec (i + 1) × prover.PrvState (i + 1)) := sorry


  -- match i with
  -- | ⟨0, isLt⟩ => do
  --   let newRand ← prover.sampleRand 0
  --   let challenge ← sampleCh 0
  --   let (msg, newState) := prover.prove 0 stmtIn (prover.fromWitnessIn witIn) newRand challenge
  --   let partialTrans :=
  --   ⟨(by intro j ; conv at j => {simp [Nat.mod_eq_of_lt]}; exact msg),
  --   fun j => (by simp [Nat.mod_eq_of_lt] at j; simp; exact challenge)⟩
  --   return ⟨partialTrans, newState⟩
  -- | ⟨j + 1, _⟩ => do
  --   let newRand ← prover.sampleRand (j + 1)
  --   let challenge ← sampleCh (j + 1)
  --   let ⟨partialTrans, state⟩ ← runProverAux prover stmtIn witIn sampleCh j
  --   let (msg, newState) := prover.prove (j + 1) stmtIn state newRand challenge
  --   return ⟨⟨msg, newState⟩, newState⟩

/--
  Running the IOR prover in the protocol; returns the transcript along with the final prover's state
-/
def runProver (prover : Prover spec relIn relOut) (sampleCh : ChallengePMF spec)
    (stmtIn : relIn.Statement) (witIn : relIn.Witness) :
    PMF (Transcript spec × prover.PrvState spec.numRounds) := do
  -- TODO: once we have `HList`, we go back and define this function
  let mut state := prover.fromWitnessIn witIn
  -- let mut oracles := HList.nil ;
  -- let mut challenges := HList.nil ;
  for h : i in [0:spec.numRounds] do {
      let newRand ← prover.sampleRand i
      let challenge ← sampleCh i
    -- let output := (prover.prove i) stmt newState newRand challenge
    -- oracles.append (spec.oracle i msg);
    -- challenges.append (challenge);
    -- newState := state
  }
  sorry

def runVerifier (verifier : Verifier spec relIn relOut) (stmtIn : relIn.Statement) (view : VerifierView spec) :
    PMF (relIn.Statement) := do
  let stmtOut := verifier.verify stmtIn view
  return stmtOut

/--
  An IOR execution between an arbitrary prover and an arbitrary verifier, on a given initial
  statement and witness.

  Returns a probability distribution over the prover's end private state and a verifier's output
  statement.
-/
def runWithTranscript (prover : Prover spec relIn relOut) (verifier : Verifier spec relIn relOut)
    (sampleCh : ChallengePMF spec) (stmtIn : relIn.Statement) (witIn : relIn.Witness) :
    PMF (Output spec × Transcript spec) := do
  let (transcript, state) ← runProver prover sampleCh stmtIn witIn
  let stmtOut ← runVerifier verifier stmtIn (transcript.toOracles)
  return ⟨⟨stmtOut, prover.toWitnessOut state⟩, transcript⟩


def run (prover : Prover spec relIn relOut) (verifier : Verifier spec relIn relOut)
    (sampleCh : ChallengePMF spec) (stmtIn : relIn.Statement) (witIn : relIn.Witness) : PMF (Output spec) := do
  let result ← runWithTranscript prover verifier sampleCh stmtIn witIn
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


def BadFunction (spec : ProtocolSpec) :=
  (i : Fin spec.numRounds) → spec.relIn.Statement →  PartialTranscript spec i → Prop

/--
  Round-by-round soundness should be defined for each round
-/
def roundByRoundSoundness (spec : ProtocolSpec) (verifier : Verifier spec)
    (badFunction : BadFunction spec) (rbrSoundnessBound : Fin spec.numRounds → I) : Prop :=
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
    -- let partialTranscript : PartialTranscript spec i := ⟨transcript.messages,
    -- transcript.challenges⟩
    -- prob true ≤ soundnessBound


end Soundness


section ZeroKnowledge


def Simulator (spec : ProtocolSpec) := spec.relIn.Statement → PMF (VerifierView spec)


/--
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts
  generated by the simulator and the interaction between the verifier and the prover are
  (statistically) indistinguishable.

  Since we are in the public-coin case anyway, the verifier can't do anything...
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




/--
  Zero-knowledge with respect to the honest verifier
-/
def honestVerifierZeroKnowledge (spec : ProtocolSpec) (protocol : Protocol spec) : Prop :=
  sorry

end ZeroKnowledge

end SecurityDefinitions



section Composition

def ProtocolSpec.composeSequential (spec1 spec2 : ProtocolSpec) : ProtocolSpec where
  numRounds := spec1.numRounds + spec2.numRounds
  Message := fun i => if i < spec1.numRounds then spec1.Message i else spec2.Message (i - spec1.numRounds)
  Challenge := fun i => if i < spec1.numRounds then spec1.Challenge i else spec2.Challenge (i - spec1.numRounds)
  OracleQuery := fun i => if i < spec1.numRounds then spec1.OracleQuery i else spec2.OracleQuery (i - spec1.numRounds)
  OracleResponse := fun i => if i < spec1.numRounds then spec1.OracleResponse i else spec2.OracleResponse (i - spec1.numRounds)
  oracleFromMessage := fun i msg q => if i < spec1.numRounds then spec1.oracleFromMessage i msg q else spec2.oracleFromMessage (i - spec1.numRounds) msg q

def ProtocolSpec.composeParallel (spec1 spec2 : ProtocolSpec) (hEqual : spec1.numRounds = spec2.numRounds) : ProtocolSpec where
  numRounds := spec1.numRounds
  Message := fun i => spec1.Message i × spec2.Message i
  Challenge := fun i => spec1.Challenge i × spec2.Challenge i
  OracleQuery := fun i => spec1.OracleQuery i × spec2.OracleQuery i
  OracleResponse := fun i => spec1.OracleResponse i × spec2.OracleResponse i
  oracleFromMessage := fun i msg q => (spec1.oracleFromMessage i msg q, spec2.oracleFromMessage i msg q)

end Composition

end

end IOR
