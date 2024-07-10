import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UnitInterval
import Jolt.Data.DVec
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
  OFunction : ∀ i, Message i → OQuery i → OResponse i -- Transforming messages to oracles that take queries and return responses


/-- The IOR transcript; also can be seen as the view of the IOR prover -/
structure Transcript (spec : Spec) where
  messages : ∀ i : Fin spec.numRounds, spec.Message i
  challenges : ∀ i : Fin spec.numRounds, spec.Challenge i

/-- The output statement and witness pair of an IOR execution -/
structure Output (spec : Spec) where
  statementOut : spec.relOut.Statement
  witnessOut : spec.relOut.Witness


/-- The verifier's view of an IOR (before returning the output statement) -/
structure VerifierView (spec : Spec) where
  oracles : ∀ i : Fin spec.numRounds, spec.OQuery i → spec.OResponse i
  challenges : ∀ i : Fin spec.numRounds, spec.Challenge i

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


/-- The full prover, including the witness input and output -/
structure Prover (spec : Spec) extends ProverRound spec where
  fromWitnessIn : spec.relIn.Witness → PrvState 0
  toWitnessOut : PrvState spec.numRounds → spec.relOut.Witness


/-- The public-coin verifier of an IOR -/
structure Verifier (spec : Spec) where
  verify : spec.relIn.Statement → VerifierView spec → spec.relOut.Statement


/-- An IOR protocol consists of an honest prover and an honest verifier, to reduce a relation `RelIn` to relation `RelOut` -/
structure Protocol (spec : Spec) extends Prover spec, Verifier spec


/-- Define family of IOR specifications, depending on public parameters `PParams` and index `Index` -/
structure SpecFamily where
  PParams : Type _
  Index : PParams → Type _
  Spec : (pp : PParams) → Index pp → Spec

/-- Define family of IOR protocols depending on `PParams` and `Index` -/
structure ProtocolFamily where
  PParams : Type _
  Index : PParams → Type _
  Spec : (pp : PParams) → Index pp → Spec
  Protocol : (pp : PParams) → (index : Index pp) → Protocol (Spec pp index)


-- Since we are using `PMF`, this section is marked as noncomputable
noncomputable section

/--
  An IOR execution between an arbitrary prover and an arbitrary verifier, on a given initial statement and witness.

  Returns a probability distribution over the prover's end private state and a verifier's output statement.
-/
def execution (spec : Spec) (prover : Prover spec) (verifier : Verifier spec) (stmt : spec.relIn.Statement) (wit : spec.relIn.Witness) : PMF (spec.relOut.Statement × spec.relOut.Witness) :=
  sorry
  -- Really have to develop support for dependent vectors
  -- Don't think I can do this with the standard `do` notation, has to do a recursive definition
  -- do {
  --   -- TODO: fix the issue of heterogeneous types

  --   -- let mut newState := prover.fromWitnessIn wit ;
  --   -- let mut oracles := HList.empty ;
  --   -- let mut challenges := HList.empty ;
  --   for h : i in [0:spec.numRounds] do {
  --       let newRand ← prover.samplePrvRand i
  --       let challenge ← spec.sampleChallenge i
  --     -- let output := (prover.prove i) stmt newState newRand challenge
  --     -- oracles.append (spec.oracle i msg);
  --     -- challenges.append (challenge);
  --     -- newState := state
  --   }
  --   -- let newStmt := verifier.verify stmt (fun j => (oracles.getD j [], challenges.getD j []))
  --   -- let newWit := prover.toWitnessOut newState
  --   -- return ⟨newStmt, newWit⟩
  -- }

-- TODO: Return the transcript of the execution as well

open unitInterval

/- Unit interval embedded into `ENNReal` -/
-- instance coe_unitInterval_ENNReal : Coe unitInterval ENNReal := fun x => x.toNNReal

-- TODO: figure out the right coercion
def unitInterval' : Set ENNReal := {x | x ≠ ⊤ ∧ x.toReal ∈ I}


section Completeness

/-- For all valid statement-witness pair for the input relation `relIn`, the execution between the honest prover and the honest verifier will result in a valid pair for the output relation `relOut`, except with probability `completenessError` -/
def completeness (spec : Spec) (protocol : Protocol spec) (completenessError : ENNReal) : Prop :=
    ∀ stmtIn : spec.relIn.Statement,
    ∀ witIn : spec.relIn.Witness,
    spec.relIn.isValid stmtIn witIn = true →
        let output := execution spec protocol.toProver protocol.toVerifier stmtIn witIn
        let prob := spec.relOut.isValidProp <$> output
        prob true ≥ 1 - completenessError


/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (spec : Spec) (protocol : Protocol spec) : Prop :=
  completeness spec protocol 0

end Completeness


section Soundness

/--
  For all initial statement `stmtIn` not in the language, all (malicious) provers with initial witness `witIn`, the execution will result in an invalid statement-witness pair for `relOut` except with probability `soundnessBound`.
-/
def soundness (spec : Spec) (verifier : Verifier spec) (soundnessBound : ENNReal) : Prop :=
  ∀ stmtIn ∉ spec.relIn.language,
  /-
    Need to quantify over the witness because of the way we defined
    the type signature of the prover, which always takes in some witness.
    Think of this as the initial state of the prover.
  -/
  ∀ witIn : spec.relIn.Witness,
  ∀ prover : Prover spec,
    let output := execution spec prover verifier stmtIn witIn
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
def Extractor (spec : Spec) := spec.relIn.Statement → Transcript spec → spec.relIn.Witness

/--
  There exists an extractor such that for all

  This is the black-box, deterministic, straightline version of knowledge soundness.
-/
def knowledgeSoundness (spec : Spec) (verifier : Verifier spec) (knowledgeBound : ENNReal) : Prop :=
  ∃ extractor : Extractor spec,
  ∀ stmtIn : spec.relIn.Statement,
  sorry



end Soundness


section ZeroKnowledge

def roundByRoundSoundness (spec : Spec) (protocol : Protocol spec) (badFunction : ∀ i : Fin spec.numRounds, spec.Message i → spec.Challenge i → Prop) : Prop :=
  sorry


def Simulator (spec : Spec) := spec.relIn.Statement → PMF (VerifierView spec)


/--
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts generated by the simulator and the interaction between the verifier and the prover are (statistically) indistinguishable.

  Since we are in the public-coin case anyway, the verifier can't do anything...
-/
def zeroKnowledge (spec : Spec) (prover : Prover spec) : Prop :=
  ∃ simulator : Simulator spec,
  ∀ verifier : Verifier spec,
    let output := execution spec prover verifier
    let prob := spec.relOut.isValid' <$> output
    prob true ≥ 1 - completenessError




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
