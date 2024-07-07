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

-- TODO: IORs where both parties have access to some oracle?

namespace IOR

/-
Public parameters `PParams` and index information `Index` are assumed throughout

Too cumbersome to do this? Is there a better way? Leaving this out for now
-/

-- variable {PParams : Type _} {Index : PParams → Type _}

/-- Define the format of an Interactive Oracle Reduction -/
structure Spec where
  relIn : Relation
  relOut : Relation
  numRounds : ℕ+
  Message : Fin numRounds → Type _
  Challenge : Fin numRounds → Type _
  sampleChallenge : ∀ i, PMF (Challenge i)
  OQuery : Fin numRounds → Type _
  OResponse : Fin numRounds → Type _
  oracle : ∀ i, Message i → OQuery i → OResponse i

/-- The IOR transcript; also can be seen as the final view of the IOR prover -/
def Transcript (spec : Spec) := (i : Fin spec.numRounds) → spec.Message i × spec.Challenge i

/-- The verifier's view of an IOR -/
def VerifierView (spec : Spec) := (i : Fin spec.numRounds) → spec.OQuery i × spec.Challenge i

/-- The prover function for each round of the IOR, disregarding the witness input and output -/
structure ProverRound (spec : Spec) where
  PrvState : Fin (spec.numRounds + 1) → Type _
  PrvRand : Fin spec.numRounds → Type _
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




-- inductive HList : List (Type u) → Type (u + 1) where
--   | nil : HList []
--   | cons {α : Type u} (x : α) {αs : List (Type u)} (xs : HList αs) : HList (α :: αs)

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

def NatInt : Fin 2 → Type _
  | 0 => ℕ
  | 1 => ℤ

def funNatInt (i : Fin 2) : NatInt i := match i with
  | 0 => (0 : ℕ)
  | 1 => (-1 : ℤ)


-- Since we are using `PMF`, this section is marked as noncomputable
noncomputable section

/--
  An IOR execution between an arbitrary prover and an arbitrary verifier, on a given initial statement and witness.

  Returns a probability distribution over the prover's end private state and a verifier's output statement.
-/
def execution (spec : Spec) (prover : Prover spec) (verifier : Verifier spec) (stmt : spec.relIn.Statement) (wit : spec.relIn.Witness) : PMF (spec.relOut.Statement × spec.relOut.Witness) :=
  sorry
  -- Really have to develop support for dependent vectors
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
-- TODO: Provide another definition without extended `do` notation sugar, then prove equivalence (to enhance the trustworthiness of the definition)

#check execution

open unitInterval

/- Unit interval embedded into `ENNReal` -/
-- instance coe_unitInterval_ENNReal : Coe unitInterval ENNReal := fun x => x.toNNReal

-- TODO: figure out the right coercion
def unitInterval' : Set ENNReal := {x | x ≠ ⊤ ∧ x.toReal ∈ I}

set_option pp.universes true

/-- For all valid statement-witness pair for the input relation `relIn`, the execution between the honest prover and the honest verifier will result in a valid pair for the output relation `relOut`, except with probability `completenessError` -/
def completeness (spec : Spec) (protocol : Protocol spec) (completenessError : ENNReal) : Prop :=
    ∀ stmtIn : spec.relIn.Statement,
    ∀ witIn : spec.relIn.Witness,
    spec.relIn.isValid stmtIn witIn = true →
        let output := execution spec protocol.toProver protocol.toVerifier stmtIn witIn
        let prob := spec.relOut.isValidProp <$> output
        prob true ≥ 1 - completenessError

-- #check completeness

/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (spec : Spec) (protocol : Protocol spec) : Prop :=
  completeness spec protocol 0


/--
  For all initial statement `stmtIn` not in the language, all (malicious) provers with initial witness `witIn`, the execution will result in an invalid statement-witness pair for `relOut` except with probability `soundnessBound`.
-/
def soundness (spec : Spec) (verifier : Verifier spec) (soundnessBound : ENNReal) : Prop :=
  -- sorry
  ∀ stmtIn ∉ spec.relIn.language,
  -- need to quantify over the witness because of the way we defined the type signature of the prover, which always takes in a witness
  ∀ witIn : spec.relIn.Witness,
  ∀ prover : Prover spec,
    let output := execution spec prover verifier stmtIn witIn
    let prob := spec.relOut.isValid' <$> output
    prob true ≤ soundnessBound



def roundByRoundSoundness (spec : Spec) (protocol : Protocol spec) (badFunction : ∀ i : Fin spec.numRounds, spec.Message i → spec.Challenge i → Prop) : Prop :=
  sorry

def zeroKnowledge (spec : Spec) (protocol : Protocol spec) : Prop :=
  sorry

end

end IOR


-- TODO: IOP as a special case of IOR, where `relOut = boolRel`
