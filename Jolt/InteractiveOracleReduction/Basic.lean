import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.UnitInterval
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
  StatementIn : Type _
  StatementOut : Type _
  WitnessIn : Type _
  WitnessOut : Type _
  relIn : Relation StatementIn WitnessIn
  relOut : Relation StatementOut WitnessOut
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
  prove : ∀ (i : Fin spec.numRounds), spec.StatementIn → PrvState i → PrvRand i → spec.Challenge i → spec.Message i × (PrvState (i + 1))


/-- The full prover, including the witness input and output -/
structure Prover (spec : Spec) extends ProverRound spec where
  fromWitnessIn : spec.WitnessIn → PrvState 0
  toWitnessOut : PrvState spec.numRounds → spec.WitnessOut

/-- The public-coin verifier of an IOR -/
structure Verifier (spec : Spec) where
  verify : spec.StatementIn → VerifierView spec → spec.StatementOut

/-- An IOR protocol consists of an honest prover and an honest verifier, to reduce a relation `RelIn` to relation `RelOut` -/
structure Protocol (spec : Spec) extends Prover spec, Verifier spec




-- inductive HList : List (Type u) → Type (u + 1) where
--   | nil : HList []
--   | cons {α : Type u} (x : α) {αs : List (Type u)} (xs : HList αs) : HList (α :: αs)

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)



-- Since we are using `PMF`, this section is marked as noncomputable
noncomputable section

/--
  An IOR execution between an arbitrary prover and an arbitrary verifier, on a given initial statement and witness.

  Returns a probability distribution over the prover's end private state and a verifier's output statement.
-/
-- TODO: Return the transcript of the execution as well
-- TODO: Provide another definition without extended `do` notation sugar, then prove equivalence (to enhance trustworthiness of the definition)
def execution (spec : Spec) (prover : Prover spec) (verifier : Verifier spec) (stmt : spec.StatementIn) (wit : spec.WitnessIn) : PMF (spec.StatementOut × spec.WitnessOut) :=
  do {
    -- TODO: fix the issue of heterogeneous types

    -- let mut newState := prover.fromWitnessIn wit ;
    -- let mut oracles := HList.empty ;
    -- let mut challenges := HList.empty ;
    for h : i in [0:spec.numRounds] do {
        let newRand ← prover.samplePrvRand i
        let challenge ← spec.sampleChallenge i
      -- let output := (prover.prove i) stmt newState newRand challenge
      -- oracles.append (spec.oracle i msg);
      -- challenges.append (challenge);
      -- newState := state
    }
    -- let newStmt := verifier.verify stmt (fun j => (oracles.getD j [], challenges.getD j []))
    -- let newWit := prover.toWitnessOut newState
    -- return ⟨newStmt, newWit⟩
  }


-- def PolyIop.complete (F : Type) [Field F] [Fintype F] {Stmt Wit : Type}
--     (Relation : Stmt → Wit → Prop)
--     (𝓟 : PolyIop F Stmt Wit) : Prop :=  -- For any statement and witness that satisfy the relation ...
--   ∀ stmt : Stmt, ∀ wit : Wit, Relation stmt wit →
--   -- The proof should verify with probability 1
--     (do -- This do block over the probability monad is interpreted as a function
--       let coins ← 𝓟.roundRandomness stmt
--       let oracles : ℕ → Polynomial' F := fun i =>
--         𝓟.prover stmt wit (coins.take i)
--       let oracle_queries : ℕ → List F := fun i => (𝓟.oracleQueries stmt coins).getD i []
--       let oracle_responses : ℕ → List F := fun i =>
--         (oracles i).eval <$> (oracle_queries i)
--       let query_response_pairs : ℕ → List (F × F) := fun i =>
--         List.zip (oracle_queries i) (oracle_responses i)
--       let verified := (𝓟.verification stmt coins query_response_pairs)
--       return verified
--     ).toFun true = 1


open unitInterval

/-- For all valid statement-witness pair, the honest prover will convince the verifier except with probability `completenessError` -/
def completeness (spec : Spec) (protocol : Protocol spec) (RelIn : Relation spec.StatementIn WitnessIn) (RelOut : Relation spec.StatementOut WitnessOut) (completenessError : unitInterval) : Prop := sorry
-- ∀ stmt wit : R.isValid stmt wit = True,
-- PMF.run ((execution Iop Iop.honestProver Iop.honestVerifier stmt wit).1 = false) ≥ 1 - completenessError


/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (spec : Spec) (protocol : Protocol spec) (RelIn : Relation spec.StatementIn WitnessIn) (RelOut : Relation spec.StatementOut WitnessOut) : Prop :=
  completeness spec protocol RelIn RelOut 0


/-- For all statement not in the language and all (malicious) provers, the honest verifier will accept the interaction with probability at most `soundnessBound` -/
def soundness (Ior : IOR) (verifier : Verifier Ior) (prover : Prover Ior) (soundnessBound : unitInterval) : Prop :=
-- How to quantify over all possible provers? We could quantify over all `PrvState` and `PrvRand`?
  sorry


def roundByRoundSoundness (Ior : IOR) (verifier : Verifier Ior) (prover : Prover Ior) (badFunction : ∀ i : Fin Ior.numRounds, Ior.Message i → Ior.Challenge i → Prop) : Prop :=
  sorry

def zeroKnowledge (Ior : IOR) (verifier : Verifier Ior) (prover : Prover Ior) : Prop :=
  sorry

end

end IOR


-- TODO: IOP as a special case of IOR, where `StatementOut := Prop`
