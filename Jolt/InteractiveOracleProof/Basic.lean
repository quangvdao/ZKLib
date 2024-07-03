import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.UnitInterval
import Jolt.Relation.Basic

/-!
# Formalism of Interactive Oracle Proofs

We define (public-coin) interactive oracle proofs (IOPs). This is an interactive protocol between a prover and a verifier with the following format:

  - At the beginning, the prover and verifier both hold a public statement x (and potentially have access to some public parameters pp). The prover may also hold some private state which in particular may contain a witness w to the statement x.

  - In each round, the verifier sends some random challenges, and the prover sends back responses to the challenges. The responses are received as oracles by the verifier. The verifier only sees some abstract representation of the responses, and is only allowed to query these oracles in specific ways (i.e. point queries, polynomial evaluation queries, tensor queries).

  - At each step, the verifier may make oracle queries and perform some checks on the responses so far. At the end of the interaction, the verifier outputs a bit indicating accept or reject; it may also output the bit earlier at any round.

Note: the definition of IOPs as defined above generalizes those found in the literature. It has the same name as the interactive protocol in the [BCS16] paper, but it is strictly more general. We call the IOP defined in [BCS16] as a "point IOP". We also get "polynomial IOP" [BCG+19] and "tensor IOP" [BCG20] (and other kinds of IOPs) from our definition.

We formalize IOPs with the following objects:

  - The prover and verifier are modeled as probabilistic, stateful computations, where the prover outputs oracles, and the verifier has black-box access to oracles.

-/

/- Public parameters `PParams` and index information `Index` are assumed throughout -/
variable (PParams : Type _) (Index : PParams → Type _)

/--
  Define the format of a Public-Coin Interactive Oracle Proof
-/
-- structure IOPFormat where
--   Statement : Type _
--   numRounds : ℕ+
--   Message : Fin numRounds → Type _
--   Challenge : Fin numRounds → Type _
--   OQuery : Fin numRounds → Type _
--   OResponse : Fin numRounds → Type _
--   oracle : ∀ i, Message i → OQuery i → OResponse i

-- structure IOP extends IOPFormat where
--   PrvState : Fin (numRounds + 1) → Type _
--   PrvRand : Fin (numRounds + 1) → Type _
--   honestProver : ∀ i, Statement → PrvState i → PrvRand i → List Challenge → List Message × PrvState
--   honestVerifier : Statement → List (OQuery → OResponse) → List Challenge → Prop


  -- honestProver : StateT PrvState (Statement × PrvRand) (List Message)
  -- verifier : Statement → VerState → VerRand → List Message → List Challenge × VerState
  -- verifierFinal : Statement → VerState → VerRand → List Message → List Challenge → Prop


-- TODO: IOPs where both parties have access to some oracle?


-- TODO: Interactive Oracle Reductions?
structure IORFormat where
  StatementIn : Type _
  StatementOut : Type _
  numRounds : ℕ+
  Message : Fin numRounds → Type _
  Challenge : Fin numRounds → Type _
  OQuery : Fin numRounds → Type _
  OResponse : Fin numRounds → Type _
  oracle : ∀ i, Message i → OQuery i → OResponse i

structure IOR extends IORFormat where
  PrvState : Fin (numRounds + 1) → Type _
  PrvRand : Fin numRounds → Type _
  honestProver : ∀ i, StatementIn → PrvState i → PrvRand i → Challenge i → Message i × (PrvState (i + 1))
  honestVerifier : StatementIn → (∀ i : Fin numRounds, (OQuery i → OResponse i) × Challenge i) → StatementOut


namespace IOR

/-- Type of an IOR transcript -/
def Transcript (Ior : IOR) : Type _ := (i : Fin Ior.numRounds) → Ior.Message i × Ior.Challenge i

/-- Type of an IOR prover -/
@[simp]
def Prover (Ior : IOR) : Type _ := ∀ i, Ior.StatementIn → Ior.PrvState i → Ior.PrvRand i → Ior.Challenge i → Ior.Message i × (Ior.PrvState (i + 1))

/-- Type of an IOR verifier -/
@[simp]
def Verifier (Ior : IOR) : Type _ := Ior.StatementIn → (∀ i : Fin Ior.numRounds, (Ior.OQuery i → Ior.OResponse i) × Ior.Challenge i) → Ior.StatementOut


/-- An IOR execution on a given statement; returns both the transcript and the verifier's decision -/
def execution (Ior : IOR) (verifier : Verifier Ior) (prover : Prover Ior) (stmt : Ior.StatementIn) : Ior.StatementOut × Transcript Ior :=
  sorry


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
def completeness (Ior : IOR) (WitnessIn : Type _) (WitnessOut : Type _) (RelIn : Relation Ior.StatementIn WitnessIn) (RelOut : Relation Ior.StatementOut WitnessOut) (completenessError : unitInterval) : Prop := sorry
-- ∀ stmt wit : R.isValid stmt wit = True,
-- PMF.run ((execution Iop Iop.honestProver Iop.honestVerifier stmt wit).1 = false) ≥ 1 - completenessError


/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (Ior : IOR) (WitnessIn : Type _) (WitnessOut : Type _) (RelIn : Relation Ior.StatementIn WitnessIn) (RelOut : Relation Ior.StatementOut WitnessOut) : Prop :=
  completeness Ior WitnessIn WitnessOut RelIn RelOut 0


/-- For all statement not in the language and all (malicious) provers, the honest verifier will accept the interaction with probability at most `soundnessBound` -/
def soundness (Ior : IOR) (verifier : Verifier Ior) (prover : Prover Ior) (soundnessBound : unitInterval) : Prop :=
  sorry


def roundByRoundSoundness (Ior : IOR) (verifier : Verifier Ior) (prover : Prover Ior) (badFunction : ∀ i : Fin Ior.numRounds, Ior.Message i → Ior.Challenge i → Prop) : Prop :=
  sorry

def zeroKnowledge (Ior : IOR) (verifier : Verifier Ior) (prover : Prover Ior) : Prop :=
  sorry

end IOR


-- TODO: IOP as a special case of IOR, where `StatementOut := Prop`
