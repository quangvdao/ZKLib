import Mathlib.Control.Monad.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.UnitInterval
import Jolt.Relation.Basic
-- import Jolt.Data.SPMF

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


/--
  Define the class of Public-Coin Interactive Oracle Proofs
-/
class IOP (PParams : Type _) (Index : PParams → Type _) where
  numRounds : (pp : PParams) → Index pp → ℕ
  Statement : (pp : PParams) → Index pp → Type _
  PrvState : (pp : PParams) → Index pp → Type _
  PrvRand : (pp : PParams) → (index : Index pp) → Fin (numRounds pp index) → Type _
  -- These are not needed for public-coin verifier
  -- VerState : (pp : PParams) → Index pp → Type _
  -- VerRand : (pp : PParams) → (index : Index pp) → Fin (numRounds pp index) → Type _
  Message : (pp : PParams) → (index : Index pp) → Fin (numRounds pp index) → Type _
  Challenge : (pp : PParams) → (index : Index pp) → Fin (numRounds pp index) → Type _
  OQuery : (pp : PParams) → (index : Index pp) → Fin (numRounds pp index) → Type _
  OResponse : (pp : PParams) → (index : Index pp) → Fin (numRounds pp index) → Type _
  oracle : (pp : PParams) → (index : Index pp) → (n : Fin (numRounds pp index)) → Message pp index n → OQuery pp index n → OResponse pp index n

class IOPWithHonestParties (PParams : Type _) (Index : PParams → Type _) extends IOP PParams Index where
  honestProver : Statement → PrvState → PrvRand → List Challenge → List Message × PrvState
  honestVerifier : Statement → List (OQuery → OResponse) → List Challenge → Prop



  -- honestProver : StateT PrvState (Statement × PrvRand) (List Message)
  -- verifier : Statement → VerState → VerRand → List Message → List Challenge × VerState
  -- verifierFinal : Statement → VerState → VerRand → List Message → List Challenge → Prop


/--
  Collection of IOPs with the same public parameters `PParams` but possible different indices `Index`
-/
structure IOPFamily (PParams : Type _) where
  Index : PParams → Type _
  [IOP : IOP PParams Index]

attribute [instance] IOPFamily.IOP


namespace IOP

/-- Type of an IOP transcript -/
def Transcript (Iop : IOP pp index) : Type _ := List (Iop.Message × Iop.Challenge)

/-- Type of an IOP prover -/
@[simp]
def Prover (Iop : IOP pp index) : Type _ := Iop.Statement → Iop.PrvState → Iop.PrvRand → List Iop.Challenge → List Iop.Message × Iop.PrvState

/-- Type of an IOP verifier -/
@[simp]
def Verifier (Iop : IOP pp index) : Type _ := Iop.Statement → List (Iop.OQuery → Iop.OResponse) → List Iop.Challenge → Prop


/-- An IOP execution on a given statement; returns both the transcript and the verifier's decision -/
def execution (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) (stmt : Iop.Statement) : Prop × Transcript Iop :=
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
def completeness (Iop : IOP pp index) (R : Relation pp index) (completenessError : unitInterval) : Prop := sorry
-- ∀ stmt wit : R.isValid stmt wit = True,
-- PMF.run ((execution Iop Iop.honestProver Iop.honestVerifier stmt wit).1 = false) ≥ 1 - completenessError


/-- Perfect completeness when there is no completeness error -/
def perfectCompleteness (Iop : IOP pp index) (R : Relation pp index) : Prop :=
  completeness Iop R 0


/-- For all statement not in the language and all (malicious) provers, the honest verifier will accept the interaction with probability at most `soundnessBound` -/
def soundness (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) (soundnessBound : unitInterval) : Prop :=
  sorry


def roundByRoundSoundness (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) (badFunction : List Iop.Message → List Iop.Challenge → Prop) : Prop :=
  sorry

def zeroKnowledge (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) : Prop :=
  sorry

end IOP
