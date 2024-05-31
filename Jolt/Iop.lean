import Mathlib.Data.Fintype.Basic
import Jolt.ComputableTypes



-- Hmmm, seems like the most general object we should define is an "Interactive Oracle Reduction"
--
structure InteractiveOracleReduction (F : Type) [Fintype F] (Instance Witness : Type) :=
  (numRounds : Instance → ℕ)
  (messageMask : Type → Type)
  (queryType : Type → Type)
  (proverType : Type → Type → Type → Type → Type → Type)
  (verifierType : Type → Type → Type → Type → Type → Type)
  (prover : ℕ)
  (verifier : ℕ)






-- Type signature for a single round of the prover
-- Takes in an instance, a prover state, a list of challenges for the current round, and a randomness value, then outputs a response and a new prover state
def proverRound (Instance ProverState Challenge Randomness Response : Type) :=
  Instance → ProverState → List Challenge → Randomness → (Response × ProverState)

-- Define the structure for the interactive proof system
-- Note: this structure is bad / not general enough, since it assumes the verifier takes the same action in each round (i.e. for ver1)
structure InteractiveProof (Instance VerifierState Response Randomness Challenge : Type) :=
  (ver0 : Instance → VerifierState → Bool)
  (ver1 : Instance → Response → Randomness → Challenge → List Challenge → VerifierState → (Bool × Instance × VerifierState))

-- Define the prove function within the context of InteractiveProof
namespace InteractiveProof

-- variables {Instance VerifierState Response Randomness Challenge ProverState : Type}

def execution (ip : InteractiveProof Instance VerifierState Response Randomness Challenge)
          (vs : VerifierState) (prv : proverRound Instance ProverState Challenge Randomness Response)
          (ps : ProverState) (inst : Instance) (rnd : Randomness) (rounds : List (Challenge × Randomness)) : Bool :=
  match rounds with
  | [] => ip.ver0 inst vs
  | (round_data, rnd') :: remaining_rounds =>
    let (resp, ps') := prv inst round_data (remaining_rounds.map Prod.fst) rnd ps in
    let (ok, inst', vs') := ip.ver1 inst resp rnd' round_data (remaining_rounds.map Prod.fst) vs in
    ok && prove ip vs' prv ps' inst' rnd' remaining_rounds

end InteractiveProof



def Coins (F : Type) : Type := List (List F)

-- def ProofProducer {F : Type} : Type := Coins F → Polynomial' F

structure PolyIop (F : Type) [Field F] [Fintype F] (Stmt : Type) (Wit : Type) where
  -- number of rounds, may depend on statement
  numRounds : Stmt → ℕ

  -- number of polynomials in each round
  numPolys : Stmt → ℕ → ℕ

  -- number of variables in each polynomial
  numVars : Stmt → ℕ → ℕ → ℕ

  -- maximum number of variables for any polynomial
  maxNumVars : Stmt → ℕ

  -- degree bounds for each polynomial
  degreeBounds : Stmt → ℕ → ℕ → Finset ℕ

  -- number of challenges in each round
  -- (each challenge is a field element)
  numChals : Stmt → ℕ → ℕ

  proverType (Instance ProverState Challenge Randomness Response : Type) (num : Type) :
  Instance → ProverState → List Challenge → Randomness → (Response × ProverState × num)


  honestProver : proverRound Instance ProverState Challenge Randomness Response

  honestVerifier : ℕ

  -- prover should be defined uniformly at random
  -- base case: takes in statement and witness and first round's prover randomness, then outputs numPolys(x,0) number of polynomials, and a new state


  -- Define the prover function
  prover : Stmt → Wit → ℕ → List F → (List (Polynomial' F), List F)
  prover stmt wit 0 randomness :=
    let polys := List.range (numPolys stmt 0) |>.map (λ _, generatePolynomial (numVars stmt 0 _) (degreeBound stmt 0 _))
    let newState := updateState stmt wit randomness
    (polys, newState)
  prover stmt wit (i + 1) randomness :=
    let (prevPolys, prevState) := prover stmt wit i randomness
    let newRandomness := proverRandomness stmt (i + 1)
    let polys := List.range (numPolys stmt (i + 1)) |>.map (λ _, generatePolynomial (numVars stmt (i + 1) _) (degreeBound stmt (i + 1) _))
    let newState := updateStateBasedOnPrevState stmt wit prevState newRandomness
    (polys, newState)


  roundRandomness : Stmt → ComputableDistribution (Coins F)

  oracleQueries : Stmt → (Coins F) → List (List F)

  verification : Stmt → (Coins F) → (ℕ → List (F × F)) → Bool



-- Perfect completeness here
def PolyIop.complete (F : Type) [Field F] [Fintype F] {Stmt Wit : Type}
    (Relation : Stmt → Wit → Prop)
    (𝓟 : PolyIop F Stmt Wit) : Prop :=  -- For any statement and witness that satisfy the relation ...
  ∀ stmt : Stmt, ∀ wit : Wit, Relation stmt wit →
  -- The proof should verify with probability 1
    (do -- This do block over the probability monad is interpreted as a function
      let coins ← 𝓟.roundRandomness stmt
      let oracles : ℕ → Polynomial' F := fun i =>
        𝓟.prover stmt wit (coins.take i)
      let oracle_queries : ℕ → List F := fun i => (𝓟.oracleQueries stmt coins).getD i []
      let oracle_responses : ℕ → List F := fun i =>
        (oracles i).eval <$> (oracle_queries i)
      let query_response_pairs : ℕ → List (F × F) := fun i =>
        List.zip (oracle_queries i) (oracle_responses i)
      let verified := (𝓟.verification stmt coins query_response_pairs)
      return verified
    ).toFun true = 1


-- Todo: allow promises of statements
-- Note that PIOPs are info-theoretically sound (excluding the polynomial commitment).
def PolyIop.sound (F : Type) [Field F] [Fintype F] {Stmt Wit : Type}
    (Relation : Stmt → Wit → Prop)
    (𝓟 : PolyIop F Stmt Wit)
    (extractor :-- Should the extractor have access to stmt? Does it matter?
        Stmt →
        @ProofProducer F → Wit)
    (soundnessBound : Rat) : Prop :=
-- For any statement and any adversary ...
  ∀ stmt : Stmt, ∀ adv_prover : @ProofProducer F,
  -- ... if the probability of convinicing the verifier is more than the soundness ε ...
  (do
    let coins ← 𝓟.roundRandomness stmt
    let oracles : ℕ → Polynomial' F := fun i =>
      adv_prover (coins.take i)
    let oracle_queries : ℕ → List F := fun i => (𝓟.oracleQueries stmt coins).getD i []
    let oracle_responses : ℕ → List F := fun i =>
      (oracles i).eval <$> (oracle_queries i)
    let query_response_pairs : ℕ → List (F × F) := fun i =>
      List.zip (oracle_queries i) (oracle_responses i)
    let verified := (𝓟.verification stmt coins query_response_pairs)
    return verified
      ).toFun true > soundnessBound
      -- ... then the extractor gives a valid witness.
      → Relation stmt (extractor stmt adv_prover)

-- A notion of soundness enriched with a return value (should I build it into the statement?)
def PolyIop.sound_enriched (F : Type) [Field F] [Fintype F] {Stmt Wit A : Type}
    (Relation : Stmt → Wit -> A → Prop)
    (𝓟 : PolyIop F Stmt Wit)
    (extractor :-- Should the extractor have access to stmt? Does it matter?
        Stmt →
        @ProofProducer F → Wit)
    (soundnessBound : Rat) : Prop :=
-- For any statement and any adversary ...
  ∀ stmt : Stmt, ∀ adv_prover : @ProofProducer F, ∀ a : A,
  (do
    let coins ← 𝓟.roundRandomness stmt
    let oracles : ℕ → Polynomial' F := fun i =>
      adv_prover (coins.take i)
    let oracle_queries : ℕ → List F := fun i => (𝓟.oracleQueries stmt coins).getD i []
    let oracle_responses : ℕ → List F := fun i =>
      (oracles i).eval <$> (oracle_queries i)
    let query_response_pairs : ℕ → List (F × F) := fun i =>
      List.zip (oracle_queries i) (oracle_responses i)
    let verified := (𝓟.verification stmt coins query_response_pairs)
    return verified ∨ ¬ Relation stmt (extractor stmt adv_prover) a
      ).toFun true > soundnessBound
