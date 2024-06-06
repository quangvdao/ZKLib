import Piops.ProofProducer


/-!
# Polynomial IOP Proof Systems

This file contains the main definition of the polynomial IOP as a struct containing two critical elements: A prover, and a verifier.

The file also defines what it means for a proof system to be complete and sound.

-/

-- TODO dependentify?

/--
A structure representing a Proof system in the polynomial IOP model. Each round corresponds to a single polynomial commitment. A few things to note:

* The functions here do not actually carry out cryptographic operations (such as the operations carried out to confirm an opening of a commit). These are simply abstractions that assume that the polynomials committed to actually exist and that the openings yield their expected results, and that the verifier will error out if not in a way that makes that eventuality ignorable in the security proof. The security proof is therefore *statistically* sound, at this level of abstraction.
* This formalization does not not make reference to preprocessing. To formalize a succinct IOP with preprocessing in this model, one commits to the preprocess commitments in the first rounds and passes all the infomation needed to verify this is accurate in these round in full. This makes the IOP at hand technically unsuccinct, but it is to be understood that to make it succinct, the verification of the proof as a whole can be considered as not just something that the verifier does alone, but rather something that the verifier and the trusted third party polynomials do together.
  * Thus, to compile this to a succinct proof system, we would provide a commitment number after which all the info has been given, and compile to three entities: a prover, a trusted third party to verify the first rounds, and a verifier to verify the remaining rounds.
  * Note that this does not actually affect zero knowledge
* Rather than track the precise number of rounds, we track the number of commitments. We assume there is one commitment per round and the only data we track wrt the communication parttern is the the number of randomnesses between each commitment.
  * Again, this is a situation where, to save efficiency, we could batch multiple commitments with no intervening randomnesses into a single round, but we leave this as a matter for a more advanced compiler of the system to handle.
* This struct does not itself make reference to what actual relation the IOP is targeted at proving. This is because a particular IOP might be complete or sound for multiple relations. Indeed, an IOP complete for relation R is also complete for any restriction of that relation, and an IOP sound for a relation R is also sound for broader relations (TODO these should in fact be lemmas). The relation itself is unimportant to the functioning of the IOP, and is only relevant to broader context the soundness and completeness properties.
* XXX: Pitfall - the soundness here assumes all the openings happen at the end. There is no reason why this can't be, but the monad allows monadic calls to the openings at any time, so care should be taken to compile the monad to a list of openings at the end.
* XXX You can try to dependently type this by replacing the ℕs with Fin (numCommitments + something) everywhere, but this is not recommended, as it makes the types when defining the monad operations a nightmare.
-/
structure ProofSystem (F : Type) [Field F] [Fintype F] (Stmt : Type)
    (Wit : Type) where
  /-- Each PIOP proof system has scheduled a number of commitments that the prover should send over the course of the protocol -/
  numCommitments : ℕ
  -- TODO it actually seems like this is techincally not necessary, since the completeness and soundness don't reference it. In some sense it's important for the fiat shamir application, though.

  /--  The verifier can technically generate randomness to send to the prover before and after each of these commitments (though in practice randomness is hardly ever sent before the first commitment, and any randomness generated after the last is unnecessary to send) -/
  prover : Stmt → Wit → @ProofProducer F

  /-- A probability distribution on the randomnesses given to the prover over the course of the protocol (in other words, a ComputableDistribution on functions from rounds to lists of random coins) -/
  roundRandomness :
    -- Note that the round is inside the ComputableDistribution, since it is theoretically possible for the distribution of randomness in one round to depend on the randomness of another round. In practice this is rarely the case.
    Stmt → ComputableDistribution (Coins F)

  /-- The queries that should be made to the commitments at the end of the protocol.
  note that in General definition of IOP, this could depend on the witness  -/
  oracleQueries :
    --- Takes a statement
    Stmt
    -- ... the coins ...
    → (Coins F)
    -- ... and returns a list of lists of queries to open, one for each commitment
    → List (List F)
  -- TODO perhaps the round argument should be folded into the output, so that it has the signature
  -- (Stmt → (Coins F) → List (List F))
  -- This makes it more similar to the Coins type.
  -- It also probably makes it easier to construct the monad stuff later, since we are dealing with concreate data
  --
  -- Is it ok for coins of later rounds to affect queries of earlier rounds?
  -- I think it is, but it is a bit weird. The point is that the verifier knows all the coins at the end, so they know what queries should be made. Emphasize again that all query responses are sent at the end, since there is no need for them to be sent until the verifier is doing their final check.
  --
  -- Why isn't Wit present here? In theory we could have a prover which decides what query to make based on the witness

  /-- Called "Decision procedure" in the paper. This is a *deterministic* algorithm for the verifier to determine if the proof is valid - the random coins are supplied to it via an argument. -/
  verification : --
    -- Takes a statement ...
    Stmt
    -- ... the random coins of the verifier ...
    → (Coins F)
    -- ... and a list of field elements representing, for each commitment, the queries that the prover opened, with the responses to those queries. Note that responsibility for checking that the queries are the correct ones is on the verifier.
    -- Note: this should be either
    -- * be just a List F to represent the responses I think, since the verifier can implictly access the queries by reimplenenting the oracleQueries function (perhaps not if the queries depend on the witness though)
    -- * or the coins should be removed altogether, if we are assuming that the the verifier (without the witness) can compute what queries should be made from what coins in `oracleQueries`. If this is the case, then we can make it implicit that the verifier checks that the queries are the correct ones.
    → (ℕ → List (F × F))
    -- And returns a bool representing success (true) or failure (false).
    → Bool



-- Perfect completeness here
def ProofSystem.complete (F : Type) [Field F] [Fintype F] {Stmt Wit : Type}
    (Relation : Stmt → Wit → Prop)
    (𝓟 : ProofSystem F Stmt Wit) : Prop :=  -- For any statement and witness that satisfy the relation ...
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
def ProofSystem.sound (F : Type) [Field F] [Fintype F] {Stmt Wit : Type}
    (Relation : Stmt → Wit → Prop)
    (𝓟 : ProofSystem F Stmt Wit)
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
def ProofSystem.sound_enriched (F : Type) [Field F] [Fintype F] {Stmt Wit A : Type}
    (Relation : Stmt → Wit -> A → Prop)
    (𝓟 : ProofSystem F Stmt Wit)
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
