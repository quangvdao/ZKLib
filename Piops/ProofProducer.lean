import Mathlib.Data.Polynomial.Eval
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic
import Piops.ComputableTypes

/-!

# Proof Producer

This file defines the type of provers in the polynomial IOP model. These which produce polynomials to commit to, given a particular round and a collection of prior round randomnesses.


-/


-- A name for the type of algorithms which produce polynomials to commit to, given a particular round and a collection of prior round randomnesses.
def ProofProducer' {F : Type} [Field F]
    (nRounds nOraclesPerRound randomnessesPerRound : ℕ) : Type :=
  -- Takes a round
  (round : Fin nRounds) ->
  -- And a table of randomness for preceeding rounds
  ( --That is, a function taking an index into the oracles for the current round
    Fin round →
    -- and an index into the randomnesses for the current round
    Fin randomnessesPerRound →
    -- and which returns the oracle for that index
    F) →
  -- and returns a (vector of) polynomial(s) to commit to
  Fin nOraclesPerRound → Polynomial' F


-- A name for the type of algorithms which produce polynomials to commit to, given a particular round and a collection of prior round randomnesses.
-- nOraclesPerRound and randomnessesPerRound are functions from all ℕ, not just Fin nRounds, because using Fin nRounds makes for a type mismatch.
def ProofProducerDependent {F : Type} [Field F]
    (nRounds : ℕ) (nOraclesPerRound randomnessesPerRound : ℕ → ℕ) : Type :=
  -- Takes a round
  (round : Fin nRounds) ->
  -- And a table of randomness for preceeding rounds
  ( --That is, a function taking an index into the oracles for the current round
    (i : Fin round) →
    -- and an index into the randomnesses for the current round
    Fin (randomnessesPerRound i) →
    -- and which returns the oracle for that index
    F) →
  -- and returns a (vector of) polynomial(s) to commit to
  Fin (nOraclesPerRound round) → Polynomial' F


-- A name for the type of algorithms which produce polynomials to commit to, given a particular round and a collection of prior round randomnesses.
-- nOraclesPerRound is now assumed to just be 1 to simplify things. If you need to do mulitple oracles in a round, just treat them as a bunch or rounds without randomnesses, follwed by a last round with all the randomnesses you needed.
-- TODO do the same operation but for the randomnessesPerRound
def ProofProducerDependentv2 {F : Type} [Field F]
    (nRounds : ℕ) (randomnessesPerRound : ℕ → ℕ) : Type :=
  -- Takes a round (TODO rename round to message)
  (round : Fin nRounds) ->
  -- And a table of randomness for preceeding rounds
  ( --That is, a function taking an index into the oracles for the current round
    (i : Fin round) →
    -- and an index into the randomnesses for the current round
    Fin (randomnessesPerRound i) →
    -- and which returns the oracle for that index
    F) →
  -- and returns a polynomial to commit to
  Polynomial' F

-- A name for the type of algorithms which produce polynomials to commit to, given a particular round and a collection of prior round randomnesses.
-- We have now removed the number of rounds. This information is considered to be encoded in the randomnessesPerRound parameter, which is now a finitely supported function - the number of rounds is (one more than) the highest element of the support.
-- def ProofProducerDependentv3
def ProofProducerv3 {F : Type} [Field F] (randomnessesPerRound : ℕ →₀ ℕ) : Type :=
  -- Takes a round (TODO rename round to message)
  (round : ℕ) ->
  -- And a table of randomness for preceeding rounds
  ( --That is, a function taking an index into the preceeding rounds
    (i : Fin round) →
    -- and an index into the randomnesses for the that round
    Fin (randomnessesPerRound i) →
    -- and which returns the oracle for that index
    F) →
  -- and returns a polynomial to commit to
  Polynomial' F




def ProofProducerv5 {F : Type} [Field F] (rounds : ℕ) (randomnessesPerRound : Fin (rounds + 1) → ℕ) : Type :=
  -- Takes a round (TODO rename round to message)
  (round : Fin rounds) ->
  -- And a table of randomness for preceeding rounds
  ( --That is, a function taking an index into the preceeding rounds
    (i : Fin ((↑round) + 1)) →
    -- and an index into the randomnesses for the that round
    Fin (randomnessesPerRound ⟨i, by sorry⟩) →
    -- and which returns the oracle for that index
    F) →
  -- and returns a polynomial to commit to
  Polynomial' F


/-- A type of coins for a protocol over a field F. This is a list of lists of field elements: The ith element of the outer list is the list of elements that are to be revealed in the ith round -/
def Coins (F : Type) : Type := List (List F)

-- A name for the type of algorithms which produce polynomials to commit to, given a particular round and a collection of prior round randomnesses.
-- We have now removed the number of rounds. This information is considered to be encoded in the randomnessesPerRound parameter, which is now a finitely supported function - the number of rounds is (one more than) the highest element of the support.
-- def ProofProducerDependentv3
def ProofProducer {F : Type} : Type :=
  -- A (potentially truncated) list of coins
  Coins F →
  -- and returns a polynomial to commit to
  Polynomial' F




-- -- Takes a prover algorithm and a sequence of round randomnesses and returns the vector of
-- -- polynomials the prover commits to
-- def proverToOracles {F : Type} [Field F]
--     (rounds : ℕ)
--     (randomnessesPerRound : Fin rounds → ℕ)
--     (producer : @ProofProducer F _ rounds randomnessesPerRound)
--     (round : Fin rounds)
--     (all_round_randomness : (round : ℕ) → Fin (randomnessesPerRound round) → F)  :
--     Polynomial' F :=
--   by
--   -- show_term {
--   apply producer round
--   · intro prev_round rand
--     apply all_round_randomness prev_round rand
