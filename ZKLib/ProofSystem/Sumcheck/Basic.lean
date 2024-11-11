/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.ToOracle
import ZKLib.OracleReduction.Security
import ZKLib.ProofSystem.Relation.Sumcheck

/-!
# The Sum-check Protocol

We define the sum-check protocol as a series of Interactive Oracle Reductions (IORs), where the
underlying polynomials are represented using Mathlib's noncomputable types `Polynomial` and
`MvPolynomial`.

Other files will deal with implementations of the protocol, and we will prove that those
implementations derive security from that of the abstract protocol.

## Protocol Specification

The sum-check protocol is parameterized by the following:
- `R`: the underlying ring (for soundness, required to be finite and a domain)
- `n`: the number of variables (also number of rounds)
- `deg`: the individual degree bound for the polynomial
- `D`: the set of `m` evaluation points for each variable (for some `m`), represented as an
  injection `Fin m ↪ R`. The image of `D` as a finite subset of `R` is written as `Finset.univ.map
  D`.

The sum-check relation has no witness. The statement for the `i`-th round, where `i ≤ n`, contains:
- `poly : MvPolynomial (Fin n) R`, which is the multivariate polynomial that is summed over
- `target : R`, which is the target value for sum-check
- `challenges : Fin i → R`, which is the list of challenges sent from the verifier to the prover in
  previous rounds
- `earlyReject : Bool`, which is whether the verifier has already rejected

The sum-check relation for the `i`-th round checks that:
- `earlyReject = false`
- `∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨challenges, x⸩ = target`.

Note that the last statement (when `i = n`) is the output statement of the sum-check protocol.

For `i = 0, ..., n - 1`, the `i`-th round of the sum-check protocol consists of the following:

1. The prover sends a univariate polynomial `p_i ∈ R⦃≤ deg⦄[X]` of degree at most `deg`. If the
   prover is honest, then we have:
   `p_i(X) = ∑ x ∈ (univ.map D) ^ᶠ (n - i - 1), poly ⸨X ⦃i⦄, challenges, x⸩`.

  Here, `poly ⸨X ⦃i⦄, challenges, x⸩` is the polynomial `poly` evaluated at the concatenation of the
  prior challenges `challenges`, the `i`-th variable as the new indeterminate `X`, and the rest of
  the values `x ∈ (univ.map D) ^ᶠ (n - i - 1)`.

  In the oracle protocol, this polynomial `p_i` is turned into an oracle for which the verifier can
  query for evaluations at arbitrary points.

2. The verifier then sends the `i`-th challenge `r_i` sampled uniformly at random from `R`.

3. The (oracle) verifier then performs queries for the evaluations of `p_i` at all points in
`(univ.map D)`, and checks that: `∑ x in (univ.map D), p_i.eval x = target`.

   It then outputs a statement for the next round as follows:
   - `poly` is unchanged
   - `target` is updated to `p_i.eval r_i`
   - `challenges` equals the concatenation of the previous challenges and `r_i`
   - `earlyReject` equals prior `earlyReject` and the result of the above check

## Notes & TODOs

Note that to represent sum-check as a series of IORs, we will need to implicitly constrain the
degree of the polynomials via using subtypes, such as `Polynomial.degreeLE` and
`MvPolynomial.degreeOf`. This is because the oracle verifier only gets oracle access to evaluating
the polynomials, but does not see the polynomials in the clear.

When this is compiled to an interactive proof, the corresponding polynomial commitment schemes will
enforce that the declared degree bound holds, via letting the (non-oracle) verifier perform explicit
degree checks.

There are some generalizations that we could consider later:

- Generalize to `degs : Fin n → ℕ` and `domain : Fin n → Finset R`, e.g. can vary the degree bound
  and the summation domain for each variable

- Generalize the challenges to come from a suitable subset of `R` (e.g. subtractive sets), and not
  necessarily the whole domain. This is used in lattice-based protocols.

- Sumcheck over modules instead of just rings. This will require extending `MvPolynomial` to have
  such a notion of evaluation, something like `evalModule (x : σ → M) (p : MvPolynomial σ R) : M`,
  where we have `[Module R M]`.

-/

namespace Sumcheck

noncomputable section
namespace Spec

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

-- The variables for sum-check
variable (R : Type) [CommSemiring R] [Sampleable R] (n : ℕ) (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- Statement for sum-check, parameterized by the ring `R`, the number of variables `n`, the domain
  `D`, and the round index `i ≤ n`

Note that when `i = n`, this is the output statement of the sum-check protocol -/
structure Statement (i : ℕ) (hi : i ≤ n) where
  -- The multivariate polynomial for sum-check
  poly : R⦃≤ deg⦄[X Fin n]
  -- The target value for sum-check
  target : R
  -- The challenges sent from the verifier to the prover from previous rounds
  challenges : Fin i → R
  -- Whether the statement has already been rejected
  earlyReject : Bool

/-- The sum-check relation for the `i`-th round, for `i ≤ n` -/
def relation (i : ℕ) (hi : i ≤ n) : (Statement R n deg i hi) → Unit → Prop :=
  fun ⟨⟨poly, _⟩, target, challenges, earlyReject⟩ _ =>
    earlyReject = false ∧ ∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨challenges, x⸩ = target

/-- Protocol specification for the `i`-th round of the sum-check protocol

Consists of a message from prover to verifier of degree at most `deg`, and a message
from verifier to prover of a field element in `R`. -/
def pSpec : ProtocolSpec 2 := ![(.P_to_V, R⦃≤ deg⦄[X]), (.V_to_P, R)]

/-- Combination of the protocol specifications for all rounds -/
def pSpecCombined (n : ℕ) : ProtocolSpec (n * 2) := by
  simpa using Fin.join (fun (_ : Fin n) => pSpec R deg)

/-- There is only one message from the prover to the verifier -/
instance : Unique (MessageIndex (pSpec R deg)) where
  default := ⟨0, by simp [pSpec, getDir]⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose hi
    have : i = 1 := by omega
    simp [pSpec, getDir, this]

/-- There is only one challenge from the verifier to the prover -/
instance : Unique (ChallengeIndex (pSpec R deg)) where
  default := ⟨1, by simp [pSpec, getDir]⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose hi
    have : i = 0 := by omega
    simp [pSpec, getDir, this]

/-- Recognize that the (only) message from the prover to the verifier has type `R⦃≤ deg⦄[X]`, and
  hence can be turned into an oracle for evaluating the polynomial -/
instance : (i : MessageIndex (pSpec R deg)) → ToOracle ((pSpec R deg).Message i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  simp [this, default, pSpec, Message, getType]
  exact instToOraclePolynomialDegreeLE

/-- Prover input for the `i`-th round of the sum-check protocol, where `i < n` -/
def proverIn (i : Fin n) : ProverIn (pSpec R deg) (Statement R n deg i (by omega)) Unit
    (Statement R n deg i (by omega)) where
  load := fun stmt _ => stmt

/-- Prover interaction for the `i`-th round of the sum-check protocol, where `i < n`. This is only
  well-defined for `n > 0` -/
def proverRound (i : Fin n) (hn : n > 0) :
    ProverRound (pSpec R deg) emptySpec (Statement R n deg i (by omega)) where
  sendMessage := fun idx state => by
    have ⟨⟨poly, _⟩, target, challenges, earlyReject⟩ := state
    haveI : idx = default := Unique.uniq (inferInstance) idx
    rw [this]
    simp [pSpec, Message, getType, this, default]
    let n' := n - 1
    have : n = n' + 1 := by omega
    simp_rw [this] at poly
    exact pure ⟨ ⟨∑ x ∈ (univ.map D) ^ᶠ (n' - i), poly ⸨X ⦃i⦄, challenges, x⸩, sorry⟩, state ⟩
  receiveChallenge := fun _ state _ => state

/-- Since there is no witness, the prover's output for each round `i < n` of the sum-check protocol
  is trivial -/
def proverOut (i : Fin n) : ProverOut Unit (Statement R n deg i (by omega)) where
  output := fun _ => ()

/-- The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only
  well-defined for `n > 0`, since when `n = 0` there is no protocol. -/
def prover (i : Fin n) (hn : n > 0) : Prover (pSpec R deg) emptySpec
    (Statement R n deg i (by omega)) Unit (Statement R n deg (i + 1) (by omega)) Unit
    (Statement R n deg i (by omega)) where
  toProverIn := proverIn R n deg i
  toProverRound := proverRound R n deg D i hn
  toProverOut := proverOut R n deg i

/-- The default value for the tuple (message index, query, response) -/
instance : Inhabited ((i : MessageIndex (pSpec R deg)) × ToOracle.Query ((pSpec R deg).Message i)
    × ToOracle.Response ((pSpec R deg).Message i)) where
  default := ⟨default,
    by simp [pSpec, Message, getType, default, instToOracleMessagePSpec,
      instToOraclePolynomialDegreeLE]; exact 0,
    by simp [pSpec, Message, getType, default, instToOracleMessagePSpec,
      instToOraclePolynomialDegreeLE]; exact 0⟩

/-- The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n` -/
def verifier (i : Fin n) : Verifier (pSpec R deg) emptySpec
    (Statement R n deg i (by omega)) (Statement R n deg (i + 1) (by omega)) where
  verify := fun ⟨poly, target, challenges, earlyReject⟩ transcript => by
    let ⟨p_i, _⟩ : R⦃≤ deg⦄[X] := transcript 0
    let r_i : R := transcript 1
    let accept := decide (∑ x ∈ (univ.map D), p_i.eval x = target)
    exact pure ⟨poly, p_i.eval r_i, Fin.snoc challenges r_i, earlyReject ∨ ¬ accept⟩

/-- The oracle verifier for the `i`-th round, where `i < n` -/
def oracleVerifier (i : Fin n) : OracleVerifier (pSpec R deg) emptySpec
    (Statement R n deg i (by omega)) (Statement R n deg (i + 1) (by omega)) where
  -- Queries for the evaluations of the polynomial at all points in `D`,
  -- plus one query for the evaluation at the challenge `r_i`
  genQueries := fun _ chal => List.ofFn (fun j => ⟨default, D j⟩) ++ [⟨default, chal default⟩]
  -- Check that the sum of the evaluations equals the target, and updates the statement accordingly
  -- (the new target is the evaluation of the polynomial at the challenge `r_i`)
  verify := fun ⟨poly, target, challenges, earlyReject⟩ chal responses => by
    simp [ResponseList] at responses
    have f : (i : MessageIndex (pSpec R deg)) × ToOracle.Query ((pSpec R deg).Message i)
        × ToOracle.Response ((pSpec R deg).Message i) → R := fun ⟨i, q, r⟩ => by
      haveI : i = default := Unique.uniq (inferInstance) i
      subst this
      simp [pSpec, Message, getType, default] at r
      exact r
    letI accept := decide ((responses.dropLast.map f).sum = target)
    letI newTarget : R := by
      haveI newTarget := (List.getLastI responses).2.2
      haveI : responses.getLastI.fst = default := Unique.uniq (inferInstance) _
      rw [this] at newTarget
      simp [pSpec, Message, getType, default, instToOracleMessagePSpec,
        instToOraclePolynomialDegreeLE] at newTarget
      exact newTarget
    exact pure ⟨poly, newTarget, Fin.snoc challenges (chal default), earlyReject ∨ ¬ accept⟩

section Security

-- First state the polynomial-only theorems that establish completeness and soundness, then apply
-- them to the protocol

-- /-- Completeness theorem for sumcheck-/
-- theorem perfect_completeness : perfectCompleteness (protocol params) := by
--   unfold perfectCompleteness completeness relation runProtocol runProtocolAux evalDist
--   intro ⟨target⟩ ⟨poly⟩ valid
--   simp at valid; simp
--   sorry

-- /-- State function for round-by-round soundness -/
-- def stateFunction : @StateFunction (pSpec (R := R)) (relation R params) := sorry

-- What is the state function?
-- For empty transcript, outputs whether the relation holds
-- After message `p_i` from the prover, the state


-- /-- Round-by-round soundness theorem for sumcheck -/
-- theorem round_by_round_soundness : roundByRoundSoundness (verifier params) (badFunction params)
--     (fun _ => ⟨(1 : ℝ) / Fintype.card R, by simp; sorry⟩) := sorry

end Security

end Spec

end

end Sumcheck
