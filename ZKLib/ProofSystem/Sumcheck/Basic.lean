/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Basic
import ZKLib.ProofSystem.Relation.Sumcheck

/-!
# The Sum-check Protocol

We define the sum-check protocol as a series of Interactive Oracle Reductions (IORs), where the
underlying polynomials are represented using Mathlib's noncomputable types `Polynomial` and
`MvPolynomial`.

Other files will deal with implementations of the protocol, and we will prove that those
implementations derive security from that of the abstract protocol.

We split the sum-check protocol into the following stages:

0. Before the protocol starts, we assume that the prover has already sent the multivariate
   polynomial `P`, so that it can be in the statement of the relation.

1. For round `0`, the verifier sends nothing, and the prover sends the univariate polynomial `p_0`
   for the first sum-check round.

The verifier checks that `p_0` satisfies `∑ x in domain, p_0.eval x = T`, where `T` is the target
value of sum-check.

2. For round `i = 1` to `n - 1`, the verifier sends a challenge `r_{i-1} : R`, and the prover sends
   back the univariate polynomial `p_i` for that round.

The verifier then checks that `p_i` satisfies `∑ x in domain, p_i.eval x = p_{i - 1}.eval r_{i-1}`,
where `p_{i-1}` is the polynomial from the previous round (added to the current round's statement).

3. In the last round `i = n`, the verifier sends a challenge `r_n : R`, and the prover does not send
   anything.

The verifier checks that `p_{n-1}` satisfies `∑ x in domain, p_{n-1}.eval x = P.eval (fun i => r_i)`

Note that to represent sum-check as a series of IORs, we will need to implicitly constrain the
degree of the polynomials via using subtypes, such as `Polynomial.degreeLE` and
`MvPolynomial.degreeOf`. This is because the oracle verifier only gets oracle access to evaluating
the polynomials, but does not see the polynomials in the clear. When this is compiled to an
interactive proof, the corresponding polynomial commitment schemes will enforce that the declared
degree bound holds, via letting the (non-oracle) verifier perform explicit degree checks.

-/

namespace Sumcheck

noncomputable section
namespace Spec

open Polynomial MvPolynomial OracleComp

-- For now, we assume uniform sampling from `R`
-- structure SamplingSet (R : Type _) where
--   pred : R → Prop
--   decPred : DecidablePred pred
--   inhabited : Inhabited (Subtype pred)


/-- Public parameters for the sum-check protocol with `n` rounds -/
structure Params (R : Type) (n : ℕ) where
  degrees : Fin n → ℕ
  -- Possible generalization in the future: `domain : Fin n → Finset R`
  domain : Finset R

variable {R : Type} [CommSemiring R] [Sampleable R] {n : ℕ} (params : Params R n)

/-- Initial statement for sum-check -/
structure Statement where
  -- The multivariate polynomial for sum-check
  poly : MvPolynomial (Fin n) R
  -- The target value for sum-check
  target : R
  -- The degree bound for the polynomial (will put in the `poly` field directly as a subtype)
  hPoly : ∀ j : Fin n, poly.degreeOf j ≤ params.degrees j

/-- Statement for the `i`-th round of sum-check -/
structure StatementRound (i : Fin n) where
  -- The multivariate polynomial for sum-check
  poly : MvPolynomial (Fin n) R
  -- The degree bound for the polynomial (will put in the `poly` field directly as a subtype)
  hPoly : ∀ j : Fin n, poly.degreeOf j ≤ params.degrees j
  -- The target value for sum-check in each round
  target : R
  -- The message polynomial from the previous round
  lastMessage : R[X]
  -- The challenges sent from the verifier to the prover from previous rounds
  challenges : Fin i → R

/-- The overall sum-check relation -/
instance relation : Relation (Statement params) Unit where
  isValid := fun stmt _ =>
    sumAll n (fun _ => params.domain) stmt.poly = stmt.target
      ∧ ∀ j : Fin n, stmt.poly.degreeOf j ≤ params.degrees j

/-- The sum-check relation for the `i`-th round -/
instance relationRound (i : Fin n) :
    Relation (StatementRound params i) Unit where
  isValid := fun stmt _ =>
    ∑ x ∈ params.domain, stmt.lastMessage.eval x = stmt.target
      ∧ ∀ j : Fin n, stmt.poly.degreeOf j ≤ params.degrees j

variable (params : Params R n)

-- Let's try defining a single round as a reduction

def polynomialOracle : ToOracle R[X] where
  Query := R
  Response := R
  respond := fun poly point => poly.eval point

/-- Protocol spec for the first round, where the verifier sends no message,
and the prover sends the polynomial `p_0` -/
def pSpecFirst : ProtocolSpec 1 where
  Challenge := fun _ => Empty
  Message := fun _ => R[X]

/-- Protocol spec for the intermediate rounds, where the verifier sends a challenge `r_{i-1}`,
and the prover sends back the polynomial `p_i` -/
def pSpecMiddle : ProtocolSpec 1 where
  Challenge := fun _ => R
  Message := fun _ => R[X]

/-- Protocol spec for the last round, where the verifier sends a challenge `r_{n-1}`,
and the prover does not send anything -/
def pSpecLast : ProtocolSpec 1 where
  Challenge := fun _ => R
  Message := fun _ => Unit

/- Note:
1. If `n = 0`, then there is no round.
2. If `n = 1`, then we only have the last round.
3. If `n = 2`, then we have the first and last round.
4. If `n ≥ 3`, then we have all rounds (including middle rounds).
-/

-- def pSpec (n : ℕ) : ProtocolSpec n
  -- | 0 => isEmptyElim
  -- | 1 => pSpecLast R
  -- | n + 2 => pSpecFirst R ++ₚ (n ×ₚ pSpecMiddle R) ++ₚ pSpecLast R

/-- Type signature for the sum-check prover's state -/
@[ext]
structure PrvState (params : Params R n) where
  poly : MvPolynomial (Fin n) R
  -- { x : MvPolynomial (Fin (n - i)) R // ∀ j, x.degreeOf j ≤ params.degrees (Fin.castAdd i j) }
  chals : List R

/-- Initialization of the sum-check prover -/
def proverInit : ProverInit pSpecFirst emptySpec (PrvState params) (Statement params) Unit where
  load := fun stmt _ => do return { poly := stmt.poly, chals := [] }

/-- Honest sum-check prover for the first round -/
def proverFirst (h : n > 0) : ProverRound (pSpecFirst R) emptySpec (PrvState R (n := n)) where
  prove := fun 0 _ state => by
    -- Compute the message
    letI message := sumExceptFirst' n h (fun _ => params.domain) state.poly
    exact pure ⟨ message, state ⟩

/-- Honest sum-check verifier for the first round -/
def verifierFirst : Verifier (pSpecFirst R) emptySpec (Statement R params) where
  verify := fun stmt transcript => do
    -- Compute the sum of the message polynomial evaluated over the domain
    letI sum := ∑ x in params.domain, (transcript.messages 0).eval x
    -- Return the `Bool` value of deciding whether `sum = stmt.target`
    return decide (sum = stmt.target)

/-- Honest sum-check prover for the intermediate round `i` -/
def proverMiddle (i : ℕ) : ProverRound (pSpecMiddle R) emptySpec (PrvState R (n := n)) where
  prove := fun 0 chal state => by
    -- Compute the message for this round
    letI message := sumExceptFirst' n (by sorry) (fun _ => params.domain) state.poly
    -- Compute the target for this round
    -- Update the state
    exact pure ⟨ message, state ⟩

/-- Honest sum-check verifier for the intermediate round `i` -/
def verifierMiddle : Verifier (pSpecMiddle R) emptySpec (Statement R params) where
  verify := fun stmt transcript => do
    -- Compute the sum over the domain
    letI sum := ∑ x in params.domain, (transcript.messages 0).eval x
    -- Return the `Bool` value of deciding whether `sum = stmt.target`
    return decide (sum = stmt.target)

/-- Honest sum-check prover for the last round -/
def proverLast : ProverRound (pSpecLast R) emptySpec (PrvState R (n := n)) where
  prove := fun 0 _ state => by
    simp [pSpecLast]
    exact pure ⟨ (), state ⟩

/-- Honest sum-check verifier for the last round -/
def verifierLast (h : n > 0) : Verifier (pSpecLast R) emptySpec
    (StatementRound R params ⟨n - 1, by omega⟩) where
  verify := fun stmt transcript => do
    -- Compute the evaluation of the multivariate polynomial
    -- at the challenges sent by the verifier
    have priorChallenges : Fin (n - 1) → R := stmt.challenges
    have finalChallenge : R := transcript.challenges 0
    letI evalPoint : Fin n → R := by
      have : n - 1 + 1 = n := by omega
      exact this ▸ Fin.snoc priorChallenges finalChallenge
    letI eval := MvPolynomial.eval evalPoint stmt.poly
    return decide (eval = stmt.target)

/-
2. For round `i = 1` to `n - 1`, the verifier sends a challenge `r_{i-1} : R`, and the prover sends back the univariate polynomial `p_i` for that round.

The verifier then checks that `p_i` satisfies `∑ x in domain, p_i.eval x = p_{i - 1}.eval r_{i-1}`, where `p_{i-1}` is the polynomial from the previous round (added to the current round's statement).

3. In the last round `i = n`, the verifier sends a challenge `r_n : R`, and the prover does not send anything.

The verifier checks that `p_{n-1}` satisfies `∑ x in domain, p_{n-1}.eval x = P.eval (fun i => r_i)`.
-/



def protocolFirst (h : n > 1) : Protocol (pSpecFirst R) emptySpec (PrvState R (n := n)) (Statement R params) Unit :=
  Protocol.mk (Prover.mk (proverFirst R params (by omega)) (proverInit R params)) (verifierFirst R params)

-- def protocolMiddle (h : n > 1) : Protocol (pSpecMiddle R) emptySpec (PrvState R (n := n)) (Statement R params) Unit :=
--   Protocol.mk (proverMiddle R params) (verifierMiddle R params)

-- def protocolLast (h : n > 0) : Protocol (pSpecLast R) emptySpec (PrvState R (n := n)) (Statement R params) Unit :=
--   Protocol.mk (proverLast R params) (verifierLast R params)

section Security

-- First state the polynomial-only theorems that establish completeness and soundness, then apply
-- them to the protocol

-- /-- Completeness theorem for sumcheck-/
-- theorem perfect_completeness : perfectCompleteness (protocol params) := by
--   unfold perfectCompleteness completeness relation runProtocol runProtocolAux evalDist
--   intro ⟨target⟩ ⟨poly⟩ valid
--   simp at valid; simp
--   sorry

-- /-- Bad function for round-by-round soundness -/
-- def badFunction : @BadFunction (pSpec (R := R)) (relation R params) := sorry

-- /-- Round-by-round soundness theorem for sumcheck -/
-- theorem round_by_round_soundness : roundByRoundSoundness (verifier params) (badFunction params)
--     (fun _ => ⟨(1 : ℝ) / Fintype.card R, by simp; sorry⟩) := sorry

end Security

end Spec

end

end Sumcheck
