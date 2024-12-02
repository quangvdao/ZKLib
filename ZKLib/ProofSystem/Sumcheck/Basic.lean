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
- `oSpec`: the set of underlying oracles (e.g. random oracles) that may be needed for other
  reductions. However, the sum-check protocol does _not_ use any oracles.

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
   prover is honest, then we have: `p_i(X) = ∑ x ∈ (univ.map D) ^ᶠ (n - i - 1), poly ⸨X ⦃i⦄,
   challenges, x⸩`.

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

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

noncomputable section

namespace Spec


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

instance : IsSingleRound (pSpec R deg) where
  prover_first' := by simp [pSpec, getDir]
  verifier_last' := by simp [pSpec, getDir, Neg.neg]

/-- Recognize that the (only) message from the prover to the verifier has type `R⦃≤ deg⦄[X]`, and
  hence can be turned into an oracle for evaluating the polynomial -/
instance instToOracleMessagePSpec : ToOracle ((pSpec R deg).Message default) := by
  simp only [pSpec, default, getDir_apply, getType_apply, Matrix.cons_val_zero]
  exact instToOraclePolynomialDegreeLE

/-- Recognize that the challenge from the verifier to the prover has type `R`, and hence can be
  sampled uniformly at random -/
instance instSampleableChallengePSpec : Sampleable ((pSpec R deg).Challenge default) := by
  simp only [pSpec, default, getDir_apply, getType_apply, Matrix.cons_val_one, Matrix.head_cons]
  infer_instance

@[reducible]
def proverState (i : Fin n) : ProverState 2 := ⟨fun _ => Statement R n deg i (by omega)⟩

/-- Prover input for the `i`-th round of the sum-check protocol, where `i < n` -/
def proverIn (i : Fin n) : ProverIn (Statement R n deg i (by omega)) Unit
    ((proverState R n deg i).PrvState 0) where
  input := fun stmt _ => stmt

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Prover interaction for the `i`-th round of the sum-check protocol, where `i < n`. This is only
  well-defined for `n > 0` -/
def proverRound (i : Fin n) (hn : n > 0) :
    ProverRound (pSpec R deg) oSpec (Statement R n deg i (by omega)) where
  PrvState := (proverState R n deg i).PrvState
  sendMessage := fun idx state => by
    have ⟨⟨poly, hp⟩, target, challenges, earlyReject⟩ := state
    haveI : idx = default := Unique.uniq _ idx
    simp [pSpec, Message, getType, this, default]
    generalize hn : n - 1 = n'
    haveI : n = n' + 1 := by omega
    simp_rw [this] at hp poly
    exact pure ⟨ ⟨∑ x ∈ (univ.map D) ^ᶠ (n' - i), poly ⸨X ⦃i⦄, challenges, x⸩, by
      refine Polynomial.mem_degreeLE.mpr ?_
      refine le_trans (Polynomial.degree_sum_le ((univ.map D) ^ᶠ (n' - i)) _) ?_
      simp only [Finset.sup_le_iff, Fintype.mem_piFinset, mem_map, mem_univ, true_and]
      intro x hx
      refine le_trans (Polynomial.degree_map_le _ _) ?_
      sorry
      ⟩, state ⟩
  receiveChallenge := fun _ state _ => state

/-- Since there is no witness, the prover's output for each round `i < n` of the sum-check protocol
  is trivial -/
def proverOut (i : Fin n) : ProverOut (Statement R n deg (i + 1) (by omega)) Unit
    ((proverState R n deg i).PrvState (Fin.last 2)) where
  output := fun state => ⟨sorry, ()⟩

#check Prover.mk

/-- The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only
  well-defined for `n > 0`, since when `n = 0` there is no protocol. -/
def prover (i : Fin n) (hn : n > 0) : Prover (pSpec R deg) oSpec
    (Statement R n deg i (by omega)) Unit (Statement R n deg (i + 1) (by omega)) Unit where
  toProverState := proverState R n deg i
  toProverIn := proverIn R n deg i
  sendMessage := (proverRound R n deg D oSpec i hn).sendMessage
  receiveChallenge := (proverRound R n deg D oSpec i hn).receiveChallenge
  toProverOut := proverOut R n deg i

/-- The default value for the tuple (message index, query, response) -/
instance : Inhabited ((i : MessageIndex (pSpec R deg)) × ToOracle.Query ((pSpec R deg).Message i)
    × ToOracle.Response ((pSpec R deg).Message i)) where
  default := ⟨default,
    by simpa (config := {autoUnfold := true}) [instToOracleMessagePSpec] using 0,
    by simpa (config := {autoUnfold := true}) [instToOracleMessagePSpec] using 0⟩

/-- The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n` -/
def verifier (i : Fin n) : Verifier (pSpec R deg) oSpec
    (Statement R n deg i (by omega)) (Statement R n deg (i + 1) (by omega)) where
  verify := fun ⟨poly, target, challenges, earlyReject⟩ transcript =>
    have ⟨p_i, _⟩ : R⦃≤ deg⦄[X] := transcript 0
    letI r_i : R := transcript 1
    letI accept := decide (∑ x ∈ (univ.map D), p_i.eval x = target)
    pure ⟨poly, p_i.eval r_i, Fin.snoc challenges r_i, earlyReject ∨ ¬ accept⟩

/-- The oracle verifier for the `i`-th round, where `i < n` -/
def oracleVerifier (i : Fin n) : OracleVerifier (pSpec R deg) oSpec
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
      haveI : i = default := Unique.uniq _ i
      subst this
      simpa (config := {autoUnfold := true}) using r
    letI accept := decide ((responses.dropLast.map f).sum = target)
    letI newTarget : R := by
      haveI newTarget := (List.getLastD responses default).2.2
      haveI : (responses.getLastD default).fst = default := Unique.uniq _ _
      rw [this] at newTarget
      simpa (config := {autoUnfold := true}) using newTarget
    exact pure ⟨poly, newTarget, Fin.snoc challenges (chal default), earlyReject ∨ ¬ accept⟩

/-- The sum-check reduction for the `i`-th round, where `i < n` and `n > 0` -/
def reduction (hn : n > 0) (i : Fin n) : Reduction (pSpec R deg) oSpec
    (Statement R n deg i (by omega)) Unit (Statement R n deg (i + 1) (by omega)) Unit :=
  .mk (prover R n deg D oSpec i hn) (verifier R n deg D oSpec i)

/-- The sum-check oracle reduction for the `i`-th round, where `i < n` and `n > 0` -/
def oracleReduction (hn : n > 0) (i : Fin n) : OracleReduction (pSpec R deg) oSpec
    (Statement R n deg i (by omega)) Unit (Statement R n deg (i + 1) (by omega)) Unit :=
  .mk (prover R n deg D oSpec i hn) (oracleVerifier R n deg D oSpec i)

section Security

open Reduction

variable {R : Type} [CommSemiring R] [Sampleable R] {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} {hn : n > 0} {i : Fin n}

@[simp]
theorem PMF.eq_pure_iff_ge_one {α : Type*} {p : PMF α} {a : α} : p = pure a ↔ p a ≥ 1 := by
  constructor <;> intro h
  · sorry
  · ext b
    simp only [pure, PMF.pure_apply]
    by_cases hb : b = a
    · simp [hb]; exact le_antisymm (PMF.coe_le_one p a) h
    · simp [hb]; sorry

omit [DecidableEq ι] in
/-- The oracle verifier does the same thing as the non-oracle verifier -/
theorem oracleVerifier_eq_verifier :
    (oracleVerifier R n deg D oSpec i).toVerifier = verifier R n deg D oSpec i := by
  simp only [OracleVerifier.toVerifier, getType_apply, getDir_apply, oracleVerifier,
    eq_mp_eq_cast, List.map_dropLast, decide_eq_true_eq, decide_not, ToOracle.oracle,
    Bool.decide_or, Bool.decide_eq_true, bind_pure_comp, verifier, sum_map,
    Verifier.mk.injEq, pSpec, instToOracleMessagePSpec]
  funext stmt transcript
  split; next x p_i hp_i hEq =>
  have : p_i = (transcript 0).1 := by simp only [hEq]
  subst this
  stop
  simp [default, Transcript.messages, Transcript.challenges, instToOraclePolynomialDegreeLE]
  constructor
  · rw [cast_eq_iff_heq, List.map_append _ _ _]
    simp only [Fin.isValue, List.map_cons, Matrix.cons_val_zero, cast_eq, List.map_nil,
      instToOracleMessageOfDefaultMessageIndex]
    rw [List.getLastD_concat _ _ _]
  · congr
    simp only [List.ofFn, Fin.foldr_eq_foldr_list, List.map_eq_foldr]
    congr
    clear * -
    induction m with
    | zero => simp only [Fin.list_zero, List.finRange_zero]
    | succ n ih => simp only [Fin.list_succ, ih, List.finRange_succ_eq_map]

set_option trace.profiler true

/-- Completeness theorem for sumcheck-/
theorem perfect_completeness : (reduction R n deg D oSpec hn i).perfectCompleteness
    (relation R n deg D i (by omega)) (relation R n deg D (i + 1) (by omega)) := by
  simp only [perfectCompleteness_eq, eq_iff_iff, iff_true, probEvent_eq_one_iff, Prod.forall]
  unfold relation reduction prover verifier Reduction.run
  intro ⟨⟨poly, hPoly⟩, target, challenges, earlyReject⟩ _ hValid
  simp only [eq_iff_iff, iff_true] at hValid
  obtain ⟨hReject, hSum⟩ := hValid
  intro transcript _ stmt _ hRun
  simp [Reduction.run, Prover.run] at hRun ⊢
  save
  sorry
  -- simp [Reduction.run]
  -- simp only [pSpec, getType_apply, getDir_apply, evalDist, eq_mp_eq_cast, reduction, prover,
  --   proverIn, proverRound, eq_mpr_eq_cast, proverOut, verifier, Matrix.cons_val_zero,
  --   sum_map, decide_eq_true_eq, Bool.decide_or, Bool.decide_eq_true, decide_not, challengeOracle,
  --   append, SubSpec.liftComp, simulate', simulate, Transcript.mk2, map_pure, bind_pure_comp,
  --   PMF.pure_bind, Function.comp_apply]
  -- simp only [map_eq_bind_pure_comp, bind, pure, PMF.bind_bind, PMF.pure_bind, Function.comp_apply,
  --   Function.uncurry_apply_pair, PMF.bind_apply, PMF.uniformOfFintype_apply, PMF.pure_apply,
  --   eq_iff_iff, eq_mp_eq_cast, mul_ite, mul_one, mul_zero, iff_true]
  -- by_cases hp : p = True
  -- · simp [hp, hReject]
  --   sorry
  -- · simp at hp
  --   simp [hp, hReject]
  --   intro r
  --   constructor
  --   · simp_rw [Polynomial.eval_finset_sum _ _ _, ← hSum]
  --     simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]
  --     sorry
  --   · simp_rw [Polynomial.eval_finset_sum _ _ _]
  --     sorry
  --   -- at this point we have reduced to a purely polynomial problem

#check evalDist_bind_eq_bind

/-- State function for round-by-round soundness -/
def stateFunction (i : Fin n) : StateFunction
    (relation R n deg D (i + 1) (by omega)).language (verifier R n deg D oSpec i) where
  fn := fun m stmt partialTranscript => match m with
    -- If `m = 0`, so the transcript is empty, returns whether the statement satisfies the relation
    | 0 => relation R n deg D i (by omega) stmt () = true
    -- If `m = 1`, so the transcript contains the new polynomial `p_i`, returns the above check,
    -- and also whether `p_i` is as expected
    | 1 => sorry
    -- If `m = 2`, so we get the full transcript, returns the above checks, and also whether the
    -- updated statement satisfies the new relation
    | 2 => sorry
    -- If `m = 3`, which is unconstrained, returns `False`
    | _ => sorry
  fn_empty := sorry
  fn_next := sorry
  fn_full := sorry

-- -- /-- Round-by-round soundness theorem for sumcheck -/
-- theorem rbr_soundness : Reduction.rbrSoundness (pSpec R deg) oSpec
--     (verifier R n deg D oSpec i) (relation R n deg D i (by omega))
--       (relation R n deg D (i + 1) (by omega)) (stateFunction i)
--         (fun _ => ⟨(deg : ℝ) / Fintype.card R, by
--           refine div_nonneg ?_ ?_ <;> simp only [Nat.cast_nonneg]⟩) := sorry

end Security

end Spec

end

end Sumcheck
