/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.InteractiveOracleReduction.Basic
import ZKLib.Relation.Sumcheck

/-!
# The Sumcheck Protocol

We define the sumcheck protocol using Mathlib's types for polynomials, which are noncomputable. Other files will deal with implementations of the protocol, and we will prove that those implementations are instances of the abstract protocol (or maybe that their soundness can be derived from the soundness of this abstract protocol)

-/

namespace Sumcheck

noncomputable section

namespace Spec

open Polynomial MvPolynomial IOR OracleComp


structure SamplingSet (R : Type _) where
  pred : R → Prop
  decPred : DecidablePred pred
  inhabited : Inhabited (Subtype pred)

variable {R : Type _} [CommSemiring R] [DecidableEq R] [Inhabited R] [Fintype R] [SelectableType R]

/-- Evaluate the first variable of a multivariate polynomial -/
def evalFirstVar (n : ℕ+) (p : MvPolynomial (Fin n) R) (r : R) : MvPolynomial (Fin (n - 1)) R := by
  have p : MvPolynomial (Fin ((n : Nat) - 1 + 1)) R := by
    have : n - 1 + 1 = (n : ℕ) := @Nat.sub_add_cancel n.1 1 (n.2)
    exact this ▸ p
  exact (finSuccEquiv R (n - 1) p).eval (C r)

variable (index : Index R)

-- Let's try defining a single round as a reduction

def oracleizePolynomial : Oracleize 1 (fun _ => R[X]) where
  Query := fun _ => R
  Response := fun _ => R
  oracle := fun _ poly point => poly.eval point

instance : ValidOracleize (oracleizePolynomial (R := R)) where
  domain_decidableEq := inferInstance
  range_decidableEq := inferInstance
  range_inhabited := fun _ => by simpa [oracleizePolynomial]
  range_fintype := fun _ => by simpa [oracleizePolynomial]

instance instValidChallenge : ValidChallenge (fun (_ : Fin 1) => R) where
  fintype := inferInstance
  decidableEq := inferInstance
  inhabited := inferInstance
  selectable := inferInstance

def pSpec : ProtocolSpec where
  numRounds := 1
  Message := fun _ => R[X]
  Challenge := fun _ => R
  Oracle := oracleizePolynomial
  validChallenge := instValidChallenge
  validOracle := inferInstance

/-- Honest sum-check prover -/
def prover : Prover (pSpec (R := R)) emptySpec (relation R index) where

  PrvState := fun i => MvPolynomial (Fin (index.nVars - i)) R
  -- { x : MvPolynomial (Fin (index.nVars - i)) R // ∀ j, x.degreeOf j ≤ index.degrees (Fin.castAdd i j) }

  prove := fun i _ state chal => by
    -- Since there is only one round, we can rewrite `i = 0`
    have : i = 0 := by aesop
    subst this; simp_all;
    -- Compute the new state
    let newState := evalFirstVar index.nVars state chal
    -- Compute the message
    let message := sumExceptFirst' index.nVars index.domain state
    exact pure ⟨ message, newState ⟩
  fromWitnessIn := fun wit => wit.poly
  -- toWitnessOut := fun newState => { poly := newState }

def verifier : Verifier (pSpec (R := R)) emptySpec (relation R index) where
  verify := fun stmt chal => do
    let isValid : Bool := sorry
    return isValid

def protocol : Protocol (pSpec (R := R)) emptySpec (relation R index) := Protocol.mk (prover index) (verifier index)

-- def pSpec : ProtocolSpec where
--   numRounds := index.nVars
--   Message := fun _ => Polynomial R -- verifier will do degree-check later
--   Challenge := fun _ => Subtype samplingSet.pred
--   sampleChallenge := fun _ => PMF.uniformOfFintype (Subtype samplingSet.pred)
--   OQuery := fun _ => R
--   OResponse := fun _ => R
--   oracleFromMessage := fun _ poly point => poly.eval point


-- def prover : Prover (pSpec (R := R)) emptySpec relIn where
--   PrvState := fun i => MvPolynomial (Fin (index.nVars - i)) R
--   prove := fun i stmt state chal => do
--     have state : MvPolynomial (Fin (index.nVars - i)) R := by
--       simpa only [Fin.coe_fin_one, tsub_zero, Nat.cast_zero, Fin.val_zero] using state
--     let newState := evalFirstVar (index.nVars - i - 1) state chal
--     have newState : prover.PrvState (i + 1) := by simp_all
--     return ⟨ sumFinsetExceptFirst _ index.domain state, newState ⟩
--   fromWitnessIn := fun _ => _


/-- Completeness theorem for sumcheck-/
theorem perfect_completeness : perfectCompleteness (protocol index) := by
  unfold perfectCompleteness completeness relation runProtocol runProtocolAux evalDist
  intro ⟨target⟩ ⟨poly⟩ valid
  simp at valid; simp
  sorry

/-- Bad function for round-by-round soundness -/
def badFunction : @BadFunction (pSpec (R := R)) (relation R index) := sorry

/-- Round-by-round soundness theorem for sumcheck -/
theorem round_by_round_soundness : roundByRoundSoundness (verifier index) (badFunction index) (fun _ => ⟨(1 : ℝ) / Fintype.card R, by simp; sorry⟩) := sorry



end Spec

end

end Sumcheck
