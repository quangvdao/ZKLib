/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.InteractiveOracleReduction.Basic
import ZKLib.Relation.Sumcheck

/-!
# The Sumcheck Protocol, abstract version

We define the sumcheck protocol using Mathlib's types for polynomials, which are noncomputable. Other files will deal with implementations of the protocol, and we will prove that those implementations are instances of the abstract protocol (or maybe that their soundness can be derived from the soundness of this abstract protocol)

-/

namespace Sumcheck

noncomputable section

namespace Abstract

open Polynomial MvPolynomial
open Sumcheck.Abstract


structure SamplingSet (R : Type _) where
  pred : R → Prop
  decPred : DecidablePred pred
  inhabited : Inhabited (Subtype pred)

variable {R : Type _} [CommSemiring R] [Fintype R] [Inhabited R]

/-- Evaluate the first variable of a multivariate polynomial -/
def evalFirstVar (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (r : R) : MvPolynomial (Fin n) R := (finSuccEquiv R n p).eval (C r)

variable (index : Index R) (samplingSet : SamplingSet R)

def spec : IOR.Spec where
  relIn := relation R index
  relOut := boolRel Empty
  numRounds := index.nVars
  Message := fun _ => Polynomial R -- verifier will do degree-check later
  Challenge := fun _ => Subtype samplingSet.pred
  sampleChallenge := fun _ => PMF.uniformOfFintype (Subtype samplingSet.pred)
  OQuery := fun _ => R
  OResponse := fun _ => R
  oracleFromMessage := fun _ poly point => poly.eval point

def proverRound : IOR.ProverRound (spec index samplingSet) where
  PrvState := fun i => MvPolynomial (Fin (index.nVars - i - 1)) R
  PrvRand := fun _ => PEmpty
  samplePrvRand := fun i => _
  -- This gets really annoying because Lean cannot automatically infer the type of `state`
  -- Consider not (ab)using dependent types
  prove := fun i stmt state _ ⟨chal, _⟩ => ⟨ sumFinsetExceptFirst state index.domain , evalFirstVar (index.nVars - i) state chal ⟩

def prover : IOR.Prover (spec index samplingSet) where
  toProverRound := proverRound index samplingSet
  fromWitnessIn := fun _ => _
  toWitnessOut := fun _ => _


def verifier : IOR.Verifier (spec index samplingSet) where
  verify := fun i state _ ⟨chal, _⟩ => sorry


def protocol : IOR.Protocol (spec index samplingSet) := IOR.mkProverProver (prover index samplingSet) verifier


/- Completeness theorem for sumcheck-/
theorem perfect_completeness : true := sorry




/- State function definition for round-by-round soundness -/




end Abstract

end

end Sumcheck
