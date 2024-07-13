import Jolt.InteractiveOracleReduction.Basic
import Jolt.Relation.Sumcheck

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
  nonempty : Nonempty (Subtype pred)

attribute [instance] SamplingSet.decPred SamplingSet.nonempty

variable {R : Type _} [CommSemiring R] [Fintype R] [Nonempty R]

/-- Evaluate the first variable of a multivariate polynomial -/
def boundFirstVar (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (r : R) : MvPolynomial (Fin n) R := (finSuccEquiv R n p).eval (C r)


def spec (index : Index R) (samplingSet : SamplingSet R) : IOR.Spec where
  relIn := relation R index
  relOut := boolRel Empty
  numRounds := index.nVars
  Message := fun _ => Polynomial R -- verifier will do degree-check later
  Challenge := fun _ => Subtype samplingSet.pred
  sampleChallenge := fun _ => PMF.uniformOfFintype (Subtype samplingSet.pred)
  OQuery := fun _ => R
  OResponse := fun _ => R
  oracleFromMessage := fun _ poly point => poly.eval point

def proverRound (index : Index R) (sSet : SamplingSet R) : IOR.ProverRound (spec index sSet) where
  PrvState := fun i => MvPolynomial (Fin (index.nVars - i - 1)) R
  PrvRand := fun _ => PEmpty
  samplePrvRand := fun i => _
  -- This gets really annoying because Lean cannot automatically infer the type of `state`
  -- Consider not (ab)using dependent types
  prove := fun i stmt state _ ⟨chal, _⟩ => ⟨ sumFinsetExceptFirst state index.domain , boundFirstVar (index.nVars - i) state chal ⟩

def prover (index : Index R) (sSet : SamplingSet R) : IOR.Prover (spec index sSet) where
  toProverRound := proverRound index sSet
  fromWitnessIn := fun _ => _
  toWitnessOut := fun _ => _




/- Completeness theorem for sumcheck-/
theorem completeness' : true := sorry




/- State function definition for round-by-round soundness -/




end Abstract

end

end Sumcheck
