-- import Jolt.InteractiveOracleProof.Basic
import Jolt.Relation.Sumcheck

/-!
# The Sumcheck Protocol, abstract version

We define the sumcheck protocol using Mathlib's types for polynomials, which are noncomputable. Other files will deal with implementations of the protocol, and we will prove that those implementations are instances of the abstract protocol (or maybe that their soundness can be derived from the soundness of this abstract protocol)
-/

noncomputable section

namespace AbstractSumcheck

open Polynomial
open MvPolynomial
open AbstractSumcheck

variable {R : Type _} [CommSemiring R]

-- structure SumcheckAbstract extends InteractiveOracleProofs := sorry

-- For now, even if we haven't figured out the full theory for IOPs, we can still define the sumcheck prover/verifier and state theorems about completeness and soundness

def ProverType : Type _ := sorry
def VerifierType : Type _ := sorry


def proverRound : Type _ := (index : IndexType) → StmtType index


/-- Evaluate the first variable of a multivariate polynomial -/
def boundFirstVar (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (r : R) : MvPolynomial (Fin n) R := (finSuccEquiv R n p).eval (C r)


-- Input: p(X_0, X_1, ..., X_{n+1}), subset D of R, value r
-- Output: q(X) := ∑ (b_0, b_1, ..., b_{n-1}) in D^n, p(r, X, b_0, ..., b_{n-1})
-- Why not? First bound the first variable, then do a sum over the last n variables
def boundTopVarSum (n : ℕ) (p : MvPolynomial (Fin (n + 2)) R) (D : Finset R) (r : R) : Polynomial R := sorry



def SamplingSet : Finset R


/- Completeness theorem for sumcheck-/
theorem completeness' : ∀ (chals : List R)


/- State function definition for round-by-round soundness -/
def stateFunction :




end AbstractSumcheck

end
