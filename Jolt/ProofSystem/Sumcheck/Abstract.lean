import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Fin
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

def abstractSumcheckProver : Type _ := sorry
def abstractSumcheckVerifier : Type _ := sorry

/-- Evaluate the first variable of a multivariate polynomial -/
def boundFirstVar (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (r : R) : MvPolynomial (Fin n) R := (finSuccEquiv R n p).eval (C r)

-- def productDomain (n : ℕ) (D : Finset R) : Finset (Fin n → R) :=
--   @Fintype.piFinset (Fin n) _ _ (fun _ => R) (fun _ => D)

-- Equivalence that sends 0 to n and shift everything down by 1
def Fin.finSuccEquiv (n : ℕ) : Fin (n + 1) ≃ Sum (Fin n) (Fin 1) := by apply Equiv.symm (@finSumFinEquiv n 1)

#check sumAlgEquiv

-- Sum over all but the first variable
-- First convert p(X_0,...,X_n) to q(X)(X_0,...,X_{n-1})
def sumOverDomainPoly (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (D : Finset R) : Polynomial R :=
  let q := sumAlgEquiv R (Fin n) (Fin 1)
  sumOverDomain n (productDomain n D) q


-- Input: p(X_0, X_1, ..., X_{n+1}), subset D of R, value r
-- Output: q(X) := ∑ (b_0, b_1, ..., b_{n-1}) in D^n, p(r, X, b_0, ..., b_{n-1})
-- Why not? First bound the first variable, then do a sum over the last n variables
def boundTopVarSum (n : ℕ) (p : MvPolynomial (Fin (n + 2)) R) (D : Finset R) (r : R) : Polynomial R := sorry


end AbstractSumcheck

end
