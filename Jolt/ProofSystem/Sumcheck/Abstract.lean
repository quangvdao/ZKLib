import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Equiv
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

#check MvPolynomial.commSemiring

#check MvPolynomial.C (1 : ℤ)

#check Polynomial.eval



/-- Evaluate the first variable of a multivariate polynomial -/
def boundFirstVar (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (r : R) : MvPolynomial (Fin n) R := ((finSuccEquiv R n).toFun p).eval (C r)

def testPoly : MvPolynomial (Fin 2) ℕ := X 0 * X 0

theorem eval_testPoly : boundFirstVar 1 testPoly 2 = 4 := by
  simp only [boundFirstVar, testPoly, finSuccEquiv_X_zero]
  -- conv in MvPolynomial.eval _ (C 2) => { unfold finnSuccEquiv }
  -- simp [finSuccEquiv_X_zero]

-- def boundFirstVar (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (r : R) : MvPolynomial (Fin n) R := rename (Fin.rev)(boundLastVar n (rename (Fin.rev) p) r)

-- def productDomain (n : ℕ) (D : Finset R) : Finset (Fin n → R) :=
--   @Fintype.piFinset (Fin n) _ _ (fun _ => R) (fun _ => D)

-- def sumOverDomain (n : ℕ) (p : MvPolynomial (Fin n) R) (D : Finset R) : R :=
--   Finset.sum (productDomain n D) (fun x => eval x p)

--

def boundTopVarSum (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (D : Finset R) : Polynomial R := sorry


end AbstractSumcheck

end
