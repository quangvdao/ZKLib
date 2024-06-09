import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic
import Jolt.Models.InteractiveOracleProof

/-!
# The Sumcheck Protocol, abstract version

We define the sumcheck protocol using Mathlib's types for polynomials, which are noncomputable. Other files will deal with implementations of the protocol, and we will prove that those implementations are instances of the abstract protocol (or maybe that their soundness can be derived from the soundness of this abstract protocol)
-/

open Polynomial
open MvPolynomial

structure SumcheckAbstract extends InteractiveOracleProofs :=
  (sumcheck : ∀ (p : MvPolynomial σ R) (h : p = 0), ∃ (q : MvPolynomial σ R), p.coeff 0 = q.coeff 0 ∧ ∀ (i : σ), p.coeff i = q.coeff i)
