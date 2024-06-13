import Mathlib.Data.MvPolynomial.Basic
import Jolt.Relation.Basic

/-!
# Sumcheck Relation

This file defines the relation for the sumcheck protocol. The relation is parametrized by:

  - a coefficient field $R$, which is a CommSemiring
  - the number of variables $n$
  - the degree of each variable $d_1, \dots, d_n$

The statement of the sumcheck protocol is a multivariate polynomial $p(x_1, \dots, x_n)$ over $R$, of degree $d_i$ in variable $x_i$ for each $i \in \{1, \dots, n\}$.

The witness of the sumcheck protocol is a value $T \in R$.

The sumcheck relation states that the following holds:
$$ \sum_{y \in \{0,1\}^n} p(y) = T. $$
-/

noncomputable section

open MvPolynomial BigOperators

open Relation

variable {R : Type _} [CommSemiring R]


-- def zero_one : Finset R := {0, 1}

def zero_one : Type := {r : R // r = 0 ∨ r = 1}

def hyperCube (n : ℕ) : Type := Fin n → @zero_one R _

def hCTwo : @hyperCube R _ 2 :=
  fun i => if i = 0 then ⟨0, Or.inl rfl⟩ else ⟨1, Or.inr rfl⟩

def sumOverSubset (n : ℕ) (p : MvPolynomial (Fin n) R) (H : Finset ((Fin n) → R)) : R :=
  Finset.sum H (fun x => eval x p)

-- def sumOverHyperCube (n : ℕ) (p : MvPolynomial (Fin n) R) : R :=
--   sumOverSubset n p (Finset (hyperCube n))

structure AbstractSumcheckInstance (R : Type) [CommSemiring R] where
  nVars : ℕ
  degs : Fin nVars → ℕ
  poly : MvPolynomial (Fin nVars) R
  domainPredicate : R → Prop
  target : R

-- instance AbstractSumcheckRelation [Inhabited R] [CommSemiring R] : Relation (R × (n : ℕ) × (Fin n → ℕ)) _ _ where
--   isValid := fun {pp stmt wit} => isValidBool stmt wit

namespace Sumcheck

end Sumcheck
