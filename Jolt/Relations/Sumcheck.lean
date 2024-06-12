import Mathlib.Data.MvPolynomial.Basic
import Jolt.Relations.Basic
import Mathlib.Data.Finset.Basic

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

open MvPolynomial

open Relation

variable {R : Type} [CommSemiring R]

def isBool (r : R) : Prop := r = 0 ∨ r = 1

-- def zero_one : Finset R := {0, 1}
def zero_one : Type := {r : R // isBool r}

def hyperCube (n : ℕ) : Type := Fin n → zero_one

-- def f : hyperCube {ℕ} 2 :=
--   fun i => if i = 0 then (0, or.inl rfl) else (1, or.inr rfl)

def sumHypercube (n : ℕ) (p : MvPolynomial (Fin n) R) : R :=
  ∑ (y in hyperCube n) p.eval y

structure AbstractSumcheckInstance (R : Type) [CommSemiring R] (n : ℕ) where
  d : Fin n → ℕ
  stmt : MvPolynomial (Fin n) R
  wit : R

-- instance AbstractSumcheckRelation [Inhabited R] [CommSemiring R] : Relation (R × (n : ℕ) × (Fin n → ℕ)) _ _ where
--   isValid := fun {pp stmt wit} => isValidBool stmt wit

namespace Sumcheck

end Sumcheck
