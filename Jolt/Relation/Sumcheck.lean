import Mathlib.Algebra.MvPolynomial.Equiv
-- import Mathlib.Data.Fintype.Basic
-- import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.BigOperators.RingEquiv
import Jolt.Relation.Basic
import Jolt.ToMathlib.MvPolynomial.Aux

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

## TODOs

Extend the relation to capture sumcheck over modules. This will allow instantiating e.g. the Bulletproofs protocol as an instance of sumcheck.

## References

[JACM:LFKN92]

[C:BooChiSot21]

-/

namespace AbstractSumcheck

noncomputable section

open MvPolynomial BigOperators

open Relation

variable {R : Type _} [CommSemiring R]

structure IndexType (R : Type _) [CommSemiring R] where
  nVars : ℕ
  degs : Fin nVars → ℕ
  domain : Finset R

structure StmtType (R : Type _) [CommSemiring R] (index : IndexType R) where
  poly : MvPolynomial (Fin index.nVars) R
  target : R

def WitType (R : Type _) [CommSemiring R] (_ : IndexType R) : Type := Empty

/-- The sumcheck relation -/
instance SumcheckRelation (R : Type _) [CommSemiring R] : Relation R where
  Index := IndexType R
  Stmt := StmtType R
  Wit := WitType R
  isValid := fun index stmt _ =>
    sumFinset index.nVars index.domain stmt.poly = stmt.target
        ∧ ∀ i : Fin index.nVars, stmt.poly.degreeOf i ≤ index.degs i

end

end AbstractSumcheck
