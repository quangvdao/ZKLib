import Jolt.Data.MvPolynomial.PartialSum
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

## TODOs

Extend the relation to capture sumcheck over modules. This will allow instantiating e.g. the Bulletproofs protocol as an instance of sumcheck.

## References

[JACM:LFKN92]

[C:BooChiSot21]

-/

namespace Sumcheck

open Relation

noncomputable section

namespace Abstract

open MvPolynomial

variable (R : Type _) [CommSemiring R]

structure Index where
  nVars : ℕ+
  degrees : Fin nVars → ℕ
  domain : Finset R

structure Statement (index : Index R) where
  poly : MvPolynomial (Fin index.nVars) R
  target : R

def Witness (_ : Index R) : Type := Empty

def relation (index : Index R) : Relation where
  Statement := Statement R index
  Witness := Witness R index
  isValid := fun stmt _ =>
    sumFinsetAll index.nVars index.domain stmt.poly = stmt.target
      ∧ ∀ i : Fin index.nVars, stmt.poly.degreeOf i ≤ index.degrees i

/-- The sumcheck relation -/
def relationFamily : RelationFamily where
  Index := Index R
  Relation := relation R

end Abstract

end

end Sumcheck
