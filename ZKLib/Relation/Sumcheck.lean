/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.Data.MvPolynomial.Sumcheck
import ZKLib.Relation.Basic

/-!
# Sumcheck Relation

This file defines the relation for the sumcheck protocol. The relation is parametrized by:

  - a coefficient field $R$, which is a CommSemiring
  - the number of variables $n$
  - the degree of each variable $d_1, \dots, d_n$
  - the domain $D$ of the protocol, which is a finite subset of $R$.

The witness of the sumcheck protocol is a multivariate polynomial $p(x_1, \dots, x_n)$ over $R$, of degree $d_i$ in variable $x_i$ for each $i \in \{1, \dots, n\}$.

The statement of the sumcheck protocol is a value $T \in R$, supposed to be the sum of the polynomial over the domain $D^n$.

The sumcheck relation states that the following holds:
`∑ y in D ^ n, p(y) = T`.

## TODOs

Extend the relation to capture sumcheck over modules. This will allow instantiating e.g. the Bulletproofs protocol as an instance of sumcheck.

## References

[JACM:LFKN92]

[C:BooChiSot21]

-/

namespace Sumcheck

open Relation

noncomputable section

namespace Spec

open MvPolynomial

-- Move this to `ProofSystem/Sumcheck/Basic.lean` for now, so that I don't have to back and forth.

-- variable (R : Type _) [CommSemiring R]

-- structure Index where
--   n : ℕ+
--   degrees : Fin n → ℕ
--   domain : Finset R

-- structure Statement (index : Index R) where
--   poly : MvPolynomial (Fin index.n) R
--   target : R

-- -- structure Witness (index : Index R) where
--   -- hDeg : ∀ i, poly.degreeOf i ≤ index.degrees i

-- /-- The sumcheck relation -/
-- def relation (index : Index R) : Relation (Statement R index) Unit where
--   isValid := fun stmt _ =>
--     sumAll index.n index.domain stmt.poly = stmt.target
--       ∧ ∀ i : Fin index.n, stmt.poly.degreeOf i ≤ index.degrees i

-- -- TODO: define intermediate relations for each round `i` of sum-check
-- structure IntermediateStatement (index : Index R) (i : Fin index.n) where
--   poly : MvPolynomial (Fin (index.n - i)) R
--   target : R
--   messages : Fin i → Polynomial R
--   challenges : Fin i → R

end Spec

end

end Sumcheck
