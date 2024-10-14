/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Basic

/-!
  # Notation for Multivariate Polynomials
    We define notation `R[X σ]` to be `MvPolynomial σ R`.

    For a Finset `s` and a natural number `n`, we also define `s ^ᶠ n` to be
    `Fintype.piFinset (fun (_ : Fin n) => s)`. This matches the intuition that `s ^ᶠ n`
    is the set of all tuples of length `n` with elements in `s`.
-/

noncomputable section
open MvPolynomial

set_option quotPrecheck false in
@[inherit_doc] scoped[MvPolynomial] notation:9000 R "[X " σ "]"  => MvPolynomial σ R

notation:20 set "^ᶠ" pow => Fintype.piFinset (fun (_ : Fin pow) => set)

end
