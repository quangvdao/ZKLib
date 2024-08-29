/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Basic

/-!
  # Notation for Multivariate Polynomials
    We define notation `R[X σ]` to be `MvPolynomial R σ`.
-/

noncomputable section
open MvPolynomial

set_option quotPrecheck false in
@[inherit_doc] scoped[MvPolynomial] notation:9000 R "[X " σ "]"  => MvPolynomial R σ

end