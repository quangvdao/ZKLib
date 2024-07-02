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
