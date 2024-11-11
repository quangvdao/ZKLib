/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
  # Useful Notation
    We define notation `R[X σ]` to be `MvPolynomial σ R`.

    For a Finset `s` and a natural number `n`, we also define `s ^ᶠ n` to be
    `Fintype.piFinset (fun (_ : Fin n) => s)`. This matches the intuition that `s ^ᶠ n`
    is the set of all tuples of length `n` with elements in `s`.
-/

noncomputable section

-- TODO: Upstream these to `Mathlib.Algebra.MvPolynomial.Equiv`
namespace MvPolynomial

section Equiv

variable (R : Type*) [CommSemiring R] {n : ℕ}

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and polynomials over
  multivariable polynomials in `Fin n`, where the `i`-th variable is the indeterminate `X`.

  For `i = 0`, this is definitionally the same as `finSuccEquiv`. -/
def finSuccEquiv' (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv' i)).trans (optionEquivLeft R (Fin n))

/-- Equivalence between `MvPolynomial (Fin 1) R` and `Polynomial R` -/
def finOneEquiv : MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R :=
  (finSuccEquiv R 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv R (Fin 0)))

end Equiv

end MvPolynomial

end

open MvPolynomial

@[inherit_doc] scoped[Polynomial] notation:9000 R "⦃< " d "⦄[X]" => Polynomial.degreeLT R d
@[inherit_doc] scoped[Polynomial] notation:9000 R "⦃≤ " d "⦄[X]" => Polynomial.degreeLE R d

@[inherit_doc] scoped[MvPolynomial] notation:9000 R "[X " σ "]"  => MvPolynomial σ R
@[inherit_doc] scoped[MvPolynomial] notation:9000
  R "⦃≤ " d "⦄[X " σ "]"  => MvPolynomial.restrictDegree σ R d

-- `𝔽⦃≤ 1⦄[X Fin n]` is the set of multilinear polynomials in `n` variables over `𝔽`.

notation:70 s:70 " ^^ " t:71 => Fintype.piFinset fun (i : t) ↦ s i
notation:70 s:70 " ^ᶠ " t:71 => Fintype.piFinset fun (i : Fin t) ↦ s

/--
  Notation for multivariate polynomial evaluation. The expression `p ⸨x_1, ..., x_n⸩` is expanded to
  the evaluation of `p` at the concatenated vectors `x_1, ..., x_n`, with the casting handled by
  `omega`.

  For example, `p ⸨x, y, z⸩` is expanded to `MvPolynomial.eval (Fin.append (Fin.append x y) z ∘
  Fin.cast (by omega)) p`.
-/
syntax (name := mvEval) term "⸨" term,* "⸩" : term
macro_rules (kind := mvEval)
  | `($p⸨$x⸩) => `(MvPolynomial.eval $x $p)
  | `($p⸨$x, $y⸩) => `(MvPolynomial.eval (Fin.append $x $y ∘ Fin.cast (by omega)) $p)
  | `($p⸨$x, $y, $z⸩) =>
      `(MvPolynomial.eval (Fin.append (Fin.append $x $y) $z ∘ Fin.cast (by omega)) $p)

example : (X 0 + X 1 * X 2 : ℕ[X Fin 3]) ⸨![1, 2], ![8], ![]⸩ = 17 := by simp_arith

/--
  Notation for evaluating a multivariate polynomial with one variable left intact. The expression `p
  ⸨X ⦃i⦄, x_1, ..., x_n⸩` is expanded to the evaluation of `p`, viewed as a multivariate polynomial
  in all but the `i`-th variable, on the vector that is the concatenation of `x_1, ..., x_n`.
  Similar to `mvEval` syntax, casting between `Fin` types is handled by `omega`.

  For example, `p ⸨X ⦃i⦄, x, y⸩` is expanded to
    `Polynomial.map (MvPolynomial.eval (Fin.append x y ∘ Fin.cast (by omega)))`
    `(MvPolynomial.finSuccEquiv' i p)`.
-/
syntax (name := mvEvalToPolynomial) term "⸨X " "⦃" term "⦄" "," term,* "⸩" : term
macro_rules (kind := mvEvalToPolynomial)
  | `($p⸨X ⦃$i⦄, $x⸩) =>
      `(Polynomial.map (MvPolynomial.eval $x) (MvPolynomial.finSuccEquiv' _ $i $p))
  | `($p⸨X ⦃$i⦄, $x, $y⸩) =>
      `(Polynomial.map (MvPolynomial.eval (Fin.append $x $y ∘ Fin.cast (by omega)))
        (MvPolynomial.finSuccEquiv' _ $i $p))
  | `($p⸨X ⦃$i⦄, $x, $y, $z⸩) =>
      `(Polynomial.map (MvPolynomial.eval (Fin.append (Fin.append $x $y) $z ∘ Fin.cast (by omega)))
        (MvPolynomial.finSuccEquiv' _ $i $p))

-- State theorems here showing that the notation is correct
example {a b n : ℕ} (x : Fin a → ℕ) (y : Fin b → ℕ) (p : ℕ[X Fin n]) (h : a + b + 1 = n) :
  p ⸨x, ![n], y⸩ =
    MvPolynomial.eval (Fin.append (Fin.append x ![n]) y ∘ Fin.cast (by omega)) p := rfl

example {n : ℕ} (p : ℕ[X Fin (n + 1)]) (a : Fin n → ℕ) :
  p ⸨X ⦃0⦄, a⸩ = Polynomial.map (MvPolynomial.eval a) (MvPolynomial.finSuccEquiv' _ 0 p) := rfl
