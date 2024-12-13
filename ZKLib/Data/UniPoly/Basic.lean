/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import ZKLib.Data.Math.Operations

/-!
  # Univariate Polynomials with Efficient Operations

  Note: this file was originally taken from Bolton Bailey, but has been heavily modified to fit our
  needs.
-/

section Polynomial

/-- A type analogous to `Polynomial` that supports computable operations. This polynomial is
  represented internally as an Array of coefficients.

For example the Array `#[1,2,3]` represents the polynomial `1 + 2x + 3x^2`. Two arrays may represent
the same polynomial via zero-padding, for example `#[1,2,3] = #[1,2,3,0,0,0,...]`.
 -/
structure UniPoly (R : Type _) [Semiring R] where
  mk::
  coeffs : Array R
  -- h : coeffs last is non zero
deriving Inhabited, DecidableEq, Repr

namespace UniPoly

variable {R : Type _} [Semiring R]

/-- Another way to access `coeffs` -/
def toArray (p : UniPoly R) : Array R := p.coeffs

/-- The size of the underlying array. This may not correspond to the degree of the corresponding
  polynomial if the array has leading zeroes. -/
def size (p : UniPoly R) : Nat := p.coeffs.size

@[simp] theorem size_eq_size (p : UniPoly R) : p.size = p.coeffs.size := rfl

/-- The constant polynomial `C r`. -/
def C (r : R) : UniPoly R := ⟨#[r]⟩

/-- The variable `X`. -/
def X : UniPoly R := ⟨#[0, 1]⟩

section Operations

variable {S : Type*}

-- p(x) = a_0 + a_1 x + a_2 x^2 + ... + a_n x^n

-- eval₂ f x p = f(a_0) + f(a_1) x + f(a_2) x^2 + ... + f(a_n) x^n

/-- Evaluates a `UniPoly` at a given value, using a ring homomorphism `f: R →+* S`. -/
def eval₂ [Semiring S] (f : R →+* S) (x : S) (p : UniPoly R) : S :=
  p.coeffs.zipWithIndex.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluates a `UniPoly` at a given value. -/
def eval (x : R) (p : UniPoly R) : R :=
  p.eval₂ (RingHom.id R) x

/-- Addition of two `UniPoly`s. Defined as the pointwise sum of the underlying coefficient arrays
  (properly padded with zeroes). -/
def add (p q : UniPoly R) : UniPoly R :=
  let ⟨p', q'⟩ := Array.matchSize p.coeffs q.coeffs 0
  .mk (Array.zipWith p' q' (· + ·) )

/-- Scalar multiplication of `UniPoly` by an element of `R`. -/
def smul (r : R) (p : UniPoly R) : UniPoly R :=
  .mk (Array.map (fun a => r * a) p.coeffs)

/-- Scalar multiplication of `UniPoly` by a natural number. -/
def nsmul (n : ℕ) (p : UniPoly R) : UniPoly R :=
  .mk (Array.map (fun a => n * a) p.coeffs)

/-- Scalar multiplication of `UniPoly` by an integer. -/
def zsmul [Ring R] (z : ℤ) (p : UniPoly R) : UniPoly R :=
  .mk (Array.map (fun a => z * a) p.coeffs)

/-- Negation of a `UniPoly`. -/
def neg [Ring R] (p : UniPoly R) : UniPoly R := p.smul (-1)

/-- Subtraction of two `UniPoly`s. -/
def sub [Ring R] (p q : UniPoly R) : UniPoly R := p.add q.neg

/-- Multiplication of a `UniPoly` by `X ^ i`, i.e. pre-pending `i` zeroes to the
underlying array of coefficients. -/
def mulPowX (i : Nat) (p : UniPoly R) : UniPoly R := .mk (Array.replicate i 0 ++ p.coeffs)

/-- Multiplication of a `UniPoly` by `X`, reduces to `mulPowX 1`. -/
@[reducible] def mulX (p : UniPoly R) : UniPoly R := p.mulPowX 1

/-- Multiplication of two `UniPoly`s, using the naive `O(n^2)` algorithm. -/
def mul (p q : UniPoly R) : UniPoly R :=
  p.coeffs.zipWithIndex.foldl (fun acc ⟨a, i⟩ => acc.add <| (smul a q).mulPowX i) (C 0)

/-- Exponentiation of a `UniPoly` by a natural number `n` via repeated multiplication. -/
def pow (p : UniPoly R) (n : Nat) : UniPoly R := (mul p)^[n] (C 1)

-- TODO: define repeated squaring version of `pow`

instance : Zero (UniPoly R) := ⟨UniPoly.mk #[]⟩
instance : One (UniPoly R) := ⟨UniPoly.C 1⟩
instance : Add (UniPoly R) := ⟨UniPoly.add⟩
instance : SMul R (UniPoly R) := ⟨UniPoly.smul⟩
instance : SMul ℕ (UniPoly R) := ⟨UniPoly.nsmul⟩
instance [Ring R] : SMul ℤ (UniPoly R) := ⟨UniPoly.zsmul⟩
instance [Ring R] : Neg (UniPoly R) := ⟨UniPoly.neg⟩
instance [Ring R] : Sub (UniPoly R) := ⟨UniPoly.sub⟩
instance : Mul (UniPoly R) := ⟨UniPoly.mul⟩
instance : Pow (UniPoly R) Nat := ⟨UniPoly.pow⟩
instance : NatCast (UniPoly R) := ⟨fun n => UniPoly.C (n : R)⟩
instance [Ring R] : IntCast (UniPoly R) := ⟨fun n => UniPoly.C (n : R)⟩

/-- Convert a `UniPoly` to a `Polynomial`. -/
noncomputable def toPoly (p : UniPoly R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Return a bound on the degree of a `UniPoly` as the size of the underlying array
(and `⊥` if the array is empty). -/
def degreeBound (p : UniPoly R) : WithBot Nat :=
  match p.coeffs.size with
  | 0 => ⊥
  | .succ n => n

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound (p : UniPoly R) : Nat :=
  (degreeBound p).getD 0

/-- Remove leading zeroes from a `UniPoly`. Requires `BEq` to check if the coefficients are zero. -/
def trim [BEq R] (p : UniPoly R) : UniPoly R := ⟨p.coeffs.popWhile (fun a => a == 0)⟩

/-- Return the degree of a `UniPoly` as size of the underlying trimmed array. -/
def degree [BEq R] (p : UniPoly R) : Nat := p.trim.size

/-- Return the leading coefficient of a `UniPoly` as the last coefficient of the trimmed array,
or `0` if the trimmed array is empty. -/
def leadingCoeff [BEq R] (p : UniPoly R) : R := p.trim.coeffs.getLastD 0

/-- Check if a `UniPoly` is monic, i.e. its leading coefficient is 1. -/
def monic [BEq R] (p : UniPoly R) : Bool := p.leadingCoeff == 1

-- TODO: remove dependence on `BEq` for division and modulus

/-- Division and modulus of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def divModByMonicAux [BEq R] [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R × UniPoly R :=
  go (p.size - q.size) p q
where
  go : Nat → UniPoly R → UniPoly R → UniPoly R × UniPoly R
  | 0, p, _ => ⟨0, p⟩
  | n+1, p, q =>
      let k := p.coeffs.size - q.coeffs.size -- k should equal n, this is technically unneeded
      let q' := C p.leadingCoeff * (q * X.pow k)
      let p' := (p - q').trim
      let (e, f) := go n p' q
      -- p' = q * e + f
      -- Thus p = p' + q' = q * e + f + p.leadingCoeff * q * X^n
      -- = q * (e + p.leadingCoeff * X^n) + f
      ⟨e + C p.leadingCoeff * X^k, f⟩

/-- Division of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def divByMonic [BEq R] [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def modByMonic [BEq R] [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R :=
  (divModByMonicAux p q).2

/-- Division of two `UniPoly`s. -/
def div [BEq R] [Field R] (p q : UniPoly R) : UniPoly R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `UniPoly`s. -/
def mod [BEq R] [Field R] (p q : UniPoly R) : UniPoly R :=
  (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [BEq R] [Field R] : Div (UniPoly R) := ⟨UniPoly.div⟩
instance [BEq R] [Field R] : Mod (UniPoly R) := ⟨UniPoly.mod⟩

/-- Pseudo-division of a `UniPoly` by `X`, which shifts all non-constant coefficients
to the left by one. -/
def divX (p : UniPoly R) : UniPoly R := ⟨p.coeffs.extract 1 p.size⟩

theorem ext {p q : UniPoly R} (h : p.coeffs = q.coeffs) : p = q := by
  cases p; cases q; simp at h; rw [h]

@[simp] theorem zero_def : (0 : UniPoly R) = ⟨#[]⟩ := rfl

theorem add_comm {p q : UniPoly R} : p + q = q + p := by
  simp only [instHAdd, Add.add, add, List.zipWith_toArray, mk.injEq, Array.mk.injEq]
  exact List.zipWith_comm_of_comm _ (fun x y ↦ by change x + y = y + x; rw [_root_.add_comm]) _ _

private lemma zipWith_const {α β : Type _} {f : α → β → β} {l₁ : List α} {l₂ : List β}
  (h₁ : l₁.length = l₂.length) (h₂ : ∀ a b, f a b = b) : l₁.zipWith f l₂ = l₂ := by
  induction' l₁ with hd tl ih generalizing l₂ <;> rcases l₂ <;> aesop

@[simp] theorem zero_add {p : UniPoly R} : 0 + p = p := by
  simp [instHAdd, instAdd, add, List.matchSize]
  refine UniPoly.ext (Array.ext' ?_)
  simp only
  rw [List.zipWith_congr
        (g := fun _ x ↦ x)
        (h := by simp [List.forall₂_iff_get]
                 intros i h
                 change 0 + p.coeffs[i] = p.coeffs[i]
                 simp)]
  exact zipWith_const (by simp) (by simp)

@[simp] theorem add_assoc (p q r : UniPoly R) : p + q + r = p + (q + r) := by
  simp [instHAdd, instAdd, add, List.matchSize]
  -- refine Array.ext' ?_
  -- simp [Array.toList_zipWith]
  sorry

-- TODO: define `SemiRing` structure on `UniPoly`
-- instance : AddCommMonoid (UniPoly R) := {
--   add_assoc := fun p q r => by simp [instHAdd, instAdd, add]
--   zero_add := sorry
--   add_zero := sorry
--   add_comm := sorry
--   nsmul := sorry
-- }



end Operations


section Equiv

/-- An equivalence relation `equiv` on `UniPoly`s where `p ~ q` iff one is a
zero-padding of the other. -/
def equiv (p q : UniPoly R) : Prop :=
  match p.coeffs.matchSize q.coeffs 0 with
  | (p', q') => p' = q'

/-- Reflexivity of the equivalence relation. -/
@[simp] theorem equiv_refl (p : UniPoly R) : equiv p p :=
  by simp [equiv, List.matchSize]

/-- Symmetry of the equivalence relation. -/
@[simp] theorem equiv_symm {p q : UniPoly R} : equiv p q → equiv q p :=
  fun h => by simp [equiv] at *; exact Eq.symm h

open List in
/-- Transitivity of the equivalence relation. -/
@[simp] theorem equiv_trans {p q r : UniPoly R} : equiv p q → equiv q r → equiv p r :=
  fun hpq hqr => by
    simp_all [equiv, Array.matchSize]
    have hpq' := (List.matchSize_eq_iff_forall_eq p.coeffs.toList q.coeffs.toList 0).mp hpq
    have hqr' := (List.matchSize_eq_iff_forall_eq q.coeffs.toList r.coeffs.toList 0).mp hqr
    have hpr' : ∀ (i : Nat), p.coeffs.toList.getD i 0 = r.coeffs.toList.getD i 0 :=
      fun i => Eq.trans (hpq' i) (hqr' i)
    exact (List.matchSize_eq_iff_forall_eq p.coeffs.toList r.coeffs.toList 0).mpr hpr'

/-- The `UniPoly.equiv` is indeed an equivalence relation. -/
instance instEquivalenceEquiv : Equivalence (equiv (R := R)) where
  refl := equiv_refl
  symm := equiv_symm
  trans := equiv_trans

/-- The `Setoid` instance for `UniPoly R` induced by `UniPoly.equiv`. -/
instance instSetoidUniPoly: Setoid (UniPoly R) where
  r := equiv
  iseqv := instEquivalenceEquiv

/-- The quotient of `UniPoly R` by `UniPoly.equiv`. This will be shown to be equivalent to
  `Polynomial R`. -/
def QuotientUniPoly := Quotient (@instSetoidUniPoly R _)

-- TODO: show that operations on `UniPoly` descend to `QuotientUniPoly`



end Equiv

end UniPoly

-- unique polynomial of degree n that has nodes at ω^i for i = 0, 1, ..., n-1
def Lagrange.nodal' {F : Type} [Semiring F] (n : ℕ) (ω : F) : UniPoly F :=
  .mk (Array.range n |>.map (fun i => ω^i))

/--
This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1,
..., n-1.
-/
def Lagrange.interpolate' {F : Type} [Semiring F] (n : ℕ) (ω : F) (r : Fin n → F) : UniPoly F :=
  -- .mk (Array.finRange n |>.map (fun i => r i))
  sorry

section Tropical
/-- This section courtesy of Junyan Xu -/

instance : LinearOrderedAddCommMonoidWithTop (OrderDual (WithBot ℕ)) where
  __ : LinearOrderedAddCommMonoid (OrderDual (WithBot ℕ)) := inferInstance
  __ : Top (OrderDual (WithBot ℕ)) := inferInstance
  le_top _ := bot_le (α := WithBot ℕ)
  top_add' x := WithBot.bot_add x


noncomputable instance (R) [Semiring R] : Semiring (Polynomial R × Tropical (OrderDual (WithBot ℕ)))
  := inferInstance

noncomputable instance (R) [CommSemiring R] : CommSemiring
    (Polynomial R × Tropical (OrderDual (WithBot ℕ))) := inferInstance


def TropicallyBoundPoly (R) [Semiring R] : Subsemiring
    (Polynomial R × Tropical (OrderDual (WithBot ℕ))) where
  carrier := {p | p.1.degree ≤ OrderDual.ofDual p.2.untrop}
  mul_mem' {p q} hp hq := (p.1.degree_mul_le q.1).trans (add_le_add hp hq)
  one_mem' := Polynomial.degree_one_le
  add_mem' {p q} hp hq := (p.1.degree_add_le q.1).trans (max_le_max hp hq)
  zero_mem' := Polynomial.degree_zero.le


noncomputable def UniPoly.toTropicallyBoundPolynomial {R : Type} [Semiring R] (p : UniPoly R) :
    Polynomial R × Tropical (OrderDual (WithBot ℕ)) :=
  (UniPoly.toPoly p, Tropical.trop (OrderDual.toDual (UniPoly.degreeBound p)))

def degBound (b: WithBot ℕ) : ℕ := match b with
  | ⊥ => 0
  | some n => n + 1

def TropicallyBoundPolynomial.toUniPoly {R : Type} [Semiring R]
    (p : Polynomial R × Tropical (OrderDual (WithBot ℕ))) : UniPoly R :=
  match p with
  | (p, n) => UniPoly.mk (Array.range (degBound n.untrop) |>.map (fun i => p.coeff i))

noncomputable def Equiv.UniPoly.TropicallyBoundPolynomial {R : Type} [Semiring R] :
    UniPoly R ≃+* Polynomial R × Tropical (OrderDual (WithBot ℕ)) where
      toFun := UniPoly.toTropicallyBoundPolynomial
      invFun := TropicallyBoundPolynomial.toUniPoly
      left_inv := by sorry
      right_inv := by sorry
      map_mul' := by sorry
      map_add' := by sorry

end Tropical


end Polynomial
