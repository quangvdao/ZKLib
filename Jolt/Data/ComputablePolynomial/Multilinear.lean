-- import Mathlib.Algebra.Ring.Defs
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Algebra.Ring.InjSurj

import Jolt.Data.MathOperations
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Defs

-- We define multilinear polynomials over rings by their evaluation on the hypercube {0,1}^n (i.e. the Lagrange basis)
-- We put the number of variables directly into the type for efficiency
structure MlPoly (R : Type) [DecidableEq R] [Inhabited R] [Ring R] where
  evals : Array R
  nVars : ℕ

namespace MlPoly


variable {R : Type} [DecidableEq R] [Inhabited R] [Ring R]


instance inhabited : Inhabited (MlPoly R) := ⟨{ evals := #[Inhabited.default], nVars := 1 }⟩

-- maybe this can be done way better
instance : DecidableEq (MlPoly R) :=
  fun p q =>
    if hEvals : p.evals = q.evals then
      if hNVars : p.nVars = q.nVars then
        isTrue (by cases p; cases q; simp only at hEvals hNVars; rw [hEvals, hNVars])
      else
        isFalse (by intro h; cases h; contradiction)
    else
      isFalse (by intro h; cases h; contradiction)


-- Automatically pad to the next power of two
def new (evals : Array R) : MlPoly R :=
  let n : ℕ := Nat.clog 2 evals.size -- upper log base 2
  let padEvals : Array R := (Array.range (2 ^ n)).map (λ i => if i < evals.size then evals.get! i else 0)
  { evals := padEvals, nVars := n }


-- Create a zero polynomial over n variables
def newZero (n : ℕ) : MlPoly R :=
{ evals := Array.mkArray (2 ^ n) 0, nVars := n }


-- Check if the polynomial is valid
def isValid (p : MlPoly R) : Prop := p.evals.size = 2 ^ (Nat.log 2 p.nVars)


-- Generate the Lagrange basis for evaluation point r
-- First, a helper function
def lagrangeBasisAux (r : Array R) (evals : Array R) (ell : Nat) (j : Nat) (size : Nat) : Array R :=
  if j >= ell then
    evals
  else
    let size := size * 2
    let evals :=
      (Array.range size).reverse.foldl
        (fun evals i =>
          if i % 2 == 1 then
            let scalar := evals.get! (i / 2)
            let evals := evals.set! i (scalar * r.get! j)
            let evals := evals.set! (i - 1) (scalar - evals.get! i)
            evals
          else evals)
        evals
    lagrangeBasisAux r evals ell (j + 1) size
termination_by (ell - j)

def lagrangeBasis (r : Array R) : Array R :=
  let ell := r.size
  let evals := Array.mkArray (2 ^ ell) 1
  lagrangeBasisAux r evals ell 0 1


def add (p q : MlPoly R) : MlPoly R :=
  if p.nVars ≠ q.nVars then
    panic! "Polynomials must have same number of variables"
  else
    { evals := p.evals.zip q.evals |>.map (λ (a, b) => a + b), nVars := p.nVars }


def scalarMul (r : R) (p : MlPoly R) : MlPoly R := { evals := p.evals.map (λ a => r * a), nVars := p.nVars }

-- Technically this is not the product of two multilinear polynomials, since the result of that would no longer be multilinear. This is only defining the product of the evaluations.
def mul (p q : MlPoly R) : MlPoly R :=
  if p.nVars ≠ q.nVars then
    panic! "Polynomials must have same number of variables"
  else
    { evals := p.evals.zip q.evals |>.map (λ (a, b) => a * b), nVars := p.nVars }


def eval (p : MlPoly R) (x : Array R) : R :=
  if p.nVars ≠ x.size then
    panic! "Number of variables must match"
  else
  dotProduct p.evals (lagrangeBasis x)

-- Partially evaluate the polynomial at some variables
-- def bound_top_vars (p : MlPoly R) (x : Array R) : MlPoly R :=


-- Theorems about evaluations

-- Evaluation at a point in the Boolean hypercube is equal to the corresponding evaluation in the array
theorem eval_eq_eval_array (p : MlPoly R) (x : Array R) (h : x.size = p.nVars) (h' : isBoolean x): eval p x = p.evals.get! (toNum x) := by
  unfold eval
  unfold dotProduct
  simp [↓reduceIte, h]
  sorry

#eval eval (new (Array.mk [(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)])) (Array.mk [(1 : ℤ), (1 : ℤ)])

example (a b c : Prop) [Decidable a] (h : a) : (if a then b else c) = b := by
  simp_all only [↓reduceIte]

end MlPoly




-- Multilinear polynomials, now in the monomial basis
structure MlPoly' (R : Type) [Inhabited R] [Ring R] where
  coeffs : Array R
  nVars : ℕ

namespace MlPoly'

variable {R : Type} [DecidableEq R] [Inhabited R] [Ring R]

-- Convert to multilinear polynomial in the monomial basis
def fromMlPoly (p : MlPoly R) : MlPoly' R :=
  { coeffs := evalToMonomial p.evals, nVars := p.nVars }

end MlPoly'
