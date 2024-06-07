-- import Mathlib.Algebra.Ring.Defs
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Algebra.Ring.InjSurj

import Jolt.Data.MathOperations
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.ZMod.Defs

-- We define multilinear polynomials over rings by their evaluation on the hypercube {0,1}^n (i.e. the Lagrange basis)
-- We put the number of variables directly into the type for efficiency
structure MlPoly (R : Type) [Inhabited R] [Ring R] where
  evals : Array R
  nVars : ℕ

namespace MlPoly


variable {R : Type} [Inhabited R] [Ring R]


instance inhabited : Inhabited (MlPoly R) := ⟨{ evals := #[Inhabited.default], nVars := 1 }⟩

-- maybe this can be done way better
instance [DecidableEq R] : DecidableEq (MlPoly R) :=
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
          if i % 2 == 0 then
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

#eval IO.println #[1,2]
#eval lagrangeBasis #[(3 : ℤ), (2 : ℤ)]


def add (p q : MlPoly R) : MlPoly R :=
  if p.nVars ≠ q.nVars then
    panic! "Polynomials must have same number of variables"
  else
    { evals := p.evals.zip q.evals |>.map (λ (a, b) => a + b), nVars := p.nVars }


def scalarMul (r : R) (p : MlPoly R) : MlPoly R := { evals := p.evals.map (λ a => r * a), nVars := p.nVars }


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

def p : MlPoly (ZMod 59) := new (Array.mk [1, 2])
def q : MlPoly (ZMod 59) := new (Array.mk [5, 6, 7, 8])

#eval eval p (Array.mk [3])
#eval eval q (Array.mk [1, 2])

#eval (1 * (1 - 3) + 2 * 3)

#eval (1 * (1 - 3) * (1 - 2) + 2 * 3 * (1 - 2) + 3 * (1 - 3) * 2 + 4 * 3 * 2)

end MlPoly




-- Multilinear polynomials, now in the monomial basis
structure MlPoly' (R : Type) [Inhabited R] [Ring R] where
  coeffs : Array R
  nVars : ℕ

namespace MlPoly'

variable {R : Type} [Inhabited R] [Ring R]

-- Convert to multilinear polynomial in the monomial basis
def fromMlPoly (p : MlPoly R) : MlPoly' R :=
  { coeffs := p.evals, nVars := p.nVars }

end MlPoly'
