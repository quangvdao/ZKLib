/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/


import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Log
import Batteries.Data.Array.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation

/-!
  # Multilinear Polynomials

  This file defines an efficient representation of multilinear polynomials, by their evaluations
  on the Boolean hypercube `{0,1}^n`.

  Our operations are designed to be as efficient as possible.
-/

-- We define multilinear polynomials over rings by their evaluation on the hypercube {0,1}^n (i.e.
-- the Lagrange basis).
structure MlPoly (R : Type) [CommSemiring R] where
  evals : Array R
  nVars : ℕ
  isValid : evals.size = 2 ^ nVars
deriving DecidableEq, Repr

-- variable {R : Type} [DecidableEq R] [Inhabited R] [Ring R]

section Math

variable {R : Type} [Mul R] [AddCommMonoid R]

/-- Inner product between two arrays. Do automatic truncation for arrays of different lengths. -/
def Array.dotProduct (a b : Array R) : R :=
  a.zip b |>.map (λ (a, b) => a * b) |>.foldl (· + ·) 0

def Array.dotProduct' (a b : Array R) (hEq : a.size = b.size) : R := Array.dotProduct a b



@[simp]
lemma Array.dotProduct_eq_matrix_dotProduct (a b : Array R) (h : a.size = b.size) :
    Array.dotProduct a b = Matrix.dotProduct a.get (h ▸ b.get) := sorry

end Math


namespace MlPoly

variable {R : Type} [DecidableEq R] [Inhabited R] [Ring R]

-- This function converts multilinear representation in the evaluation basis to the monomial basis
-- This is also called the Walsh-Hadamard transform (either that or the inverse)

def walshHadamardTransform (a : Array R) (n : ℕ) (h : ℕ) : Array R :=
  if h < n then
    let a := (Array.range (2 ^ n)).foldl (fun a i =>
      if i &&& (2 ^ h) == 0 then
        let u := a.get! i
        let v := a.get! (i + (2 ^ h))
        (a.set! i (u + v)).set! (i + (2 ^ h)) (v - u)
      else
        a
    ) a
    walshHadamardTransform a n (h + 1)
  else
    a

def evalToMonomial (a : Array R) : Array R := walshHadamardTransform a (Nat.clog 2 a.size) 0

def invWalshHadamardTransform (a : Array R) (n : ℕ) (h : ℕ) : Array R :=
  if h < n then
    let a := (Array.range (2 ^ n)).foldl (fun a i =>
      if i &&& (2 ^ h) == 0 then
        let u := a.get! i
        let v := a.get! (i + (2 ^ h))
        (a.set! i (u + v)).set! (i + (2 ^ h)) (v - u)
      else
        a
    ) a
    invWalshHadamardTransform a n (h + 1)
  else
    a

def monomialToEval (a : Array R) : Array R := invWalshHadamardTransform a (Nat.clog 2 a.size) 0

@[simp]
lemma evalToMonomial_size (a : Array R) : (evalToMonomial a).size = 2 ^ (Nat.clog 2 a.size) := by
  unfold evalToMonomial
  sorry


def unitArray {R : Type} [Inhabited R] [Ring R] (n k : ℕ) : Array R :=
  let initialArray : Array R := Array.mkArray n 0
  initialArray.set! k 1


instance inhabited : Inhabited (MlPoly R) :=
  ⟨{ evals := #[Inhabited.default], nVars := 0, isValid := by simp }⟩

-- maybe this can be done way better
-- instance : DecidableEq (MlPoly R) :=
--   fun p q =>
--     if hEvals : p.evals = q.evals then
--       if hNVars : p.nVars = q.nVars then
--         isTrue (by cases p; cases q; simp only at hEvals hNVars; rw [hEvals, hNVars])
--       else
--         isFalse (by intro h; cases h; contradiction)
--     else
--       isFalse (by intro h; cases h; contradiction)


-- Automatically pad to the next power of two
def new (evals : Array R) : MlPoly R :=
  let n : ℕ := Nat.clog 2 evals.size -- upper log base 2
  let padEvals : Array R := (Array.range (2 ^ n)).map
    (λ i => if i < evals.size then evals.get! i else 0)
  { evals := padEvals, nVars := n, isValid := by simp [padEvals] }


-- Create a zero polynomial over n variables
def newZero (n : ℕ) : MlPoly R :=
  { evals := Array.mkArray (2 ^ n) 0, nVars := n, isValid := by simp }


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


def add (p q : MlPoly R) (h : p.nVars = q.nVars) : MlPoly R :=
  { evals := p.evals.zip q.evals |>.map (λ (a, b) => a + b),
    nVars := p.nVars,
    isValid := by simp [h, p.isValid, q.isValid, Array.size_zip] }


def scalarMul (r : R) (p : MlPoly R) : MlPoly R :=
  { evals := p.evals.map (λ a => r * a), nVars := p.nVars, isValid := by simp [p.isValid] }

-- Technically this is not the product of two multilinear polynomials, since the result of that
-- would no longer be multilinear. This is only defining the product of the evaluations.
def mul (p q : MlPoly R) (h : p.nVars = q.nVars) : MlPoly R :=
  { evals := p.evals.zip q.evals |>.map (λ (a, b) => a * b),
    nVars := p.nVars,
    isValid := by simp [h, p.isValid, q.isValid, Array.size_zip] }


def eval (p : MlPoly R) (x : Array R) (h : x.size = p.nVars) : R :=
  Array.dotProduct p.evals (lagrangeBasis x)

-- Partially evaluate the polynomial at some variables
-- def bound_top_vars (p : MlPoly R) (x : Array R) : MlPoly R :=


-- Theorems about evaluations

-- Evaluation at a point in the Boolean hypercube is equal to the corresponding evaluation in the array
-- theorem eval_eq_eval_array (p : MlPoly R) (x : Array Bool) (h : x.size = p.nVars): eval p x.map (fun b => b) = p.evals.get! (x.foldl (fun i elt => i * 2 + elt) 0) := by
--   unfold eval
--   unfold dotProduct
--   simp [↓reduceIte, h]
--   sorry

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
-- def fromMlPoly (p : MlPoly R) : MlPoly' R :=
--   { coeffs := evalToMonomial p.evals, nVars := p.nVars }

end MlPoly'
