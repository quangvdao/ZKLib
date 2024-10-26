/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/


import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Batteries.Data.Array.Lemmas
import Batteries.Data.Vector.Lemmas

/-!
  # Multilinear Polynomials

  This file defines an efficient representation of multilinear polynomials, by their evaluations
  on the Boolean hypercube `{0,1}^n`.

  Our operations are designed to be as efficient as possible.
-/

open Batteries

-- TODO: Make this the definition (and use coefficient basis by default)
/-- `MlPoly n R` is the type of multilinear polynomials in `n` variables over a ring `R`. It is
  represented by its coefficients as a `Batteries.Vector` of length `2^n`, i.e. an `Array` of size
  `2^n`. We also do not put any algebraic structure on `R` to allow for more flexibility. -/
def MlPoly'' (n : ℕ) (R : Type*) := Vector R (2 ^ n)

-- We define multilinear polynomials over rings by their evaluation on the hypercube {0,1}^n (i.e.
-- the Lagrange basis).
structure MlPoly (R : Type*) (n : ℕ) where
  evals : Array R
  hSize : evals.size = 2 ^ n
deriving DecidableEq, Repr

-- Alternative definition with coefficients in the monomial basis
structure MlPoly' (R : Type*) (n : ℕ) where
  coeffs : Array R
  hSize : coeffs.size = 2 ^ n
deriving DecidableEq, Repr


-- variable {R : Type} [DecidableEq R] [Inhabited R] [Ring R]

section Math

variable {R : Type} [Mul R] [AddCommMonoid R]

/-- Inner product between two arrays. Do automatic truncation for arrays of different lengths. -/
def Array.dotProduct (a b : Array R) : R :=
  a.zip b |>.map (fun (a, b) => a * b) |>.foldl (· + ·) 0

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

variable [CommSemiring R] {n : ℕ}

instance inhabited : Inhabited (MlPoly R n) :=
  ⟨{ evals := Array.mkArray (2 ^ n) 0, hSize := by simp }⟩

-- Automatically pad to the next power of two
def new (evals : Array R) : MlPoly R (Nat.clog 2 evals.size) :=
  let n : ℕ := Nat.clog 2 evals.size -- upper log base 2
  let padEvals : Array R := (Array.range (2 ^ n)).map
    (fun i => if i < evals.size then evals.get! i else 0)
  { evals := padEvals, hSize := by simp [padEvals] }

-- Create a zero polynomial over n variables
def newZero (n : ℕ) : MlPoly R n :=
  { evals := Array.mkArray (2 ^ n) 0, hSize := by simp }


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


def add (p q : MlPoly R n) : MlPoly R n :=
  { evals := p.evals.zip q.evals |>.map (fun (a, b) => a + b),
    hSize := by simp [p.hSize, q.hSize, Array.size_zip] }


def scalarMul (r : R) (p : MlPoly R n) : MlPoly R n :=
  { evals := p.evals.map (fun a => r * a), hSize := by simp [p.hSize] }

-- Technically this is not the product of two multilinear polynomials, since the result of that
-- would no longer be multilinear. This is only defining the product of the evaluations.
def mul (p q : MlPoly R n) : MlPoly R n :=
  { evals := p.evals.zip q.evals |>.map (fun (a, b) => a * b),
    hSize := by simp [p.hSize, q.hSize, Array.size_zip] }


def eval (p : MlPoly R n) (x : Array R) (h : x.size = n) : R :=
  Array.dotProduct p.evals (lagrangeBasis x)

-- Partially evaluate the polynomial at some variables
-- def bound_top_vars (p : MlPoly R) (x : Array R) : MlPoly R :=

-- Theorems about evaluations

-- Evaluation at a point in the Boolean hypercube is equal to the corresponding evaluation in the
-- array
-- theorem eval_eq_eval_array (p : MlPoly R) (x : Array Bool) (h : x.size = p.nVars): eval p
-- x.map (fun b => b) = p.evals.get! (x.foldl (fun i elt => i * 2 + elt) 0) := by unfold eval unfold
-- dotProduct simp [↓reduceIte, h] sorry

end MlPoly
