-- import Mathlib.Algebra.Ring.Defs
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Algebra.Ring.InjSurj

import Jolt.Data.MathOperations

-- We define multilinear polynomials over rings by their evaluation on the hypercube {0,1}^n
-- We put the number of variables directly into the type for efficiency
structure MlPoly (R : Type) where
  evals : Array R
  nVars : ℕ

namespace MlPoly

variable {R : Type} [Inhabited R] [Ring R]

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
-- def lagrangeBasis (r : Array R) : Array R :=
--   let ell := r.size
--   -- Initialize the evals array with 1s
--   let mut evals : Array R := Array.mkArray (2 ^ ell) 1
--   let mut size := 1
--   for j in [0:ell] do
--     size := size * 2
--     for i in (List.range size).reverse in
--       if i % 2 == 1 then
--         let scalar := evals.get! (i / 2)
--         evals := evals.set! i (scalar * r[j])
--         evals := evals.set! (i - 1) (scalar - evals.get! i)
--   evals


-- Helper function to update the evals array
def updateEvals (evals : Array R) (r : Array R) (j : ℕ) (size : ℕ) : Array R :=
  (List.range size).reverse.foldl (fun evals i =>
    if i % 2 == 1 then
      let scalar : R := evals.get! (i / 2)
      evals.set! i (scalar * r[j]!)
      evals.set! (i - 1) (scalar - (scalar * r[j]))
    else
      evals
  ) evals

-- Generate the Lagrange basis for evaluation point r
def eqPoly (r : Array R) : Array R :=
  let ell := r.size
  let initialEvals := Array.mkArray (2 ^ ell) (1 : R)
  (List.range ell).foldl (fun (evals, size) j =>
    let newSize := size * 2
    (updateEvals evals r j newSize, newSize)
  ) (initialEvals, 1) |>.1


def add (p q : MlPoly R) [Inhabited R] [CommSemiring R] : MlPoly R :=
  if p.nVars ≠ q.nVars then
    panic! "Polynomials must have same number of variables"
  else
    { evals := p.evals.zip q.evals |>.map (λ (a, b) => a + b), nVars := p.nVars }


def scalarMul (r : R) (p : MlPoly R) : MlPoly R := { evals := p.evals.map (λ a => r * a), nVars := p.nVars }


def mul (p q : MlPoly R) [Inhabited R] [CommSemiring R] : MlPoly R :=
  if p.nVars ≠ q.nVars then
    panic! "Polynomials must have same number of variables"
  else
    { evals := p.evals.zip q.evals |>.map (λ (a, b) => a * b), nVars := p.nVars }


def eval (p : MlPoly R) (x : Array R) : R := sorry


-- def bound_top_vars (p : MlPoly R) (x : Array R) : MlPoly R :=



-- Convert to multivariate polynomial




-- def MultilinearPolynomial.C {R : Type} {n : ℕ} [CommSemiring R] (r : R) : MultilinearPolynomial R n := (Array.range (2 ^ n)).map (λ i => if i = 0 then r else 0)

-- def MultilinearPolynomial.X {R : Type} {n : ℕ} [CommSemiring R] (s : (Fin n)) : MultilinearPolynomial R n := ⟨ (List.range (2 ^ n)).map (λ i => if i = 2 ^ s.1 then 1 else 0) , by rw [List.length_map, List.length_range]⟩




end MlPoly
