import Mathlib.Data.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

def fibonacci (n : ℕ) : ℕ :=
  let rec loop (n : ℕ) : ℕ × ℕ :=
    if n = 0 then (0, 1) else
      let (a, b) := loop (n - 1)
      (b, a + b)
  (loop n).snd

#eval timeit "fibonacci 30" (IO.println (fibonacci 1000))

def a := Array.range 20

def sumOfSquares (n : Nat) : Nat := ∑ i in Finset.range n, i * i

#eval timeit "sumOfSquares 20" (IO.println (sumOfSquares 1000))
