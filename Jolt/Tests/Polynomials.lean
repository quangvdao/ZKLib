import Mathlib.Data.Polynomial.Basic

def fibonacci (n : Nat) : Nat :=
  if n <= 1 then n else fibonacci (n - 1) + fibonacci (n - 2)

#eval timeit "fibonacci 30" (IO.println (fibonacci 30))

def a := Array.range 20
