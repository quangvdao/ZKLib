import Mathlib.Data.Nat.Log


def padPowerOfTwo {R : Type} [Inhabited R] [CommSemiring R] (arr : Array R) : Array R × ℕ := Id.run do
let n : ℕ := Nat.clog 2 arr.size -- upper log base 2
let padArr : Array R := (Array.range (2 ^ n)).map (λ i => if i < arr.size then arr.get! i else 0)
(padArr, n)


def dotProduct {R : Type} [Inhabited R] [CommSemiring R] (x : Array R) (y : Array R) : R :=
  let products := Array.zip x y |>.map (λ (a, b) => a * b)
  products.foldl (λ acc elem => acc + elem) 0
