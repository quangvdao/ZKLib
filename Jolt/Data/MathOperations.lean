import Mathlib.Data.Nat.Log

def isBoolean {R : Type} [Zero R] [One R] (x : Array R) : Prop := ∀ i, (h : i < x.size) → x[i] = 0 ∨ x[i] = 1

def toNum {R : Type} [Zero R] [One R] [DecidableEq R] (x : Array R) : ℕ :=
  (Array.map (λ r => if r = 0 then 0 else 1) x).reverse.foldl (λ acc elem => (acc * 2) + elem) 0


def padPowerOfTwo {α : Type} [Inhabited α] (arr : Array α) : Array α × ℕ :=
  let n := Nat.clog 2 arr.size -- upper log base 2
  let padArr := (Array.range (2 ^ n)).map (λ i => dite (i < arr.size) (λ h => arr[i]'h) (λ _ => default))
  (padArr, n)
