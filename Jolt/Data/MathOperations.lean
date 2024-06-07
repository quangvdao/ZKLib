import Mathlib.Data.Nat.Log

def padPowerOfTwo {R : Type} [Inhabited R] [Ring R] (arr : Array R) : Array R × ℕ := Id.run do
let n : ℕ := Nat.clog 2 arr.size -- upper log base 2
let padArr : Array R := (Array.range (2 ^ n)).map (λ i => if i < arr.size then arr.get! i else 0)
(padArr, n)


def dotProduct {R : Type} [Inhabited R] [Ring R] (x : Array R) (y : Array R) : R :=
  let products := Array.zip x y |>.map (λ (a, b) => a * b)
  products.foldl (λ acc elem => acc + elem) 0


def walshHadamard {R : Type} [Inhabited R] [Ring R] (a : Array R) (n : ℕ) : Array R :=
  if a.size ≠ 2 ^ n then
    panic! "Array size must match number of variables"
  else
    let rec loop (a : Array R) (h : ℕ) : Array R :=
      if h = 0 then a
      else if h < 2 ^ n then
        let a := (List.range (2 ^ n)).foldl (fun a i =>
          if i &&& h == 0 then
            let u := a.get! i
            let v := a.get! (i + h)
            (a.set! i (u + v)).set! (i + h) (u - v)
          else
            a
        ) a
        loop a (h * 2)
      else
        a
    termination_by (2 ^ n - h)
    loop a 1

-- def {R : Type} [Singleton R] [Ring R] := {x : R // x = 1}

-- #eval walshHadamard (Array.mk {ℤ} [1, 2, 3, 4, 5, 6, 7, 8]) (3 : ℤ)
