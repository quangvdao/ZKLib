import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.Basic
import Mathlib.Data.Bitvec.Defs



def isBoolean {R : Type} [DecidableEq R] [Inhabited R] [Ring R] (x : Array R) : Bool := ∀ i, i < x.size → x.get! i = 0 ∨ x.get! i = 1

#eval isBoolean #[(1 : ℤ )]

def toNum {R : Type} [DecidableEq R] [Inhabited R] [Ring R] (x : Array R) : ℕ :=
  (Array.map (λ r => if r = 0 then 0 else 1) x).foldl (λ acc elem => (acc * 2) + elem) 0



def padPowerOfTwo {R : Type} [Inhabited R] [Ring R] (arr : Array R) : Array R × ℕ := Id.run do
let n : ℕ := Nat.clog 2 arr.size -- upper log base 2
let padArr : Array R := (Array.range (2 ^ n)).map (λ i => if i < arr.size then arr.get! i else 0)
(padArr, n)


def dotProduct {R : Type} [Inhabited R] [Ring R] (x : Array R) (y : Array R) : R :=
  let products := Array.zip x y |>.map (λ (a, b) => a * b)
  products.foldl (λ acc elem => acc + elem) 0

lemma func_product_comm {R : Type} [Inhabited R] [CommRing R] : (λ (a : R) (b : R) => a * b) = (λ (a : R) (b : R) => b * a) := by
  funext a b
  apply mul_comm a b

theorem dotProduct_comm {R : Type} [Inhabited R] [CommRing R] (x : Array R) (y : Array R) : dotProduct x y = dotProduct y x := by
  unfold dotProduct
  sorry

-- This function converts multilinear representation in the evaluation basis to the monomial basis
-- This is also called the Walsh-Hadamard transform (either that or the inverse)
def evalToMonomial {R : Type} [Inhabited R] [Ring R] (a : Array R) : Array R :=
  let n := Nat.clog 2 a.size
  if a.size ≠ 2 ^ n then
    panic! "Array size is not a power of two!"
  else
    let rec loop (a : Array R) (h : ℕ) : Array R :=
      if h = 0 then a
      else if h < 2 ^ n then
        let a := (List.range (2 ^ n)).foldl (fun a i =>
          if i &&& h == 0 then
            let u := a.get! i
            let v := a.get! (i + h)
            (a.set! i (u + v)).set! (i + h) (v - u)
          else
            a
        ) a
        loop a (h * 2)
      else
        a
  termination_by (2 ^ n - h)
  loop a 1

def monomialToEval {R : Type} [Inhabited R] [CommSemiring R] [HSub R R R] (a : Array R) (n : ℕ) : Array R :=
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
            (a.set! i (u + v)).set! (i + h) (v - u)
          else
            a
        ) a
        loop a (h * 2)
      else
        a
  termination_by (2 ^ n - h)
  loop a 1

#eval evalToMonomial #[(5 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ)]


def unitArray {R : Type} [Inhabited R] [Ring R] (n k : ℕ) : Array R :=
  let initialArray : Array R := Array.mkArray n 0
  initialArray.set! k 1

-- #eval unitArray 3 2

theorem unitArray_size {R : Type} [Inhabited R] [Ring R] (n k : ℕ) (h : k < n) : (unitArray n k).get! k = (1 : R) := by
  unfold unitArray
  simp [h]


theorem dotProduct_unitArray_eq_get! {R : Type} [Inhabited R] [Ring R] (x : Array R) (k : ℕ) (h : k < x.size) : dotProduct x (unitArray x.size k) = x.get! k := by
  unfold dotProduct
  simp [unitArray_size]
  sorry
