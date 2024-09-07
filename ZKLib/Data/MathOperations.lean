/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.Nat.Log
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Lemmas
import Batteries.Data.Nat.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
  # Helper Functions and Lemmas
-/

namespace Nat

-- TODO: add lemmas connecting `log2` and `log`, and `nextPowerOfTwo` and `pow`?

-- @[simp] theorem log2_eq_log_two (n : Nat) : log2 n = log 2 n
--   | 0 => by simp
--   | n + 1 => by simp

-- @[simp] theorem nextPowerOfTwo_eq_pow_clog (n : Nat) : nextPowerOfTwo n = 2 ^ (clog2 n) := by

/-- Iterate a binary operation `op` on an argument `x` by decomposing the argument in binary form. -/
def iterateBin {α : Sort u} (op : α → α) : ℕ → α → α :=
  fun n => op^[n % 2] ∘ (op^[n / 2])^[2]

notation:max f "^["n"]₂" => Nat.iterateBin f n

end Nat

namespace Function

@[simp] theorem iterateBin_eq_iterate {α : Type u} (op : α → α) (n : Nat) :
    Nat.iterateBin op n = op^[n] := by
  simp [Nat.iterateBin, ←Function.iterate_add op _ _]
  have : n % 2 + (n / 2 + n / 2) = n := by omega
  rw [this]

end Function

namespace List

@[simp] theorem rightpad_length (n : Nat) (unit : α) (l : List α) :
    (rightpad n unit l).length = max n l.length := by
  simp only [rightpad, length_append, length_replicate, Nat.add_comm l.length _, Nat.sub_add_eq_max]

@[simp] theorem rightpad_prefix (n : Nat) (unit : α) (l : List α) :
    l <+: rightpad n unit l := by
  simp only [IsPrefix, rightpad]
  exact Exists.intro (replicate (n - l.length) unit) rfl

@[simp] theorem rightpad_suffix (n : Nat) (unit : α) (l : List α) :
    replicate (n - l.length) unit <:+ rightpad n unit l := by
  simp only [IsSuffix, rightpad]
  exact Exists.intro l rfl

/-- `List.dropWhile` but starting from the last element. Performed by `dropWhile` on the reversed list, followed by a reversal. -/
def dropLastWhile (p : α → Bool) (l : List α) : List α :=
  (l.reverse.dropWhile p).reverse

-- TODO: add lemmas connecting `dropLastWhile` with `leftpad` and `rightpad`

end List

-- abbrev isBoolean {R : Type _} [Zero R] [One R] (x : R) : Prop := x = 0 ∨ x = 1

namespace Array

/-- Checks if an array of elements from a type `R` is a boolean array, i.e., if every element is either `0` or `1`. -/
def isBoolean {R : Type _} [Zero R] [One R] (a : Array R) : Prop := ∀ i : Fin a.size, a.get i = 0 ∨ a.get i = 1

/-- Interpret an array as the binary representation of a number, sending `0` to `0` and `≠ 0` to `1`. -/
def toNum {R : Type _} [Zero R] [DecidableEq R] (a : Array R) : ℕ :=
  (a.map (fun r => if r = 0 then 0 else 1)).reverse.foldl (fun acc elem => (acc * 2) + elem) 0

/-- `Array` version of `List.enum`, which just invokes the list version. -/
@[reducible]
def enum (a : Array α) : Array (Nat × α) :=
  ⟨a.toList.enum⟩

/-- `Array` version of `List.replicate`, which just invokes the list version. -/
@[reducible]
def replicate (n : Nat) (a : α) : Array α :=
  ⟨List.replicate n a⟩

/-- `Array` version of `List.leftpad`, which just invokes the list version. -/
@[reducible]
def leftpad (n : Nat) (unit : α) (a : Array α) : Array α :=
  ⟨a.toList.leftpad n unit⟩

/-- `Array` version of `List.rightpad`, which just invokes the list version. -/
@[reducible]
def rightpad (n : Nat) (unit : α) (a : Array α) : Array α :=
  ⟨a.toList.rightpad n unit⟩

/-- Given two arrays of different lengths, right-pads the shorter array with `unit` elements until they are the same length. -/
def matchSize (a : Array α) (b : Array α) (unit : α) : Array α × Array α :=
  (a.rightpad (b.size) unit, b.rightpad (a.size) unit)

/-- Right-pads an array with `unit` elements until its length is a power of two. Returns the padded array and the number of elements added. -/
def padPowerOfTwo (unit : α) (a : Array α) : Array α :=
  a.rightpad (2 ^ (Nat.clog 2 a.size)) unit

@[simp] theorem padPowerOfTwo_size (unit : α) (a : Array α) : (a.padPowerOfTwo unit).size = 2 ^ (Nat.clog 2 a.size) := by simp [padPowerOfTwo, Nat.le_pow_iff_clog_le]

/-- Get the last element of an array, assuming the array is non-empty. -/
def getLast (a : Array α) (h : a.size > 0) : α :=
  a.get ⟨a.size - 1, Nat.sub_lt_self (by decide) (gt_iff_lt.mpr h)⟩

/-- Get the last element of an array, or `v₀` if the array is empty. -/
def getLastD (a : Array α) (v₀ : α) : α := a.getD (a.size - 1) v₀


@[simp] theorem popWhile_nil_or_last_false (p : α → Bool) (as : Array α) (h : (as.popWhile p).size > 0) :
    ¬ (p <| (as.popWhile p).getLast h) := sorry


theorem range_succ (n : Nat) : range (n + 1) = (range n).push n := by
  simp [range, Nat.fold, flip]

@[simp]
theorem range_data (n : Nat) : (Array.range n).data = List.range n := by
  induction n with
  | zero => simp only [Array.range]; rfl
  | succ n ih => simp [range_succ, List.range_succ, ih]

@[simp]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
  exact (Array.mem_data).symm.trans (by simp)

/-- `Array` version of `List.finRange`. -/
def finRange (n : Nat) : Array (Fin n) := Array.ofFn (fun i => i)

@[simp] theorem finRange_data (n : Nat) : (finRange n).data = List.finRange n := by sorry

end Array

namespace Mathlib

namespace Vector

def interleave {n : Nat} (xs : Vector α n) (ys : Vector α n) : Vector α (2 * n) := sorry

-- def pairwise {α : Type} {n : Nat} (v : Vector α (2 * n)) : Vector (α × α) n :=
--   Vector.ofFn (fun i =>
--     let j := 2 * i
--     (v.get ⟨j, by omega; exact i.isLt⟩,
--      v.get ⟨j + 1, by simp [Nat.mul_two, Nat.lt_succ]; exact i.isLt⟩))

def chunkPairwise {α : Type} : {n : Nat} → Vector α (2 * n) → Vector (α × α) n
  | 0, Vector.nil => Vector.nil
  | n + 1, xs => by
    have : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [this] at xs
    exact ⟨xs.head, xs.tail.head⟩ ::ᵥ chunkPairwise xs.tail.tail

end Vector

end Mathlib


namespace ZMod

/--
  Perform exponentiation over `ZMod n` by decomposing the exponent `k` in base `b`,
  then recursively computing the result.

  NOTE: this is basically subsumed by `Nat.iterateBin` above
-/
def powSplit (a : ZMod n) (k : ℕ) (b : ℕ) (h : b ≥ 2) : ZMod n :=
  if k = 0 then 1
  else a ^ (k % b) * (a.powSplit (k / b) b h) ^ b
termination_by k
decreasing_by
  simp_wf
  rename_i hk
  exact Nat.div_lt_self (Nat.ne_zero_iff_zero_lt.mp hk) h

@[simp]
lemma powSplit_zero (a : ZMod n) {h : b ≥ 2} : a.powSplit 0 b h = 1 := by simp [powSplit]

@[simp]
lemma powSplit_lt_base (a : ZMod n) {h : b ≥ 2} (hk : k < b) : a.powSplit k b h = a ^ k := by
  unfold powSplit
  have h1 : k % b = k := Nat.mod_eq_of_lt (by linarith)
  have h2 : k / b = 0 := Nat.div_eq_of_lt (by linarith)
  simp [h1, h2]
  intro hZero ; simp [hZero]

theorem pow_eq_powSplit {x : ZMod n} {k : ℕ} (b : ℕ) (h : b ≥ 2) : x ^ k = x.powSplit k b h := by
  induction k using Nat.caseStrongInductionOn with
  | zero => simp
  | ind k ih =>
    unfold powSplit
    simp
    have : (k + 1) / b ≤ k := by
      refine Nat.le_of_lt_add_one ?_
      obtain hPos : k + 1 > 0 := by omega
      exact Nat.div_lt_self hPos h
    rw [←ih ((k + 1) / b) this, ←pow_mul, ←pow_add, Nat.mod_add_div' (k + 1) b]

/--
  Special case of `powSplit` where the base is binary, namely `b = 2`.
-/
def powBinary (x : ZMod n) (k : ℕ) : ZMod n := powSplit x k 2 (by decide)

@[simp]
lemma powBinary_zero (x : ZMod n) : x.powBinary 0 = 1 := by simp [powBinary]

@[simp]
lemma powBinary_one (x : ZMod n) : x.powBinary 1 = x := by simp [powBinary]

end ZMod
