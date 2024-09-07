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

  TODO: split these files into different files based on each namespace
-/

namespace Nat

-- Note: this is already done with `Nat.sub_add_eq_max`
theorem max_eq_add_sub {m n : Nat} : Nat.max m n = m + (n - m) := by
  by_cases h : n ≤ m
  · simp [Nat.sub_eq_zero_of_le, h]
  · simp [Nat.max_eq_max, Nat.max_eq_right (Nat.le_of_not_le h), Nat.add_sub_of_le (Nat.le_of_not_le h)]


-- TODO: add lemmas connecting `log2` and `log`, and `nextPowerOfTwo` and `pow`?

-- @[simp] theorem log2_eq_log_two (n : Nat) : log2 n = log 2 n
--   | 0 => by simp
--   | n + 1 => by simp

-- @[simp] theorem nextPowerOfTwo_eq_pow_clog (n : Nat) : nextPowerOfTwo n = 2 ^ (clog2 n) := by

-- Note: `iterateRec` is not as efficient as `Nat.iterate`. For the repeated squaring in exponentiation, we need to additionally do memoization of intermediate values.
-- TODO: add this
-- See [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Binary.20version.20of.20.60Nat.2Eiterate.60.3F/near/468437958)

/-- Iterate a binary operation `op` for `n` times by decomposing `n` in base `b`,
  then recursively computing the result. -/
def iterateRec {α : Sort u} (op : α → α) (n : ℕ) (b : ℕ) (h : b ≥ 2) : α → α :=
  if n = 0 then id
  else op^[n % b] ∘ (iterateRec op (n / b) b h)^[b]
termination_by n
decreasing_by
  simp_wf
  rename_i hn
  exact Nat.div_lt_self (Nat.ne_zero_iff_zero_lt.mp hn) h

/-- Special case of `Nat.iterateRec` where the base `b` is binary.
  Corresponds to repeated squaring for exponentiation. -/
def iterateBin {α : Sort u} (op : α → α) (n : ℕ) : α → α := iterateRec op n 2 (by decide)

notation:max f "^["n"]₂" => Nat.iterateBin f n

end Nat

namespace Function

@[simp]
lemma iterateRec_zero {α : Sort u} (op : α → α) : Nat.iterateRec op 0 b h = id := by simp [Nat.iterateRec]

@[simp]
lemma iterateRec_lt_base {α : Type u} (op : α → α) {h : b ≥ 2} (hk : k < b) : Nat.iterateRec op k b h = op^[k] := by
  unfold Nat.iterateRec
  have h1 : k % b = k := Nat.mod_eq_of_lt (by omega)
  have h2 : k / b = 0 := Nat.div_eq_of_lt (by omega)
  simp [h1, h2]
  intro hZero ; simp [hZero]

theorem iterateRec_eq_iterate {α : Type u} (op : α → α) (n : Nat) :
    Nat.iterateRec op n b h = op^[n] := by
  induction n using Nat.caseStrongInductionOn with
  | zero => simp
  | ind k ih =>
    unfold Nat.iterateRec
    have : (k + 1) / b ≤ k := by
      refine Nat.le_of_lt_add_one ?_
      obtain hPos : k + 1 > 0 := by omega
      exact Nat.div_lt_self hPos h
    rw [ih ((k + 1) / b) this, ←iterate_mul, ←iterate_add, Nat.mod_add_div' (k + 1) b]
    simp

theorem iterateBin_eq_iterate {α : Type u} (op : α → α) (n : Nat) :
    op^[n]₂ = op^[n] := by simp [Nat.iterateBin, iterateRec_eq_iterate]

end Function

namespace List

@[simp] theorem leftpad_eq_self (l : List α) (n : Nat) (h : l.length ≥ n) :
    leftpad n unit l = l := by simp [leftpad, Nat.sub_eq_zero_of_le h]

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

@[simp] theorem rightpad_eq_self (l : List α) (n : Nat) (h : n ≤ l.length) :
    rightpad n unit l = l := by simp [rightpad, Nat.sub_eq_zero_of_le h]

theorem rightpad_eq_rightpad_max (l : List α) (n : Nat) :
    rightpad n unit l = rightpad (max n l.length) unit l := by simp [rightpad]; omega

theorem rightpad_eq_rightpad_append_replicate_of_ge
  (l : List α) (m n : Nat) (h : n ≤ m) :
    rightpad m unit l = rightpad n unit l ++ replicate (m - max n l.length) unit := by
  simp [rightpad]; omega

theorem rightpad_eq_if_rightpad_eq_of_ge (l l' : List α) (m n n' : Nat) (h : n ≤ m) (h' : n' ≤ m) :
    rightpad n unit l = rightpad n' unit l' →
        rightpad m unit l = rightpad m unit l' := by
  intro hEq
  rw [rightpad_eq_rightpad_append_replicate_of_ge l _ n h]
  rw [rightpad_eq_rightpad_append_replicate_of_ge l' _ n' h']
  have hLen : max n l.length = max n' l'.length := calc
    max n l.length = (rightpad n unit l).length := Eq.symm (rightpad_length n unit l)
    _ = (rightpad n' unit l').length := congrArg length hEq
    _ = max n' l'.length := rightpad_length n' unit l'
  simp [hEq, hLen]


@[simp] theorem rightpad_twice_eq_rightpad_max (m n : Nat) (unit : α) (l : List α) :
    rightpad n unit (rightpad m unit l) = rightpad (max m n) unit l := by
  rw (config := { occs := .neg [0] }) [rightpad, rightpad_length]
  simp [rightpad]
  by_cases h : m.max n ≤ l.length
  · simp [Nat.max_le.mp h]
  · refine Nat.eq_sub_of_add_eq ?_
    conv => { enter [1, 1]; rw [Nat.add_comm] }
    rw [Nat.add_assoc, Nat.sub_add_eq_max, Nat.sub_add_eq_max]
    simp at h
    by_cases h' : m ≤ l.length <;> omega

-- TODO: finish this lemma, may need many cases
@[simp] theorem rightpad_getD_eq_getD (l : List α) (n : Nat) (unit : α) (i : Nat) :
    (rightpad n unit l).getD i unit = l.getD i unit := by
  by_cases h : i < min n l.length
  · have : i < l.length := by omega
    simp [this]
    sorry
  · simp [h, List.getD]; sorry

#check List.getD_eq_get?
#check List.get?_append



/-- Given two lists of potentially different lengths, right-pads the shorter list with `unit` elements until they are the same length. -/
def matchSize (l₁ : List α) (l₂ : List α) (unit : α) : List α × List α :=
  (l₁.rightpad (l₂.length) unit, l₂.rightpad (l₁.length) unit)

theorem matchSize_comm (l₁ : List α) (l₂ : List α) (unit : α) :
    matchSize l₁ l₂ unit = (matchSize l₂ l₁ unit).swap := by
  simp [matchSize]


/-- `List.matchSize` returns two equal lists iff the two lists agree at every index `i : Nat` (extended by `unit` if necessary). -/
theorem matchSize_eq_iff_forall_eq (l₁ l₂ : List α) (unit : α) :
    (fun (x, y) => x = y) (matchSize l₁ l₂ unit) ↔ ∀ i : Nat, l₁.getD i unit = l₂.getD i unit := by sorry
    -- TODO: finish this lemma based on `rightpad_getD_eq_getD`




/-- `List.dropWhile` but starting from the last element. Performed by `dropWhile` on the reversed list, followed by a reversal. -/
def dropLastWhile (p : α → Bool) (l : List α) : List α :=
  (l.reverse.dropWhile p).reverse

end List

-- abbrev isBoolean {R : Type _} [Zero R] [One R] (x : R) : Prop := x = 0 ∨ x = 1

namespace Array

/-- Checks if an array of elements from a type `R` is a boolean array, i.e., if every element is either `0` or `1`. -/
def isBoolean {R : Type _} [Zero R] [One R] (a : Array R) : Prop := ∀ i : Fin a.size, a.get i = 0 ∨ a.get i = 1

/-- Interpret an array as the binary representation of a number, sending `0` to `0` and `≠ 0` to `1`. -/
def toNum {R : Type _} [Zero R] [DecidableEq R] (a : Array R) : ℕ :=
  (a.map (fun r => if r = 0 then 0 else 1)).reverse.foldl (fun acc elem => (acc * 2) + elem) 0

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

/-- `Array` version of `List.matchSize`, which just invokes the list version. -/
@[reducible]
def matchSize (a : Array α) (b : Array α) (unit : α) : Array α × Array α :=
  let tuple := List.matchSize a.toList b.toList unit
  (⟨tuple.1⟩, ⟨tuple.2⟩)

-- @[simp] theorem matchSize_comm (a : Array α) (b : Array α) (unit : α) :
--     matchSize a b unit = (matchSize b a unit).swap := by
--   simp [matchSize, List.matchSize]


/-- Right-pads an array with `unit` elements until its length is a power of two. Returns the padded array and the number of elements added. -/
def rightpadPowerOfTwo (unit : α) (a : Array α) : Array α :=
  a.rightpad (2 ^ (Nat.clog 2 a.size)) unit

@[simp] theorem rightpadPowerOfTwo_size (unit : α) (a : Array α) : (a.rightpadPowerOfTwo unit).size = 2 ^ (Nat.clog 2 a.size) := by simp [rightpadPowerOfTwo, Nat.le_pow_iff_clog_le]

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
