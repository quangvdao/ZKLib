/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.ZMod.Basic

/-!
  # Efficient Modular Exponentiation

  We define a more efficient exponentiation algorithm for `ZMod n` by decomposing the exponent
  in some base `b` and recursively computing the result.
-/

namespace ZMod

/--
  Perform exponentiation over `ZMod n` by decomposing the exponent `k` in base `b`,
  then recursively computing the result.
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
