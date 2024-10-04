/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Fin.Tuple.Basic

/-!
  # (Dependent) Finite Vectors

  We define operations on (dependent) finite vectors that are needed
  for composing interactive (oracle) protocols.
-/
namespace Fin

open Function

/-- Version of `Fin.addCases` that splits the motive into two dependent vectors, and maps the result type through some function `φ`. -/
def addCases_fun {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    {φ : Sort u → Sort v} (left : (i : Fin m) → φ (motive i)) (right : (j : Fin n) → φ (motive' j))
        (i : Fin (m + n)) : φ (addCases motive motive' i) := by
  refine addCases ?_ ?_ i <;> intro j <;> simp
  · exact left j
  · exact right j

@[simp]
theorem addCases_fun_left {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    {φ : Sort u → Sort v} (left : (i : Fin m) → φ (motive i)) (right : (j : Fin n) → φ (motive' j))
        (i : Fin m) : (@addCases_left _ _ (fun _ => Sort u) motive _ _) ▸
            (addCases_fun left right (Fin.castAdd n i)) = left i := by
  simp [addCases_fun]; symm
  apply eq_of_heq
  refine (heq_eqRec_iff_heq _ _ (left i)).mpr ?_
  symm; exact cast_heq _ (left i)

@[simp]
theorem addCases_fun_right {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    {φ : Sort u → Sort v} (left : (i : Fin m) → φ (motive i)) (right : (j : Fin n) → φ (motive' j))
        (i : Fin n) : (@addCases_right _ _ (fun _ => Sort u) _ motive' _) ▸
            (addCases_fun left right (Fin.natAdd m i)) = right i := by
  simp [addCases_fun]; symm
  apply eq_of_heq
  refine (heq_eqRec_iff_heq _ _ (right i)).mpr ?_
  symm; exact cast_heq _ (right i)

/-- Version of `Fin.addCases_fun` with `φ = id`. -/
def addCases' {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    (left : (i : Fin m) → motive i) (right : (j : Fin n) → motive' j)
        (i : Fin (m + n)) : addCases motive motive' i :=
  Fin.addCases_fun (φ := id) left right i

@[simp]
theorem addCases'_left {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    (left : (i : Fin m) → motive i) (right : (j : Fin n) → motive' j)
        (i : Fin m) : (@addCases_left _ _ (fun _ => Sort u) motive _ _) ▸
            (addCases' left right (Fin.castAdd n i)) = left i :=
  addCases_fun_left (φ := id) left right i

@[simp]
theorem addCases'_right {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    (left : (i : Fin m) → motive i) (right : (j : Fin n) → motive' j)
        (i : Fin n) : (@addCases_right _ _ (fun _ => Sort u) _ motive' _) ▸
            (addCases' left right (Fin.natAdd m i)) = right i :=
  addCases_fun_right (φ := id) left right i


variable {n : ℕ} {α : Fin n → Sort*}

/-- Take the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `m`-tuple. -/
def take (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) : (i : Fin m) → α (castLE h i) :=
  fun i ↦ v (castLE h i)

@[simp]
theorem take_def (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) (i : Fin m) :
    (take v m h) i = v (castLE h i) := rfl

@[simp]
theorem take_zero (v : (i : Fin n) → α i) : take v 0 (Nat.zero_le n) = fun i ↦ elim0 i := by
  ext i; exact elim0 i

@[simp]
theorem take_eq_self (v : (i : Fin n) → α i) :
    take v n (le_refl n) = v := by ext i; simp [take]

/-- Taking `m + 1` elements is equal to taking `m` elements and adding the `(m + 1)`th one. -/
theorem take_succ_eq_snoc (v : (i : Fin n) → α i) (m : ℕ) (h : m < n) :
    take v m.succ h = snoc (take v m (le_of_lt h)) (v ⟨m, h⟩) := by
  ext i
  induction m with
  | zero =>
    have h' : i = 0 := by
      ext
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, coe_fin_one]
    subst h'
    simp [take, snoc, castLE]
  | succ m _ =>
    induction i using reverseInduction with
    | last => simp [take, snoc, castLT]; congr
    | cast i _ => simp [snoc_cast_add]

/-- `take` commutes with `update` for indices in the range of `take`. -/
@[simp]
theorem take_update_of_lt (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) (i : Fin m)
    (x : α (castLE h i)) : take (update v (castLE h i) x) m h = update (take v m h) i x := by
  ext j
  by_cases h' : j = i
  · rw [h']
    simp only [take, update_same]
  · have : castLE h j ≠ castLE h i := by simp [h']
    simp only [take, update_noteq h', update_noteq this]

/-- `take` is the same after `update` for indices outside the range of `take`. -/
@[simp]
theorem take_update_of_ge (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) (i : Fin n) (hi : i ≥ m)
    (x : α i) : take (update v i x) m h = take v m h := by
  ext j
  have : castLE h j ≠ i := by
    refine ne_of_val_ne ?_
    simp only [coe_castLE]
    exact Nat.ne_of_lt (lt_of_lt_of_le j.isLt hi)
  simp only [take, update_noteq this]

/-- Taking the first `m ≤ n` elements of an `append u v`, where `u` is a `n`-tuple, is the same as
taking the first `m` elements of `u`. -/
@[simp]
theorem take_append_left {n' m : ℕ} {α : Sort*} (u : (i : Fin n) → α) (v : (i : Fin n') → α)
    (h : m ≤ n) : take (append u v) m (Nat.le_add_right_of_le h) = take u m h := by
  ext i
  have : castLE (Nat.le_add_right_of_le h) i = castAdd n' (castLE h i) := rfl
  simp only [take, append_left, this]

/-- Taking the first `n + m` elements of an `append u v`, where `v` is a `n'`-tuple and `m ≤ n'`,
is the same as appending `u` with the first `m` elements of `v`. -/
@[simp]
theorem take_append_right {n' m : ℕ} {α : Sort*} (u : (i : Fin n) → α) (v : (i : Fin n') → α)
    (h : m ≤ n') : take (append u v) (n + m) (Nat.add_le_add_left h n) = append u (take v m h) := by
  ext i
  by_cases h' : i < n
  · have : castLE (Nat.add_le_add_left h n) i = castAdd n' ⟨i.val, h'⟩ := by
      simp only [castAdd_mk]
      rfl
    rw [take, this, append_left]
    have : i = castAdd m ⟨i.val, h'⟩ := by simp only [castAdd_mk]
    conv_rhs => rw [this, append_left]
  · simp only [not_lt] at h'
    let j := subNat n (cast (Nat.add_comm _ _) i) h'
    have : i = natAdd n j := by simp [j]
    conv_rhs => rw [this, append_right, take]
    have : castLE (Nat.add_le_add_left h n) i = natAdd n (castLE h j) := by
      simp_all only [natAdd_subNat_cast, j]
      ext : 1
      simp_all only [coe_castLE, coe_natAdd, coe_subNat, coe_cast, Nat.add_sub_cancel']
    rw [take, this, append_right]

@[simp]
theorem take_init {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) (m : ℕ) (h : m ≤ n) :
    take (init v) m h = take v m (Nat.le_succ_of_le h) := by
  ext i
  simp only [take, init]
  congr

theorem take_List_ofFn {n : ℕ} {α : Type u} (v : Fin n → α) (m : ℕ) (h : m ≤ n) : List.ofFn (take v m h) = (List.ofFn v).take m := by
  induction m with
  | zero => simp [take_zero]
  | succ m ih =>
    simp only [List.ofFn_add, List.take_succ]
    congr
    · rw [←(ih (by omega))]; congr
    · have hLt : m < n := by omega
      simp [take, List.getElem?_ofFn, List.ofFnNthVal, hLt, castLE]

@[simp]
theorem take_append_eq_self {n m : ℕ} {α : Type u} (v : (i : Fin n) → α) (w : (i : Fin m) → α) :
    take (Fin.append v w) n (Nat.le_add_right n m) = v := by
  ext i
  simp [take, append, addCases]
  congr 1

-- theorem take_addCases_eq_self {n m : ℕ} {α : Fin n → Sort u} {β : Fin m → Sort u} (v : (i : Fin n) → α i) (w : (i : Fin m) → β i) :
--     take (Fin.addCases' v w) n (Nat.le_add_right n m) = v := by
--   ext i
--   simp only [take, append]
--   congr

/-- Take the last `m` elements of a finite vector -/
def rtake {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) :
    (i : Fin m) → α (Fin.cast (by omega) (Fin.natAdd (n - m) i)) :=
  fun i => v (Fin.cast (by omega) (Fin.natAdd (n - m) i))

@[simp]
theorem rtake_def {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) (i : Fin m) :
    rtake v m h i = v (Fin.cast (by omega) (Fin.natAdd (n - m) i)) := rfl

@[simp]
theorem rtake_zero {n : ℕ} {α : Sort u} (v : Fin n → α) :
    rtake v 0 (by omega) = fun i => Fin.elim0 i := by ext i; exact Fin.elim0 i

@[simp]
theorem rtake_self {n : ℕ} {α : Sort u} (v : Fin n → α) :
    rtake v n (by omega) = v := by ext i; simp [rtake, Fin.natAdd]

-- @[simp]
-- theorem rtake_succ {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     rtake v (Fin.succ m) = Fin.addCases (v (Fin.cast (by omega) (Fin.natAdd (n - m) m))) (rtake (v ∘ Fin.succ) m) := by
--   ext i <;> simp [rtake, Fin.natAdd]

-- @[simp]
-- theorem rtake_eq_take_rev {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     rtake v m = take v m ∘ Fin.rev := by
--   ext i
--   simp [rtake, take, Fin.natAdd, Fin.cast, Fin.rev]
--   congr;

-- @[simp]
-- theorem take_rtake_append {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     fun i => Fin.addCases (take v m) (rtake v (n - m)) i = v := by
--   ext i
--   refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [take, rtake]
--   · exact v j
--   · exact v (Fin.addNat j (n - m))


end Fin
