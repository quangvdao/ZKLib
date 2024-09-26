/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.Matrix.Reflection

/-!
  # (Dependent) Finite Vectors

  We define operations on (dependent) finite vectors that are needed
  for composing interactive (oracle) protocols.
-/

namespace Fin

/-- Version of `Fin.addCases` that splits the motive into two dependent vectors, and maps the result type through some function `φ`. -/
def addCases' {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    {φ : Sort u → Sort v} (left : (i : Fin m) → φ (motive i)) (right : (j : Fin n) → φ (motive' j))
        (i : Fin (m + n)) : φ (addCases motive motive' i) := by
  refine addCases ?_ ?_ i <;> intro j <;> simp
  · exact left j
  · exact right j

@[simp]
theorem addCases'_left {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    {φ : Sort u → Sort v} (left : (i : Fin m) → φ (motive i)) (right : (j : Fin n) → φ (motive' j))
        (i : Fin m) : (@addCases_left _ _ (fun _ => Sort u) motive _ _) ▸
            (addCases' left right (Fin.castAdd n i)) = left i := by
  simp [addCases']; symm
  apply eq_of_heq
  refine (heq_eqRec_iff_heq _ _ (left i)).mpr ?_
  symm; exact cast_heq _ (left i)

@[simp]
theorem addCases'_right {m n : ℕ} {motive : Fin m → Sort u} {motive' : Fin n → Sort u}
    {φ : Sort u → Sort v} (left : (i : Fin m) → φ (motive i)) (right : (j : Fin n) → φ (motive' j))
        (i : Fin n) : (@addCases_right _ _ (fun _ => Sort u) _ motive' _) ▸
            (addCases' left right (Fin.natAdd m i)) = right i := by
  simp [addCases']; symm
  apply eq_of_heq
  refine (heq_eqRec_iff_heq _ _ (right i)).mpr ?_
  symm; exact cast_heq _ (right i)


/-- Take the first `m` elements of a finite vector -/
def take {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) :
    (i : Fin m) → α (Fin.castLE (by omega) i) :=
  fun i => v (Fin.castLE (by omega) i)

/-- Take the first `m` elements of a finite vector.

Alternate version of `take` that takes `m : Fin (n + 1)` as input -/
def take' {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) (m : Fin (n + 1)) :
    (i : Fin m.val) → α (Fin.castLE (by omega) i) :=
  take v m.val (Nat.le_of_lt_add_one m.isLt)

@[simp]
theorem take_def {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) (i : Fin m) :
    (take v m h) i = v (Fin.castLE (by omega) i) := rfl

@[simp]
theorem take_zero {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) :
    take v 0 (by omega) = fun i => Fin.elim0 i :=
  by ext i; exact Fin.elim0 i

@[simp]
theorem take_self {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) :
    take v n (by omega) = v := by ext i; simp [take]

#check Fin.snoc

theorem take_succ {n : ℕ} {α : Fin n → Type u} (v : (i : Fin n) → α i) (m : ℕ) (h : m < n) :
    take v m.succ (by omega) = @Fin.snoc m (fun i => α (Fin.castLE (by omega) i))
      (take v m (by omega)) (v ⟨m, h⟩) := by
  ext i
  induction m with
  | zero =>
    have h' : i = 0 := by aesop
    subst h'
    simp [take, snoc, castLE]
  | succ m _ =>
    induction i using Fin.reverseInduction with
    | last => simp [take, snoc, castLT]; congr
    | cast i _ => simp [snoc_cast_add]


theorem take_ofFn {n : ℕ} {α : Type u} (v : Fin n → α) (m : ℕ) (h : m ≤ n) : List.ofFn (take v m h) = (List.ofFn v).take m := by
  induction m with
  | zero => simp [take_zero]
  | succ m ih =>
    simp only [List.ofFn_add, List.take_succ]
    congr
    · rw [←(ih (by omega))]; congr
    · have hLt : m < n := by omega
      simp [take, List.getElem?_ofFn, List.ofFnNthVal, hLt, castLE]

/-
List.take_succ.{u_1} {α : Type u_1} {l : List α} {n : ℕ} : List.take (n + 1) l = List.take n l ++ l[n]?.toList
-/
#check List.take_cons_succ

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

-- #check Fin.succRecOn

-- #check Fin.succRec

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
