/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Logic.Lemmas

/-!
  # Lemmas on `n`-tuples

  We define operations on (dependent) finite vectors that are needed
  for composing interactive (oracle) protocols.
-/
universe u v

/-- Version of `funext_iff` for dependent functions `f : (x : α) → β x`. -/
theorem funext_iff' {α : Sort u} {β : α → Sort v} {γ : α → Sort v}
    {f : (x : α) → β x} {g : (x : α) → γ x} (h : ∀ x, β x = γ x) :
      HEq f g ↔ ∀ x, HEq (f x) (g x) := by
  have : β = γ := funext h
  subst this
  simp [funext_iff]

namespace Fin

open Function

theorem append_comp {n m : ℕ} {α : Sort*} {β : Sort*} {a : Fin n → α} {b : Fin m → α} (f : α → β)
    (i : Fin (n + m)) : append (f ∘ a) (f ∘ b) i = f (append a b i) := by
  dsimp [append, addCases]
  by_cases h : i < n <;> simp [h]

/-- Version of `Fin.heq_fun_iff` for dependent functions `f : (i : Fin k) → α i`. -/
protected theorem heq_fun_iff' {k l : ℕ} {α : Fin k → Sort u} {β : Fin l → Sort u} (h : k = l)
    (h' : ∀ i : Fin k, (α i) = (β (cast h i))) {f : (i : Fin k) → α i} {g : (j : Fin l) → β j} :
    HEq f g ↔ ∀ i : Fin k, HEq (f i) (g (cast h i)) := by
  subst h
  simp only [cast_eq_self]
  exact funext_iff' h'

/-- Version of `Fin.addCases` that splits the motive into two dependent vectors `α` and `β`, and
  the return type is `Fin.append α β`. -/
def addCases' {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u} (left : (i : Fin m) → α i)
    (right : (j : Fin n) → β j) (i : Fin (m + n)) : append α β i := by
  refine addCases ?_ ?_ i <;> intro j <;> simp
  · exact left j
  · exact right j

@[simp]
theorem addCases'_left {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (left : (i : Fin m) → α i) (right : (j : Fin n) → β j) (i : Fin m) :
      addCases' left right (Fin.castAdd n i) = (Fin.append_left α β i) ▸ (left i) := by
  simp [addCases', cast_eq_iff_heq]

@[simp]
theorem addCases'_right {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (left : (i : Fin m) → α i) (right : (j : Fin n) → β j) (i : Fin n) :
      addCases' left right (Fin.natAdd m i) = (Fin.append_right α β i) ▸ (right i) := by
  simp [addCases', cast_eq_iff_heq]

-- theorem addCases'_heq_addCases {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
--     (left : (i : Fin m) → α i) (right : (j : Fin n) → β j) :
--       HEq (addCases' left right) = addCases (motive := append α β) left right := by
--   ext i
--   refine addCasesFn_iff.mpr (fun i => ?_)
--   simp [addCases']

variable {n : ℕ} {α : Fin n → Sort u}

theorem take_addCases'_left {n' : ℕ} {β : Fin n' → Sort u} (m : ℕ) (h : m ≤ n)
    (u : (i : Fin n) → α i) (v : (j : Fin n') → β j) (i : Fin m) :
    take m (Nat.le_add_right_of_le h) (addCases' u v) i =
      (append_left α β (castLE h i)) ▸ (take m h u i) := by
  have : i < n := Nat.lt_of_lt_of_le i.isLt h
  simp [take_apply, addCases', addCases, this, cast_eq_iff_heq, castLT, castLE]

-- theorem take_addCases'_right {n' : ℕ} {β : Fin n' → Sort u} (m : ℕ) (h : m ≤ n')
--     (u : (i : Fin n) → α i) (v : (j : Fin n') → β j) (i : Fin (n + m)) :
--       take (n + m) (Nat.add_le_add_left h n) (addCases' u v) i =
--         addCases' u (take m h v) i := by
--   have : i < n := Nat.lt_of_lt_of_le i.isLt h
--   simp [take_apply, addCases', addCases, this, cast_eq_iff_heq, castLT, castLE]
--   have {i : Fin m} : castLE (Nat.le_add_right_of_le h) i = natAdd n (castLE h i) := by congr
--   refine (Fin.heq_fun_iff' rfl (fun i => ?_)).mpr (fun i => ?_)
--   · sorry
--     simp only [append_right, cast_eq_self]
--   · rw [take, this]
--     simp [addCases_right]


/-- Take the last `m` elements of a finite vector -/
def rtake (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin m) → α (cast (Nat.sub_add_cancel h) (natAdd (n - m) i)) :=
  fun i => v (cast (Nat.sub_add_cancel h) (natAdd (n - m) i))

@[simp]
theorem rtake_apply (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n)
    (i : Fin m) : rtake m h v i = v (cast (Nat.sub_add_cancel h) (natAdd (n - m) i)) := rfl

@[simp]
theorem rtake_zero {n : ℕ} {α : Sort u} (v : Fin n → α) :
    rtake 0 (by omega) v = fun i => Fin.elim0 i := by ext i; exact Fin.elim0 i

@[simp]
theorem rtake_self {n : ℕ} {α : Sort u} (v : Fin n → α) :
    rtake n (by omega) v = v := by ext i; simp [rtake, Fin.natAdd]

-- @[simp]
-- theorem rtake_succ {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     rtake v (Fin.succ m) = Fin.addCases (v (Fin.cast (by omega) (Fin.natAdd (n - m) m)))
--       (rtake (v ∘ Fin.succ) m) := by
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

/-
* `Fin.drop`: Given `h : m ≤ n`, `Fin.drop m h v` for a `n`-tuple `v = (v 0, ..., v (n - 1))` is the
  `(n - m)`-tuple `(v m, ..., v (n - 1))`.
-/
section Drop

/-- Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. -/
def drop (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin (n - m)) → α (cast (Nat.sub_add_cancel h) (addNat i m)) :=
  fun i ↦ v (cast (Nat.sub_add_cancel h) (addNat i m))

@[simp]
theorem drop_apply (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin (n - m)) :
    (drop m h v) i = v (cast (Nat.sub_add_cancel h) (addNat i m)) := rfl

@[simp]
theorem drop_zero (v : (i : Fin n) → α i) : drop 0 n.zero_le v = v := by
  ext i
  simp only [Nat.sub_zero, Nat.add_zero, addNat, Fin.eta, cast_eq_self, drop_apply]

@[simp]
theorem drop_one {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    drop 1 (Nat.le_add_left 1 n) v = tail v := by
  ext i
  simp only [drop, tail]
  congr

@[simp]
theorem drop_of_succ {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    drop n n.le_succ v = fun i => v (cast (Nat.sub_add_cancel n.le_succ) (addNat i n)) := by
  ext i
  simp only [drop]

-- @[simp]
-- theorem drop_all (v : (i : Fin n) → α i) :
--     HEq (drop n (le_refl n) v)
--       (fun (i : Fin 0) ↦ @elim0 (α (cast (Nat.sub_add_cancel (le_refl n)) (i.addNat n))) i) := by
--   refine (Fin.heq_fun_iff ?_).mpr ?_
--   · simp
--   · intro i

theorem drop_tail {α : Fin (n + 1) → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin (n + 1)) → α i) :
    HEq (drop m h (tail v)) (drop m.succ (Nat.succ_le_succ h) v) := by
  refine (Fin.heq_fun_iff' (Nat.succ_sub_succ_eq_sub n m).symm (fun i => by congr)).mpr ?_
  intro i
  simp [drop, tail]
  congr

theorem drop_repeat {α : Type*} {n' : ℕ} (m : ℕ) (h : m ≤ n) (a : Fin n' → α) :
    HEq (drop (m * n') (Nat.mul_le_mul_right n' h) (Fin.repeat n a)) (Fin.repeat (n - m) a) :=
  (Fin.heq_fun_iff (Nat.sub_mul n m n').symm).mpr (fun i => by simp [cast, modNat])

end Drop

section Sum

-- Append multiple `Fin` tuples?

#print Fin.addCases

def castSum (l : List ℕ) {i : ℕ} (h : i ∈ l) : Fin i → Fin l.sum := fun j =>
  match l with
  | [] => by contradiction
  | i' :: l' => by
    simp only [List.sum_cons]
    by_cases hi : i = i'
    · exact castAdd l'.sum (cast hi j)
    · exact natAdd i' (castSum l' (List.mem_of_ne_of_mem hi h) j)

theorem castSum_castLT {l' : List ℕ} {i : ℕ} (j : Fin i) :
    castSum (i :: l') (by simp) j =
      castLT j (Nat.lt_of_lt_of_le j.isLt (List.le_sum_of_mem (by simp))) := by
  simp [castSum, castAdd, castLE, castLT]

theorem castSum_castAdd {n m : ℕ} (i : Fin n) : castSum [n, m] (by simp) i = castAdd m i := by
  simp [castSum]

def sumCases {l : List ℕ} {motive : Fin l.sum → Sort*}
    (cases : ∀ {i} (h : i ∈ l) (j : Fin i), motive (castSum l h j))
    (j : Fin l.sum) : motive j := match l with
  | [] => by simp only [List.sum_nil] at j; exact elim0 j
  | i' :: l' => by
    simp only [List.sum_cons] at j motive
    by_cases hj : j < i'
    · convert cases (i := i') (by simp) ⟨j.val, hj⟩
      simp [castSum]
    · have hj' : j.val - i' < l'.sum := by sorry
      sorry
      -- refine sumCases (l := l') (motive := motive ∘ natAdd i') ?_ ⟨j.val - i', hj'⟩

end Sum

end Fin
