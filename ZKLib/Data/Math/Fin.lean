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

namespace List

-- TODO: put this elsewhere (for some reason `@[to_additive]` doesn't work)
def partialSum {α : Type*} [AddMonoid α] (l : List α) : List α :=
  [0] ++ match l with
  | [] => []
  | a :: l' => (partialSum l').map (a + ·)

@[to_additive existing]
def partialProd {α : Type*} [Monoid α] (l : List α) : List α :=
  [1] ++ match l with
  | [] => []
  | a :: l' => (partialProd l').map (a * ·)

@[simp]
theorem partialSum_nil : [].partialSum = [0] := rfl

variable {α : Type*} [AddMonoid α]

@[simp]
theorem partialSum_succ {a : α} {l : List α} :
    (a :: l).partialSum = [0] ++ (partialSum l).map (a + ·) := rfl

variable [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)]

-- Pinpoint the first element in the list whose partial sum up to that point is more than `j`
def findSum (l : List α) (j : α) : Option α := l.partialSum.find? (j < ·)

-- TODO: extend theorems to more general types than just `ℕ`

theorem findSum_of_le_sum {l : List ℕ} {j : ℕ} (h : j < l.sum) : ∃ n, findSum l j = some n := by
  match l with
  | [] => simp only [sum_nil, not_lt_zero'] at h ⊢
  | a :: l' =>
    simp at h
    sorry
    -- by_cases h' : j < a
    -- · use a
    --   simp [findSum, h', findSome?_cons]
    -- · simp [findSum, h'] at h
    --   specialize @findSum_of_le_sum l' (j - a)
    --   simp at h

-- Pinpoint the first index in the list whose partial sum is more than `j`
def findSumIdx (l : List α) (j : α) : ℕ := l.partialSum.findIdx (j < ·)

-- Variant of `findSumIdx` with bounds
def findSumIdx' (l : List ℕ) (j : Fin l.sum) : Fin l.length := ⟨findSumIdx l j, sorry⟩

def findSumIdxWith (l : List ℕ) (j : Fin l.sum) : (i : Fin l.length) × Fin (l.get i) := sorry

@[simp]
theorem ranges_length_eq_self_length {l : List ℕ} : l.ranges.length = l.length := by
  induction l with
  | nil => simp only [List.ranges, List.length_nil]
  | cons n l' ih => simp only [List.ranges, List.length_cons, List.length_map, ih]

@[simp]
theorem ranges_nil : List.ranges [] = [] := rfl

@[simp]
theorem ranges_succ {a : ℕ} {l : List ℕ} :
    List.ranges (a :: l) = range a :: l.ranges.map (map (a + ·)) := rfl

end List

namespace Fin

open Function

theorem partialProd_eq_partialProd_list {α : Type*} {n : ℕ} [Monoid α] (a : Fin n → α) :
    List.partialProd (List.ofFn a) = List.ofFn (Fin.partialProd a) := by sorry
  -- induction l with
  -- | nil => simp [List.partialProd, List.ofFn]
  -- | cons a l' ih => simp [List.partialProd, List.ofFn, ih]

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

def castSum (l : List ℕ) {n : ℕ} (h : n ∈ l) : Fin n → Fin l.sum := fun i =>
  match l with
  | [] => by contradiction
  | n' :: l' => by
    simp only [List.sum_cons]
    by_cases hi : n = n'
    · exact castAdd l'.sum (cast hi i)
    · exact natAdd n' (castSum l' (List.mem_of_ne_of_mem hi h) i)

theorem castSum_castLT {l' : List ℕ} {i : ℕ} (j : Fin i) :
    castSum (i :: l') (by simp) j =
      castLT j (Nat.lt_of_lt_of_le j.isLt (List.le_sum_of_mem (by simp))) := by
  simp [castSum, castAdd, castLE, castLT]

theorem castSum_castAdd {n m : ℕ} (i : Fin n) : castSum [n, m] (by simp) i = castAdd m i := by
  simp [castSum]

def sumCases {l : List ℕ} {motive : Fin l.sum → Sort*}
    (cases : ∀ (n : ℕ) (h : n ∈ l) (i : Fin n), motive (castSum l h i))
    (i : Fin l.sum) : motive i := match l with
  | [] => by simp only [List.sum_nil] at i; exact elim0 i
  | n' :: l' => by
    simp only [List.sum_cons] at i
    by_cases hi : i < n'
    · convert cases n' (by simp) ⟨i.val, hi⟩
      simp [castSum]
    · have hj' : i.val - n' < l'.sum := by sorry
      sorry
      -- refine sumCases (l := l') (motive := motive ∘ natAdd i') ?_ ⟨j.val - i', hj'⟩

end Sum

section Join

variable {n : ℕ}

def map {α β : Fin n → Sort*} (f : (i : Fin n) → α i → β i) (a : (i : Fin n) → α i) :
    (i : Fin n) → β i := fun i => f i (a i)

def range (n : ℕ) : Fin n → ℕ := fun i => i

def ranges {n : ℕ} (a : Fin n → ℕ) : (i : Fin n) → Fin (a i) → ℕ :=
  match n with
  | 0 => fun i => elim0 i
  | n + 1 => fun i => by
    by_cases h : i = 0
    · exact val
    · letI rest := ranges (tail a) (i.pred h)
      simp only [tail, pred, subNat_one_succ] at rest
      exact fun j => rest j + a 0

theorem ranges_eq_ranges_list {a : Fin n → ℕ} :
    List.ofFn (fun i => List.ofFn (ranges a i)) = List.ranges (List.ofFn a) := by
  induction n using Nat.strongRec with
  | ind n IH => sorry

/-- Find the first index `i` such that `k` is smaller than `∑ j < i, a j`, and return `none`
  otherwise.
  -/
def findSumIdx? (a : Fin n → ℕ) (k : ℕ) : Option (Fin n) :=
  find (fun i => k < ∑ j with j < i, a j)
  -- find (fun i => find (fun j => k = ranges a i j) |>.isSome)

#check find_eq_some_iff

theorem findSumIdx?_is_some_iff_le_sum {a : Fin n → ℕ} {k : ℕ} :
    (findSumIdx? a k).isSome ↔ k < ∑ i, a i := by
  sorry

/-- When `k` is less than `∑ i, a i`, `findSumIdx' a k` returns some index `idx < n` -/
def findSumIdx (a : Fin n → ℕ) (k : Fin (∑ i, a i)) : Fin n :=
  (findSumIdx? a k.val).get (findSumIdx?_is_some_iff_le_sum.mpr k.isLt)

def remainderFromSum' (a : Fin n → ℕ) (k : ℕ) : ℕ := by
  letI i := finSuccEquivLast.invFun (findSumIdx? a k)
  exact k - ∑ j with j.1 < i.1, a j

theorem remainderFromSum'_le_next {a : Fin n → ℕ} {k : Fin (∑ i, a i)} :
    remainderFromSum' a k < a (findSumIdx a k) := sorry

def remainderFromSum (a : Fin n → ℕ) (k : Fin (∑ i, a i)) : Fin (a (findSumIdx a k)) :=
  ⟨remainderFromSum' a k, remainderFromSum'_le_next⟩

variable {a : Fin n → ℕ} {α : (i : Fin n) → (j : Fin (a i)) → Sort*}

def finSigmaFinEquiv {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i, n i) where
  toFun := fun ⟨i, j⟩ => ⟨∑ k with k < i, n k + j, sorry⟩
  invFun := fun k => ⟨findSumIdx n k, remainderFromSum n k⟩
  left_inv := sorry
  right_inv := sorry

def join (v : (i : Fin n) → (j : Fin (a i)) → α i j) (k : Fin (∑ i, a i)) :
    α (findSumIdx a k) (remainderFromSum a k) := v (findSumIdx a k) (remainderFromSum a k)

theorem join_addCases : True := sorry

theorem join_eq_addCases : True := sorry

theorem join_eq_join_list : True := sorry

end Join

end Fin
