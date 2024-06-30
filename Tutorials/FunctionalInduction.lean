import Mathlib.Tactic.Common

def alternate : (xs ys : List α) → List α
  | [], ys => ys
  | x :: xs, ys => x :: alternate ys xs
termination_by xs ys => xs.length + ys.length

#eval alternate [1, 2, 3] [4, 5, 6]

-- theorem alternate_length_attempt (xs ys : List α) : (alternate xs ys).length = xs.length + ys.length := by
--   induction xs with
--   | nil => simp [alternate]
--   | cons x xs ih =>
--     simp [alternate]
--     -- stuck here due to the goal having `alternate ys xs` but the induction hypothesis is the reverse, `alternate xs ys`
--     sorry

theorem alternate_length (xs ys : List α) : (alternate xs ys).length = xs.length + ys.length := by
  unfold alternate
  split
  next => simp
  next x xs =>
    -- crucial point: we can apply the theorem with the arguments reversed
    have ih := alternate_length ys xs
    simp [ih]
    omega
termination_by xs.length + ys.length

-- more compact proof, but still not great
theorem alternate_length' : (xs ys : List α) → (alternate xs ys).length = xs.length + ys.length
  | [], ys => by simp [alternate]
  | x :: xs, ys => by
    have ih := alternate_length' ys xs
    simp [alternate, ih]
    omega
termination_by xs ys => xs.length + ys.length

/- Functional induction in Lean: every recursive function `f` comes with an induction principle `f.induct` -/
#check alternate.induct

theorem alternate_length_better (xs ys : List α) : (alternate xs ys).length = xs.length + ys.length := by
  induction xs, ys using alternate.induct with
  | case1 ys => simp [alternate]
  | case2 x xs ys ih =>
      simp [alternate, ih]
      omega

theorem alternate_length_best (xs ys : List α) : (alternate xs ys).length = xs.length + ys.length := by
  induction xs, ys using alternate.induct
  all_goals simp [alternate, *] ; try omega


theorem alternate_length_full (xs ys : List α) :
    (alternate xs ys).length = xs.length + ys.length := by
  induction xs, ys using alternate.induct with
  | case1 ys => calc
        (alternate [] ys).length
      _ = ys.length               := by simp only [alternate]
      _ = [].length + ys.length   := by simp
  | case2 x xs ys ih => calc
        (alternate (x :: xs) ys).length
      _ = (x :: alternate ys xs).length  := by simp only [alternate]
      _ = (alternate ys xs).length + 1   := by rfl
      _ = (ys.length + xs.length) + 1    := by rw [ih]
      _ = (x :: xs).length + ys.length   := by simp; omega


def cutN (n : Nat) : (xs : List α) → List (List α)
  | [] => []
  | x::xs => (x::xs.take (n-1)) :: cutN n (xs.drop (n-1))
termination_by xs => xs.length

#check cutN.induct

theorem cutNJoin_best (n : Nat) (xs : List α) : List.join (cutN n xs) = xs := by
  induction xs using cutN.induct n <;> simp [cutN, *]

def destutter : (xs : List Bool) → List Bool
  | [] => []
  | true :: true :: xs => destutter (true :: xs)
  | false :: false :: xs => destutter (false :: xs)
  | x :: xs => x :: destutter xs

theorem length_destutter2 : (destutter xs).length ≤ xs.length := by
  induction xs using destutter.induct <;>
    simp [destutter] at * <;> omega


-- TODO: test out the rest of the examples from (https://lean-lang.org/blog/2024-5-17-functional-induction/
