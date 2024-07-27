-- Minimum working example (MWE) to post on Zulip

-- import Mathlib.Algebra.MvPolynomial.Equiv

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Fin.Basic

variable (n : ℕ+)

structure PartialLog (i : Fin (n + 1)) where
  Messages : Fin i → Type
  messages : ∀ j : Fin i, Messages j

structure Log where
  Messages : Fin n → Type
  messages : ∀ j : Fin n, Messages j

def Log.toPartial (log : Log n) (i : Fin (n + 1)) :
    PartialLog n i where
  Messages := fun j => log.Messages j
  messages := fun j => log.messages j

def PartialLog.toFull (pLog : PartialLog n n) : Log n where
  /-
  application type mismatch
    pLog.Messages j
  argument
    j
  has type
    Fin ↑n : Type
  but is expected to have type
    Fin ↑↑↑n : Type
  -/
  /-
  ↑n := (PNat.val n)
  ↑↑n := @Nat.cast (Fin (↑n + 1)) Fin.instNatCast ↑n : Fin (↑n + 1)
  ↑↑↑n := @Fin.val (↑n + 1) ↑↑n : ℕ
  -/
  Messages := fun j => pLog.Messages ⟨j, by simp⟩
  messages := fun j => pLog.messages ⟨j, by simp⟩


noncomputable section

open Polynomial
open MvPolynomial

def testPoly : MvPolynomial (Fin 2) ℕ := X 0 * X 0 + X 1

def testPoly2 : Polynomial (MvPolynomial (Fin 1) ℕ) := finSuccEquiv ℕ 1 testPoly

-- theorem testPoly2_eval : testPoly2.eval 2 = 4 + X 0 := by
--   simp only [testPoly2, testPoly]
--   simp only [ map_add, map_mul]
--   simp only [MvPolynomial.finSuccEquiv_X_zero]
--   have : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by rfl
--   rw [this]
--   simp only [MvPolynomial.finSuccEquiv_X_succ]
--   simp
--   congr
--   . norm_num

theorem testPoly2_eval : testPoly2.eval 2 = 4 + X 0 := by
  simp [testPoly2, testPoly]
  congr
  · norm_num
  · have : (1 : Fin 2) = Fin.succ 0 := by rfl
    rw [this]
    rw [Fin.cases_succ]
    simp


def double_fin (n : Nat) : Fin (n + n) → Nat
  | ⟨k, _⟩ => (Fin.cases 0 (fun k' : Fin (n + 1) => 2 * k') k)

#eval double_fin 5 ⟨5, by decide⟩

example : double_fin 5 ⟨5, by decide⟩ = 8 := by
  simp [double_fin]
  have : (5 : Fin 7) = Fin.succ 4 := by rfl
  rw [this]
  simp [Fin.cases_succ]
  rfl

end

-- def IteratedPolynomial (n : ℕ) : (F : Type _) × (CommSemiring F) × List F :=
--   match n with
--   | 0 => ⟨ ℕ, inferInstance, [(1 : ℕ)] ⟩
--   | n + 1 =>
--     let ⟨ Fn, _, elts ⟩ := IteratedPolynomial n
--     ⟨ Polynomial Fn, inferInstance, [(X : Polynomial Fn)] ++ elts.map (fun x => C x) ⟩

-- def iterZero : Type _ := (IteratedPolynomial 0).1
-- def iterOne : Type _ := (IteratedPolynomial 1).1


-- @[simp]
-- theorem iterZero_is_nat : iterZero = ℕ := rfl

-- @[simp]
-- theorem iterOne_is_poly : iterOne = Polynomial ℕ := rfl

-- theorem iterPoly_is_mvPoly (n : ℕ) : (IteratedPolynomial n).1 =
