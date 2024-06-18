import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Adjoin.Basic
-- import Mathlib.Data.Polynomial.Basic

/-!
# Binary Tower Field

Define the binary tower field GF(2^{2^k}) as an iterated quadratic extension of GF(2).

-/

noncomputable section

open Polynomial

notation:10 "GF(" term:10 ")" => GaloisField term 1

#check (AdjoinRoot.mk (X^2 + X + 1 : Polynomial (GaloisField 2 1))).toFun X

#check GaloisField 2 1

def func (k : ℕ) : ℕ :=
  match k with
  | 0 => 0
  | k + 1 => new_k
    where new_k := k + 1

def someType : (F : Type _) × List F := ⟨ Nat, ([1] : List Nat) ⟩

#check (F : Type _) × List F

-- structure FieldWithDistinguishedElements (F : Type _) [Field F] where
--   distinguishedElements : List F

def AbstractBTF (k : ℕ) : (F : Type _) × List F :=
  match k with
  | 0 =>
    let F := GaloisField 2 1
    have : Inhabited F := inferInstance
    have : Semiring F := inferInstance
    ⟨ F, [(1 : F)] ⟩
  | k + 1 =>
    let ⟨ F, elements ⟩ := AbstractBTF k
    have : Semiring F := inferInstance
    let newF := AdjoinRoot (X^2 + elements.getLastD * X + 1 : Polynomial F)
    have : Semiring newF := inferInstance
    let newX := AdjoinRoot.root (X^2 + elements.getLastD * X + 1 : Polynomial F)
    ⟨ newF, elements.map (fun x => AdjoinRoot.of.toFun x) ++ [newX] ⟩


end

/- Concrete implementation of BTF uses BitVec -/
