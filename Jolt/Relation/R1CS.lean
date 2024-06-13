import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Hadamard
import Jolt.Relations.Basic

/-!
# R1CS

This file defines the R1CS (Rank-1 Constraint System) relation.

-/

open Matrix

structure R1CS (R : Type) [Inhabited R] [Ring R] where
  m : Nat -- number of columns
  inputSize : Nat
  witnessSize : Nat
  -- TODO: define n to be this sum
  A : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
  B : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
  C : Matrix (Fin m) (Fin (1 + inputSize + witnessSize)) R
  x : Fin inputSize → R
  w : Fin witnessSize → R


namespace R1CS

variable {R : Type} [Inhabited R] [Ring R]

def satisfied (r : R1CS R) : Prop :=
  let z : Fin (1 + r.inputSize + r.witnessSize) → R := Fin.append (Fin.append (λ _ => 1 : Fin 1 → R) r.x) r.w
  (r.A *ᵥ z) * (r.B *ᵥ z) = (r.C *ᵥ z)


end R1CS
