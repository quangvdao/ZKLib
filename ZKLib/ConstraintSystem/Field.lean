import Mathlib.FieldTheory.Finite.Basic
import ZKLib.Data.ScalarPrimeField.Bn254
import Batteries.Data.UInt

/-!
  # Define the field for Jolt
-/

instance : Function.Injective UInt64.toNat :=
  fun x y h => UInt64.ext (by simp [h])

class FromUInt64 (F : Type u) where
  embed : UInt64 ↪ F

class JoltField (F : Type u) extends Field F, Inhabited F, Fintype F, FromUInt64 F where
  decEq : DecidableEq F

instance [JoltField F] : DecidableEq F := JoltField.decEq

-- Needs to make use of the fact that `UInt64` is a bijection with `Fin 2^64`
open Function in
instance : FromUInt64 BN254.ScalarField where
  embed := ⟨fun j => j.toNat, by unfold Function.Injective ; intro x y ; simp ; sorry⟩
