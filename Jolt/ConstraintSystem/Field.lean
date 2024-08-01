import Mathlib.FieldTheory.Finite.Basic

/-!
  # Define the field for Jolt
-/

class FromUInt64 (F : Type u) where
  embed : UInt64 ↪ F

class JoltField (F : Type u) extends Field F, Inhabited F, Fintype F, FromUInt64 F where
  decEq : DecidableEq F

instance [JoltField F] : DecidableEq F := JoltField.decEq
