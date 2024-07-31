import Mathlib.FieldTheory.Finite.Basic


/-!
  # Define the field for Jolt
-/

class FromUInt64 (F : Type u) where
  embedding : UInt64 ↪ F
