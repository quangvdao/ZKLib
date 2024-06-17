import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Finite.GaloisField
-- import Mathlib.Data.Polynomial.Basic

/-!
# Binary Tower Field

Define the binary tower field GF(2^{2^k}) as an iterated quadratic extension of GF(2).

-/

noncomputable section

open Polynomial

#check Polynomial.C 1

notation:10 "GF(" term:10 ")" => GaloisField term 1

#check (X + 1 : GaloisField 3 3)

class FieldWithDistinguishedElements (F : Type _) extends Field F where
  distinguishedElements : List F

def AbstractBTF (k : ℕ) : FieldWithDistinguishedElements :=
  | 0 => GaloisField 2 1
  | 1 => AdjoinRoot (X^2 + X + 1 : Polynomial (GaloisField 2 1))
  | k + 1 => sorry -- Quotient (Polynomial (AbstractBTF k)) (X^2 + X + 1)

end

/- Concrete implementation of BTF uses BitVec -/
