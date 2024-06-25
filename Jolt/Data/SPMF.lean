import Std.Data.Rat.Basic
import Std.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.Distributions.Uniform

/-! `SPMF` is a computable type representing sub-probability distributions with finite support. -/
def SPMF (α : Type) := List α
-- def SPMF (α : Type) [BEq α] [Hashable α] := Std.HashMap α Rat

#check Std.HashMap

namespace SPMF

def length {α : Type} (d : SPMF α) : Rat := List.length d

def count {α : Type} [BEq α] (d : SPMF α) (a : α) : Rat := List.count a d

def pure {α : Type} (a : α) := List.pure a

def bind {α β : Type} (d : SPMF α) (f : α → SPMF β) : SPMF β :=
  List.bind d f

instance Monad : Monad SPMF := {
  pure := @pure,
  bind := @bind
}

def toFun {α : Type} [BEq α] (d : SPMF α) : α → Rat :=
  fun a => d.count a / d.length

def uniformOfFintype (α : Type) [Fintype α] [Nonempty α] : SPMF α := [] -- TODO implement

end SPMF
