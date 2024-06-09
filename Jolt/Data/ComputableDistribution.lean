import Std.Data.Rat.Basic
import Std.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.Distributions.Uniform

section PMF

/-- A type analogous to `PMF` that supports computable operations. -/
def ComputableDistribution (α : Type) := List α
-- def ComputableDistribution (α : Type) [BEq α] [Hashable α] := Std.HashMap α Rat


def ComputableDistribution.length {α : Type} (d : ComputableDistribution α) : Rat := List.length d

def ComputableDistribution.count {α : Type} [BEq α] (d : ComputableDistribution α) (a : α) : Rat := List.count a d

def ComputableDistribution.pure {α : Type} (a : α) := List.pure a

def ComputableDistribution.bind {α β : Type} (d : ComputableDistribution α) (f : α → ComputableDistribution β) : ComputableDistribution β :=
  List.bind d f

instance ComputableDistribution.Monad : Monad ComputableDistribution := {
  pure := @ComputableDistribution.pure,
  bind := @ComputableDistribution.bind
}

def ComputableDistribution.toFun {α : Type} [BEq α] (d : ComputableDistribution α) : α → Rat :=
  fun a => d.count a / d.length

def ComputableDistribution.uniformOfFintype (α : Type) [Fintype α] [Nonempty α] : ComputableDistribution α := [] -- TODO implement

end PMF
