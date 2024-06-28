import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Control.Monad.Basic
-- import Jolt.Data.SPMF

/-!
# Formalism of Interactive Oracle Proofs

We define (public-coin) interactive oracle proofs (IOPs). This is an interactive protocol between a prover and a verifier with the following format:

  - At the beginning, the prover and verifier both hold a public statement x (and potentially have access to some public parameters pp). The prover may also hold some private state which in particular may contain a witness w to the statement x.

  - In each round, the verifier sends some random challenges, and the prover sends back responses to the challenges. The responses are received as oracles by the verifier. The verifier only sees some abstract representation of the responses, and is only allowed to query these oracles in specific ways (i.e. point queries, polynomial evaluation queries, tensor queries).

  - At each step, the verifier may make oracle queries and perform some checks on the responses so far. At the end of the interaction, the verifier outputs a bit indicating accept or reject; it may also output the bit earlier at any round.

Note: the definition of IOPs as defined above generalizes those found in the literature. It has the same name as the interactive protocol in the [BCS16] paper, but it is strictly more general. We call the IOP defined in [BCS16] as a "point IOP". We also get "polynomial IOP" [BCG+19] and "tensor IOP" [BCG20] (and other kinds of IOPs) from our definition.

We formalize IOPs with the following objects:

  - The prover and verifier are modeled as probabilistic, stateful computations, where the prover outputs oracles, and the verifier has black-box access to oracles.

-/


/--
  Define the class of Public-Coin Interactive Oracle Proofs
-/
class IOP (PParams : Type _) (Index : PParams → Type _) where
  numRounds : ℕ
  Statement : Type _
  PrvState : Type _
  PrvRand : Type _
  Message : Type _
  Challenge : Type _
  OQuery : Type _
  OResponse : Type _
  oracle : Message → OQuery → OResponse
  honestProver : Statement → PrvState → PrvRand → List Challenge → List Message × PrvState
  honestVerifier : Statement → List (OQuery → OResponse) → List Challenge → Prop

/--
  Collection of IOPs with the same public parameters `PParams` but possible different indices `Index`
-/
structure IOPFamily (PParams : Type _) where
  Index : PParams → Type _
  [IOP : IOP PParams Index]

attribute [instance] IOPFamily.IOP


namespace IOP

/-- Type of an IOP prover -/
@[simp]
def Prover (Iop : IOP pp index) : Type _ := Iop.Statement → Iop.PrvState → Iop.PrvRand → List Iop.Challenge → List Iop.Message × Iop.PrvState

/-- Type of an IOP verifier -/
@[simp]
def Verifier (Iop : IOP pp index) : Type _ := Iop.Statement → List (Iop.OQuery → Iop.OResponse) → List Iop.Challenge → Prop


def execution (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) : Prop :=
  sorry


def completeness (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) : Prop :=
  sorry


def soundness (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) (soundnessBound : Rat) : Prop :=
  sorry


def roundByRoundSoundness (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) (badFunction : List Iop.Message → List Iop.Challenge → Prop) : Prop :=
  sorry

def zeroKnowledge (Iop : IOP pp index) (verifier : Verifier Iop) (prover : Prover Iop) : Prop :=
  sorry

end IOP
