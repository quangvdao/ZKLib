import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Control.Monad.Basic
import Jolt.Data.SPMF

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



-- Type signature for a single round of the prover
-- Takes in an instance, a prover state, a list of challenges for the current round, and a randomness value, then outputs a response and a new prover state
def proverRound (Instance ProverState Challenge Response : Type _) : Type _ :=
  Instance → List Challenge → ProverState → SPMF (Response × ProverState)

universes u v w y

variable (σ : Type u) (Input : Type v) (Output: Type w)

def State := String

structure Party (α : Type y) where
  run : State → Input → State × Output

class PartyM (m : Type _ → Type _) where
  getInput : m (Option Input)
  returnOutput : Output → m Unit



-- Define the structure for the interactive proof system
structure IOP (ProverType : Type _) (VerifierType : Type _) where
  honestProver : ProverType
  honestVerifier : VerifierType

-- Define the prove function within the context of IOP
namespace IOP

def execution (ip : IOP Instance VerifierState Response Randomness Challenge)
          (vs : VerifierState) (prv : proverRound Instance ProverState Challenge Randomness Response)
          (ps : ProverState) (inst : Instance) (rnd : Randomness) (rounds : List (Challenge × Randomness)) : Bool :=
  match rounds with
  | [] => ip.ver0 inst vs
  | (round_data, rnd') :: remaining_rounds =>
    let (resp, ps') := prv inst round_data (remaining_rounds.map Prod.fst) rnd ps in
    let (ok, inst', vs') := ip.ver1 inst resp rnd' round_data (remaining_rounds.map Prod.fst) vs in
    ok && prove ip vs' prv ps' inst' rnd' remaining_rounds

end IOP
