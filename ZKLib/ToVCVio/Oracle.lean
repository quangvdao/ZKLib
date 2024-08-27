/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio

/-!
  # Deterministic Oracle Simulation

  This is a special case of `simulate` where the `SimOracle` is a deterministic function `f`. We
  allow the oracle to possibly keep some state in addition to providing responses according to `f`.
  We can run an oracle computation to create a return value by replacing oracle calls to
  `DeterministicOracle spec f σ` with function calls to `f`.
-/

open OracleSpec OracleComp

/--
  A function that implements the oracle interface specified by `spec`, and queries no further oracles.
-/
def Oracle (spec : OracleSpec ι) := (i : ι) → spec.domain i → spec.range i


variable [DecidableEq α] [DecidableEq β] [Inhabited β] [Fintype β] [Inhabited γ] [Fintype γ]

-- turn a function into an oracle implementation, while logging queries
-- the stateless oracle introduces a useless `Unit` to the internal state which we mask
-- `simulate` with this will answer queries with `f` and log input and outputs
def oracleize (f : α → β) : (α →ₒ β) →[QueryLog (α →ₒ β)]ₛₒ (α →ₒ β) :=
  (loggingOracle ∘ₛₒ statelessOracle (λ () t ↦ return f t)).maskState
    (Equiv.punitProd (α →ₒ β).QueryLog)

/--
  A deterministic oracle simulation with state defined via `SimOracle`.
-/
def StatefulOracle (spec : OracleSpec ι) (σ : Type) :=
  SimOracle spec emptySpec σ

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α σ : Type}

/--
  Run an oracle computation `OracleComp spec α` with an oracle coming from
  a (deterministic) function `f` that queries no further oracles.

  TODO: add state for `f`
-/
def runWithOracle (f : Oracle spec) : OracleComp spec α → α
  | pure' _ x => x
  | queryBind' i q _ oa => runWithOracle f (oa (f i q))

end OracleComp
