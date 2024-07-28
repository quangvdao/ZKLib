/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.SimSemantics.Simulate

/-!
  # Deterministic Oracle Simulation

  This is a special case of `simulate` where the `SimOracle` is a deterministic function `f`. We
  allow the oracle to possibly keep some state in addition to providing responses according to `f`.
  We can run an oracle computation to create a return value by replacing oracle calls to
  `DeterministicOracle spec f σ` with function calls to `f`.
-/

open OracleSpec

/--
  A deterministic oracle simulation.
-/
def DeterministicOracle {ι : Type} (spec : OracleSpec ι) (σ : Type) :=
  SimOracle spec emptySpec σ

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α σ : Type}

/--
  Run an oracle computation `OracleComp spec α` with an oracle coming from
  a deterministic function `f`.

  TODO: add state for `f`
-/
def deterministicRun (f : (i : ι) → spec.domain i → spec.range i) : OracleComp spec α → α
  | pure' _ x => x
  | queryBind' i q _ oa => deterministicRun f (oa (f i q))

end OracleComp
