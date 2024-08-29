/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.CommitmentScheme.Basic

/-!
  # Trivial Commitment Scheme

  This is the simplest (oracle) commitment scheme, which just sends the data directly.
-/

/-- The trivial polynomial commitment scheme where you just send the polynomial directly -/
class TrivialCommitmentScheme extends CommitmentScheme where
  Statement := Statement
  Witness := Witness