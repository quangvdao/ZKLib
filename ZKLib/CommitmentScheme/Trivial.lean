import ZKLib.CommitmentScheme.Basic

/-!
  # Trivial Commitment Scheme

  This is the simplest (oracle) commitment scheme, which just sends the data directly.
-/

/-- The trivial polynomial commitment scheme where you just send the polynomial directly -/
class TrivialCommitmentScheme extends CommitmentScheme where
  Statement := Statement
  Witness := Witness
