import Jolt.CommitmentScheme.Basic

/-!
  # Trivial Commitment Scheme

  This is the simplest (oracle) commitment scheme, which just sends the data directly.
-/

/-- The trivial polynomial commitment scheme where you just send the polynomial directly -/
class TrivialCommitmentScheme (pp : PParams) (index : Index pp) extends CommitmentScheme pp index where
  Statement := Statement pp index
  Witness := Witness pp index
