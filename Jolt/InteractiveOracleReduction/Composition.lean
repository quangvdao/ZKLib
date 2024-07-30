import Jolt.InteractiveOracleReduction.Basic

/-!
  # Composition of IORs

  We define two kinds of compositions with IORs.

  ## Composing two IORs with compatible relations

  We compose an IOR for reducing relations R1 => R2 with another IOR for reducing relations R2 =>
  R3. This gives us an IOR for reducing relations R1 => R3.

  ## Composing an IOR with a commitment scheme

  We compose an IOR with a commitment scheme that is compatible with the oracle type of a message.
  The commitment scheme itself may be an IOP for the corresponding oracle opening relation.
-/
