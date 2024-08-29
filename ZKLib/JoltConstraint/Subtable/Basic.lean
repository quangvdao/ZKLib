/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Batteries.Data.BitVec.Lemmas
import ZKLib.JoltConstraint.Field
import ZKLib.JoltConstraint.Constants

/-!
  # Interface for Lasso Subtables in Jolt

  This fine defines the basic interface for Lasso subtables.
-/

namespace Jolt

variable (F : Type) [JoltField F]

/- Represents a subtable in the Jolt system

  Each of the two operands is a `m`-bit unsigned integer.

  Compared to the Rust implementation, we have `2 ^ (2 * m) = M`, the size of the materialized table.
 -/
structure LassoSubtable where
  /-- The whole table materialized as a vector of `2 ^ (2 * m)` unsigned 64-bit integers (which is then embedded into field elements).

  We need `m ≤ 64` because we are casting into `UInt64`.
   -/
  materialize (m : Nat) (isLE : m ≤ 64) : Fin (2 ^ (2 * m)) → UInt64

  /-- The multilinear extension of the subtable -/
  evaluateMLE (point : List F) : F
-- deriving Repr, Inhabited, DecidableEq

/-- A subtable is valid if the multilinear extension correctly evaluates to the materialized table. -/
def LassoSubtable.isValid (subtable : LassoSubtable F) : Prop :=
  (m : Nat) → (isLE : m ≤ 64) → (idx : Fin (2 ^ (2 * m))) → subtable.evaluateMLE (List.map (fun b => if b then 1 else 0) idx.val.bits) = FromUInt64.embed (subtable.materialize m isLE idx)


/-- Represents a set of Jolt subtables. -/
structure SubtableSet where
  list : List (LassoSubtable F)
-- deriving Repr, Inhabited, DecidableEq

/-
  Corresponding Rust code:
  ```rust
    fn materialize(&self, M: usize) -> Vec<F> {
      let cutoff = WORD_SIZE % log2(M) as usize;

      let mut entries: Vec<F> = Vec::with_capacity(M);
      for idx in 0..M {
          let (_, lower_bits) = split_bits(idx, cutoff);
          let row = F::from_u64(lower_bits as u64).unwrap();
          entries.push(row);
      }
      entries
    }
  ```
-/

/- Which subtables to cover?

`And`
`DivByZero`
`Eq`
`EqAbs`
`Identity`
`LeftIsZero`
`LeftMsb`
`LtAbs`
`Ltu`
`Mod`
`Or`
`RightIsZero`
`RightMsb`
`SignExtend`
`Sll`
`SraSign`
`Srl`
`Test`
`TruncateOverflow`
`Xor`
`ZeroLsb`

-/

end Jolt