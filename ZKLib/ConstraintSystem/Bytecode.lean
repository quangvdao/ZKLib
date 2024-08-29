/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.ConstraintSystem.Constants
import ZKLib.ConstraintSystem.Field
import ZKLib.ConstraintSystem.Trace

/-!
  # The bytecode checking of Jolt

  This describes the read-only memory checking part for the bytecode in Jolt. Essentially, `Bytecode.Preprocessing` contains the information needed to check the bytecode witness.
-/


namespace Jolt

variable (F : Type) [JoltField F]

namespace Bytecode

-- TODO: derive `Repr` for `HashMap`?
-- TODO: replace `HashMap` with just `AssocList`? We don't care too much about performance here
-- We can prove that the keys are distinct, assuming we do preprocessing on a valid `ELF` file
structure Preprocessing where
  codeSize : UInt64
  vInitFinal : Fin NUM_BYTECODE_VALUE_FIELDS → Array F
  virtualAddressMap : Array (UInt64 × UInt64)
deriving Repr, Inhabited, DecidableEq


-- Generate preprocessing data from `Array ELFInstruction` and `Array (UInt64 × UInt8)`

def Preprocessing.new (bytecode : Array Row) : Preprocessing F := sorry
-- Id.run do
--   assert! bytecode.size > 0
--   let codeSize := bytecode.size
--   let vInitFinal := Array.range NUM_BYTECODE_VALUE_FIELDS |> Array.map (fun _ => Array.range codeSize |> Array.map (fun _ => 0 : F))
--   let virtualAddressMap := HashMap.empty
--   { codeSize := codeSize, vInitFinal := vInitFinal, virtualAddressMap := virtualAddressMap }

structure Witness where
  readWriteAddress : Array F
  readWriteValue : Fin NUM_BYTECODE_VALUE_FIELDS → Array F
  readTimestamp : Array F
  finalBytecodeTimestamp : Array F
deriving Repr, Inhabited, DecidableEq

def isValid (preprocessing : Preprocessing F) (wit : Witness F) : Prop := sorry

end Bytecode

end Jolt