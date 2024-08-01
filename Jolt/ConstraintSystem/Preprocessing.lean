import Jolt.ConstraintSystem.Constants
import Jolt.ConstraintSystem.Field
import Jolt.ConstraintSystem.Trace
import Jolt.ConstraintSystem.InstructionLookup
import Jolt.ConstraintSystem.MemoryChecking



namespace Jolt

variable (F : Type) [JoltField F]

-- TODO: derive `Repr` for `HashMap`?
-- TODO: replace `HashMap` with just `AssocList`? We don't care too much about performance here
-- We can prove that the keys are distinct, assuming we do preprocessing on a valid `ELF` file
open Lean in
structure BytecodePreprocessing where
  codeSize : UInt64
  vInitFinal : Fin NUM_BYTECODE_VALUE_FIELDS → Array F
  virtualAddressMap : AssocList UInt64 UInt64
deriving Inhabited

structure ReadWriteMemoryPreprocessing where
  minBytecodeAddress : UInt64
  bytecodeBytes : Array UInt8
  programIo : Option JoltDevice
deriving Repr, Inhabited

structure InstructionLookupsPreprocessing where
  subtableToMemoryIndices : Array (Array UInt64)
  instructionToMemoryIndices : Array (Array UInt64)
  memoryToSubtableIndex : Array UInt64
  memoryToDimensionIndex : Array UInt64
  materializedSubtables : Array (Array F)
  numMemories : UInt64
deriving Repr, Inhabited

structure JoltPreprocessing extends
  BytecodePreprocessing F,
  ReadWriteMemoryPreprocessing,
  InstructionLookupsPreprocessing F
deriving Inhabited


-- TODO: will need to add R1CS constraints as part of `JoltPreprocessing`.
-- Will do this after the changes are made to the Rust codebase

-- Generate preprocessing data from `Array ELFInstruction` and `Array (UInt64 × UInt8)`

open Lean in
def BytecodePreprocessing.new (bytecode : Array BytecodeRow) : BytecodePreprocessing F := sorry
-- Id.run do
--   assert! bytecode.size > 0
--   let codeSize := bytecode.size
--   let vInitFinal := Array.range NUM_BYTECODE_VALUE_FIELDS |> Array.map (fun _ => Array.range codeSize |> Array.map (fun _ => 0 : F))
--   let virtualAddressMap := HashMap.empty
--   { codeSize := codeSize, vInitFinal := vInitFinal, virtualAddressMap := virtualAddressMap }

def ReadWriteMemoryPreprocessing.new (memoryInit : Array (UInt64 × UInt8)) :
    ReadWriteMemoryPreprocessing :=
  let minBytecodeAddress := memoryInit.map Prod.fst |> Array.min? |> Option.get!
  let maxBytecodeAddress := memoryInit.map Prod.fst |> Array.max? |> Option.get!
  let size := (maxBytecodeAddress - minBytecodeAddress + 1).toNat
  let emptyArray := mkArray size 0
  let bytecodeBytes := memoryInit.foldl (init := emptyArray)
    (fun acc (addr, byte) =>
      let remappedIndex := (addr - minBytecodeAddress).toNat
      acc.set! remappedIndex byte)
  { minBytecodeAddress := minBytecodeAddress,
    bytecodeBytes := bytecodeBytes,
    programIo := none }


-- TODO: this definition depends on the `InstructionSet` and `SubtableSet`
-- for a given architecture (i.e. RV32IM)
def InstructionLookupsPreprocessing.new : InstructionLookupsPreprocessing F := sorry

def JoltPreprocessing.new (bytecode : Array BytecodeRow) (memoryInit : Array (UInt64 × UInt8)) :
    JoltPreprocessing F :=
  let bytecodePrep := BytecodePreprocessing.new F bytecode
  let memoryPrep := ReadWriteMemoryPreprocessing.new memoryInit
  let instructionLookupsPrep := InstructionLookupsPreprocessing.new F
  { toBytecodePreprocessing := bytecodePrep,
    toReadWriteMemoryPreprocessing := memoryPrep,
    toInstructionLookupsPreprocessing := instructionLookupsPrep }

end Jolt
