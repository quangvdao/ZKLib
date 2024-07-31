import Jolt.Relation.R1CS
import Jolt.ConstraintSystem.Constants
import Jolt.ConstraintSystem.Field



namespace Jolt

section Memory

inductive MemoryOpRead where
  | RS1_Read
  | RS2_Read
  | RD_Read
  | RAM_Read_Byte0
  | RAM_Read_Byte1
  | RAM_Read_Byte2
  | RAM_Read_Byte3
deriving Repr, Inhabited, DecidableEq

def MemoryOpRead.toFin (mOp : MemoryOpRead) : Fin MEMORY_OPS_PER_INSTRUCTION :=
  match mOp with
  | RS1_Read => 0
  | RS2_Read => 1
  | RD_Read => 2
  | RAM_Read_Byte0 => 3
  | RAM_Read_Byte1 => 4
  | RAM_Read_Byte2 => 5
  | RAM_Read_Byte3 => 6

instance : Coe MemoryOpRead (Fin MEMORY_OPS_PER_INSTRUCTION) := ⟨MemoryOpRead.toFin⟩

instance : Equiv MemoryOpRead (Fin MEMORY_OPS_PER_INSTRUCTION) where
  toFun := MemoryOpRead.toFin
  invFun := fun n => MemoryOpRead.ofNat (n : Nat)
  left_inv := by intro x ; rcases x <;> decide
  right_inv := by decide

instance : Fintype MemoryOpRead := Fintype.ofEquiv (Fin MEMORY_OPS_PER_INSTRUCTION) instEquivMemoryOpReadFinOfNatNat.symm


inductive MemoryOpWrite where
  | RD_Write
  | RAM_Write_Byte0
  | RAM_Write_Byte1
  | RAM_Write_Byte2
  | RAM_Write_Byte3
deriving Repr, Inhabited, DecidableEq

def MemoryOpWrite.toFin (mOp : MemoryOpWrite) : Fin NUM_MEM_WRITES :=
  match mOp with
  | RD_Write => 0
  | RAM_Write_Byte0 => 1
  | RAM_Write_Byte1 => 2
  | RAM_Write_Byte2 => 3
  | RAM_Write_Byte3 => 4

instance : Coe MemoryOpWrite (Fin NUM_MEM_WRITES) := ⟨MemoryOpWrite.toFin⟩

instance : Equiv MemoryOpWrite (Fin NUM_MEM_WRITES) where
  toFun := MemoryOpWrite.toFin
  invFun := fun n => MemoryOpWrite.ofNat (n : Nat)
  left_inv := by intro x ; rcases x <;> decide
  right_inv := by decide

instance : Fintype MemoryOpWrite := Fintype.ofEquiv (Fin NUM_MEM_WRITES) instEquivMemoryOpWriteFinOfNatNat.symm

end Memory

section Bytecode

inductive BytecodeValues where
  | ELFAddress
  | Bitflags
  | RS1
  | RS2
  | RD
  | Imm
deriving Repr, Inhabited, DecidableEq

def BytecodeValues.toFin (bValue : BytecodeValues) : Fin NUM_BYTECODE_VALUE_FIELDS :=
  match bValue with
  | BytecodeValues.ELFAddress => 0
  | BytecodeValues.Bitflags => 1
  | BytecodeValues.RS1 => 2
  | BytecodeValues.RS2 => 3
  | BytecodeValues.RD => 4
  | BytecodeValues.Imm => 5

instance : Coe BytecodeValues (Fin NUM_BYTECODE_VALUE_FIELDS) := ⟨BytecodeValues.toFin⟩

instance : Equiv BytecodeValues (Fin NUM_BYTECODE_VALUE_FIELDS) where
  toFun := BytecodeValues.toFin
  invFun := fun n => BytecodeValues.ofNat (n : Nat)
  left_inv := by intro x ; rcases x <;> decide
  right_inv := by decide

instance : Fintype BytecodeValues := Fintype.ofEquiv (Fin NUM_BYTECODE_VALUE_FIELDS) instEquivBytecodeValuesFinOfNatNat.symm

end Bytecode


section Flags

inductive CircuitFlags where
  | OpFlags_IsRs1Rs2
  | OpFlags_IsImm
  | OpFlags_IsLoad
  | OpFlags_IsStore
  | OpFlags_IsJmp
  | OpFlags_IsBranch
  | OpFlags_LookupOutToRd
  | OpFlags_SignImm
  | OpFlags_IsConcat
  | OpFlags_IsVirtualSequence
  | OpFlags_IsVirtual
deriving Repr, Inhabited, DecidableEq

def CircuitFlags.toFin (cFlag : CircuitFlags) : Fin NUM_CIRCUIT_FLAGS :=
  match cFlag with
  | OpFlags_IsRs1Rs2 => 0
  | OpFlags_IsImm => 1
  | OpFlags_IsLoad => 2
  | OpFlags_IsStore => 3
  | OpFlags_IsJmp => 4
  | OpFlags_IsBranch => 5
  | OpFlags_LookupOutToRd => 6
  | OpFlags_SignImm => 7
  | OpFlags_IsConcat => 8
  | OpFlags_IsVirtualSequence => 9
  | OpFlags_IsVirtual => 10

instance : Coe CircuitFlags (Fin NUM_CIRCUIT_FLAGS) := ⟨CircuitFlags.toFin⟩

instance : Equiv CircuitFlags (Fin NUM_CIRCUIT_FLAGS) where
  toFun := CircuitFlags.toFin
  invFun := fun n => CircuitFlags.ofNat (n : Nat)
  left_inv := by intro x ; rcases x <;> decide
  right_inv := by decide

instance : Fintype CircuitFlags := Fintype.ofEquiv (Fin NUM_CIRCUIT_FLAGS) instEquivCircuitFlagsFinOfNatNat.symm

inductive InstructionFlags where
  | IF_Add
  | IF_Sub
  | IF_And
  | IF_Or
  | IF_Xor
  | IF_Lb
  | IF_Lh
  | IF_Sb
  | IF_Sh
  | IF_Sw
  | IF_Beq
  | IF_Bge
  | IF_Bgeu
  | IF_Bne
  | IF_Slt
  | IF_Sltu
  | IF_Sll
  | IF_Sra
  | IF_Srl
  | IF_Movsign
  | IF_Mul
  | IF_MulU
  | IF_MulHu
  | IF_Virt_Adv
  | IF_Virt_Assert_LTE
  | IF_Virt_Assert_VALID_SIGNED_REMAINDER
  | IF_Virt_Assert_VALID_UNSIGNED_REMAINDER
  | IF_Virt_Assert_VALID_DIV0
deriving Repr, Inhabited, DecidableEq

def InstructionFlags.toFin (iFlag : InstructionFlags) : Fin NUM_INSTRUCTION_FLAGS :=
  match iFlag with
  | IF_Add => 0
  | IF_Sub => 1
  | IF_And => 2
  | IF_Or => 3
  | IF_Xor => 4
  | IF_Lb => 5
  | IF_Lh => 6
  | IF_Sb => 7
  | IF_Sh => 8
  | IF_Sw => 9
  | IF_Beq => 10
  | IF_Bge => 11
  | IF_Bgeu => 12
  | IF_Bne => 13
  | IF_Slt => 14
  | IF_Sltu => 15
  | IF_Sll => 16
  | IF_Sra => 17
  | IF_Srl => 18
  | IF_Movsign => 19
  | IF_Mul => 20
  | IF_MulU => 21
  | IF_MulHu => 22
  | IF_Virt_Adv => 23
  | IF_Virt_Assert_LTE => 24
  | IF_Virt_Assert_VALID_SIGNED_REMAINDER => 25
  | IF_Virt_Assert_VALID_UNSIGNED_REMAINDER => 26
  | IF_Virt_Assert_VALID_DIV0 => 27

instance : Coe InstructionFlags (Fin NUM_INSTRUCTION_FLAGS) := ⟨InstructionFlags.toFin⟩

instance : Equiv InstructionFlags (Fin NUM_INSTRUCTION_FLAGS) where
  toFun := InstructionFlags.toFin
  invFun := fun n => InstructionFlags.ofNat (n : Nat)
  left_inv := by intro x ; rcases x <;> decide
  right_inv := by decide

instance : Fintype InstructionFlags := Fintype.ofEquiv (Fin NUM_INSTRUCTION_FLAGS) instEquivInstructionFlagsFinOfNatNat.symm

end Flags

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [FromUInt64 F]

-- TODO: figure out how `JoltWitness` is transformed into `R1CSWitness`

-- TODO: describe `inductive` types that enumerate / give names to each of the multiple vectors

structure R1CSWitness where
  paddedTraceLength : UInt64
  -- `PcIn`
  programCounter : Fin paddedTraceLength.toNat → F
  -- `Bytecode_A`
  bytecodeAddress : Fin paddedTraceLength.toNat → F
  -- `Bytecode_ELFAddress`, `Bytecode_Bitflags`, `Bytecode_RS1`, `Bytecode_RS2`, `Bytecode_RD`, `Bytecode_Imm`
  bytecodeValue : BytecodeValues → Fin paddedTraceLength.toNat → F
  -- `RAM_A`
  readWriteMemoryAddress : Fin paddedTraceLength.toNat → F
  -- `RS1_Read`, `RS2_Read`, `RD_Read`, `RAM_Read_Byte0-3`
  readMemoryValues : MemoryOpRead → Fin paddedTraceLength.toNat → F
  -- `RD_Write`, `RAM_Write_Byte0-3`
  writeMemoryValue : MemoryOpWrite → Fin paddedTraceLength.toNat → F
  -- `ChunksX_0-3`
  chunksX : Fin NUM_BYTES_IN_WORD → Fin paddedTraceLength.toNat → F
  -- `ChunksY_0-3`
  chunksY : Fin NUM_BYTES_IN_WORD → Fin paddedTraceLength.toNat → F
  -- `ChunksQ_0-3`
  chunksQuery : Fin NUM_BYTES_IN_WORD → Fin paddedTraceLength.toNat → F
  -- `LookupOutput`
  lookupOutput : Fin paddedTraceLength.toNat → F
  -- `CircuitFlags`
  circuitFlags : CircuitFlags → Fin paddedTraceLength.toNat → F
  -- `InstructionFlags`
  instructionFlags : InstructionFlags → Fin paddedTraceLength.toNat → F


-- Copying the constraints being enforced from the Jolt codebase
-- TODO: converting these constraints into R1CS matrices and cross-validating with Jolt's

def R1CSWitness.isBinaryFlags (wit : R1CSWitness F) :=
  ∀ cFlag : CircuitFlags, ∀ iFlag : InstructionFlags, ∀ i : Fin wit.paddedTraceLength.toNat,
    (wit.circuitFlags cFlag i = 0 ∨ wit.circuitFlags cFlag i = 1) ∧
    (wit.instructionFlags iFlag i = 0 ∨ wit.instructionFlags iFlag i = 1)


def R1CSWitness.isEqual (wit : R1CSWitness F) :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    wit.programCounter i = wit.bytecodeAddress i

-- TODO: check if this is big-endian
def R1CSWitness.packFlagsBE (wit : R1CSWitness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => ∑ cFlag : CircuitFlags, (wit.circuitFlags cFlag i) * (2 ^ cFlag.toFin.val)
    + (2 ^ NUM_CIRCUIT_FLAGS) *
      ∑ iFlag : InstructionFlags, (wit.instructionFlags iFlag i) * (2 ^ iFlag.toFin.val)


def R1CSWitness.isEqualPacked (wit : R1CSWitness F) :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    wit.packFlagsBE F i = wit.bytecodeValue BytecodeValues.Bitflags i


def R1CSWitness.realPc (wit : R1CSWitness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => 4 * wit.programCounter i + (FromUInt64.embedding PC_START_ADDRESS - FromUInt64.embedding PC_NOOP_SHIFT)


def R1CSWitness.x (wit : R1CSWitness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => if (wit.circuitFlags CircuitFlags.OpFlags_IsRs1Rs2 i = 1)
    then wit.realPc F i else wit.readMemoryValues MemoryOpRead.RS1_Read i


def R1CSWitness.y (wit : R1CSWitness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => if (wit.circuitFlags CircuitFlags.OpFlags_IsImm i = 1)
    then wit.bytecodeValue BytecodeValues.Imm i else wit.readMemoryValues MemoryOpRead.RS2_Read i


def R1CSWitness.signedOutput (wit : R1CSWitness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.bytecodeValue BytecodeValues.Imm i - (4294967295 + 1)


def R1CSWitness.immSigned (wit : R1CSWitness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => if (wit.circuitFlags CircuitFlags.OpFlags_SignImm i = 1)
    then wit.signedOutput F i else wit.bytecodeValue BytecodeValues.Imm i


def R1CSWitness.isLoadOrStore (wit : R1CSWitness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.circuitFlags CircuitFlags.OpFlags_IsLoad i + wit.circuitFlags CircuitFlags.OpFlags_IsStore i


def R1CSWitness.isEqualConditionalIsLoadOrStore (wit : R1CSWitness F) (memoryStart : UInt64) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat, if (wit.isLoadOrStore F i ≠ 0)
    then (wit.readMemoryValues MemoryOpRead.RS1_Read i + wit.immSigned F i
      = wit.readWriteMemoryAddress i + FromUInt64.embedding memoryStart)
    else True


def R1CSWitness.isEqualConditionalIsLoad (wit : R1CSWitness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat, if (wit.circuitFlags CircuitFlags.OpFlags_IsLoad i = 1)
    then
      (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte0 i = wit.writeMemoryValue MemoryOpWrite.RAM_Write_Byte0 i) &&
      (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte1 i = wit.writeMemoryValue MemoryOpWrite.RAM_Write_Byte1 i) &&
      (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte2 i = wit.writeMemoryValue MemoryOpWrite.RAM_Write_Byte2 i) &&
      (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte3 i = wit.writeMemoryValue MemoryOpWrite.RAM_Write_Byte3 i)
    else True


def R1CSWitness.packedLoadStoreLE (wit : R1CSWitness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.readMemoryValues MemoryOpRead.RAM_Read_Byte0 i +
    (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte1 i) * (2 ^ 8) +
    (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte2 i) * (2 ^ 16) +
    (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte3 i) * (2 ^ 24)



/-
  Missing checks:

  - If `IsStore`, then `packedLoadStore = LookupOutput`

  - If `IfAdd`, then `packedQuery = x + y`

  - If `IfSub`, then `packedQuery = x - y + (4294967295 + 1)`

  - If `IsLoad`, then `packedQuery = packedLoadStore`

  - If `IsStore`, then `packedQuery = RS2_Read`

  etc.

-/




-- Do all of the checks above
def R1CSWitness.isValid (witness : R1CSWitness F) : Prop := sorry





end Jolt
