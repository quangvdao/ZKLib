import Jolt.Relation.R1CS
import Jolt.ConstraintSystem.Constants
import Jolt.ConstraintSystem.Field
-- import Mathlib.Data.FinEnum


-- namespace FinEnum

-- TODO: add `FinEnum` supporting lemmas, then derive `FinEnum` instances for the `enum` types below

-- variable {α : Type u}

-- @[simp]
-- lemma finset_card [FinEnum α] : Finset.card (univ : Finset α) = card α := by simp



-- end FinEnum


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

-- instance : FinEnum MemoryOpRead := ⟨MEMORY_OPS_PER_INSTRUCTION, instEquivMemoryOpReadFinOfNatNat⟩

instance : Fintype MemoryOpRead :=
  Fintype.ofEquiv (Fin MEMORY_OPS_PER_INSTRUCTION) instEquivMemoryOpReadFinOfNatNat.symm

@[simp]
lemma MemoryOpRead_card : Fintype.card MemoryOpRead = MEMORY_OPS_PER_INSTRUCTION :=
  by simp [Fintype.ofEquiv_card]


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

-- instance : FinEnum MemoryOpWrite := ⟨NUM_MEM_WRITES, instEquivMemoryOpWriteFinOfNatNat⟩

instance : Fintype MemoryOpWrite :=
  Fintype.ofEquiv (Fin NUM_MEM_WRITES) instEquivMemoryOpWriteFinOfNatNat.symm

@[simp]
lemma MemoryOpWrite_card : Fintype.card MemoryOpWrite = NUM_MEM_WRITES := by
  simp [Fintype.ofEquiv_card]

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

-- instance : FinEnum BytecodeValues := ⟨NUM_BYTECODE_VALUE_FIELDS, instEquivBytecodeValuesFinOfNatNat⟩

instance : Fintype BytecodeValues :=
  Fintype.ofEquiv (Fin NUM_BYTECODE_VALUE_FIELDS) instEquivBytecodeValuesFinOfNatNat.symm

@[simp]
lemma BytecodeValues_card : Fintype.card BytecodeValues = NUM_BYTECODE_VALUE_FIELDS := by
  simp [Fintype.ofEquiv_card]

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

-- instance : FinEnum CircuitFlags := ⟨NUM_CIRCUIT_FLAGS, instEquivCircuitFlagsFinOfNatNat⟩

instance : Fintype CircuitFlags :=
  Fintype.ofEquiv (Fin NUM_CIRCUIT_FLAGS) instEquivCircuitFlagsFinOfNatNat.symm

@[simp]
lemma CircuitFlags_card : Fintype.card CircuitFlags = NUM_CIRCUIT_FLAGS := by
  simp [Fintype.ofEquiv_card]

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

-- instance : FinEnum InstructionFlags := ⟨NUM_INSTRUCTION_FLAGS, instEquivInstructionFlagsFinOfNatNat⟩

instance : Fintype InstructionFlags :=
  Fintype.ofEquiv (Fin NUM_INSTRUCTION_FLAGS) instEquivInstructionFlagsFinOfNatNat.symm

@[simp]
lemma InstructionFlags_card : Fintype.card InstructionFlags = NUM_INSTRUCTION_FLAGS := by
  simp [Fintype.ofEquiv_card]

end Flags

namespace R1CS

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [FromUInt64 F]

-- TODO: figure out how `Jolt.Witness` is transformed into `Jolt.R1CS.WitnessMain`

structure WitnessMain where
  -- TODO: pull these `UInt64` out into an `Index` structure
  paddedTraceLength : UInt64
  memoryStart : UInt64
  -- `PcIn`
  programCounter : Fin paddedTraceLength.toNat → F
  -- `Bytecode_A`
  bytecodeAddress : Fin paddedTraceLength.toNat → F
  -- `Bytecode_ELFAddress`, `Bytecode_Bitflags`, `Bytecode_RS1`,
  -- `Bytecode_RS2`, `Bytecode_RD`, `Bytecode_Imm`
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

structure Witness extends WitnessMain F where
  x : Fin paddedTraceLength.toNat → F
  y : Fin paddedTraceLength.toNat → F
  immSigned : Fin paddedTraceLength.toNat → F
  relevantChunkY : Fin 4 → Fin paddedTraceLength.toNat → F
  RdNonzeroAndLookupToRd : Fin paddedTraceLength.toNat → F
  RdNonzeroAndJump : Fin paddedTraceLength.toNat → F
  branchAndLookupOutput : Fin paddedTraceLength.toNat → F
  nextPcJump : Fin paddedTraceLength.toNat → F
  nextPcJumpBranch : Fin paddedTraceLength.toNat → F

-- Copying the constraints being enforced from the Jolt codebase
-- TODO: converting these constraints into R1CS matrices and cross-validating with Jolt's

/- ### These are auxiliary values derived from the witness -/

-- TODO: make `packBE` and `packLE` be separate functions, instead of deriving them ad-hoc

-- TODO: for some of these, we actually create an auxiliary variable for the R1CS witness
-- that holds the value of the function. I've manually tagged them for now, will make sure
-- to model this in the future

/-- Pack all flag witness values into a single field element, big-endian format -/
def Witness.packFlagsBE (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => ∑ iFlag : InstructionFlags, (wit.instructionFlags iFlag i) * (2 ^ (NUM_INSTRUCTION_FLAGS - 1 - iFlag.toFin.val))
    + (2 ^ NUM_INSTRUCTION_FLAGS) *
      ∑ cFlag : CircuitFlags, (wit.circuitFlags cFlag i) * (2 ^ (NUM_CIRCUIT_FLAGS - 1 - cFlag.toFin.val))

/-- The true value of the program counter -/
def Witness.realPc (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => 4 * wit.programCounter i + (FromUInt64.embedding PC_START_ADDRESS - FromUInt64.embedding PC_NOOP_SHIFT)

/-- The signed value of the immediate operand -/
def Witness.signedOutput (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.bytecodeValue BytecodeValues.Imm i - (4294967295 + 1)

/-- Whether the instruction is a load or store -/
def Witness.isLoadOrStore (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.circuitFlags CircuitFlags.OpFlags_IsLoad i + wit.circuitFlags CircuitFlags.OpFlags_IsStore i

/-- The little-endian value of the RAM memory value that is read -/
-- TODO: make this an `allocate` operation (is it needed?)
def Witness.packedLoadStoreLE (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.readMemoryValues MemoryOpRead.RAM_Read_Byte0 i +
    (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte1 i) * (2 ^ 8) +
    (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte2 i) * (2 ^ 16) +
    (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte3 i) * (2 ^ 24)

/-- The big-endian value of the packed lookup query -/
-- TODO: make this an `allocate` operation
def Witness.packedQueryBE (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.chunksQuery 0 i * (2 ^ (3 * LOG_M)) + wit.chunksQuery 1 i * (2 ^ (2 * LOG_M))
    + wit.chunksQuery 2 i * (2 ^ LOG_M) + wit.chunksQuery 3 i


/-- The big-endian value of the packed `X` chunk -/
-- TODO: make this an `allocate` operation. However, we may not actually have to allocate this...
def Witness.chunksXBE (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.chunksX 0 i * (2 ^ (3 * LOG_M)) + wit.chunksX 1 i * (2 ^ (2 * LOG_M))
    + wit.chunksX 2 i * (2 ^ LOG_M) + wit.chunksX 3 i

/-- The big-endian value of the packed `Y` chunk -/
-- TODO: make this an `allocate` operation. However, we may not actually have to allocate this...
def Witness.chunksYBE (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.chunksY 0 i * (2 ^ (3 * LOG_M)) + wit.chunksY 1 i * (2 ^ (2 * LOG_M))
    + wit.chunksY 2 i * (2 ^ LOG_M) + wit.chunksY 3 i

/-- Whether the instruction is a shift operation -/
def Witness.isShift (wit : Witness F) : Fin wit.paddedTraceLength.toNat → F :=
  fun i => wit.instructionFlags InstructionFlags.IF_Sll i
    + wit.instructionFlags InstructionFlags.IF_Srl i
    + wit.instructionFlags InstructionFlags.IF_Sra i

-- TODO: do `relevant_chunk_y` and `allocate_if_else` for `OpFlags_IsConcat`

/- ### These are the constraints being enforced -/

/-- Flags are binary -/
def Witness.eqBinaryFlags (wit : Witness F) : Prop :=
  ∀ cFlag : CircuitFlags, ∀ iFlag : InstructionFlags, ∀ i : Fin wit.paddedTraceLength.toNat,
    (wit.circuitFlags cFlag i = 0 ∨ wit.circuitFlags cFlag i = 1) ∧
    (wit.instructionFlags iFlag i = 0 ∨ wit.instructionFlags iFlag i = 1)

/-- The program counter is equal to the bytecode address -/
def Witness.eqPcBytecodeAddress (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    wit.programCounter i = wit.bytecodeAddress i

/-- Packed flags (big-endian) are equal to bytecode `bitflags` field -/
def Witness.eqPackedFlags (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    wit.packFlagsBE F i = wit.bytecodeValue BytecodeValues.Bitflags i

/-- The first operand of the instruction is equal to the program counter or the value read from `RS1_Read`, depending on `OpFlags_IsRs1Rs2` -/
def Witness.eqIfElseX (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsRs1Rs2 i = 1)
      then (wit.x i = wit.realPc F i)
      else (wit.x i = wit.readMemoryValues MemoryOpRead.RS1_Read i)

/-- The second operand of the instruction is equal to the value of the immediate operand or the value read from `RS2_Read`, depending on `OpFlags_IsImm` -/
def Witness.eqIfElseY (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsImm i = 1)
      then (wit.y i = wit.bytecodeValue BytecodeValues.Imm i)
      else (wit.y i = wit.readMemoryValues MemoryOpRead.RS2_Read i)

/-- The immediate operand is set to be `signedOutput` if the `SignImm` flag is set, else it is equal to the existing bytecode immediate's value -/
def Witness.eqIfElseImmSigned (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_SignImm i = 1)
      then (wit.immSigned i = wit.signedOutput F i)
      else (wit.immSigned i = wit.bytecodeValue BytecodeValues.Imm i)


/-- If the instruction is a load or store, then the value read from `RS1_Read` plus the immediate operand is equal to the value written to memory -/
def Witness.eqConditionalIsLoadOrStore (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.isLoadOrStore F i = 1)
      then (wit.readMemoryValues MemoryOpRead.RS1_Read i + wit.immSigned i
        = wit.readWriteMemoryAddress i + FromUInt64.embedding wit.memoryStart)
      else True

/-- If the instruction is a load, then the value read from memory is equal to the value written to memory -/
def Witness.eqConditionalIsLoadMemory (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsLoad i = 1)
      then
        (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte0 i = wit.writeMemoryValue MemoryOpWrite.RAM_Write_Byte0 i) &&
        (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte1 i = wit.writeMemoryValue MemoryOpWrite.RAM_Write_Byte1 i) &&
        (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte2 i = wit.writeMemoryValue MemoryOpWrite.RAM_Write_Byte2 i) &&
        (wit.readMemoryValues MemoryOpRead.RAM_Read_Byte3 i = wit.writeMemoryValue MemoryOpWrite.RAM_Write_Byte3 i)
      else True

/-- If the instruction is a `Store`, then the packed load-store value is equal to the lookup output -/
def Witness.eqConditionalIsStore (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsStore i = 1)
      then (wit.packedLoadStoreLE F i = wit.lookupOutput i)
      else True

/-- If the instruction is an `Add`, then the packed query is equal to the sum of the operands -/
def Witness.eqConditionalIsAdd (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.instructionFlags InstructionFlags.IF_Add i = 1)
      then (wit.packedQueryBE F i = wit.x i + wit.y i)
      else True

/-- If the instruction is a `Sub`, then the packed query is equal to the difference of the operands -/
def Witness.eqConditionalIsSub (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.instructionFlags InstructionFlags.IF_Sub i = 1)
      then (wit.packedQueryBE F i = wit.x i - wit.y i + (0xffffffff + 1))
      else True

/-- If the instruction is a `Load`, then the packed query is equal to the packed load-store value -/
def Witness.eqConditionalIsLoadQuery (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsLoad i = 1)
      then (wit.packedQueryBE F i = wit.packedLoadStoreLE F i)
      else True

/-- If the instruction is a `Store`, then the packed query is equal to the value read from `RS2_Read` -/
def Witness.eqConditionalIsStoreQuery (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsStore i = 1)
      then (wit.packedQueryBE F i = wit.readMemoryValues MemoryOpRead.RS2_Read i)
      else True

/-- If the instruction is a `Concat`, then the packed `X` chunk is equal to the value of `RS1` and the packed `Y` chunk is equal to the value of `RS2` -/
def Witness.eqConditionalIsConcat (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsConcat i = 1)
      then (wit.chunksXBE F i = wit.x i) ∧ (wit.chunksYBE F i = wit.y i)
      else True


def Witness.eqIfElseIsShiftChunksY (j : Fin 4) (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.isShift F i = 1)
      then (wit.relevantChunkY j i = wit.chunksY 3 i)
      else (wit.relevantChunkY j i = wit.chunksY 0 i)


def Witness.eqConditionalIsConcatChunksQuery (j : Fin 4) (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsConcat i = 1)
      then (wit.chunksQuery j i = (1 <<< 8) * wit.chunksXBE F i + wit.relevantChunkY j i)
      else True


def Witness.eqProdRdNonzeroAndLookupToRd (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    wit.RdNonzeroAndLookupToRd i = wit.bytecodeValue BytecodeValues.RD i * wit.circuitFlags CircuitFlags.OpFlags_LookupOutToRd i


def Witness.eqConditionalRdNonzeroAndLookupToRd (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.RdNonzeroAndLookupToRd i = 1)
      then (wit.writeMemoryValue MemoryOpWrite.RD_Write i = wit.lookupOutput i)
      else True


def Witness.eqProdRdNonzeroAndJmp (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    wit.RdNonzeroAndJump i = wit.bytecodeValue BytecodeValues.RD i * wit.circuitFlags CircuitFlags.OpFlags_IsJmp i

-- TODO: double-check if this is the correct representation of the constraint
def Witness.eqConditionalRdNonzeroAndJmp (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.RdNonzeroAndJump i = 1)
      then (wit.writeMemoryValue MemoryOpWrite.RD_Write i = wit.programCounter i + ( FromUInt64.embedding PC_START_ADDRESS - FromUInt64.embedding PC_NOOP_SHIFT))
      else True


def Witness.eqProdBranchAndLookupOutput (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    wit.branchAndLookupOutput i = wit.circuitFlags CircuitFlags.OpFlags_IsBranch i * wit.lookupOutput i


def Witness.eqIfElseNextPcJump (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.circuitFlags CircuitFlags.OpFlags_IsJmp i = 1)
      then (wit.lookupOutput i + 4 = 4 * wit.programCounter i + FromUInt64.embedding PC_START_ADDRESS + 4)
      else True


def Witness.eqIfElseNextPcJumpBranch (wit : Witness F) : Prop :=
  ∀ i : Fin wit.paddedTraceLength.toNat,
    if (wit.branchAndLookupOutput i = 1)
      then (4 * wit.programCounter i + FromUInt64.embedding PC_START_ADDRESS + wit.immSigned i = wit.nextPcJump i)
      else True

-- TODO: figure out what this is
-- assert_static_aux_index!(next_pc_jump_branch, PC_BRANCH_AUX_INDEX);

-- TODO: double-check if we miss any constraint



-- Do all of the checks above
def Witness.isValid (witness : Witness F) : Prop :=
  witness.eqBinaryFlags F ∧
  witness.eqPcBytecodeAddress F ∧
  witness.eqPackedFlags F ∧
  witness.eqIfElseX F ∧
  witness.eqIfElseY F ∧
  witness.eqIfElseImmSigned F ∧
  witness.eqConditionalIsLoadOrStore F ∧
  witness.eqConditionalIsLoadMemory F ∧
  witness.eqConditionalIsStore F ∧
  witness.eqConditionalIsAdd F ∧
  witness.eqConditionalIsSub F ∧
  witness.eqConditionalIsLoadQuery F ∧
  witness.eqConditionalIsStoreQuery F ∧
  witness.eqConditionalIsConcat F ∧
  witness.eqIfElseIsShiftChunksY F 0 ∧
  witness.eqIfElseIsShiftChunksY F 1 ∧
  witness.eqIfElseIsShiftChunksY F 2 ∧
  witness.eqIfElseIsShiftChunksY F 3 ∧
  witness.eqConditionalIsConcatChunksQuery F 0 ∧
  witness.eqConditionalIsConcatChunksQuery F 1 ∧
  witness.eqConditionalIsConcatChunksQuery F 2 ∧
  witness.eqConditionalIsConcatChunksQuery F 3 ∧
  witness.eqProdRdNonzeroAndLookupToRd F ∧
  witness.eqConditionalRdNonzeroAndLookupToRd F ∧
  witness.eqProdRdNonzeroAndJmp F ∧
  witness.eqConditionalRdNonzeroAndJmp F ∧
  witness.eqProdBranchAndLookupOutput F ∧
  witness.eqIfElseNextPcJump F ∧
  witness.eqIfElseNextPcJumpBranch F



end R1CS

end Jolt
