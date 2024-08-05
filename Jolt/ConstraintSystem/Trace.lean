import Jolt.ConstraintSystem.Constants
import Jolt.ConstraintSystem.Instruction.Basic
import Jolt.RiscV.ISA

/-!
  # Trace model for Jolt
-/

namespace Jolt

open RiscV

structure ELFInstruction where
  address : UInt64
  opcode : RV32IM.Instr
  rs1 : Option UInt64
  rs2 : Option UInt64
  rd : Option UInt64
  imm : Option UInt32
  virtualSequenceIndex : Option USize
deriving Repr, Inhabited, DecidableEq

structure RegisterState where
  rs1Value : Option UInt64
  rs2Value : Option UInt64
  rdValue : Option UInt64
deriving Repr, Inhabited, DecidableEq

section Memory

inductive MemoryState where
  | Read (address : UInt64) (value : UInt64)
  | Write (address : UInt64) (value : UInt64)
deriving Repr, Inhabited, DecidableEq

inductive MemoryOp where
  | Read (address : UInt64)
  | Write (address : UInt64) (value : UInt64)
deriving Repr, Inhabited, DecidableEq

structure MemoryLayout where
  maxInputSize : UInt64
  maxOutputSize : UInt64
deriving Repr, Inhabited, DecidableEq

def MemoryLayout.ramWitnessOffset (m : MemoryLayout) : UInt64 :=
  (REGISTER_COUNT + m.maxInputSize + m.maxOutputSize + 1).nextPowerOfTwo

def MemoryLayout.inputStart (m : MemoryLayout) : UInt64 :=
  RAM_START_ADDRESS - m.ramWitnessOffset + REGISTER_COUNT

def MemoryLayout.inputEnd (m : MemoryLayout) : UInt64 :=
  m.inputStart + m.maxInputSize

def MemoryLayout.outputStart (m : MemoryLayout) : UInt64 :=
  m.inputEnd + 1

def MemoryLayout.outputEnd (m : MemoryLayout) : UInt64 :=
  m.outputStart + m.maxOutputSize

def MemoryLayout.panic (m : MemoryLayout) : UInt64 :=
  m.outputEnd + 1

end Memory

structure RVTraceRow where
  instruction : ELFInstruction
  registerState : RegisterState
  memoryState : Option MemoryState
  adviceValue : Option UInt64
deriving Repr, Inhabited, DecidableEq

-- We want to define it here before `Bytecode.lean`
-- since we need it for defining `TraceStep`
structure Bytecode.Row where
  address : USize
  bitflags : UInt64
  rs1 : UInt64
  rs2 : UInt64
  rd : UInt64
  imm : UInt64
deriving Repr, Inhabited, DecidableEq


structure TraceStep (C : Nat) (logM : Nat) where
  instructionLookup : Option (InstructionSet F C logM)
  bytecodeRow : Bytecode.Row
  memoryOps : Fin MEMORY_OPS_PER_INSTRUCTION → MemoryOp
-- deriving Repr, Inhabited, DecidableEq

/-- The program's input, output, whether the program panics, and its memory layout -/
structure Device where
  inputs : Array UInt8
  outputs : Array UInt8
  panic : Bool
  memoryLayout : MemoryLayout
deriving Repr, Inhabited, DecidableEq


section Enum

/- Defining `enum`s relevant for trace generation and R1CS -/

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

instance : Fintype InstructionFlags :=
  Fintype.ofEquiv (Fin NUM_INSTRUCTION_FLAGS) instEquivInstructionFlagsFinOfNatNat.symm

@[simp]
lemma InstructionFlags_card : Fintype.card InstructionFlags = NUM_INSTRUCTION_FLAGS := by
  simp [Fintype.ofEquiv_card]

end Flags

end Enum

section Generation

/- Generate traces from ELF instructions -/

/-- Generate the circuit flags for a given `opcode`. TODO: figure out exact mapping -/
def CircuitFlags.fromOpcode (opcode : RV32IM.Instr) : List CircuitFlags :=
  match opcode with
  | RV32IM.Instr.I (RV32I.Instr.ADD) => [OpFlags_IsRs1Rs2, OpFlags_IsImm]
  | RV32IM.Instr.I (RV32I.Instr.SUB) => [OpFlags_IsRs1Rs2, OpFlags_IsImm]
  | RV32IM.Instr.I (RV32I.Instr.AND) => [OpFlags_IsRs1Rs2, OpFlags_IsImm]
  | RV32IM.Instr.I (RV32I.Instr.OR) => [OpFlags_IsRs1Rs2, OpFlags_IsImm]
  | RV32IM.Instr.I (RV32I.Instr.XOR) => [OpFlags_IsRs1Rs2, OpFlags_IsImm]
  -- For now, all other instructions are virtual
  | _ => [OpFlags_IsVirtual]

/-- Generate the instruction flag for a given `opcode`. TODO: figure out exact mapping -/
def InstructionFlags.fromOpcode (opcode : RV32IM.Instr) : InstructionFlags :=
  match opcode with
  | RV32IM.Instr.I (RV32I.Instr.ADD) => IF_Add
  | RV32IM.Instr.I (RV32I.Instr.SUB) => IF_Sub
  | RV32IM.Instr.I (RV32I.Instr.AND) => IF_And
  | RV32IM.Instr.I (RV32I.Instr.OR) => IF_Or
  | RV32IM.Instr.I (RV32I.Instr.XOR) => IF_Xor
  | RV32IM.Instr.I (RV32I.Instr.LB) => IF_Lb
  | RV32IM.Instr.I (RV32I.Instr.LH) => IF_Lh
  | RV32IM.Instr.I (RV32I.Instr.SB) => IF_Sb
  | RV32IM.Instr.I (RV32I.Instr.SH) => IF_Sh
  | RV32IM.Instr.I (RV32I.Instr.SW) => IF_Sw
  | RV32IM.Instr.I (RV32I.Instr.BEQ) => IF_Beq
  | RV32IM.Instr.I (RV32I.Instr.BGE) => IF_Bge
  | RV32IM.Instr.I (RV32I.Instr.BGEU) => IF_Bgeu
  | RV32IM.Instr.I (RV32I.Instr.BNE) => IF_Bne
  | RV32IM.Instr.I (RV32I.Instr.SLT) => IF_Slt
  | RV32IM.Instr.I (RV32I.Instr.SLTU) => IF_Sltu
  | RV32IM.Instr.I (RV32I.Instr.SLL) => IF_Sll
  | RV32IM.Instr.I (RV32I.Instr.SRA) => IF_Sra
  | RV32IM.Instr.I (RV32I.Instr.SRL) => IF_Srl
  | RV32IM.Instr.I (RV32I.Instr.SRAI) => IF_Sra
  | RV32IM.Instr.I (RV32I.Instr.SRLI) => IF_Srl
  -- Not sure if these two are correct
  | RV32IM.Instr.I (RV32I.Instr.JAL) => IF_Movsign
  | RV32IM.Instr.I (RV32I.Instr.JALR) => IF_Movsign
  -- the rest just goes to this one for now
  | _ => IF_Virt_Adv
  -- | IF_Mul => 20
  -- | IF_MulU => 21
  -- | IF_MulHu => 22
  -- | IF_Virt_Adv => 23
  -- | IF_Virt_Assert_LTE => 24
  -- | IF_Virt_Assert_VALID_SIGNED_REMAINDER => 25
  -- | IF_Virt_Assert_VALID_UNSIGNED_REMAINDER => 26
  -- | IF_Virt_Assert_VALID_DIV0 => 27


/-- Pack the circuit flags and instruction flags into a single bitflag. The circuit flags are the higher bits, and the instruction flags are the lower bits.
TODO: prove that the modulo `UInt64` does not overflow -/
def packBitflags (cFlags : List CircuitFlags) (iFlag : InstructionFlags) : UInt64 :=
  let packedFlags := cFlags.foldl (fun acc flag => acc + (1 <<< flag.toFin)) (1 <<< iFlag.toFin)
  packedFlags.toUInt64


/-- Generate `Bytecode.Row` from `ELFInstruction`. For now, we ignore the `virtualSequenceIndex` field which is only relevant for a few instructions. -/
def Bytecode.Row.fromELFInstruction (instr : ELFInstruction) : Bytecode.Row where
  address := instr.address.toUSize
  bitflags := packBitflags (CircuitFlags.fromOpcode instr.opcode) (InstructionFlags.fromOpcode instr.opcode)
  rs1 := instr.rs1.getD 0
  rs2 := instr.rs2.getD 0
  rd := instr.rd.getD 0
  imm := (instr.imm.getD 0).toUInt64


end Generation


end Jolt
