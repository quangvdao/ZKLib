/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.JoltConstraint.Subtable.Basic

/-!
  # Interface for Instructions in Jolt
-/

namespace Jolt

variable (F : Type) [JoltField F]

-- `F` must be big enough

/--
  Interface for an instruction in Jolt.

  Here, `C` is the "dimension" of the decomposition, i.e. the number of values read from each subtable, and `logM` is the number of bits for the subtable.
-/
class Instruction (Instr : Type) where
  -- The first operand of the instruction. Should be `C * (logM / 2)` bits.
  firstOperand : Instr → UInt64

  -- The second operand of the instruction
  secondOperand : Instr → UInt64

  toQueries : Instr → List (BitVec logM)

  -- The subtables used by the instruction
  subtables (C : Nat) (logM : Nat) : List (LassoSubtable F)

  -- Combine table lookups into final value
  -- Here, `vals` is modeled as a list of `C`-length vectors of the subtables.
  combineLookups (C : Nat) (logM : Nat) : Instr → (vals : List (Fin C → LassoSubtable F)) → F

  -- The expected output of the instruction
  expectedOutput : UInt64
-- deriving Repr, Inhabited, DecidableEq

/-- An instruction is valid if the expected output is equal to the result of combining lookup results from querying subtables with the indices -/
def isValid (instr : Instruction F Instr) : Prop := sorry

class InstructionSet where
  numInstructions : Nat
  instructions : Fin numInstructions → Instruction F Instr
-- deriving Repr, Inhabited, DecidableEq

end Jolt


/-
ADD(ADDInstruction(0, 0)): 0
SUB(SUBInstruction(0, 0)): 1
AND(ANDInstruction(0, 0)): 2
OR(ORInstruction(0, 0)): 3
XOR(XORInstruction(0, 0)): 4
LB(LBInstruction(0)): 5
LH(LHInstruction(0)): 6
SB(SBInstruction(0)): 7
SH(SHInstruction(0)): 8
SW(SWInstruction(0)): 9
BEQ(BEQInstruction(0, 0)): 10
BGE(BGEInstruction(0, 0)): 11
BGEU(BGEUInstruction(0, 0)): 12
BNE(BNEInstruction(0, 0)): 13
SLT(SLTInstruction(0, 0)): 14
SLTU(SLTUInstruction(0, 0)): 15
SLL(SLLInstruction(0, 0)): 16
SRA(SRAInstruction(0, 0)): 17
SRL(SRLInstruction(0, 0)): 18
MOVSIGN(MOVSIGNInstruction(0)): 19
MUL(MULInstruction(0, 0)): 20
MULU(MULUInstruction(0, 0)): 21
MULHU(MULHUInstruction(0, 0)): 22
VIRTUAL_ADVICE(ADVICEInstruction(0)): 23
VIRTUAL_ASSERT_LTE(ASSERTLTEInstruction(0, 0)): 24
VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER(AssertValidSignedRemainderInstruction(0, 0)): 25
VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER(AssertValidUnsignedRemainderInstruction(0, 0)): 26
VIRTUAL_ASSERT_VALID_DIV0(AssertValidDiv0Instruction(0, 0)): 27
-/