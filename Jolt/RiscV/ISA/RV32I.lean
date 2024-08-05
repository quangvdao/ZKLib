/-
 Copyright 2023 RISC Zero, Inc.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Jolt.RiscV.R0sy
import Jolt.RiscV.ISA.Basic

namespace RiscV

namespace RV32I

open R0sy

/-
Volume I: RISC-V Unprivileged ISA V20191213
RV32I Base Instruction Set

funct7          rs2   rs1   funct3          rd    opcode    R-type
imm[11:0]             rs1   funct3          rd    opcode    I-type
imm[11:5]       rs2   rs1   funct3     imm[4:0]   opcode    S-type
imm[12|10:5]    rs2   rs1   funct3  imm[4:1|11]   opcode    B-type
imm[31:12]                                  rd    opcode    U-type
imm[20|10:1|11|19:12]                       rd    opcode    J-type

imm[31:12]                                  rd    0110111   LUI
imm[31:12]                                  rd    0010111   AUIPC
imm[20|10:1|11|19:12]                       rd    1101111   JAL
imm[11:0]             rs1   000             rd    1100111   JALR
imm[12|10:5]    rs2   rs1   000     imm[4:1|11]   1100011   BEQ
imm[12|10:5]    rs2   rs1   001     imm[4:1|11]   1100011   BNE
imm[12|10:5]    rs2   rs1   100     imm[4:1|11]   1100011   BLT
imm[12|10:5]    rs2   rs1   101     imm[4:1|11]   1100011   BGE
imm[12|10:5]    rs2   rs1   110     imm[4:1|11]   1100011   BLTU
imm[12|10:5]    rs2   rs1   111     imm[4:1|11]   1100011   BGEU
imm[11:0]             rs1   000             rd    0000011   LB
imm[11:0]             rs1   001             rd    0000011   LH
imm[11:0]             rs1   010             rd    0000011   LW
imm[11:0]             rs1   100             rd    0000011   LBU
imm[11:0]             rs1   101             rd    0000011   LHU
imm[11:5]       rs2   rs1   000       imm[4:0]    0100011   SB
imm[11:5]       rs2   rs1   001       imm[4:0]    0100011   SH
imm[11:5]       rs2   rs1   010       imm[4:0]    0100011   SW
imm[11:0]             rs1   000             rd    0010011   ADDI
imm[11:0]             rs1   010             rd    0010011   SLTI
imm[11:0]             rs1   011             rd    0010011   SLTIU
imm[11:0]             rs1   100             rd    0010011   XORI
imm[11:0]             rs1   110             rd    0010011   ORI
imm[11:0]             rs1   111             rd    0010011   ANDI
0000000       shamt   rs1   001             rd    0010011   SLLI
0000000       shamt   rs1   101             rd    0010011   SRLI
0100000       shamt   rs1   101             rd    0010011   SRAI
0000000         rs2   rs1   000             rd    0110011   ADD
0100000         rs2   rs1   000             rd    0110011   SUB
0000000         rs2   rs1   001             rd    0110011   SLL
0000000         rs2   rs1   010             rd    0110011   SLT
0000000         rs2   rs1   011             rd    0110011   SLTU
0000000         rs2   rs1   100             rd    0110011   XOR
0000000         rs2   rs1   101             rd    0110011   SRL
0100000         rs2   rs1   101             rd    0110011   SRA
0000000         rs2   rs1   110             rd    0110011   OR
0000000         rs2   rs1   111             rd    0110011   AND
fm    pred     succ   rs1   000             rd    0001111   FENCE
000000000000    00000       000          00000    1110011   ECALL
000000000001    00000       000          00000    1110011   EBREAK
-/

inductive Instr where
  -- R-type instructions
  | ADD
  | AND
  | OR
  | SLL
  | SLT
  | SLTU
  | SRA
  | SRL
  | SUB
  | XOR
  -- I-type instructions
  | ADDI
  | ANDI
  | JALR
  | LB
  | LBU
  | LH
  | LHU
  | LW
  | ORI
  | SLLI
  | SLTI
  | SLTIU
  | SRAI
  | SRLI
  | XORI
  -- S-type instructions
  | SB
  | SH
  | SW
  -- B-type instructions
  | BEQ
  | BGE
  | BGEU
  | BLT
  | BLTU
  | BNE
  -- U-type instructions
  | AUIPC
  | LUI
  -- J-type instructions
  | JAL
  -- Special instructions
  | ECALL
  | EBREAK
  | FENCE
deriving Repr, Inhabited, DecidableEq

def ISA: ISA where
  Mnemonic := Instr
  all := #[
    .ADD,   .ADDI,  .AND,   .ANDI,  .AUIPC, .BEQ,   .BGE,   .BGEU,
    .BLT,   .BLTU,  .BNE,   .ECALL, .EBREAK, .FENCE, .JAL,   .JALR,
    .LB,    .LBU,   .LH,    .LHU,   .LUI,    .LW,    .OR,    .ORI,
    .SB,    .SH,    .SLL,   .SLLI,  .SLT,    .SLTI,  .SLTIU, .SLTU,
    .SRA,   .SRAI,  .SRL,   .SRLI,  .SUB,    .SW,    .XOR,   .XORI
  ]
  toString
    | .ADD => "ADD"   | .ADDI => "ADDI" | .AND => "AND"   | .ANDI => "ANDI" | .AUIPC => "AUIPC" | .BEQ => "BEQ"   | .BGE => "BGE"   | .BGEU => "BGEU"
    | .BLT => "BLT"   | .BLTU => "BLTU" | .BNE => "BNE"   | .ECALL => "ECALL" | .EBREAK => "EBREAK" | .FENCE => "FENCE" | .JAL => "JAL"   | .JALR => "JALR"
    | .LB => "LB"     | .LBU => "LBU"   | .LH => "LH"     | .LHU => "LHU"   | .LUI => "LUI"    | .LW => "LW"    | .OR => "OR"    | .ORI => "ORI"
    | .SB => "SB"     | .SH => "SH"     | .SLL => "SLL"   | .SLLI => "SLLI" | .SLT => "SLT"    | .SLTI => "SLTI" | .SLTIU => "SLTIU" | .SLTU => "SLTU"
    | .SRA => "SRA"   | .SRAI => "SRAI" | .SRL => "SRL"   | .SRLI => "SRLI" | .SUB => "SUB"    | .SW => "SW"    | .XOR => "XOR"   | .XORI => "XORI"
  encode_mnemonic (m: Instr)
    := match m with
        | .ADD    => .R <|  R.EncMnemonic.new   0b0000000   0b000   0b0110011
        | .ADDI   => .I <|  I.EncMnemonic.new               0b000   0b0010011
        | .AND    => .R <|  R.EncMnemonic.new   0b0000000   0b111   0b0110011
        | .ANDI   => .I <|  I.EncMnemonic.new               0b111   0b0010011
        | .AUIPC  => .U <|  U.EncMnemonic.new                       0b0010111
        | .BEQ    => .B <|  B.EncMnemonic.new               0b000   0b1100011
        | .BGE    => .B <|  B.EncMnemonic.new               0b101   0b1100011
        | .BGEU   => .B <|  B.EncMnemonic.new               0b111   0b1100011
        | .BLT    => .B <|  B.EncMnemonic.new               0b100   0b1100011
        | .BLTU   => .B <|  B.EncMnemonic.new               0b110   0b1100011
        | .BNE    => .B <|  B.EncMnemonic.new               0b001   0b1100011
        | .ECALL  => .Const <|  Const.EncMnemonic.new   0b000000000000    0b00000   0b000   0b00000   0b1110011
        | .EBREAK => .Const <|  Const.EncMnemonic.new   0b000000000001    0b00000   0b000   0b00000   0b1110011
        | .FENCE  => .I <|  I.EncMnemonic.new               0b000   0b0001111
        | .JAL    => .J <|  J.EncMnemonic.new                       0b1101111
        | .JALR   => .I <|  I.EncMnemonic.new               0b000   0b1100111
        | .LB     => .I <|  I.EncMnemonic.new               0b000   0b0000011
        | .LBU    => .I <|  I.EncMnemonic.new               0b100   0b0000011
        | .LH     => .I <|  I.EncMnemonic.new               0b001   0b0000011
        | .LHU    => .I <|  I.EncMnemonic.new               0b101   0b0000011
        | .LUI    => .U <|  U.EncMnemonic.new                       0b0110111
        | .LW     => .I <|  I.EncMnemonic.new               0b010   0b0000011
        | .OR     => .R <|  R.EncMnemonic.new   0b0000000   0b110   0b0110011
        | .ORI    => .I <|  I.EncMnemonic.new               0b110   0b0010011
        | .SB     => .S <|  S.EncMnemonic.new               0b000   0b0100011
        | .SH     => .S <|  S.EncMnemonic.new               0b001   0b0100011
        | .SLL    => .R <|  R.EncMnemonic.new   0b0000000   0b001   0b0110011
        | .SLLI   => .R <|  R.EncMnemonic.new   0b0000000   0b001   0b0010011
        | .SLT    => .R <|  R.EncMnemonic.new   0b0000000   0b010   0b0110011
        | .SLTI   => .I <|  I.EncMnemonic.new               0b010   0b0010011
        | .SLTIU  => .I <|  I.EncMnemonic.new               0b011   0b0010011
        | .SLTU   => .R <|  R.EncMnemonic.new   0b0000000   0b011   0b0110011
        | .SRA    => .R <|  R.EncMnemonic.new   0b0100000   0b101   0b0110011
        | .SRAI   => .R <|  R.EncMnemonic.new   0b0100000   0b101   0b0010011
        | .SRL    => .R <|  R.EncMnemonic.new   0b0000000   0b101   0b0110011
        | .SRLI   => .R <|  R.EncMnemonic.new   0b0000000   0b101   0b0010011
        | .SUB    => .R <|  R.EncMnemonic.new   0b0100000   0b000   0b0110011
        | .SW     => .S <|  S.EncMnemonic.new               0b010   0b0100011
        | .XOR    => .R <|  R.EncMnemonic.new   0b0000000   0b100   0b0110011
        | .XORI   => .I <|  I.EncMnemonic.new               0b100   0b0010011
  run
    | .ADD, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (x + y)
    | .ADDI, args
        => do let x <- RegFile.get_word args.rs1
              RegFile.set_word args.rd (x + args.imm)
    | .AND, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (x &&& y)
    | .ANDI, args
        => do let x <- RegFile.get_word args.rs1
              RegFile.set_word args.rd (x &&& args.imm)
    | .AUIPC, args
        => do let pc <- RegFile.get_word .PC
              RegFile.set_word args.rd (pc - 4 + args.imm)
    | .BEQ, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              let pc <- RegFile.get_word .PC
              if x == y then do
                let newPC := pc - 4 + args.imm
                if newPC % 4 != 0 then throw (.InstructionAddressMisaligned newPC.toNat)
                RegFile.set_word .PC newPC
    | .BGE, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              let pc <- RegFile.get_word .PC
              if UInt32.ge_signed x y then do
                let newPC := pc - 4 + args.imm
                if newPC % 4 != 0 then throw (.InstructionAddressMisaligned newPC.toNat)
                RegFile.set_word .PC newPC
    | .BGEU, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              let pc <- RegFile.get_word .PC
              if x >= y then do
                let newPC := pc - 4 + args.imm
                if newPC % 4 != 0 then throw (.InstructionAddressMisaligned newPC.toNat)
                RegFile.set_word .PC newPC
    | .BLT, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              let pc <- RegFile.get_word .PC
              if UInt32.lt_signed x y then do
                let newPC := pc - 4 + args.imm
                if newPC % 4 != 0 then throw (.InstructionAddressMisaligned newPC.toNat)
                RegFile.set_word .PC newPC
    | .BLTU, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              let pc <- RegFile.get_word .PC
              if x < y then do
                let newPC := pc - 4 + args.imm
                if newPC % 4 != 0 then throw (.InstructionAddressMisaligned newPC.toNat)
                RegFile.set_word .PC newPC
    | .BNE, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              let pc <- RegFile.get_word .PC
              if x != y then do
                let newPC := pc - 4 + args.imm
                if newPC % 4 != 0 then throw (.InstructionAddressMisaligned newPC.toNat)
                RegFile.set_word .PC newPC
    | .ECALL, _
        => do let pc <- RegFile.get_word .PC
              throw (.ECall pc.toNat)
    | .EBREAK, _ => pure ()
    | .FENCE, _ => pure ()
    | .JAL, args
        => do let pc <- RegFile.get_word .PC
              RegFile.set_word args.rd pc
              let newPC := pc - 4 + args.imm
              if newPC % 4 != 0 then throw (.InstructionAddressMisaligned newPC.toNat)
              RegFile.set_word .PC newPC
    | .JALR, args
        => do let pc <- RegFile.get_word .PC
              RegFile.set_word args.rd pc
              let base <- RegFile.get_word args.rs1
              let newPC := (base + args.imm) &&& 0xfffffffe
              if newPC % 4 != 0 then throw (.InstructionAddressMisaligned newPC.toNat)
              RegFile.set_word .PC newPC
    | .LB, args
        => do let a <- RegFile.get_word args.rs1
              let addr := a + args.imm
              let x <- Mem.get_byte addr.toNat
              RegFile.set_word args.rd (UInt32.ofUInt8_signed x)
    | .LBU, args
        => do let a <- RegFile.get_word args.rs1
              let addr := a + args.imm
              let x <- Mem.get_byte addr.toNat
              RegFile.set_word args.rd x.toUInt32
    | .LH, args
        => do let a <- RegFile.get_word args.rs1
              let addr := a + args.imm
              let x <- Mem.get_half addr.toNat
              RegFile.set_word args.rd (UInt32.ofUInt16_signed x)
    | .LHU, args
        => do let a <- RegFile.get_word args.rs1
              let addr := a + args.imm
              let x <- Mem.get_half addr.toNat
              RegFile.set_word args.rd x.toUInt32
    | .LUI, args
        => RegFile.set_word args.rd args.imm
    | .LW, args
        => do let a <- RegFile.get_word args.rs1
              let addr := a + args.imm
              let x <- Mem.get_word addr.toNat
              RegFile.set_word args.rd x
    | .OR, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (x ||| y)
    | .ORI, args
        => do let x <- RegFile.get_word args.rs1
              RegFile.set_word args.rd (x ||| args.imm)
    | .SB, args
        => do let a <- RegFile.get_word args.rs1
              let addr := a + args.imm
              let x <- RegFile.get_word args.rs2
              Mem.set_byte addr.toNat x.toNat.toUInt8
    | .SH, args
        => do let a <- RegFile.get_word args.rs1
              let addr := a + args.imm
              let x <- RegFile.get_word args.rs2
              Mem.set_half addr.toNat x.toNat.toUInt16
    | .SLL, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (x <<< y)
    | .SLLI, args
        => do let x <- RegFile.get_word args.rs1
              let shamt6 := (Reg.index args.rs2).toUInt32
              RegFile.set_word args.rd (x <<< shamt6)
    | .SLT, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (if UInt32.lt_signed x y then 1 else 0)
    | .SLTI, args
        => do let x <- RegFile.get_word args.rs1
              RegFile.set_word args.rd (if UInt32.lt_signed x args.imm then 1 else 0)
    | .SLTIU, args
        => do let x <- RegFile.get_word args.rs1
              RegFile.set_word args.rd (if x < args.imm then 1 else 0)
    | .SLTU, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (if x < y then 1 else 0)
    | .SRA, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (UInt32.shr_signed x y)
    | .SRAI, args
        => do let x <- RegFile.get_word args.rs1
              let shamt6 := (Reg.index args.rs2).toUInt32
              RegFile.set_word args.rd (UInt32.shr_signed x shamt6)
    | .SRL, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (x >>> y)
    | .SRLI, args
        => do let x <- RegFile.get_word args.rs1
              let shamt6 := (Reg.index args.rs2).toUInt32
              RegFile.set_word args.rd (x >>> shamt6)
    | .SUB, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (x - y)
    | .SW, args
        => do let a <- RegFile.get_word args.rs1
              let addr := a + args.imm
              let x <- RegFile.get_word args.rs2
              Mem.set_word addr.toNat x
    | .XOR, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs2
              RegFile.set_word args.rd (x ^^^ y)
    | .XORI, args
        => do let x <- RegFile.get_word args.rs1
              RegFile.set_word args.rd (x ^^^ args.imm)

end RV32I

end RiscV
