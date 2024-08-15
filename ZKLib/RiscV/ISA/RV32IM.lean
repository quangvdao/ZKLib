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

import ZKLib.RiscV.ISA.RV32I
import ZKLib.RiscV.ISA.RV32M

namespace RiscV

namespace RV32IM
  inductive Instr where
    | I (instr: RV32I.Instr)
    | M (instr: RV32M.Instr)
  deriving Repr, Inhabited, DecidableEq

  @[always_inline, inline]
  def ISA: ISA where
    Mnemonic := Instr
    all := RV32I.ISA.all.map .I ++ RV32M.ISA.all.map .M
    toString
      | .I instr => RV32I.ISA.toString instr
      | .M instr => RV32M.ISA.toString instr
    encode_mnemonic
      | .I instr => RV32I.ISA.encode_mnemonic instr
      | .M instr => RV32M.ISA.encode_mnemonic instr
    run
      | .I instr => RV32I.ISA.run instr
      | .M instr => RV32M.ISA.run instr
end RV32IM

end RiscV
