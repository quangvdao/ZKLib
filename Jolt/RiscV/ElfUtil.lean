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

import Jolt.RiscV.Machine

namespace Elf

-- This file is broken for now, TODO fix

open R0sy
open RiscV

def xlenOfElf (elf: Elf): Xlen
  := match elf.e_header.e_ident.ei_class with
      | .Ptr32 => .Xlen32
      | .Ptr64 => .Xlen64

def endianOfElf (elf: Elf): Endian
  := match elf.e_header.e_ident.ei_data with
      | .Big => .Big
      | .Little => .Little

def loadElf (elf: Elf): MachineState
  := Id.run do
        let mut blocks: Array Block := Array.mkEmpty 0
        for segment in elf.programs do
          if segment.header.p_type == .PT_LOAD
            then do let zerosRequired := segment.header.p_memsz.toNat - segment.header.p_filesz.toNat
                    let zeros: Array UInt8 := Array.mkArray zerosRequired 0
                    let data := segment.file_data.toArray ++ zeros
                    blocks := blocks.push {
                      base := segment.header.p_vaddr.toNat,
                      data
                    }
        pure {
          reg_file := RegFile.newWithPc elf.e_header.e_entry.toNat.toUInt32
          mem := { endian := endianOfElf elf, blocks }
        }

def loadElfInfo (mach: MachineState) (elf: Elf): Except RiscVException MachineState
  := Id.run do
        mach.run'
          <| do let entry := elf.e_header.e_entry.toNat.toUInt32
                RegFile.set_word .PC entry
                for segment in elf.programs do
                  if segment.header.p_type == .PT_LOAD
                    then do let base := segment.header.p_vaddr.toNat
                            for i in [0:segment.file_data.size] do
                              Mem.set_byte (base + i) segment.file_data[i]!
                MonadMachine.getMachine

def dump_elf (elf: Elf): IO Unit
  := do IO.println s!"PC: {elf.e_header.e_entry.toNat}"
        IO.println s!"Program headers: {elf.programs.size}"
        for program in elf.programs do
          IO.println s!"  vaddr: {program.header.p_vaddr.toNat} paddr: {program.header.p_paddr.toNat} filesz: {program.header.p_filesz.toNat} memsz: {program.header.p_memsz.toNat}"
        IO.println s!"Section headers: {elf.sections.size}"
        for sec in elf.sections do
          IO.println s!"  addr: {sec.header.sh_addr.toNat} size: {sec.header.sh_size.toNat}"

def main : IO Unit
  := do let filename := "rust/output/hw.bin"
        let result <- Elf.ofFile filename
        match result with
        | Except.ok elf => dump_elf elf
        | Except.error error => IO.println s!"ERROR: {error}"

end Elf
