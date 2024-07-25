import Mathlib.FieldTheory.Finite.Basic
import Jolt.Relation.Basic
import Jolt.RiscV.ISA

/-!
  # The Jolt Relation

  This file contains the specification for the Jolt relation, which is a combination of R1CS, lookups, and memory-checking (both read-only and read-write).

  We will show that the Jolt relation is exactly equal to the execution of RISC-V programs.

  Many of our specification draws directly from the main [Rust codebase](https://github.com/a16z/jolt).
-/


namespace RiscV

inductive RV32IM where
  opcode : UInt7

structure ELFInstruction where
  addr : UInt64
  opcode : RV32IM




end RiscV

variable {F : Type} [Field F] [Fintype F] [Inhabited F]
