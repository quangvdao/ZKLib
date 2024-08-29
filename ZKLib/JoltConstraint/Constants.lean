/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
  # Constants used in Jolt
-/


notation "RAM_START_ADDRESS" => (2147483648 : UInt64)
notation "PC_START_ADDRESS" => (2147483648 : UInt64)
notation "PC_NOOP_SHIFT" => (4 : UInt64)

notation "REGISTER_COUNT" => (64 : UInt64)

notation "MEMORY_OPS_PER_INSTRUCTION" => (7 : Nat)
notation "NUM_BYTECODE_VALUE_FIELDS" => (6 : Nat)
notation "NUM_MEM_WRITES" => (5 : Nat)
notation "NUM_BYTES_IN_WORD" => (4 : Nat)

notation "DEFAULT_MEMORY_SIZE" => (10485760 : UInt64) --0xA00000
notation "DEFAULT_STACK_SIZE" => (4096 : UInt64) --0x1000
notation "DEFAULT_MAX_INPUT_SIZE" => (4096 : UInt64) --0x1000
notation "DEFAULT_MAX_OUTPUT_SIZE" => (4096 : UInt64) --0x1000

notation "BYTES_PER_INSTRUCTION" => (4 : UInt64)
notation "NUM_CIRCUIT_FLAGS" => (11 : Nat)
notation "NUM_INSTRUCTION_FLAGS" => (28 : Nat)


-- notation "C" => (4 : Nat)
notation "LOG_M" => (16 : Nat)

notation "RS1" => (0 : Nat)
notation "RS2" => (1 : Nat)
notation "RD" => (2 : Nat)
notation "RAM_1" => (3 : Nat)
notation "RAM_2" => (4 : Nat)
notation "RAM_3" => (5 : Nat)
notation "RAM_4" => (6 : Nat)
notation "RAM_1_INDEX" => (RAM_1 - 3 : Nat)
notation "RAM_2_INDEX" => (RAM_2 - 3 : Nat)
notation "RAM_3_INDEX" => (RAM_3 - 3 : Nat)
notation "RAM_4_INDEX" => (RAM_4 - 3 : Nat)

example : 0x80000000 = RAM_START_ADDRESS := rfl
example : 0x80000000 = PC_START_ADDRESS := rfl
example : 0xffffffff = 4294967295 := rfl
