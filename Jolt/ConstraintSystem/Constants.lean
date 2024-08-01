

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
notation "BYTES_PER_INSTRUCTION" => (4 : UInt64)
notation "NUM_CIRCUIT_FLAGS" => (11 : Nat)
notation "NUM_INSTRUCTION_FLAGS" => (28 : Nat)
notation "LOG_M" => (16 : Nat)

example : 0x80000000 = RAM_START_ADDRESS := rfl
example : 0xffffffff = 4294967295 := rfl
