/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.ToVCVio.Oracle
import ZKLib.Data.MathOperations

/-!
  # Merkle Trees as a vector commitment
-/

-- instance : Fintype (BitVec n) := inferInstanceAs (Fin (2 ^ n))

namespace MerkleTree

open Mathlib OracleSpec OracleComp

variable (α : Type) [DecidableEq α] [Inhabited α] [Fintype α]

/-- Define the domain & range of the (single) oracle needed for constructing a Merkle tree with elements from some type `α`.

We may instantiate `α` with `BitVec n` or `Fin (2 ^ n)` to construct a Merkle tree for boolean vectors of length `n`. -/
def oracleSpec : OracleSpec Unit where
  domain _ := α × α
  range _ := α
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance
  range_inhabited' := inferInstance
  range_fintype' := inferInstance

@[simp]
lemma domain_def : (oracleSpec α).domain () = (α × α) := rfl

@[simp]
lemma range_def : (oracleSpec α).range () = α := rfl

/-- Example: a single hash computation -/
def singleHash (left : α) (right : α) : OracleComp (oracleSpec α) α := do
  let out ← query () ⟨left, right⟩
  return out

/-- Building the next layer of a Merkle tree, as an oracle computation. -/
def buildLayer (m : Nat) (leaves : Vector (α × α) (2 ^ m)) : OracleComp (oracleSpec α) (Vector α (2 ^ m)) :=
  (Vector.ofFn (n := 2 ^ m) (fun i => i)).mmap fun i => query (spec := oracleSpec α) () (leaves.get i)

/-- Building the Merkle tree from the bottommost layer to the root. -/
def build (m : Nat) (leaves : Vector α (2 ^ m)) : OracleComp (oracleSpec α) α := match m with
  | 0 => pure (leaves.get 0)
  | m + 1 => do
    have : 2 ^ (m + 1) = 2 * 2 ^ m := by omega
    let leaves := by rw [this] at leaves; exact leaves
    let leavesPair := Vector.chunkPairwise leaves
    let nextLayer ← buildLayer α m leavesPair
    return ← build m nextLayer

def exampleTest : OracleComp unifSpec Nat := do
  let x ← query 3 ()
  let y ← query 5 ()
  return x + y

#eval exampleTest.finSupport

end MerkleTree
