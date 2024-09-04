import ZKLib.ToVCVio.Oracle
import Batteries.Data.Array.Monadic

/-!
  # Merkle Trees
-/

namespace List

def test_mapM {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u} (as : List α) (f : α → m β) :=
    (as.mapM f)

-- @[simp] theorem length_mapM {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u} (as : List α) (f : α → m β) :
--     SatisfiesM (fun res => res.length = as.length) (as.mapM f) := by
--   induction as with
--   | nil => simp [List.mapM, List.mapM.loop, SatisfiesM]; use pure ⟨ [], by simp⟩ ; simp
--   | cons _ as ih => simp [List.mapM, List.mapM.loop, ih]

end List

#check Array.size_mapM

-- TODO: add `range` lemmas to `Array`, similar to `List.range` lemmas

namespace Array

@[simp]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := sorry

def finRange (n : Nat) : Array (Fin n) := Array.ofFn (fun i => i)

end Array

namespace Mathlib

namespace Vector

def interleave {n : Nat} (xs : Vector α n) (ys : Vector α n) : Vector α (2 * n) := sorry

-- def pairwise {α : Type} {n : Nat} (v : Vector α (2 * n)) : Vector (α × α) n :=
--   Vector.ofFn (fun i =>
--     let j := 2 * i
--     (v.get ⟨j, by omega; exact i.isLt⟩,
--      v.get ⟨j + 1, by simp [Nat.mul_two, Nat.lt_succ]; exact i.isLt⟩))

def chunkPairwise {α : Type} : {n : Nat} → Vector α (2 * n) → Vector (α × α) n
  | 0, Vector.nil => Vector.nil
  | n + 1, xs => by
    have : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [this] at xs
    exact ⟨xs.head, xs.tail.head⟩ ::ᵥ chunkPairwise xs.tail.tail

end Vector

end Mathlib

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
