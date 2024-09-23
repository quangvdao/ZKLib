/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.InteractiveOracleReduction.Security
import Mathlib.Data.Matrix.Reflection

/-!
  # Composition of Interactive (Oracle) Protocols with Compatible Relations

  We compose an interactive (oracle) protocol for reducing relations R1 => R2 with
  another interactive (oracle) protocol for reducing relations R2 =>
  R3. This gives us an interactive (oracle) protocol for reducing relations R1 => R3.
-/

namespace FinVec

/-- Take the first `m` elements of a finite vector -/
def take {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) : Fin m → α :=
  v ∘ Fin.castLE (by omega)

/-- Take the last `m` elements of a finite vector -/
def rtake {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) : Fin m → α :=
  v ∘ Fin.cast (by omega) ∘ Fin.natAdd (n - m)

/-- The empty vector (for any `α : Sort u`) -/
@[inline, reducible]
def empty {α : Sort u} : Fin 0 → α := Fin.elim0

@[simp]
theorem take_zero {n : ℕ} {α : Sort u} (v : Fin n → α) :
    take v 0 = empty := by ext i; exact Fin.elim0 i

@[simp]
theorem take_all {n : ℕ} {α : Sort u} (v : Fin n → α) :
    take v ⟨n, by omega⟩ = v := by ext i; simp [take]

-- @[simp]
-- theorem take_succ {n : ℕ} {α : Sort u} (v : Fin (n + 1) → α) (m : Fin (n + 1)) :
--     take v (Fin.succ m) = Fin.addCases (v 0) (take (v ∘ Fin.succ) m) := by
--   ext i <;> simp [take]

@[simp]
theorem rtake_zero {n : ℕ} {α : Sort u} (v : Fin n → α) :
    rtake v 0 = empty := by ext i; exact Fin.elim0 i

@[simp]
theorem rtake_all {n : ℕ} {α : Sort u} (v : Fin n → α) :
    rtake v ⟨n, by omega⟩ = v := by ext i; simp [rtake, Fin.natAdd]

#check Fin.succRecOn

#check Fin.succRec

-- @[simp]
-- theorem rtake_succ {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     rtake v (Fin.succ m) = Fin.addCases (v (Fin.cast (by omega) (Fin.natAdd (n - m) m))) (rtake (v ∘ Fin.succ) m) := by
--   ext i <;> simp [rtake, Fin.natAdd]

-- @[simp]
-- theorem rtake_eq_take_rev {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     rtake v m = take v m ∘ Fin.rev := by
--   ext i
--   simp [rtake, take, Fin.natAdd, Fin.cast, Fin.rev]
--   congr;

-- @[simp]
-- theorem take_addCases_rtake_eq_self {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     fun i => Fin.addCases (take v m) (rtake v (n - m)) i = v := by
--   ext i
--   refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [take, rtake]
--   · exact v j
--   · exact v (Fin.addNat j (n - m))


end FinVec

namespace FinDVec

/-- Restrict a finite dependent vector to the first `m` elements -/
def take {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) (m : Fin (n + 1)) :
    (i : Fin m) → α (Fin.castLE (by omega) i) :=
  fun i => v (Fin.castLE (by omega) i)

/-- Restrict a finite dependent vector to the last `m` elements -/
def rtake {n : ℕ} {α : Fin n → Sort u} (v : (i : Fin n) → α i) (m : Fin (n + 1)) :
    (i : Fin m) → α (Fin.cast (by omega) (Fin.castAdd (n := m) (n - m) i)) :=
  fun i => v (Fin.cast (by omega) (Fin.castAdd (n := m) (n - m) i))

-- TODO: add `simp` theorems for `take` and `rtake`

end FinDVec

section Restrict

-- #check FinVec

-- #check vecAppend

/-- For a protocol specification `PSpec` with `n` rounds, restrict `PSpec` to the first `cutoff` rounds. -/
@[inline, reducible, simps]
def ProtocolSpec.restrictFirst (PSpec : ProtocolSpec n) (cutoff : Fin (n + 1)) : ProtocolSpec cutoff where
  Message := FinVec.take PSpec.Message cutoff
  Challenge := FinVec.take PSpec.Challenge cutoff

/-- For a protocol specification `PSpec` with `n` rounds, restrict `PSpec` to the last `cutoff` rounds. -/
@[inline, reducible, simps]
def ProtocolSpec.restrictLast (PSpec : ProtocolSpec n) (cutoff : Fin (n + 1)) : ProtocolSpec cutoff where
  Message := FinVec.rtake PSpec.Message cutoff
  Challenge := FinVec.rtake PSpec.Challenge cutoff

@[simp]
theorem ProtocolSpec.restrictFirst_nil (PSpec : ProtocolSpec n) :
    ProtocolSpec.restrictFirst PSpec 0 = emptyPSpec := by
  ext i <;> exact Fin.elim0 i

@[simp]
theorem ProtocolSpec.restrictFirst_full (PSpec : ProtocolSpec n) :
    ProtocolSpec.restrictFirst PSpec ⟨n, by omega⟩ = PSpec := by
  ext i <;> simp [ProtocolSpec.restrictFirst]

@[simp]
theorem ProtocolSpec.restrictLast_nil (PSpec : ProtocolSpec n) :
    ProtocolSpec.restrictLast PSpec 0 = emptyPSpec := by
  ext i <;> exact Fin.elim0 i

@[simp]
theorem ProtocolSpec.restrictLast_full (PSpec : ProtocolSpec n) :
    ProtocolSpec.restrictLast PSpec ⟨n, by omega⟩ = PSpec := by
  ext i <;> simp [ProtocolSpec.restrictLast, Fin.addNat]

end Restrict
namespace Protocol
section Composition

/-- Sequential composition of two protocols -/
def ProtocolSpec.append (PSpec : ProtocolSpec n) (PSpec' : ProtocolSpec m) : ProtocolSpec (n + m) where
  Message := Fin.addCases PSpec.Message PSpec'.Message
  Challenge := Fin.addCases PSpec.Challenge PSpec'.Challenge

def OracleProtocolSpec.append (PSpec : OracleProtocolSpec n) (PSpec' : OracleProtocolSpec m) :
  OracleProtocolSpec (n + m) where
  toProtocolSpec := ProtocolSpec.append PSpec.toProtocolSpec PSpec'.toProtocolSpec
  Query := Fin.addCases PSpec.Query PSpec'.Query
  Response := Fin.addCases PSpec.Response PSpec'.Response
  oracleize := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j msg <;>
    unfold ProtocolSpec.Message ProtocolSpec.append at msg <;>
    simp at msg <;> simp <;>
    exact PSpec.oracleize j msg ; exact PSpec'.oracleize j msg

infixl : 65 " ++ₚ " => ProtocolSpec.append
infixl : 65 " ++ₒₚ " => OracleProtocolSpec.append

def Messages.append (M1 : Messages PSpec1) (M2 : Messages PSpec2) :
    Messages (PSpec1 ++ₚ PSpec2) := fun i => by
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [ProtocolSpec.append]
  · exact M1 j
  · exact M2 j

def Challenges.append (C1 : Challenges PSpec1) (C2 : Challenges PSpec2) :
    Challenges (PSpec1 ++ₚ PSpec2) := fun i => by
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [ProtocolSpec.append]
  · exact C1 j
  · exact C2 j

def Transcript.append (T1 : Transcript PSpec1) (T2 : Transcript PSpec2) :
    Transcript (PSpec1 ++ₚ PSpec2) where
  messages := Messages.append (PSpec1 := PSpec1)
    T1.messages T2.messages
  challenges := Challenges.append (PSpec1 := PSpec1)
    T1.challenges T2.challenges

def ProverRound.append (P1 : ProverRound PSpec OSpec PrvState)
  (P2 : ProverRound PSpec' OSpec PrvState) :
  ProverRound (PSpec ++ₚ PSpec') OSpec PrvState where
  prove := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j c <;> simp [ProtocolSpec.append]
    · simp [ProtocolSpec.append] at c
      exact P1.prove j c
    · simp [ProtocolSpec.append] at c
      exact P2.prove j c

-- def Prover.append (P : Prover PSpec OSpec PrvState Statement Witness) (P' : Prover PSpec' OSpec PrvState Statement Witness) : Prover (PSpec ++ₚ PSpec') OSpec PrvState Statement Witness where
--   loadState := fun ⟨stmt, wit⟩ => ⟨P.loadState stmt wit, P'.loadState stmt wit⟩
--   prove := ProverRound.append P.prove P'.prove

-- def Verifier.append {PSpec : ProtocolSpec n} {PSpec' : ProtocolSpec m}
--   (V : Verifier PSpec OSpec Statement) (V' : Verifier PSpec' OSpec Statement) : Verifier (PSpec ++ₚ PSpec') OSpec Statement where
--   verify := fun stmt transcript => do
--     let ⟨t1, t2⟩ ← V.verify stmt transcript.restrictFirst m
--     let ⟨t2, t2⟩ ← V'.verify stmt transcript.restrictLast (n - m)
--     return Fin.addCases t1 t2


-- Define composition of multiple protocols via recursion

def ProtocolSpec.appendMany (rounds : List ℕ) (PSpecs : ∀ i : Fin rounds.length, ProtocolSpec (rounds.get i)) : ProtocolSpec (List.sum rounds) where
  Message := sorry
  Challenge := sorry

end Composition

section Security

-- Show that composition preserves security properties such as completeness and (all variants of) soundness.

end Security

end Protocol
