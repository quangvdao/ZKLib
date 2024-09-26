/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.InteractiveOracleReduction.Security
import ZKLib.Data.Math.Fin

/-!
  # Composition of Interactive (Oracle) Protocols with Compatible Relations

  We compose an interactive (oracle) protocol for reducing relations R1 => R2 with
  another interactive (oracle) protocol for reducing relations R2 =>
  R3. This gives us an interactive (oracle) protocol for reducing relations R1 => R3.
-/

section Composition

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
