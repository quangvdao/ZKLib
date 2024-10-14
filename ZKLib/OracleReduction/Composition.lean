/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Security
import ZKLib.Data.Math.Fin

/-!
  # Composition of Interactive (Oracle) Protocols with Compatible Relations

  We compose an interactive (oracle) protocol for reducing relations R1 => R2 with
  another interactive (oracle) protocol for reducing relations R2 =>
  R3. This gives us an interactive (oracle) protocol for reducing relations R1 => R3.
-/

section Composition

@[simp]
theorem ProtocolSpec.take_append_eq_self {PSpec : ProtocolSpec n} {PSpec' : ProtocolSpec m} :
    (PSpec ++ₚ PSpec').take n (by omega) = PSpec := by
  simp [ProtocolSpec.append, ProtocolSpec.take]

def ProverRound.append (P : ProverRound PSpec OSpec PrvState)
  (P' : ProverRound PSpec' OSpec PrvState) :
  ProverRound (PSpec ++ₚ PSpec') OSpec PrvState where
  prove := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j c <;>
    simp [ProtocolSpec.append] at c ⊢
    · exact P.prove j c
    · exact P'.prove j c

def Prover.append (P : Prover PSpec OSpec PrvState Statement Witness) (P' : ProverRound PSpec' OSpec PrvState) : Prover (PSpec ++ₚ PSpec') OSpec PrvState Statement Witness where
  load := P.load
  toProverRound := ProverRound.append P.toProverRound P'

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append {PSpec : ProtocolSpec n} {PSpec' : ProtocolSpec m}
    (V : Verifier PSpec OSpec Statement) (V' : Verifier PSpec' OSpec Statement) : Verifier (PSpec ++ₚ PSpec') OSpec Statement where
  verify := fun stmt transcript => do
    let firstTranscript : Transcript PSpec := by
      have := transcript.take n (by omega)
      simp at this; exact this
    let decision ← V.verify stmt firstTranscript
    let secondTranscript : Transcript PSpec' := by
      have := transcript.rtake m (by omega)
      sorry
    let decision' ← V'.verify stmt secondTranscript
    return decision ∧ decision'


-- Define composition of multiple protocols via recursion

def ProtocolSpec.appendMany (rounds : List ℕ) (PSpecs : ∀ i : Fin rounds.length, ProtocolSpec (rounds.get i)) : ProtocolSpec (List.sum rounds) where
  Message := sorry
  Challenge := sorry

end Composition

section Security

-- Show that composition preserves security properties such as completeness and (all variants of) soundness.

end Security
