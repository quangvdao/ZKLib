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

variable {n m : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m} {ι : Type} [DecidableEq ι]
    {oSpec : OracleSpec ι} {PrvState Statement Witness : Type}

@[simp]
theorem ProtocolSpec.take_append_left :
    (pSpec ++ₚ pSpec').take n (Nat.le_add_right n m) = pSpec := by
  simp only [take, append]
  have {i : Fin n} : Fin.castLE (by omega) i = Fin.castAdd m i := by
    simp only [Fin.castLE, Fin.castAdd]
  ext i <;>
  simp only [Fin.take_apply, this, Fin.append_left]

@[simp]
theorem Transcript.take_append_left (T : Transcript pSpec) (T' : Transcript pSpec') :
    ((T ++ₜ T').take n (Nat.le_add_right n m)) =
      (@ProtocolSpec.take_append_left _ _ pSpec pSpec').symm ▸ T := by
  simp [Transcript.append, Transcript.take]
  have {i : Fin n} : Fin.castLE (by omega) i = Fin.castAdd m i := by
    simp [Fin.castLE, Fin.castAdd]
  simp [eqRec_eq_cast]
  ext i
  simp [Fin.take_apply, Fin.castLE, Fin.addCases', Fin.addCases]
  sorry

def ProverRound.append (P : ProverRound pSpec oSpec PrvState)
  (P' : ProverRound pSpec' oSpec PrvState) :
  ProverRound (pSpec ++ₚ pSpec') oSpec PrvState := sorry
  -- receiveChallenge := fun ⟨i, h⟩ => by
  --   refine Fin.addCases ?_ ?_ i <;> intro j c <;>
  --   simp [ProtocolSpec.append] at c ⊢
  --   · exact P.receiveChallenge j c
  --   · exact P'.receiveChallenge j c
  -- sendMessage := fun ⟨i, h⟩ => by
  --   refine Fin.addCases ?_ ?_ i <;> intro j c <;>
  --   simp [ProtocolSpec.append] at c ⊢
  --   · exact P.sendMessage j c
  --   · exact P'.sendMessage j c

def Prover.append (P : Prover pSpec oSpec PrvState Statement Witness)
    (P' : ProverRound pSpec' oSpec PrvState) :
        Prover (pSpec ++ₚ pSpec') oSpec PrvState Statement Witness where
  load := P.load
  toProverRound := ProverRound.append P.toProverRound P'

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append (V : Verifier pSpec oSpec Statement) (V' : Verifier pSpec' oSpec Statement) :
    Verifier (pSpec ++ₚ pSpec') oSpec Statement where
  verify := fun stmt transcript => do
    let firstTranscript : Transcript pSpec := by
      have := transcript.take n (by omega)
      simp at this; exact this
    let decision ← V.verify stmt firstTranscript
    let secondTranscript : Transcript pSpec' := by
      have := transcript.rtake m (by omega)
      sorry
    let decision' ← V'.verify stmt secondTranscript
    return decision ∧ decision'

def Protocol.append (P : Protocol pSpec oSpec PrvState Statement Witness)
    (P' : Protocol pSpec' oSpec PrvState Statement Witness) :
    Protocol (pSpec ++ₚ pSpec') oSpec PrvState Statement Witness := sorry
  -- prover := Prover.append P.prover P'.prover
  -- verifier := Verifier.append P.verifier P'.verifier

instance [O : ∀ i, ToOracle (pSpec.Message i)] [O' : ∀ i, ToOracle (pSpec'.Message i)] :
    ∀ i, ToOracle ((pSpec ++ₚ pSpec').Message i) := sorry
  -- {
  --   Query := Fin.addCases (fun j => (O j).Query) (fun j => (O' j).Query) i
  --   Response := Fin.addCases (fun j => (O j).Response) (fun j => (O' j).Response) i
  --   respond := fun msg query => by sorry
  -- }
    -- refine Fin.addCases ?_ ?_ i <;> intro j c <;>
    --   simp [ProtocolSpec.append] at c ⊢
    --   · exact (O j).respond (fun j => (O j).Query) (fun j => (O j).Response) query response
    --   · exact (O' j).respond (fun j => (O' j).Query) (fun j => (O' j).Response) query response

def OracleVerifier.append [O : ∀ i, ToOracle (pSpec.Message i)]
    [O' : ∀ i, ToOracle (pSpec'.Message i)] (V : OracleVerifier pSpec oSpec Statement)
    (V' : OracleVerifier pSpec' oSpec Statement) :
        OracleVerifier (pSpec ++ₚ pSpec') oSpec Statement := sorry
  -- genQueries := fun stmt transcript => do
  --   let queries ← V.genQueries stmt transcript.challenges
  --   let queries' ← V'.genQueries stmt transcript.challenges
  --   return queries ++ queries'
  -- verify := fun stmt transcript responseList => do
  --   let firstTranscript : Transcript pSpec := by
  --     have := transcript.take n (by omega)
  --     simp at this; exact this
  --   let decision ← V.verify stmt firstTranscript
  --   let secondTranscript : Transcript pSpec' := by
  --     have := transcript.rtake m (by omega)
  --     sorry
  --   let decision' ← V'.verify stmt secondTranscript
  --   return decision ∧ decision'

-- Define composition of multiple protocols via recursion

def ProtocolSpec.appendList (rounds : List ℕ)
    (pSpecs : ∀ i : Fin rounds.length, ProtocolSpec (rounds.get i)) :
    ProtocolSpec rounds.sum := sorry

end Composition

section Security

-- Show that composition preserves security properties such as completeness and (all variants of)
-- soundness.

end Security
