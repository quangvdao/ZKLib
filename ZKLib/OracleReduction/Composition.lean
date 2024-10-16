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

variable {n m : ℕ} {PSpec : ProtocolSpec n} {PSpec' : ProtocolSpec m} {ι : Type} [DecidableEq ι]
    {OSpec : OracleSpec ι} {PrvState Statement Witness : Type}

@[simp]
theorem ProtocolSpec.take_append_eq_self (PSpec : ProtocolSpec n) (PSpec' : ProtocolSpec m) :
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

def Prover.append (P : Prover PSpec OSpec PrvState Statement Witness)
    (P' : ProverRound PSpec' OSpec PrvState) :
        Prover (PSpec ++ₚ PSpec') OSpec PrvState Statement Witness where
  load := P.load
  toProverRound := ProverRound.append P.toProverRound P'

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append (V : Verifier PSpec OSpec Statement) (V' : Verifier PSpec' OSpec Statement) :
    Verifier (PSpec ++ₚ PSpec') OSpec Statement where
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

def Protocol.append (P : Protocol PSpec OSpec PrvState Statement Witness)
    (P' : Protocol PSpec' OSpec PrvState Statement Witness) :
    Protocol (PSpec ++ₚ PSpec') OSpec PrvState Statement Witness := sorry
  -- prover := Prover.append P.prover P'.prover
  -- verifier := Verifier.append P.verifier P'.verifier

instance [O : ∀ i, ToOracle (PSpec.Message i)] [O' : ∀ i, ToOracle (PSpec'.Message i)] :
    ∀ i, ToOracle ((PSpec ++ₚ PSpec').Message i) := fun i =>
  {
    Query := Fin.addCases (fun j => (O j).Query) (fun j => (O' j).Query) i
    Response := Fin.addCases (fun j => (O j).Response) (fun j => (O' j).Response) i
    respond := fun msg query => by sorry
  }
    -- refine Fin.addCases ?_ ?_ i <;> intro j c <;>
    --   simp [ProtocolSpec.append] at c ⊢
    --   · exact (O j).respond (fun j => (O j).Query) (fun j => (O j).Response) query response
    --   · exact (O' j).respond (fun j => (O' j).Query) (fun j => (O' j).Response) query response

def OracleVerifier.append [O : ∀ i, ToOracle (PSpec.Message i)]
    [O' : ∀ i, ToOracle (PSpec'.Message i)] (V : OracleVerifier PSpec OSpec Statement)
    (V' : OracleVerifier PSpec' OSpec Statement) :
        OracleVerifier (PSpec ++ₚ PSpec') OSpec Statement := sorry
  -- genQueries := fun stmt transcript => do
  --   let queries ← V.genQueries stmt transcript.challenges
  --   let queries' ← V'.genQueries stmt transcript.challenges
  --   return queries ++ queries'
  -- verify := fun stmt transcript responseList => do
  --   let firstTranscript : Transcript PSpec := by
  --     have := transcript.take n (by omega)
  --     simp at this; exact this
  --   let decision ← V.verify stmt firstTranscript
  --   let secondTranscript : Transcript PSpec' := by
  --     have := transcript.rtake m (by omega)
  --     sorry
  --   let decision' ← V'.verify stmt secondTranscript
  --   return decision ∧ decision'

-- Define composition of multiple protocols via recursion

def ProtocolSpec.appendMany (rounds : List ℕ)
    (PSpecs : ∀ i : Fin rounds.length, ProtocolSpec (rounds.get i)) :
    ProtocolSpec (List.sum rounds) where
  Message := sorry
  Challenge := sorry

end Composition

section Security

-- Show that composition preserves security properties such as completeness and (all variants of)
-- soundness.

end Security
