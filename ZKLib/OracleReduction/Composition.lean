/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Security

/-!
  # Composition of Interactive (Oracle) Protocols with Compatible Relations

  We compose an interactive (oracle) protocol for reducing relations R1 => R2 with
  another interactive (oracle) protocol for reducing relations R2 =>
  R3. This gives us an interactive (oracle) protocol for reducing relations R1 => R3.
-/

section Restrict

variable {n : ℕ}

abbrev ProtocolSpec.take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) :=
  Fin.take m h pSpec

abbrev ProtocolSpec.rtake (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) :=
  Fin.rtake m h pSpec

abbrev Transcript.take {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : Transcript pSpec) : Transcript (pSpec.take m h) :=
  Fin.take m h transcript

abbrev Transcript.rtake {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : Transcript pSpec) : Transcript (pSpec.rtake m h) :=
  Fin.rtake m h transcript

end Restrict

section Composition

variable {n m : ℕ}

/-- Adding a round with direction `dir` and type `Message` to the beginning of a `ProtocolSpec` -/
abbrev ProtocolSpec.cons (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  Fin.cons ⟨dir, Message⟩ pSpec

/-- Adding a round with direction `dir` and type `Message` to the end of a `ProtocolSpec` -/
abbrev ProtocolSpec.snoc (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  Fin.snoc pSpec ⟨dir, Message⟩

/-- Appending two `ProtocolSpec`s -/
abbrev ProtocolSpec.append (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) :
    ProtocolSpec (n + m) :=
  Fin.append pSpec pSpec'

def ProtocolSpec.mkSingle (dir : Direction) (Message : Type) : ProtocolSpec 1 :=
  fun _ => ⟨dir, Message⟩

infixl : 65 " ++ₚ " => ProtocolSpec.append

@[simp]
theorem ProtocolSpec.snoc_take {pSpec : ProtocolSpec n} (m : ℕ) (h : m < n) :
    (pSpec.take m (by omega) ++ₚ (fun (_ : Fin 1) => pSpec ⟨m, h⟩))
        = pSpec.take (m + 1) (by omega) := by
  simp only [append, take, Fin.append_right_eq_snoc, Fin.take_succ_eq_snoc]

/-- Appending two `ToOracle`s for two `ProtocolSpec`s -/
def ToOracle.append {pSpec₁ : ProtocolSpec n} {pSpec₂ : ProtocolSpec m}
    [O₁ : ∀ i, ToOracle (pSpec₁.Message i)] [O₂ : ∀ i, ToOracle (pSpec₂.Message i)] :
        ∀ i, ToOracle ((pSpec₁ ++ₚ pSpec₂).Message i) := fun ⟨i, h⟩ => by
  dsimp [ProtocolSpec.append, ProtocolSpec.getDir] at h ⊢
  dsimp [ProtocolSpec.Message, ProtocolSpec.getType]
  by_cases h' : i < n
  · rw [← Fin.castAdd_castLT m i h', Fin.append_left] at h ⊢
    exact O₁ ⟨i.castLT h', h⟩
  · rw [← @Fin.natAdd_subNat_cast n m i (not_lt.mp h'), Fin.append_right] at h ⊢
    exact O₂ ⟨Fin.subNat n (Fin.cast (add_comm n m) i) (not_lt.mp h'), h⟩

instance {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m}
    [∀ i, ToOracle (pSpec.Message i)] [∀ i, ToOracle (pSpec'.Message i)] :
    ∀ i, ToOracle ((pSpec ++ₚ pSpec').Message i) := ToOracle.append

/-- Appending two transcripts for two `ProtocolSpec`s -/
def Transcript.append {pSpec₁ : ProtocolSpec n} {pSpec₂ : ProtocolSpec m}
    (T₁ : Transcript pSpec₁) (T₂ : Transcript pSpec₂) : Transcript (pSpec₁ ++ₚ pSpec₂) := by
  dsimp [ProtocolSpec.append, ProtocolSpec.getDir]
  dsimp [Transcript, ProtocolSpec.getType] at T₁ T₂ ⊢
  exact fun i => (Fin.append_comp Prod.snd i) ▸ (Fin.addCases' T₁ T₂ i)

infixl : 65 " ++ₜ " => Transcript.append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def Transcript.snoc {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : Transcript pSpec) (dir : Direction) (msg : NextMessage) :
        Transcript (pSpec ++ₚ .mkSingle dir NextMessage) :=
  Transcript.append T fun _ => msg

end Composition

section Composition

variable {n m : ℕ} {pSpec₁ : ProtocolSpec n} {pSpec₂ : ProtocolSpec m} {ι : Type} [DecidableEq ι]
    {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut PrvState : Type}

@[simp]
theorem ProtocolSpec.take_append_left :
    (pSpec₁ ++ₚ pSpec₂).take n (Nat.le_add_right n m) = pSpec₁ := by
  simp only [take, append]
  have {i : Fin n} : Fin.castLE (by omega) i = Fin.castAdd m i := by
    simp only [Fin.castLE, Fin.castAdd]
  ext i <;>
  simp only [Fin.take_apply, this, Fin.append_left]

@[simp]
theorem Transcript.take_append_left (T : Transcript pSpec₁) (T' : Transcript pSpec₂) :
    ((T ++ₜ T').take n (Nat.le_add_right n m)) =
      (@ProtocolSpec.take_append_left _ _ pSpec₁ pSpec₂).symm ▸ T := by
  simp [Transcript.append, Transcript.take]
  ext i
  simp [Fin.castLE, Fin.addCases', Fin.addCases, eqRec_eq_cast, cast_eq_iff_heq]
  sorry

def ProverRound.append (P : ProverRound pSpec₁ oSpec PrvState)
    (P' : ProverRound pSpec₂ oSpec PrvState) :
    ProverRound (pSpec₁ ++ₚ pSpec₂) oSpec PrvState := sorry
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

def Prover.append (P : Prover pSpec₁ oSpec StmtIn WitIn StmtOut WitOut PrvState)
    (P' : ProverRound pSpec₂ oSpec PrvState) :
        Prover (pSpec₁ ++ₚ pSpec₂) oSpec StmtIn WitIn StmtOut WitOut PrvState where
  load := P.load
  toProverRound := ProverRound.append P.toProverRound P'
  output := P.output

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append (V : Verifier pSpec₁ oSpec StmtIn StmtOut)
    (V' : Verifier pSpec₂ oSpec StmtIn StmtOut) :
        Verifier (pSpec₁ ++ₚ pSpec₂) oSpec StmtIn StmtOut := sorry
  -- verify := fun stmt transcript => do
  --   let firstTranscript : Transcript pSpec₁ := by
  --     have := transcript.take n (by omega)
  --     simp at this; exact this
  --   let decision ← V.verify stmt firstTranscript
    -- let secondTranscript : Transcript pSpec₂ := by
    --   have := transcript.rtake m (by omega)
    --   sorry
    -- let decision' ← V'.verify stmt secondTranscript
    -- return decision ∧ decision'

def Protocol.append (P : Protocol pSpec₁ oSpec PrvState StmtIn WitIn StmtOut WitOut)
    (P' : Protocol pSpec₂ oSpec PrvState StmtIn WitIn StmtOut WitOut) :
    Protocol (pSpec₁ ++ₚ pSpec₂) oSpec PrvState StmtIn WitIn StmtOut WitOut := sorry
  -- prover := Prover.append P.prover P'.prover
  -- verifier := Verifier.append P.verifier P'.verifier

def OracleVerifier.append [O : ∀ i, ToOracle (pSpec₁.Message i)]
    [O' : ∀ i, ToOracle (pSpec₂.Message i)] (V : OracleVerifier pSpec₁ oSpec StmtIn StmtOut)
    (V' : OracleVerifier pSpec₂ oSpec StmtIn StmtOut) :
        OracleVerifier (pSpec₁ ++ₚ pSpec₂) oSpec StmtIn StmtOut := sorry
  -- genQueries := fun stmt transcript => do
  --   let queries ← V.genQueries stmt transcript.challenges
  --   let queries' ← V'.genQueries stmt transcript.challenges
  --   return queries ++ queries'
  -- verify := fun stmt transcript responseList => do
  --   let firstTranscript : Transcript pSpec₁ := by
  --     have := transcript.take n (by omega)
  --     simp at this; exact this
  --   let decision ← V.verify stmt firstTranscript
  --   let secondTranscript : Transcript pSpec₂ := by
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
