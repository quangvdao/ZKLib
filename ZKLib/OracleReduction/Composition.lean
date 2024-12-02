/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Security

/-!
  # Composition of Interactive (Oracle) Reductions with Compatible Relations

  We compose an interactive (oracle) reduction for reducing relations R1 => R2 with
  another interactive (oracle) reduction for reducing relations R2 => R3. This gives us an
  interactive (oracle) reduction for reducing relations R1 => R3.
-/

namespace Fin

#check Fin.hIterate

#check Fin.succ_castPred_eq_add_one

def foldCasesFrom {n} (α : Fin (n + 1) → Sort*) (f : ∀ (i : Fin n), α i.castSucc → α i.succ)
      (i : Fin (n + 1)) (a : α i) : α (last n) :=
  if h : i ≠ last n then
    haveI this : α (i + 1) := by simpa [succ_castPred_eq_add_one] using (f (i.castPred h) a)
    foldCasesFrom α f (i+1) this
  else
    _root_.cast (congrArg α (not_not.mp h)) a
  termination_by n - i
  decreasing_by
    have h0 : i < last n := lt_last_iff_ne_last.mpr h
    have h1 : i.val < n := by omega
    have h2 : (i + 1).val = i.val + 1 := by simp [val_add, h1]
    rw [h2]
    exact Nat.sub_add_lt_sub h1 (by omega)

def foldCases {n} (α : Fin (n + 1) → Sort*) (f : ∀(i : Fin n), α i.castSucc → α i.succ)
    (init : α 0) : α (last n) := foldCasesFrom α f 0 init

-- def foldlCases' (f : ∀ i, α i.castSucc → β i → α i.succ) (init : α 0) (v : (i : Fin n) → β i) :
--     α (Fin.last n) := by
--   induction n with
--   | zero => exact init
--   | succ n ih =>
--     exact @ih (α ∘ Fin.succ) (β ∘ Fin.succ) (fun i a => f i.succ a)
--       (f 0 init (v ⟨0, by omega⟩)) (fun i => v i.succ)

end Fin

namespace ProtocolSpec

section Restrict

variable {n : ℕ}

abbrev take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) := Fin.take m h pSpec

abbrev rtake (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) := Fin.rtake m h pSpec

abbrev FullTranscript.take {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.take m h) :=
  Fin.take m h transcript

abbrev FullTranscript.rtake {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.rtake m h) :=
  Fin.rtake m h transcript

end Restrict

variable {m n : ℕ}

/-- Adding a round with direction `dir` and type `Message` to the beginning of a `ProtocolSpec` -/
abbrev cons (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) := Fin.cons ⟨dir, Message⟩ pSpec

/-- Adding a round with direction `dir` and type `Message` to the end of a `ProtocolSpec` -/
abbrev snoc (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) := Fin.snoc pSpec ⟨dir, Message⟩

/-- Appending two `ProtocolSpec`s -/
abbrev append (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) : ProtocolSpec (m + n) :=
  Fin.append pSpec pSpec'

@[inline, reducible]
def mkSingle (dir : Direction) (Message : Type) : ProtocolSpec 1 := fun _ => ⟨dir, Message⟩

infixl : 65 " ++ₚ " => ProtocolSpec.append

def ProtocolSpec.join {n : Fin (m + 1) → ℕ} (pSpec : ∀ i, ProtocolSpec (n i)) :=
  Fin.foldCases (α := fun i => ProtocolSpec (∑ j ≤ i, n j))
    (fun i acc => by stop exact acc ++ₚ pSpec i.succ)
    (by stop exact pSpec 0)

@[simp]
theorem snoc_take {pSpec : ProtocolSpec n} (k : ℕ) (h : k < n) :
    (pSpec.take k (by omega) ++ₚ (fun (_ : Fin 1) => pSpec ⟨k, h⟩))
      = pSpec.take (k + 1) (by omega) := by
  simp only [append, take, Fin.append_right_eq_snoc, Fin.take_succ_eq_snoc]

/-- Appending two transcripts for two `ProtocolSpec`s -/
def FullTranscript.append {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
        FullTranscript (pSpec₁ ++ₚ pSpec₂) := by
  dsimp only [ProtocolSpec.append, ProtocolSpec.getDir, FullTranscript, ProtocolSpec.getType]
    at T₁ T₂ ⊢
  exact fun i => (Fin.append_comp' Prod.snd i) ▸ (Fin.addCases' T₁ T₂ i)

infixl : 65 " ++ₜ " => FullTranscript.append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def FullTranscript.snoc {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : FullTranscript pSpec) (dir : Direction) (msg : NextMessage) :
        FullTranscript (pSpec ++ₚ .mkSingle dir NextMessage) :=
  FullTranscript.append T fun _ => msg

section Test

def pSpecTest : ProtocolSpec 2 := ![⟨.P_to_V, Nat⟩, ⟨.V_to_P, Rat⟩]

def pSpecCombined : ProtocolSpec 4 := pSpecTest ++ₚ pSpecTest

theorem pSpecCombined_eq :
    pSpecCombined = ![⟨.P_to_V, Nat⟩, ⟨.V_to_P, Rat⟩, ⟨.P_to_V, Nat⟩, ⟨.V_to_P, Rat⟩] := by
  funext i
  dsimp only [pSpecCombined, pSpecTest, ProtocolSpec.append, Fin.append, Fin.addCases, Fin.castLT,
    Fin.subNat, Fin.cast]
  fin_cases i <;> simp

end Test

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

@[simp]
theorem take_append_left :
    (pSpec₁ ++ₚ pSpec₂).take m (Nat.le_add_right m n) = pSpec₁ := by
  simp only [take, append]
  have {i : Fin m} : Fin.castLE (by omega) i = Fin.castAdd n i := by
    simp only [Fin.castLE, Fin.castAdd]
  ext i <;>
  simp only [Fin.take_apply, this, Fin.append_left]

@[simp]
theorem Transcript.take_append_left (T : FullTranscript pSpec₁) (T' : FullTranscript pSpec₂) :
    ((T ++ₜ T').take m (Nat.le_add_right m n)) =
      (@take_append_left _ _ pSpec₁ pSpec₂).symm ▸ T := by
  simp [FullTranscript.append, FullTranscript.take, ProtocolSpec.append]
  ext i
  simp [Fin.castLE, Fin.addCases', Fin.addCases, eqRec_eq_cast, cast_eq_iff_heq]
  refine heq_of_eq_cast ?_ ?_
  simp [Fin.append, Fin.addCases]
  sorry

def FullTranscript.fst (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₁ :=
  fun i => by
    simpa only [getType_apply, ProtocolSpec.append, Fin.append_left] using T (Fin.castAdd n i)

def FullTranscript.snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₂ :=
  fun i => by
    simpa only [getType_apply, ProtocolSpec.append, Fin.append_right] using T (Fin.natAdd m i)

@[simp]
theorem FullTranscript.append_fst (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).fst = T₁ := by
  funext i
  simp [FullTranscript.fst, FullTranscript.append, eqRec_eq_cast]

@[simp]
theorem FullTranscript.append_snd (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).snd = T₂ := by
  funext i
  simp [FullTranscript.snd, FullTranscript.append, eqRec_eq_cast]

def MessageIndex.inl (i : MessageIndex pSpec₁) : MessageIndex (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [getDir_apply, Fin.append_left] using i.2⟩

def MessageIndex.inr (i : MessageIndex pSpec₂) : MessageIndex (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [getDir_apply, Fin.append_right] using i.2⟩

def ChallengeIndex.inl (i : ChallengeIndex pSpec₁) : ChallengeIndex (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [getDir_apply, Fin.append_left] using i.2⟩

def ChallengeIndex.inr (i : ChallengeIndex pSpec₂) : ChallengeIndex (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [getDir_apply, Fin.append_right] using i.2⟩

@[simps!]
def ChallengeIndex.sumEquiv :
    ChallengeIndex pSpec₁ ⊕ ChallengeIndex pSpec₂ ≃ ChallengeIndex (pSpec₁ ++ₚ pSpec₂) where
  toFun := Sum.elim (ChallengeIndex.inl) (ChallengeIndex.inr)
  invFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  left_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [ChallengeIndex.inl, ChallengeIndex.inr, h, isLt]
  right_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [ChallengeIndex.inl, ChallengeIndex.inr, hi]
    congr; omega

end ProtocolSpec

open ProtocolSpec

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} {ι : Type} [DecidableEq ι]
    {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}

section Instances

/-- If two protocols have sampleable challenges, then their concatenation also has sampleable
  challenges. -/
instance [h₁ : ∀ i, Sampleable (pSpec₁.Challenge i)] [h₂ : ∀ i, Sampleable (pSpec₂.Challenge i)] :
    ∀ i, Sampleable ((pSpec₁ ++ₚ pSpec₂).Challenge i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  by_cases h' : i < m <;> simp [h'] at h ⊢
  · exact h₁ ⟨⟨i, by omega⟩, h⟩
  · exact h₂ ⟨⟨i - m, by omega⟩, h⟩

/-- If two protocols' messages have oracle representations, then their concatenation's messages also
    have oracle representations. -/
instance [O₁ : ∀ i, ToOracle (pSpec₁.Message i)] [O₂ : ∀ i, ToOracle (pSpec₂.Message i)] :
    ∀ i, ToOracle ((pSpec₁ ++ₚ pSpec₂).Message i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.append, ProtocolSpec.getDir, Fin.append, Fin.addCases,
    Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  by_cases h' : i < m <;> simp [h'] at h ⊢
  · exact O₁ ⟨⟨i, by omega⟩, h⟩
  · exact O₂ ⟨⟨i - m, by omega⟩, h⟩

open OracleComp OracleSpec SubSpec

variable [∀ i, Sampleable (pSpec₁.Challenge i)] [∀ i, Sampleable (pSpec₂.Challenge i)]

variable {ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}
    (oa : OracleComp spec α)

-- lemma evalDist_eq (h : OracleComp spec α = OracleComp spec' β) :
--     evalDist (h.mp oa) = h.mpr ▸ evalDist oa := by
--   induction h; rfl

instance : SubSpec (challengeOracle pSpec₁ ++ₒ challengeOracle pSpec₂)
    (challengeOracle (pSpec₁ ++ₚ pSpec₂)) where
  toFun := fun i _ => by
    cases i with
    | inl j =>
      convert query (spec := challengeOracle (pSpec₁ ++ₚ pSpec₂)) j.inl ()
      simp [OracleSpec.append, ChallengeIndex.inl, ProtocolSpec.append]
    | inr j =>
      convert query (spec := challengeOracle (pSpec₁ ++ₚ pSpec₂)) j.inr ()
      simp [OracleSpec.append, ChallengeIndex.inr, ProtocolSpec.append]
  evalDist_toFun' := fun i q => by
    cases i with
    | inl j =>
      simp [Eq.mpr]
      -- rw [evalDist_eqRec (spec := challengeOracle (pSpec₁ ++ₚ pSpec₂)) (β := sorry) (query j.inl ()) _]
      sorry
    | inr j =>
      simp [OracleSpec.append, ChallengeIndex.inr, ProtocolSpec.append]
      sorry

end Instances

/--
Appending two provers corresponding to two reductions, where the output statement & witness type for
the first prover is equal to the input statement & witness type for the second prover. We also
require a verifier for the first protocol in order to derive the intermediate statement for the
second prover.

This is defined by combining the two provers' private states and functions, with the exception that
the last private state of the first prover is "merged" into the first private state of the second
prover (via outputting the new statement and witness, and then inputting these into the second
prover). -/
def Prover.append (P₁ : Prover pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (P₂ : Prover pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) :
      Prover (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ where

  /- The combined prover's states are the concatenation of the first prover's states, except the
  last one, and the second prover's states. -/
  PrvState := Fin.append (m := m) (Fin.init P₁.PrvState) P₂.PrvState ∘ Fin.cast (by omega)

  /- The combined prover's input function is the first prover's input function, except for when the
  first protocol is empty, in which case it is the second prover's input function -/
  input := fun stmt wit => by
    by_cases h : m > 0
    · simp [Fin.append, Fin.addCases, Fin.init, Fin.castLT, h]
      exact P₁.input stmt wit
    · simp [Fin.append, Fin.addCases, h, Fin.subNat]
      exact (
        letI state := P₁.input stmt wit
        haveI : 0 = Fin.last m := by aesop
        haveI state : P₁.PrvState (Fin.last m) := by simpa [this] using state
        P₂.input.uncurry (P₁.output state))

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m - 1`, then it sends the message & updates the state as the first prover
  - if `i = m - 1`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. It needs to
    provide a `stmt₂` for the second prover, which it derives from running the verifier on the first
    transcript. -/
  sendMessage := fun ⟨⟨i, hLt⟩, h⟩ state => by
    by_cases hi : i < m
    · dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state ⊢
      by_cases hi' : i + 1 < m
      · simp [hi, hi'] at h state ⊢
        exact P₁.sendMessage ⟨⟨i, hi⟩, h⟩ state
      · haveI : i + 1 = m := by omega
        simp [hi, this] at h state ⊢
        exact (do
          let ⟨msg, state⟩ ← P₁.sendMessage ⟨⟨i, hi⟩, h⟩ state
          haveI state : P₁.PrvState (Fin.last m) := by
            simpa only [Fin.last, Fin.succ_mk, this] using state
          return ⟨msg, P₂.input.uncurry (P₁.output state)⟩)
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi, this,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state ⊢
      exact (do
        let ⟨msg, newState⟩ ← P₂.sendMessage ⟨⟨i - m, by omega⟩, h⟩ state
        haveI newState : P₂.PrvState ⟨i + 1 - m, by omega⟩ := by
          haveI : i + 1 - m = i - m + 1 := by omega
          simpa only [this, Fin.succ] using newState
        return ⟨msg, newState⟩)

  /- Receiving challenges is implemented essentially the same as sending messages, modulo the
  difference in direction. -/
  receiveChallenge := fun ⟨⟨i, hLt⟩, h⟩ state chal => by
    by_cases hi : i < m
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state chal ⊢
      by_cases hi' : i + 1 < m
      · simp [hi']
        exact P₁.receiveChallenge ⟨⟨i, hi⟩, h⟩ state chal
      · haveI : i + 1 = m := by omega
        simp [this]
        exact (
          letI newState := P₁.receiveChallenge ⟨⟨i, hi⟩, h⟩ state chal
          haveI newState : P₁.PrvState (Fin.last m) := by
            simpa [Fin.last, this] using newState
          P₂.input.uncurry (P₁.output newState))
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi, this,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state chal ⊢
      exact (
        letI newState := P₂.receiveChallenge ⟨⟨i - m, by omega⟩, h⟩ state chal
        haveI newState : P₂.PrvState ⟨i + 1 - m, by omega⟩ := by
          haveI : i + 1 - m = i - m + 1 := by omega
          simpa [Fin.succ, this] using newState
        newState)

  /- The combined prover's output function is simply the second prover's output function. -/
  output := fun state => by
    simp [Fin.append, Fin.addCases, Fin.last] at state
    exact P₂.output state

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append (V₁ : Verifier pSpec₁ oSpec Stmt₁ Stmt₂)
    (V₂ : Verifier pSpec₂ oSpec Stmt₂ Stmt₃) :
      Verifier (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Stmt₃ where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Composition of reductions boils down to composing the provers and verifiers. -/
def Reduction.append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) :
      Reduction (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ where
  prover := Prover.append R₁.prover R₂.prover
  verifier := Verifier.append R₁.verifier R₂.verifier

def Reduction.join {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    {Stmt : Fin (m + 2) → Type} {Wit : Fin (m + 2) → Type}
    (R : ∀ i, Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ)
      (Wit i.succ)) :
      Reduction (ProtocolSpec.join pSpec) oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last (m + 1)))
      (Wit (Fin.last (m + 1))) := sorry
  -- Fin.foldCases (α := fun i => Reduction (ProtocolSpec.join (pSpec ∘ Fin.take i (by omega))) oSpec (Stmt i.castSucc) (Wit i.castSucc)
  --   (Stmt i.succ) (Wit i.succ))
  --   (fun i acc => Reduction.append acc (R i))
  --   (R 0)

variable [O₁ : ∀ i, ToOracle (pSpec₁.Message i)] [O₂ : ∀ i, ToOracle (pSpec₂.Message i)]

def OracleVerifier.append (V : OracleVerifier pSpec₁ oSpec Stmt₁ Stmt₂)
    (V' : OracleVerifier pSpec₂ oSpec Stmt₂ Stmt₃) :
      OracleVerifier (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Stmt₃ where
  genQueries := fun stmt transcript => do sorry
    -- let queries ← V.genQueries stmt transcript.fst.challenges
    -- let queries' ← V'.genQueries stmt transcript.snd.challenges
    -- return queries ++ queries'
  verify := fun stmt transcript responseList => do sorry
    -- let firstTranscript : FullTranscript pSpec₁ := by
    --   have := transcript.take n (by omega)
    --   simp at this; exact this
    -- let stmt₂ ← V.verify stmt firstTranscript
    -- let secondTranscript : FullTranscript pSpec₂ := by
    --   have := transcript.rtake m (by omega)
    --   sorry
    -- return ← V'.verify stmt₂ secondTranscript

def OracleReduction.append (R₁ : OracleReduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : OracleReduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) :
      OracleReduction (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

-- Define composition of multiple reductions via recursion with `Fin.fold`

section Execution

variable [∀ i, Sampleable (pSpec₁.Challenge i)] [∀ i, Sampleable (pSpec₂.Challenge i)]

-- theorem Prover.append_run (P₁ : Prover pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
--     (P₂ : Prover pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) (stmt : Stmt₁) (wit : Wit₁) :
--       (P₁.append P₂).run stmt wit = (do
--         let result ← P₁.run stmt wit
--         return ← P₂.output state) := sorry

-- TODO: Need to define a function that "extracts" the second prover from the combined prover

end Execution

section Security

open scoped NNReal

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} [∀ i, Sampleable (pSpec₁.Challenge i)]
    [∀ i, Sampleable (pSpec₂.Challenge i)] {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {rel₁ : Stmt₁ → Wit₁ → Prop} {rel₂ : Stmt₂ → Wit₂ → Prop} {rel₃ : Stmt₃ → Wit₃ → Prop}

namespace Reduction

/-- If two reductions satisfy completeness with compatible relations, then their concatenation also
  satisfies completeness with the sum of the completeness errors. -/
theorem completeness_append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness rel₁ rel₃ (completenessError₁ + completenessError₂) := sorry

/-- If two reductions satisfy perfect completeness with compatible relations, then their
  concatenation also satisfies perfect completeness. -/
theorem perfectCompleteness_append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃)
    (h₁ : R₁.perfectCompleteness rel₁ rel₂) (h₂ : R₂.perfectCompleteness rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness rel₁ rel₃ := by
  dsimp [perfectCompleteness] at h₁ h₂ ⊢
  convert Reduction.completeness_append R₁ R₂ h₁ h₂
  simp only [add_zero]

end Reduction

end Security
