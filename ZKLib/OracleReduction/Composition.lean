/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Basic

/-!
  # Composition of Interactive (Oracle) Protocols with Compatible Relations

  We compose an interactive (oracle) protocol for reducing relations R1 => R2 with
  another interactive (oracle) protocol for reducing relations R2 =>
  R3. This gives us an interactive (oracle) protocol for reducing relations R1 => R3.
-/

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
  simp [cast]
  sorry

theorem Transcript.eq_left_of_append (k : Fin (m + 1))
    (T : Transcript ⟨k, by omega⟩ (pSpec₁ ++ₚ pSpec₂)) : True := sorry
  --   (T.take m (by omega)).cast (by simp) = T.cast (by simp) := by
  -- sorry

def FullTranscript.fst (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₁ :=
  fun i => by
    simpa only [getType_apply, ProtocolSpec.append, Fin.append_left] using T (Fin.castAdd n i)

def FullTranscript.snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₂ :=
  fun i => by
    simpa only [getType_apply, ProtocolSpec.append, Fin.append_right] using T (Fin.natAdd m i)

end ProtocolSpec

open ProtocolSpec

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} {ι : Type} [DecidableEq ι]
    {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}

/-- Appending two `ToOracle`s for two `ProtocolSpec`s -/
def ToOracle.append [O₁ : ∀ i, ToOracle (pSpec₁.Message i)]
    [O₂ : ∀ i, ToOracle (pSpec₂.Message i)] :
      ∀ i, ToOracle ((pSpec₁ ++ₚ pSpec₂).Message i) := fun ⟨i, h⟩ => by
  dsimp [ProtocolSpec.append, ProtocolSpec.getDir] at h ⊢
  by_cases h' : i < m
  · rw [← Fin.castAdd_castLT n i h', Fin.append_left] at h ⊢
    exact O₁ ⟨i.castLT h', h⟩
  · rw [← @Fin.natAdd_subNat_cast m n i (not_lt.mp h'), Fin.append_right] at h ⊢
    exact O₂ ⟨Fin.subNat m (Fin.cast (add_comm m n) i) (not_lt.mp h'), h⟩

instance [∀ i, ToOracle (pSpec₁.Message i)] [∀ i, ToOracle (pSpec₂.Message i)] :
    ∀ i, ToOracle ((pSpec₁ ++ₚ pSpec₂).Message i) := ToOracle.append

#print ToOracle.append

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
      exact (do
        let state ← P₁.input stmt wit
        haveI : 0 = Fin.last m := by aesop
        haveI state : P₁.PrvState (Fin.last m) := by simpa [this] using state
        return ← P₂.input.uncurry (P₁.output state))

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m - 1`, then it sends the message & updates the state as the first prover
  - if `i = m - 1`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. It needs to
    provide a `stmt₂` for the second prover, which it derives from running the verifier on the first
    transcript. -/
  sendMessage := fun ⟨⟨i, hLt⟩, h⟩ state => by
    by_cases hi : i < m
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state ⊢
      by_cases hi' : i + 1 < m
      · simp [hi']
        exact P₁.sendMessage ⟨⟨i, hi⟩, h⟩ state
      · haveI : i + 1 = m := by omega
        simp [this]
        exact (do
          let ⟨msg, state⟩ ← P₁.sendMessage ⟨⟨i, hi⟩, h⟩ state
          haveI state : P₁.PrvState (Fin.last m) := by
            simpa [Fin.last, this] using state
          return ⟨msg, ← P₂.input.uncurry (P₁.output state)⟩)
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi, this,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state ⊢
      exact (do
        let ⟨msg, newState⟩ ← P₂.sendMessage ⟨⟨i - m, by omega⟩, h⟩ state
        haveI newState : P₂.PrvState ⟨i + 1 - m, by omega⟩ := by
          haveI : i + 1 - m = i - m + 1 := by omega
          simpa [Fin.succ, this] using newState
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
        exact (do
          let newState ← P₁.receiveChallenge ⟨⟨i, hi⟩, h⟩ state chal
          haveI newState : P₁.PrvState (Fin.last m) := by
            simpa [Fin.last, this] using newState
          return ← P₂.input.uncurry (P₁.output newState))
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi, this,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state chal ⊢
      exact (do
        let newState ← P₂.receiveChallenge ⟨⟨i - m, by omega⟩, h⟩ state chal
        haveI newState : P₂.PrvState ⟨i + 1 - m, by omega⟩ := by
          haveI : i + 1 - m = i - m + 1 := by omega
          simpa [Fin.succ, this] using newState
        return newState)

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

-- Define composition of multiple protocols via recursion

def ProtocolSpec.join (rounds : List ℕ)
    (pSpecs : ∀ i : Fin rounds.length, ProtocolSpec (rounds.get i)) :
    ProtocolSpec rounds.sum := sorry
