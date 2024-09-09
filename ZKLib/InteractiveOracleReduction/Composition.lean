/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.InteractiveOracleReduction.Basic

/-!
  # Composition of IORs

  We define two kinds of compositions with IORs.

  ## Composing two IORs with compatible relations

  We compose an IOR for reducing relations R1 => R2 with another IOR for reducing relations R2 =>
  R3. This gives us an IOR for reducing relations R1 => R3.

  ## Composing an IOR with a commitment scheme

  We compose an IOR with a commitment scheme that is compatible with the oracle type of a message.
  The commitment scheme itself may be an IOP for the corresponding oracle opening relation.
-/

namespace IOR

section Composition

def Oracleize.append (O1 : Oracleize n1 Message1) (O2 : Oracleize n2 Message2) : Oracleize (n1 + n2) (Fin.addCases Message1 Message2) where
  Query := Fin.addCases O1.Query O2.Query
  Response := Fin.addCases O1.Response O2.Response
  oracle := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j msg q
    · simp only [Fin.addCases_left j] at msg q
      simp only [Fin.addCases_left]
      exact O1.oracle j msg q
    · simp only [Fin.addCases_right j] at msg q
      simp only [Fin.addCases_right]
      exact O2.oracle j msg q

-- Can we make the proofs shorter? It's so repetitive...
def ValidOracleize.append (inst1: ValidOracleize O1) (inst2: ValidOracleize O2) : ValidOracleize (Oracleize.append O1 O2) where
  domain_decidableEq := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> rename_i m _ n _
    · have : (O1.append O2).Query (Fin.castAdd n j) = O1.Query j := by
        simp only [Oracleize.append]
        rw [Fin.addCases_left (m := m) (n := n)]
      exact this ▸ inst1.domain_decidableEq j
    · have : (O1.append O2).Query (Fin.natAdd m j) = O2.Query j := by
        simp only [Oracleize.append]
        rw [Fin.addCases_right (m := m) (n := n)]
      exact this ▸ inst2.domain_decidableEq j
  range_decidableEq := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> rename_i m _ n _
    · have : (O1.append O2).Response (Fin.castAdd n j) = O1.Response j := by
        simp only [Oracleize.append]
        rw [Fin.addCases_left (m := m) (n := n)]
      exact this ▸ inst1.range_decidableEq j
    · have : (O1.append O2).Response (Fin.natAdd m j) = O2.Response j := by
        simp only [Oracleize.append]
        rw [Fin.addCases_right (m := m) (n := n)]
      exact this ▸ inst2.range_decidableEq j
  range_inhabited := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> rename_i m _ n _
    · have : (O1.append O2).Response (Fin.castAdd n j) = O1.Response j := by
        simp only [Oracleize.append]
        rw [Fin.addCases_left (m := m) (n := n)]
      exact this ▸ inst1.range_inhabited j
    · have : (O1.append O2).Response (Fin.natAdd m j) = O2.Response j := by
        simp only [Oracleize.append]
        rw [Fin.addCases_right (m := m) (n := n)]
      exact this ▸ inst2.range_inhabited j
  range_fintype := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> rename_i m _ n _
    · have : (O1.append O2).Response (Fin.castAdd n j) = O1.Response j := by
        simp only [Oracleize.append]
        rw [Fin.addCases_left (m := m) (n := n)]
      exact this ▸ inst1.range_fintype j
    · have : (O1.append O2).Response (Fin.natAdd m j) = O2.Response j := by
        simp only [Oracleize.append]
        rw [Fin.addCases_right (m := m) (n := n)]
      exact this ▸ inst2.range_fintype j

def ValidChallenge.append (inst1: ValidChallenge C1) (inst2: ValidChallenge C2) : ValidChallenge (Fin.addCases C1 C2) where
  fintype := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp <;> exact fintype j
  decidableEq := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp <;> exact decidableEq j
  inhabited := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp <;> exact inhabited j
  selectable := fun i => by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp <;> sorry
    -- What's going on here??
    -- · have h : Fin.addCases C1 C2 (Fin.castAdd n j) = C1 j := by simp
    --   have hF : Fintype (Fin.addCases C1 C2 (Fin.castAdd n j)) := ValidChallenge.append.fintype (Fin.castAdd n j)
    --   have hI : Inhabited (Fin.addCases C1 C2 (Fin.castAdd n j)) := ValidChallenge.append.inhabited (Fin.castAdd n j)
    --   -- have : h ▸ (fintype j) = (ValidChallenge.append (C1 := C1) (C2 := C2)).fintype (Fin.castAdd n j) := by unfold fintype
    --   have hSelectable := selectable (C := C1) j
    --   -- have hS' : SelectableType (Fin.addCases C1 C2 (Fin.castAdd n j)) := h ▸ hSelectable
    --   -- simp; subst h
    --   sorry
    -- · sorry

/-- Sequential composition of two protocols -/
def ProtocolSpec.append (pSpec1 pSpec2 : ProtocolSpec) : ProtocolSpec where
  numRounds := pSpec1.numRounds + pSpec2.numRounds
  Message := Fin.addCases pSpec1.Message pSpec2.Message
  Challenge := Fin.addCases pSpec1.Challenge pSpec2.Challenge
  Oracle := Oracleize.append pSpec1.Oracle pSpec2.Oracle
  validChallenge := ValidChallenge.append pSpec1.validChallenge pSpec2.validChallenge
  validOracle := ValidOracleize.append pSpec1.validOracle pSpec2.validOracle



/-- Parallel repetition of two protocols

(do we need this for now?)

When proving theorems, need to add the condition that `spec1.numRounds = spec2.numRounds`? -/
def ProtocolSpec.composeParallel (spec1 spec2 : ProtocolSpec) : ProtocolSpec where
  numRounds := spec1.numRounds
  Message := fun i => spec1.Message i × spec2.Message i
  Challenge := fun i => spec1.Challenge i × spec2.Challenge i
  Oracle := sorry
  validChallenge := sorry
  validOracle := sorry


end Composition

end IOR
