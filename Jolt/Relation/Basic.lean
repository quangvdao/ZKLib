import Mathlib.Data.Set.Basic

/-!
  # Relations

  This file contains definitions related to NP (indexed) relations. An indexed relation $R$ consists of tuples $(i,x,w)$, where $i$ is called an index, $x$ is called a statement, and $w$ is called a witness. Relations can be parametrized by additional data (public parameters) such as the choice of a field.

  We define the corresponding language $L_R$ to be the set of all $(i,x)$ such that there exists some $w$ with $(i,x,w) \in R$.
-/


/-- A binary relation on an instance -/
structure Relation where
  Statement : Type _
  Witness : Type _
  isValid : Statement → Witness → Bool

/-- Alternate form where the statement and witness are in a tuple -/
def Relation.isValid' (R : Relation) : R.Statement × R.Witness → Bool := fun ⟨stmt, wit⟩ => R.isValid stmt wit

def Relation.isValidProp (R : Relation) : R.Statement × R.Witness → Prop := fun ⟨stmt, wit⟩ => R.isValid stmt wit = true

/-- A relation family indexed by public parameters `PParams` and index `Index` -/
structure RelationFamily where
  PParams : Type _
  Index : PParams → Type _
  Relation : (pp : PParams) → Index pp → Relation

/-- The trivial Boolean relation -/
def boolRel (AnyWitness : Type _) : Relation where
  Statement := Bool
  Witness := AnyWitness
  isValid := fun stmt _ => stmt

namespace Relation

/-- The corresponding language (as a set) for a relation -/
def language (R : Relation) : Set R.Statement :=
  { stmt : R.Statement | ∃ wit : R.Witness, R.isValid stmt wit }

/-- If the witness type is empty, the language is empty -/
def boolRelEmpty : Relation := boolRel Empty

theorem boolRelEmpty_language : boolRelEmpty.language = ∅ := by
  unfold language boolRelEmpty boolRel
  simp

/-- If the witness type is nonempty, the language is just `true` -/
theorem boolRel_language (AnyWitness : Type _) [Nonempty AnyWitness] : (boolRel AnyWitness).language = { true } := by
  unfold language boolRel
  simp

end Relation
