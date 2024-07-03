import Mathlib.Algebra.Polynomial.Basic

/-!
  # Relations

  This file contains definitions related to NP (indexed) relations. An indexed relation $R$ consists of tuples $(i,x,w)$, where $i$ is called an index, $x$ is called a statement, and $w$ is called a witness. Relations can be parametrized by additional data (public parameters) such as the choice of a field.

  We define the corresponding language $L_R$ to be the set of all $(i,x)$ such that there exists some $w$ with $(i,x,w) \in R$.
-/

-- variable (PParams : Type _) (Index : PParams → Type _)

-- /-- An instance is a statement-witness pair, which may depend on public parameters `PParams` and an index `Index` -/
-- structure Instance where
--   Statement : (pp : PParams) → Index pp → Type _
--   Witness : (pp : PParams) → Index pp → Type _

/-- A binary relation on an instance -/
class Relation (Statement : Type _) (Witness : Type _) where
  isValid : Statement → Witness → Prop

namespace Relation

/-- The corresponding language for a relation -/
def language (R : Relation Statement Witness) : Type _ :=
  { stmt : Statement // ∃ wit : Witness, R.isValid stmt wit }

end Relation
