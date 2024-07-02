

/-!
  # Relations

  This file contains definitions related to NP (indexed) relations. An indexed relation $R$ consists of tuples $(i,x,w)$, where $i$ is called an index, $x$ is called a statement, and $w$ is called a witness. Relations can be parametrized by additional data (public parameters) such as the choice of a field.

  We define the corresponding language $L_R$ to be the set of all $(i,x)$ such that there exists some $w$ with $(i,x,w) \in R$.
-/


/-- Define a binary relation, taking in public parameters `PParams` and an index `Index` -/
class Relation (PParams : Type _) (Index : PParams → Type _) where
  Statement : (pp : PParams) → Index pp → Type _
  Witness : (pp : PParams) → Index pp → Type _
  isValid : (pp : PParams) → (i : Index pp) → Statement pp i → Witness pp i → Prop

/-- Define a family of relations where `PParams` are the same -/
class RelationFamily (PParams : Type _) where
  Index : PParams → Type _
  [Relation : Relation PParams Index]

attribute [instance] RelationFamily.Relation


namespace Relation

-- def language [Relation PParams Index] (pp : PParams) (index : Index pp) : Subtype (Rel.isValid pp index) :=
--   { stmt // Rel.isValid pp index stmt wit }

end Relation
