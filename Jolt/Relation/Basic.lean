

/-!
  # Relations

  This file contains definitions related to NP (indexed) relations. An indexed relation $R$ consists of tuples $(i,x,w)$, where $i$ is called an index, $x$ is called a statement, and $w$ is called a witness. We define the corresponding language $L_R$ to be the set of all $(i,x)$ such that there exists some $w$ with $(i,x,w) \in R$. Relations can be parametrized by additional data (public parameters) such as the choice of a field.
-/

/-- Define a binary relation, taking in public parameters `PParams` and an index `Index` -/
class Relation (PParams : Type _) (Index : PParams → Type _) where
  Statement : Type _
  Witness : Type _
  isValid : Statement → Witness → Prop

/-- Define a family of relations where `PParams` are the same -/
class RelationFamily (PParams : Type _) where
  Index : PParams → Type _
  [Relation : Relation PParams Index]

attribute [instance] RelationFamily.Relation


instance exampleRelation : Relation Nat (fun n => Fin n) where
  Statement := Fin 10
  Witness := Fin 10
  isValid := fun x y => x = y

instance exampleRelationFamily : RelationFamily Nat where
  Index := fun n => Fin n
  Relation := exampleRelation

namespace Relation

-- def language (Rel : Type _) [Relation Rel] : Rel.Statement := { stmt // Rel.isValid index stmt wit }

end Relation
