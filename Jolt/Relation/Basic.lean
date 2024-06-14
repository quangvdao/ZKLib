

/-!
  # Relations

  This file contains definitions related to NP (indexed) relations. An indexed relation $R$ consists of tuples $(i,x,w)$, where $i$ is called an index, $x$ is called a statement, and $w$ is called a witness. We define the corresponding language $L_R$ to be the set of all $(i,x)$ such that there exists some $w$ with $(i,x,w) \in R$. Relations can be parametrized by additional data (public parameters) such as the choice of a field.

  We model relations as a type class.

  ## References

  Marlin paper?
-/

class Relation (PublicParams : Type) where
  Index : Type _
  Stmt : Index → Type _
  Wit : Index → Type _
  isValid : (index : Index) → (Stmt index) → (Wit index) → Prop

#check Relation

-- export Relation (isValid)

namespace Relation

-- variable {PublicParams : Type} {Stmt : Type} {Wit : Type}

-- def isValidBool (R : Relation PublicParams Stmt Wit) (pp : PublicParams) (stmt : Stmt pp) (wit : Wit pp) : Bool := R.isValid pp stmt wit

-- def language (R : Relation) : Type _ := { (index, stmt) // R.isValid index stmt wit }

end Relation
