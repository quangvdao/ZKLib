

/-!
  # Relations

  This file contains definitions related to NP relations. A relation $R$ consists of tuples $(x,w)$, where $x$ is called a statement and $w$ is called a witness. We define the corresponding language $L_R$ to be the set of all $x$ such that there exists some $w$ with $(x,w) \in R$. Relations can be parametrized by additional data, e.g. public parameters or an index.

  We model relations as a type class.
-/

class Relation {u v w : Level} (PublicParams : Type u) (Stmt : PublicParams → Type v) (Wit : PublicParams → Type w) where
  isValid : (pp : PublicParams) → Stmt pp → Wit pp → Bool

export Relation (isValid)

namespace Relation

variable {PublicParams : Type} {Stmt : PublicParams → Type} {Wit : PublicParams → Type}

-- def isValidBool (R : Relation PublicParams Stmt Wit) (pp : PublicParams) (stmt : Stmt pp) (wit : Wit pp) : Bool := R.isValid pp stmt wit

-- def language (R : Relation PublicParams Stmt Wit) : Subtype Stmt := { stmt | R.isValid stmt R.wit }

end Relation
