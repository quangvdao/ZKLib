import Jolt.Relation.Basic
import Jolt.CommitmentScheme.Basic

/-!
  # Lookup relations

  We define the basic lookup relation, plus the Lasso lookup relation with subtable decomposition.
-/

variable {R : Type} [Inhabited R]

def LookupRelation (cs : ListCommitmentScheme R) : Relation where
  Statement := List cs.Datum × cs.Commitment
  Witness := List cs.Datum × cs.Randomness
  isValid := fun stmt wit => cs.commit wit.1 wit.2 = stmt.2 ∧ ∀ x ∈ wit.1, x ∈ stmt.1
