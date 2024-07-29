import Jolt.Relation.Basic
import Jolt.CommitmentScheme.Basic

/-!
  # Lookup relations

  We define the basic lookup relation, plus the Lasso lookup relation with subtable decomposition.
-/

structure LookupRelation (cs : CommitmentScheme) : Relation where
  Statement := cs.Commitment × List cs.Data
  Witness := cs.Data
  isValid := fun stmt wit => sorry
