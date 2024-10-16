/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Set.Basic

/-!
  # Relations

  This file contains definitions related to (binary) relations. Such a relation `R` consists of a
  type `Statement` for the statement, a type `Witness` for the witness, and a predicate `isValid` to
  determine whether a given statement and witness pair is valid.

  Relations can be parametrized by additional data (public parameters) such as the choice of a
  field; we make this into a `RelationFamily`.

  We define the corresponding language `R.language` to be the set of all `stmt`s such that there
  exists some `wit` with `R.isValid stmt wit = True`.
-/

/-- A relation. Consists of a statement type `Statement`, a witness type `Witness`, and a predicate
  `isValid` to determine whether a given statement and witness pair is valid. -/
class Relation (Statement : Type) (Witness : Type) where
  isValid : Statement → Witness → Prop

/-- The trivial relation where the witness is `PUnit` and the statement is a `Prop`. Whether the
  relation is valid is determined by the statement itself. -/
instance trivialRelation : Relation Prop PUnit where
  isValid := fun stmt _ => stmt

/-- If the trivial relation has witness type `PEmpty` instead, then this relation is always invalid.
  -/
instance emptyRelation' : Relation Prop PEmpty where
  isValid := fun stmt _ => stmt

namespace Relation

variable {Statement Witness : Type}

/-- The language of a relation -/
def language [R : Relation Statement Witness] : Set Statement :=
  { stmt | ∃ wit : Witness, R.isValid stmt wit }

@[simp]
theorem trivialRelation_language : trivialRelation.language = { True } := by
  unfold language trivialRelation; aesop

@[simp]
theorem emptyRelation'_language : emptyRelation'.language = ∅ := by
  unfold language emptyRelation'; simp

end Relation
