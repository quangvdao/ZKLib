import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Degrees
import Mathlib.Data.Fintype.Basic
import Jolt.Relation.Basic

/-!
# Sumcheck Relation

This file defines the relation for the sumcheck protocol. The relation is parametrized by:

  - a coefficient field $R$, which is a CommSemiring
  - the number of variables $n$
  - the degree of each variable $d_1, \dots, d_n$

The statement of the sumcheck protocol is a multivariate polynomial $p(x_1, \dots, x_n)$ over $R$, of degree $d_i$ in variable $x_i$ for each $i \in \{1, \dots, n\}$.

The witness of the sumcheck protocol is a value $T \in R$.

The sumcheck relation states that the following holds:
$$ \sum_{y \in \{0,1\}^n} p(y) = T. $$

## TODOs

Extend the relation to capture sumcheck over modules. This will allow instantiating e.g. the Bulletproofs protocol as an instance of sumcheck.

## References

[JACM:LFKN92]

[C:BooChiSot21]

-/

namespace AbstractSumcheck

noncomputable section

open MvPolynomial BigOperators

open Relation

variable {R : Type _} [CommSemiring R]

-- structure AbstractSumcheckInstance (R : Type) [CommSemiring R] where
--   nVars : ℕ
--   degs : Fin nVars → ℕ
--   domain : Finset R
--   poly : MvPolynomial (Fin nVars) R
--   target : R

structure IndexType (R : Type _) [CommSemiring R] where
  nVars : ℕ
  degs : Fin nVars → ℕ
  domain : Finset R

structure StmtType (R : Type _) [CommSemiring R] (index : IndexType R) where
  poly : MvPolynomial (Fin index.nVars) R
  target : R

def WitType (R : Type _) [CommSemiring R] (_ : IndexType R) : Type := Empty

def productDomain (n : ℕ) (D : Finset R) : Finset (Fin n → R) :=
  @Fintype.piFinset (Fin n) _ _ (fun _ => R) (fun _ => D)

def sumOverDomain (n : ℕ) (p : MvPolynomial (Fin n) R) (D : Finset R) : R :=
  Finset.sum (productDomain n D) (fun x => eval x p)


instance SumcheckRelation (R : Type _) [CommSemiring R] : Relation R where
  Index := IndexType R
  Stmt := StmtType R
  Wit := WitType R
  isValid := fun index stmt _ =>
    sumOverDomain index.nVars stmt.poly index.domain = stmt.target
        ∧ ∀ i : Fin index.nVars, stmt.poly.degreeOf i ≤ index.degs i


section HyperCube

variable [Nontrivial R]

def zeroOnePred : R → Prop := fun r => r = 0 ∨ r = 1

def zeroOneSet : Set R := {r : R | zeroOnePred r}

@[simp]
instance zeroOneSetFinset : Finset R where
  val := {0, 1}
  nodup := by simp

def sumOverHyperCube (n : ℕ) (p : MvPolynomial (Fin n) R) : R :=
  sumOverDomain n p zeroOneSetFinset

-- def zeroOneSubtype : Type := {r : R // zeroOnePred r}

-- def zeroInSubtype : @zeroOneSubtype R _ := ⟨0, Or.inl rfl⟩

-- def oneInSubtype : @zeroOneSubtype R _ := ⟨1, Or.inr rfl⟩

-- instance zeroOneSubtypeFintype : Fintype (@zeroOneSubtype R _) where
--   elems := Finset.subtype zeroOnePred
--   complete := fun x => by
--     simp

-- #check zeroOneSubtype

end HyperCube


end

end AbstractSumcheck
