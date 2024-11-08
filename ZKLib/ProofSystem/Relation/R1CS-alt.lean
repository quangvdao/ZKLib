-- This file is from Bolton Bailey

import Mathlib.LinearAlgebra.Lagrange

/-!
# The Marlin Protocol

This file defines the Marlin protocol, monadically. That is, the protocol is defined as a function taking a PolyCommitIOPMonad instance on M and returning M Unit.

-/

section Marlin


variable (F : Type)

-- TODO too liberal, row, col pairs should not be repeated. They should be sorted. This guarantees unique representation, with the additional constraint that val is never zero. is uniqueness necessary though?
structure SparseMatrix (u v α : Type) where
  (k : ℕ)
  (row : Fin k -> u)
  (col : Fin k -> v)
  (val : Fin k -> α)

-- Cannot be inferred, need to say to use 0
instance (u v α : Type) : Inhabited (SparseMatrix u v α) where
  default := {
    k := 0
    row := Fin.elim0
    col := Fin.elim0
    val := Fin.elim0
  }


def SparseMatrix.toMatrix {u v α : Type} [DecidableEq u] [DecidableEq v] [CommRing α] (A : SparseMatrix u v α) : Matrix u v α :=
  -- AI gives this, pretty sure it's correct
  λ i j => (Finset.univ : Finset (Fin A.k)).sum (λ idx => if A.row idx = i ∧ A.col idx = j then A.val idx else 0)


structure R1CSStmt (n_stmt n_wit rows : ℕ) where
  (A B C : SparseMatrix (Fin rows) (Fin (n_stmt + n_wit)) F)
  (stmt : Fin n_stmt -> F)

def R1CSWit (n_wit : ℕ) := Fin n_wit -> F

def R1CS_Relation (F: Type) [Field F] (n_stmt n_wit rows : ℕ)
    (stmt : R1CSStmt F n_stmt n_wit rows)
    (wit : R1CSWit F n_wit) : Prop :=
  let ⟨A, B, C, x⟩ := stmt
  let z := fun idx => Sum.elim x wit (finSumFinEquiv.invFun idx)
  Matrix.mulVec A.toMatrix z * Matrix.mulVec B.toMatrix z = Matrix.mulVec C.toMatrix z

def R1CSStmt.fromMatrix {n_stmt n_wit rows : ℕ} (A B C : Matrix (Fin rows) (Fin (n_stmt + n_wit)) F) (k: ℕ) : R1CSStmt F n_stmt n_wit rows := sorry


-- These are abbrevs, because it's needed for them to unfold later
abbrev SquareR1CSStmt (n_stmt n_wit : ℕ) := R1CSStmt F n_stmt n_wit (n_stmt + n_wit)

abbrev SquareR1CSWit (n_wit : ℕ) := R1CSWit F n_wit

abbrev SquareR1CS_Relation (F: Type) [Field F] (n_stmt n_wit : ℕ)
    (stmt : SquareR1CSStmt F n_stmt n_wit)
    (wit : SquareR1CSWit F n_wit) : Prop :=
  R1CS_Relation F n_stmt n_wit (n_stmt + n_wit) stmt wit



instance [Inhabited F] (n_stmt n_wit : ℕ) : Inhabited (SquareR1CSStmt F n_stmt n_wit) where
  default := {
    A := default
    B := default
    C := default
    stmt := default
  }

lemma SquareR1CS.default_def [Inhabited F] (n_stmt n_wit : ℕ) :
    (default : SquareR1CSStmt F n_stmt n_wit) = {
      A := default
      B := default
      C := default
      stmt := default
    } := rfl

instance [Inhabited F] (n_wit : ℕ) : Inhabited (SquareR1CSWit F n_wit) where
  default := by
    intro _
    exact default
