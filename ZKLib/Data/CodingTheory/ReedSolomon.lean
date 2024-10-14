/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.Data.CodingTheory.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.FinEnum

/-!
  # Reed-Solomon Codes

  TODO: define the Reed-Solomon code, and prove its properties.

  TODO: define the Berkelamp-Welch algorithm for unique decoding, and Guruswami-Sudan algorithm for
  list-decoding.
-/


namespace ReedSolomon

open Polynomial

variable {F : Type*} [Field F] [Fintype F] {n : Type*} [Fintype n]

def evalOnPoints (points : FinEnum F) : F[X] →ₗ[F] (Fin points.card → F) where
  toFun := fun p => fun x => p.eval (points.equiv.invFun x)
  map_add' := fun x y => by simp; congr
  map_smul' := fun m x => by simp; congr

/-- The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `points`.
  -/
def code (deg : ℕ) (points : FinEnum F) : Submodule F (Fin points.card → F) :=
  (Polynomial.degreeLT F deg).map (evalOnPoints points)

/-- The generator matrix of the Reed-Solomon code of degree `deg` and evaluation points `points`. -/
def genMatrix (deg : ℕ) (points : FinEnum F) : Matrix (Fin deg) (Fin points.card) F :=
  .of (fun i j => points.equiv.toFun j ^ (i : ℕ))

def checkMatrix (points : FinEnum F) : Matrix (Fin points.card) (Fin points.card) F :=
  sorry

theorem code_by_genMatrix (deg : ℕ) (points : FinEnum F) :
    code deg points = codeByGenMatrix (genMatrix deg points) := by
  simp [codeByGenMatrix, code]
  rw [LinearMap.range_eq_map]
  sorry

#check LinearMap.range_eq_map

#check Basis


#check Matrix.vandermonde

end ReedSolomon
