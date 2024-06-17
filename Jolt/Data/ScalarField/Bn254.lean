import Mathlib.Data.ZMod.Defs
import Mathlib.NumberTheory.LucasPrimality

def Bn254ScalarFieldCard := 21888242871839275222246405745257275088548364400416034343698204186575808495617

theorem Bn254ScalarField_is_prime : Prime Bn254ScalarFieldCard := sorry

def Bn254ScalarField := ZMod Bn254ScalarFieldCard

instance : CommRing Bn254ScalarField := (ZMod.commRing Bn254ScalarFieldCard)

#eval (1 : Bn254ScalarField) + (1 : Bn254ScalarField)
