import Jolt.Data.ScalarPrimeField.PrattCertificate
import Jolt.Data.ZMod.Pow

/-!
  # The BN254 scalar prime field
-/

namespace BN254

notation "SCALAR_FIELD_CARD" => 21888242871839275222246405745257275088548364400416034343698204186575808495617

#eval ZMod.powSplit (5 : ZMod SCALAR_FIELD_CARD) (SCALAR_FIELD_CARD - 1) 1000 (by decide)

/-
Pratt certificate from Kestrel:

(5, (2, 3, 13, 29, 983, 11003, 237073, 405928799, 1670836401704629, 13818364434197438864469338081),
     [28, 2, 1, 1, 1, 1, 1, 1, 1, 1],
     [[], [], [], [], [], [], [],
      [22, [2, 11, 3691, 4999],
          [1, 1, 1, 1],
          [[], [], [], []]],
      [2, [2, 3, 5156902474397],
         [2, 4, 1],
         [[], [],
          [2, [2, 107, 12048837557],
             [2, 1, 1],
             [[], [],
              [2, [2, 7, 661, 93001],
                 [2, 2, 1, 1],
                 [[], [], [], []]]]]]],
      [3, [2, 5, 823, 1593227, 65865678001877903],
         [5, 1, 1, 1, 1],
         [[], [], [], [],
          [5, [2, 83, 379, 1637, 639533339],
             [1, 1, 1, 1, 1],
             [[], [], [], [],
              [2, [2, 229, 853, 1637],
                 [1, 1, 1, 1],
                 [[], [], [], []]]]]]]])
-/

-- set_option trace.profiler true
-- set_option profiler true

/-- Takes a bit -/
lemma prod_factors_eq : [2 ^ 28, 3 ^ 2, 13, 29, 983, 11003, 237073, 405928799, 1670836401704629, 13818364434197438864469338081].prod = SCALAR_FIELD_CARD - 1 := by norm_num

lemma mod_comp : (5 ^ (SCALAR_FIELD_CARD - 1) : ZMod SCALAR_FIELD_CARD) = 1 := by sorry
  -- rw [ZMod.pow_eq_powSplit 1000 (by decide)]
  -- simp
  -- repeat (unfold ZMod.powSplit <;> simp <;> norm_num)
  -- -- rw [←ZMod.pow_eq_pow']
  -- norm_num

-- It takes too long (using `reduce_mod_char`) to verify that 5 ^ (SCALAR_FIELD_CARD - 1) = 1 mod SCALAR_FIELD_CARD.
-- Needs to implement power-of-two exponentiation?
-- theorem ScalarField_is_prime : Nat.Prime SCALAR_FIELD_CARD := by
--   refine PrattCertificate.out (p := SCALAR_FIELD_CARD) ⟨5, (by norm_num), ?_⟩
--   · refine .split [2 ^ 28, 3 ^ 2, 13, 29, 983, 11003, 237073, 405928799, 1670836401704629, 13818364434197438864469338081] (fun r hr => ?_) (by norm_num)
--   · simp at *
--     rcases hr with hr | hr <;> rw [hr]
--     · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
--     · exact .prime 5 1 _ prime_5 (by reduce_mod_char; decide) (by norm_num)

def ScalarField := ZMod SCALAR_FIELD_CARD


end BN254
