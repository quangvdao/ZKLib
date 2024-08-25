import ZKLib.JoltConstraint.Subtable.Basic
import Mathlib.Logic.Equiv.Fin

/-!

# The `And` Subtable

-/

namespace Jolt

variable (F : Type) [JoltField F]

def AndSubtable : LassoSubtable F where

  materialize m isLE operands := by
    have : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by simp [Nat.two_mul, Nat.pow_add]
    rw [this] at operands
    let ⟨a, b⟩ := finProdFinEquiv.invFun operands
    have h : 2 ^ m ≤ 2 ^ 64 := Nat.pow_le_pow_of_le (a := 2) (by simp) isLE
    have c : Fin (2 ^ 64) := Fin.castLE h (Fin.land a b)
    exact UInt64.mk c

  evaluateMLE point :=
    let b := point.length / 2
    let (x, y) := point.splitAt b
    (List.range b).foldl (fun acc i => acc + 2 ^ i * x.get! (b - i - 1) * y.get! (b - i - 1)) 0

open LassoSubtable in
theorem AndSubtable_isValid : (AndSubtable F).isValid := by
  unfold isValid evaluateMLE materialize AndSubtable
  simp
  intro m isLE idx
  sorry

end Jolt

/-
  ## Rust Implementation

  ```rust
impl<F: JoltField> LassoSubtable<F> for AndSubtable<F> {
    fn materialize(&self, M: usize) -> Vec<F> {
        let mut entries: Vec<F> = Vec::with_capacity(M);
        let bits_per_operand = (log2(M) / 2) as usize;

        // Materialize table entries in order where (x | y) ranges 0..M
        for idx in 0..M {
            let (x, y) = split_bits(idx, bits_per_operand);
            let row = F::from_u64((x & y) as u64).unwrap();
            entries.push(row);
        }
        entries
    }

    fn evaluate_mle(&self, point: &[F]) -> F {
        // x * y
        debug_assert!(point.len() % 2 == 0);
        let b = point.len() / 2;
        let (x, y) = point.split_at(b);

        let mut result = F::zero();
        for i in 0..b {
            let x = x[b - i - 1];
            let y = y[b - i - 1];
            result += F::from_u64(1u64 << i).unwrap() * x * y;
        }
        result
    }
}
  ```
-/
