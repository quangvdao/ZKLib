-- import Std.Data.Bits
import Mathlib.Data.Int.Basic

-- Equality for bits
def b_eqw (x0 y0 : Bool) : Bool :=
  (x0 && y0) || (¬x0 && ¬y0)

theorem b_eqw_eqiv (x0 y0 : Bool) : b_eqw x0 y0 = (if x0 = y0 then true else false) := by
  cases x0; cases y0; simp [b_eqw]

theorem symmetry_of_b_eqw (x y : Bool) : b_eqw x y = b_eqw y x := by
  simp [b_eqw]

theorem transitivity_of_b_eqw (x y w : Bool) (h1 : b_eqw x y) (h2 : b_eqw y w) : b_eqw x w := by
  cases x; cases y; cases w; simp [b_eqw] at *; assumption

-- Measure conjecture lemmas
lemma natp_of_integer_length (x : Int) : 0 ≤ Int.natAbs x := Int.coe_nat_nonneg (Int.natAbs x)

lemma natp_when_not_bitp (x : Int) (hx : 0 ≤ x) (hnb : x ≠ 0 ∧ x ≠ 1) : 2 ≤ x :=
  by rcases x with (_ | _ | x | x); linarith

lemma integer_length_gt_0 (x : Int) (hx : 0 ≤ x) (hnb : x ≠ 0 ∧ x ≠ 1) : 0 < Int.natAbs x := by
  cases x; linarith

-- Equality for bitvectors
def eqw (x y : Int) : Bool :=
  let rec eqw_rec (x y : Int) : Bool :=
    if ¬(0 ≤ x ∧ 0 ≤ y) then false
    else if x = 0 ∧ y = 0 then true
    else if (x = 0) ≠ (y = 0) then false
    else
      let x0 := x % 2
      let y0 := y % 2
      let eq0 := b_eqw (x0 = 1) (y0 = 1)
      let x_rest := x / 2
      let y_rest := y / 2
      eq0 && eqw_rec x_rest y_rest
  eqw_rec x y

theorem lemma_1 (x : Int) (hx : 0 ≤ x) : x = Int.ofNat ((x % 2).toNat + 2 * ((x / 2).toNat)) := by
  sorry

theorem equal_logapp_loghead_logtail_1 (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h_tail : x / 2 = y / 2) (h_head : x % 2 = y % 2) : x = y := by
  sorry

theorem eqw_equal_equiv (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) : eqw x y = (if x = y then true else false) := by
  sorry

-- Measure conjecture lemmas
lemma natp_lemma_1 (a c : Int) (ha : 0 < a) (hc : 0 < c) : Int.natAbs (a - c) < a := by
  sorry

lemma natp_lemma_2 (a b c d : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  sorry

lemma natp_lemma_3 (a b c : Int) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Int.natAbs (a - c) + Int.natAbs (b - c) < a + b := by
  sorry

-- Equality for bitvectors with chunks of size wc
def eqwc (x y : Int) (wc : Nat) : Bool :=
  let rec eqwc_rec (x y : Int) (wc : Nat) : Bool :=
    if ¬(0 ≤ x ∧ 0 ≤ y) then false
    else if wc = 0 then false
    else if x = 0 ∧ y = 0 then true
    else if (x = 0) ≠ (y = 0) then false
    else
      let car_chunk_x := x % (2 ^ wc)
      let car_chunk_y := y % (2 ^ wc)
      let car_chunk_eq := eqw car_chunk_x car_chunk_y
      let cdr_chunk_x := x / (2 ^ wc)
      let cdr_chunk_y := y / (2 ^ wc)
      car_chunk_eq && eqwc_rec cdr_chunk_x cdr_chunk_y wc
  eqwc_rec x y wc

theorem lemma_2 (x : Int) (k : Nat) (hx : 0 ≤ x) : x = Int.ofNat ((x % 2^k).toNat + 2^k * ((x / 2^k).toNat)) := by
  sorry

theorem equal_logapp_loghead_logtail_k (x y : Int) (k : Nat) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h_tail : x / 2^k = y / 2^k) (h_head : x % 2^k = y % 2^k) : x = y := by
  sorry

lemma integer_length_0_implies_0 (x : Int) (hx : 0 ≤ x) (h_len : x.natAbs = 0) : x = 0 := by
  sorry

theorem eqwc_equal_equiv (x y : Int) (wc : Nat) (hx : 0 ≤ x) (hy : 0 ≤ y) (hwc : 0 < wc) : eqwc x y wc = (if x = y then true else false) := by
  sorry
