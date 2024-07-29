import Theorem.mini_separate.succ_mul_choose_eq''
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Parity

open Nat

open Finset

open BigOperators


theorem odd_sum_range_choose (n : ℕ) (h0 : n ≠ 0) : ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) else 0) = 2^(n-1) :=
  mul_right_injective₀ two_ne_zero <|
    calc
      2 * (∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) else 0))
        = ∑ k in range (n+1), (if k % 2 = 1 then 2 * ((choose n k) : ℤ) else 0) := by
          {
            rw [mul_sum]
            refine' sum_congr rfl fun y hy => _
            rw [ite_mul_zero_right (y % 2 = 1) 2 ((Nat.choose n y) : ℤ)]
          }
      _ = ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) + ((choose n k) : ℤ) else ((choose n k) : ℤ) - ((choose n k) : ℤ)) := by
          {
            refine' sum_congr rfl fun y hy => _
            congr 1
            rw [two_mul]
            simp
          }
      _ = ∑ k in range (n+1), ((if k % 2 = 1 then choose n k - (-1)^k * choose n k else choose n k - (-1)^k * choose n k) : ℤ) := by
          {
            refine' sum_congr rfl fun y fy => _
            split_ifs with h'
            . rw [←Nat.odd_iff] at h'
              rw [Odd.neg_one_pow h']
              rw [neg_one_mul]
              rw [sub_neg_eq_add]
            . rw [Nat.mod_two_ne_one, ←Nat.even_iff] at h'
              rw [Even.neg_one_pow h']
              simp
          }
      _ = ∑ k in range (n+1), ((choose n k - (-1)^k * choose n k) : ℤ) := by simp
      _ = 2^n := by
          {
            rw [sum_sub_distrib]
            rw [Int.alternating_sum_range_choose_of_ne h0]
            simp
            have := (add_pow (1:ℤ) 1 n).symm
            simpa [one_add_one_eq_two] using this
          }
      _ = 2^(n - 1 + 1) := by
          {
            have hone_le_one : 1 ≤ 1 := by linarith
            have hone_le_n : 1 ≤ n := by exact Iff.mpr one_le_iff_ne_zero h0
            rw [←tsub_tsub_assoc hone_le_n hone_le_one]
            simp
          }
      _ = 2 * 2^(n-1) := by
          {
            rw [add_one]
            rw [_root_.pow_succ 2 (n-1)]
          }


theorem odd_sum_range_choose_from_0_to_0(n : ℕ)(h0 : n ≠ 0)(gol:  (∑ x in range (n + 1), 2 * if x % 2 = 1 then ↑(Nat.choose n x) else 0) =
    ∑ k in range (n + 1), if k % 2 = 1 then 2 * ↑(Nat.choose n k) else 0) :
   (2 * ∑ k in range (n + 1), if k % 2 = 1 then ↑(Nat.choose n k) else 0) =
    ∑ k in range (n + 1), if k % 2 = 1 then 2 * ↑(Nat.choose n k) else 0 := by
  rw [mul_sum]
  apply gol

theorem odd_sum_range_choose_from_2_to_2(n : ℕ)(h0 : n ≠ 0)(y : ℕ)(hy : y ∈ range (n + 1)) :
   (2 * if y % 2 = 1 then ↑(Nat.choose n y) else 0) = if y % 2 = 1 then 2 * ↑(Nat.choose n y) else 0 := by
  rw [ite_mul_zero_right (y % 2 = 1) 2 ((Nat.choose n y) : ℤ)]

