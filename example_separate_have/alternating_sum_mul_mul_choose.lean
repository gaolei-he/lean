import Theorem.mini_separate.succ_mul_choose_eq'

open Nat

open Finset

open BigOperators

theorem alternating_sum_mul_mul_choose {n : ℕ} (h0 : 1 < n): ∑ k in range (n+1), (-1 : ℤ)^k * k * choose n k = 0 := by
  rw [range_eq_Ico]
  have hzero_lt_n : 0 < n+1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  simp [mul_assoc]
  have h1 : ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * (k * choose n k)
    = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * (n * choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    rw [←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq' h0 (mem_Ico.mp hy).left]
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]
