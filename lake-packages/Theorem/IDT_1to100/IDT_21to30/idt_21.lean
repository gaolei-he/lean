import Mathlib.Data.Nat.Choose.Sum

open Nat Finset BigOperators

theorem Idt21 (n : ℕ) : ∑ k in range (n + 1), k * choose n k = n * 2 ^ (n - 1) := by
  have h1 : ∑ k in range (n + 1), k * choose n k = ∑ k in range (n + 1), (n - k) * choose n k := by
    rw [← sum_range_reflect, add_tsub_cancel_right]
    congr! 2 with k h
    exact choose_symm (mem_range_succ_iff.mp h)
  have h2 : 2 * ∑ k in range (n + 1), k * choose n k = n * 2 ^ n := by
    nth_rw 1 [two_mul, h1, ← sum_add_distrib]
    simp_rw [← add_mul]
    rw [sum_congr (g := fun x => n * n.choose x) rfl fun x h => by
      congr 1; exact tsub_add_cancel_iff_le.mpr (mem_range_succ_iff.mp h),
      ← mul_sum, sum_range_choose]
  apply mul_right_injective₀ (show 2 ≠ 0 by norm_num)
  dsimp only
  rw [h2, mul_comm _ (_ * _), mul_assoc]
  cases' n.eq_zero_or_pos with h h
  · simp [h]
  · have d1 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      induction n
      · linarith
      · exact rfl
    exact congrArg (HMul.hMul n) d1
