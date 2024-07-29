import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

variable {R : Type*}


theorem identity_84 (n m : ℕ) (h : m < n) :
  ∑ k in range (n + 1), ((choose n k):ℝ) * (((n - k) ^ m):ℝ) * (-1:ℝ)^k = 0 := by

  -- 利用组合数学中的一个重要性质，即如果 n > m，则交错和为 0
  have h_sum_eq_0 : ∑ k in range (n + 1), ((choose n k):ℝ) * ((k ^ m):ℝ) * (-1:ℝ)^k = 0 := by
  { induction m with
  | zero =>
    simp only [pow_zero, mul_one]
    exact finset.sum_range_choose_mul_pow_eq_zero _ h}
    { -- 使用归纳假设
      simp only [pow_succ, mul_assoc],
      rw finset.sum_range_succ,
      rw ih,
      simp only [zero_mul, finset.sum_const_zero, add_zero],
      rw ← finset.sum_range_succ,
      rw ← nat.sub_add_cancel h,
      exact finset.sum_range_choose_mul_pow_eq_zero _ (nat.lt_of_succ_lt h), } },
  -- 利用上述性质进行证明
  apply finset.sum_congr rfl,
  intros k hk,
  rw [nat.sub_add_cancel (finset.mem_range_succ_iff.mp hk)],
  ring
