import Mathlib.Data.Nat.Choose.Sum
import Theorem.mini_separate.succ_mul_choose_eq''

open Nat

open Finset

open BigOperators

theorem sum_div_succ_mul_choose {n k: ℕ} : ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k = (1/(n+1)) * (2^(n+1) - 1) := by
  have : ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k
        = ∑ k in range (n+1), ((1/(n+1)) : ℝ) * choose (n+1) (k+1) := by
        refine' sum_congr rfl fun y hy => _
        exact succ_mul_choose_eq''
  rw [this, ←mul_sum]
  congr 1
  rw [←one_add_one_eq_two]
  rw [add_pow 1 1 (n+1)]
  simp
  rw [sum_range_succ' _ (n + 1)]
  simp
