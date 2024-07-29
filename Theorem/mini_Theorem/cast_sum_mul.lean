import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem cast_sum_mul {n : ℕ} : ∑ k in range (n+1), (n:ℝ) * choose (2*n) k - ∑ k in range (n+1), k * choose (2*n) k
                = (∑ k in range (n+1), n * choose (2*n) k) - (∑ k in range (n+1), k * choose (2*n) k) := by -- 这里是在变换数据类型
  rw [cast_sum (range (n+1)) fun x => n * Nat.choose (2 * n) x]
  congr 1
  refine' sum_congr rfl fun k hk => _
  rw [cast_mul]
