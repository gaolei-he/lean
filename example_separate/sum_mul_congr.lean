import Theorem.example_separate.add_div_two
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_mul_congr : ∑ k in Ico 1 (n + 1), n * choose (n-1) (k-1) = n * ∑ l in range n, choose (n-1) l := by lean_repl sorry
  rw[mul_sum]   --先把 n 提出来
  rw[sum_Ico_eq_sum_range]  -- 代换 l = k - 1
  simp
