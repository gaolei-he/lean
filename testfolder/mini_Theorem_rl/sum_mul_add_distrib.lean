import Theorem.example_separate.add_div_two
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem sum_mul_add_distrib : ∑ k in range (n+1), (k+1) * choose n k = ∑ k in range (n+1), (k * choose n k + 1 * choose n k) := by lean_repl sorry
  refine' sum_congr rfl fun y _ => _
  rw[add_mul]
