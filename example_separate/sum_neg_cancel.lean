import Theorem.example_separate.add_div_two
import Lean4Repl

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_neg_cancel(hn : 1 < n) : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by lean_repl sorry
  rw[Nat.sub_add_cancel]
  linarith
