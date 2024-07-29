import Theorem.example_separate.add_div_two
import Lean4Repl

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_neg_assoc: ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * ((-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x)) := by lean_repl sorry
  refine' sum_congr rfl fun y _ => _
  rw[mul_assoc]