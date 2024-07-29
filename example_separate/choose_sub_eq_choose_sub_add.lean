import Theorem.example_separate.add_div_two
import Lean4Repl

open Nat

set_option maxHeartbeats 999999999999999999999999
theorem choose_sub_eq_choose_sub_add(h1:1 ≤ n)(h2:1 ≤ k) : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by lean_repl sorry
  rw[Nat.sub_add_cancel h2]
