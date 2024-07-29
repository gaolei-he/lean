import Theorem.example_separate.add_div_two
import Lean4Repl

set_option maxHeartbeats 999999999999999999999999

theorem sub_two_add_one(h : 2 ≤ n ): n - 2 + 1 = n - 1 := by lean_repl sorry
        exact tsub_add_eq_add_tsub h
