import Theorem.example_separate.add_div_two
import Lean4Repl

set_option maxHeartbeats 999999999999999999999999s

theorem lt_eq_le_sub{y:ℕ}(hn0 : 0 < n) : y < n → y ≤ n - 1 := by lean_repl sorry
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
