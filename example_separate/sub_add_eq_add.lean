import Theorem.example_separate.add_div_two
import Lean4Repl

set_option maxHeartbeats 999999999999999999999999

theorem sub_add_eq_add(h: 2 ≤ n) : n - 1 + 2 = n + 1 := by lean_repl sorry
  rw[← Nat.sub_add_comm]
  rw[Nat.add_sub_assoc]
  simp
  linarith
