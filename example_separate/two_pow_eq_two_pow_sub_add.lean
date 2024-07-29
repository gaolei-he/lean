import Theorem.example_separate.add_div_two
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999
theorem two_pow_eq_two_pow_sub_add(h: 2 ≤ n) : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by lean_repl sorry
  rw[← Nat.sub_add_comm]
  simp
  linarith
