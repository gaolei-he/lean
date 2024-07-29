import Lean4Repl
set_option maxHeartbeats 999999999999999999999999
theorem two_mul_sub: 2 * n - n = 2 * n - 1 * n := by lean_repl sorry
  simp
