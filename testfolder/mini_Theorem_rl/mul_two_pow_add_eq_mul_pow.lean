import Lean4Repl
set_option maxHeartbeats 999999999999999999999999

theorem mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by lean_repl sorry
  rw[← Nat.add_mul]
