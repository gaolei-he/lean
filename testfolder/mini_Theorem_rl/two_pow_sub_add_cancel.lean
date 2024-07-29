import Lean4Repl
set_option maxHeartbeats 999999999999999999999999

theorem two_pow_sub_add_cancel(hn : 1 ≤ 2 * n) :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by lean_repl sorry
  rw[Nat.sub_add_cancel hn]
