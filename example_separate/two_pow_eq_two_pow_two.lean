import Theorem.example_separate.add_div_two
import Theorem.example_separate.two_pow_eq_two_pow_sub_add
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999
theorem two_pow_eq_two_pow_two(h: 2 ≤ n) : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by lean_repl sorry
  rw[two_pow_eq_two_pow_sub_add]
  rw[Nat.pow_succ]
  linarith
