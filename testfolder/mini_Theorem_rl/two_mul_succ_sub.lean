import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999
theorem two_mul_succ_sub(hn: n ≤ 2 * n): 2 * n + 1 - n = n + 1 := by lean_repl sorry
  rw[add_comm]
  rw[Nat.add_sub_assoc hn]
  rw[add_comm]
  rw[two_mul]
  simp
