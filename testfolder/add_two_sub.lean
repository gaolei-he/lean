import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

set_option maxHeartbeats 999999999999999999999999
theorem add_two_sub: 2 * n + 1 - n = n + 1 := by lean_repl sorry
 rw[two_mul]
 rw[add_assoc]
 rw[add_comm]
 simp
