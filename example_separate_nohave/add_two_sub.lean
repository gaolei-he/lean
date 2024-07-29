import Mathlib.Data.Nat.Choose.Sum


theorem add_two_sub: 2 * n + 1 - n = n + 1 := by
 rw[two_mul]
 rw[add_assoc]
 rw[add_comm]
 simp
