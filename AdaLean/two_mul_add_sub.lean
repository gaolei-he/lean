import Mathlib.Data.Nat.Choose.Sum


theorem two_mul_add_sub (hn: n ≤ 2 * n): 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
