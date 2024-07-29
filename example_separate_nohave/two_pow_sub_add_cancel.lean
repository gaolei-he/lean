theorem two_pow_sub_add_cancel(h : 1 ≤ 2 * n) :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h]
