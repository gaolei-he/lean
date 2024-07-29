import AdaLean.add_div_two

theorem mul_add_mul_eq_mul(h: 1 ≤ n) : n * (n - 1) + 2 * n = n * (n + 1) := by
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  norm_num
  rw [Nat.sub_add_cancel h]
  simp
