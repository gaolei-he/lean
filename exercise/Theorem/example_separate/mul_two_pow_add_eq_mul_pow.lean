theorem mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
  rw[← Nat.add_mul]


theorem mul_two_pow_add_eq_mul_pow_from_0_to_0(n : Nat) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
  rw[← Nat.add_mul]

