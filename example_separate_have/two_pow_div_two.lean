import Theorem.example_separate.two_mod_two_pow


theorem two_pow_div_two(hn : n ≠ 0): (2 ^ ( 2 * n )) / 2 = 2 ^ (( 2 * n ) - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]
