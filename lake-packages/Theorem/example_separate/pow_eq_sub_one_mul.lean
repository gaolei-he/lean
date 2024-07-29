import Theorem.example_separate.add_div_two


theorem pow_eq_sub_one_mul(hn :0 < n) :  2 ^ n = 2 ^ (n - 1) * 2  := by
    have n1 : 1 ≤ n := by linarith
    have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
      rw[Nat.sub_add_cancel n1]
    rw[← h2n]
    rw[Nat.pow_succ]


theorem pow_eq_sub_one_mul_from_0_to_0(n : ℕ)(hn : 0 < n)(gol:  2 ^ n = 2 ^ (n - 1) * 2) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  have n1 : 1 ≤ n := by linarith
  apply gol

theorem pow_eq_sub_one_mul_from_0_to_1(n : ℕ)(hn : 0 < n)(gol:  2 ^ n = 2 ^ (n - 1) * 2) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem pow_eq_sub_one_mul_from_0_to_2(n : ℕ)(hn : 0 < n)(gol:  2 ^ (n - 1 + 1) = 2 ^ (n - 1) * 2) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  rw[← h2n]
  apply gol

theorem pow_eq_sub_one_mul_from_0_to_3(n : ℕ)(hn : 0 < n) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  rw[← h2n]
  rw[Nat.pow_succ]

theorem pow_eq_sub_one_mul_from_1_to_1(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(gol:  2 ^ n = 2 ^ (n - 1) * 2) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem pow_eq_sub_one_mul_from_1_to_2(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(gol:  2 ^ (n - 1 + 1) = 2 ^ (n - 1) * 2) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  rw[← h2n]
  apply gol

theorem pow_eq_sub_one_mul_from_1_to_3(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  rw[← h2n]
  rw[Nat.pow_succ]

theorem pow_eq_sub_one_mul_from_2_to_2(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n)(gol:  2 ^ (n - 1 + 1) = 2 ^ (n - 1) * 2) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  rw[← h2n]
  apply gol

theorem pow_eq_sub_one_mul_from_2_to_3(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n) :
   2 ^ n = 2 ^ (n - 1) * 2 := by
  rw[← h2n]
  rw[Nat.pow_succ]

theorem pow_eq_sub_one_mul_from_3_to_3(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n) :
   2 ^ (n - 1 + 1) = 2 ^ (n - 1) * 2 := by
  rw[Nat.pow_succ]

