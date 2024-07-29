import Theorem.example_separate.two_mod_two_pow


theorem two_pow_div_two(hn : n ≠ 0): (2 ^ ( 2 * n )) / 2 = 2 ^ (( 2 * n ) - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]


theorem two_pow_div_two_from_0_to_0(n : ℕ)(hn : n ≠ 0)(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  apply gol

theorem two_pow_div_two_from_0_to_1(n : ℕ)(hn : n ≠ 0)(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  apply gol

theorem two_pow_div_two_from_0_to_2(n : ℕ)(hn : n ≠ 0)(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  apply gol

theorem two_pow_div_two_from_0_to_3(n : ℕ)(hn : n ≠ 0)(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  apply gol

theorem two_pow_div_two_from_0_to_4(n : ℕ)(hn : n ≠ 0)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  apply gol

theorem two_pow_div_two_from_0_to_5(n : ℕ)(hn : n ≠ 0)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  apply gol

theorem two_pow_div_two_from_0_to_6(n : ℕ)(hn : n ≠ 0)(gol:  2 ^ (2 * n - 1 + 1) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  apply gol

theorem two_pow_div_two_from_0_to_7(n : ℕ)(hn : n ≠ 0) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]

theorem two_pow_div_two_from_1_to_1(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  apply gol

theorem two_pow_div_two_from_1_to_2(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  apply gol

theorem two_pow_div_two_from_1_to_3(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  apply gol

theorem two_pow_div_two_from_1_to_4(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  apply gol

theorem two_pow_div_two_from_1_to_5(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  apply gol

theorem two_pow_div_two_from_1_to_6(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(gol:  2 ^ (2 * n - 1 + 1) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  apply gol

theorem two_pow_div_two_from_1_to_7(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]

theorem two_pow_div_two_from_2_to_2(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1 : 1 ≤ 2 * n := by
    linarith
  apply gol

theorem two_pow_div_two_from_2_to_3(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  apply gol

theorem two_pow_div_two_from_2_to_4(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  apply gol

theorem two_pow_div_two_from_2_to_5(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  apply gol

theorem two_pow_div_two_from_2_to_6(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(gol:  2 ^ (2 * n - 1 + 1) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  apply gol

theorem two_pow_div_two_from_2_to_7(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h1 : 1 ≤ 2 * n := by
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]

theorem two_pow_div_two_from_3_to_3(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(gol:  2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h02 : 0 < 2 := by simp
  apply gol

theorem two_pow_div_two_from_3_to_4(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  apply gol

theorem two_pow_div_two_from_3_to_5(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  apply gol

theorem two_pow_div_two_from_3_to_6(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(gol:  2 ^ (2 * n - 1 + 1) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  apply gol

theorem two_pow_div_two_from_3_to_7(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]

theorem two_pow_div_two_from_4_to_4(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  apply gol

theorem two_pow_div_two_from_4_to_5(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  apply gol

theorem two_pow_div_two_from_4_to_6(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2)(gol:  2 ^ (2 * n - 1 + 1) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  apply gol

theorem two_pow_div_two_from_4_to_7(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2) :
   2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) := by
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]

theorem two_pow_div_two_from_5_to_5(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2)(gol:  2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  apply gol

theorem two_pow_div_two_from_5_to_6(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2)(gol:  2 ^ (2 * n - 1 + 1) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  apply gol

theorem two_pow_div_two_from_5_to_7(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2) :
   2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]

theorem two_pow_div_two_from_6_to_6(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2)(two_pow_sub_add_cancel : 2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n))(gol:  2 ^ (2 * n - 1 + 1) = 2 * 2 ^ (2 * n - 1)) :
   2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
  rw[← two_pow_sub_add_cancel]
  apply gol

theorem two_pow_div_two_from_6_to_7(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2)(two_pow_sub_add_cancel : 2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n)) :
   2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]

theorem two_pow_div_two_from_7_to_7(n : ℕ)(hn : n ≠ 0)(h1n : 1 ≤ n)(h2 : 2 ∣ 2 ^ (2 * n))(h1 : 1 ≤ 2 * n)(h02 : 0 < 2)(two_pow_sub_add_cancel : 2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n)) :
   2 ^ (2 * n - 1 + 1) = 2 * 2 ^ (2 * n - 1) := by
  rw[Nat.pow_succ, mul_comm]

