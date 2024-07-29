import Theorem.example_separate.sum_mul_choose_eq_mul_two_pow_sub

open Nat

open Finset

open BigOperators


theorem sum_succ_choose(hn :0 < n) :  ∑ k in range (n+1), (k+1) * choose n k = 2 ^ (n - 1) * (n + 2) := by
  have sum_mul_add_distrib : ∑ k in range (n+1), (k+1) * choose n k = ∑ k in range (n+1), (k * choose n k + 1 * choose n k) := by
    refine' sum_congr rfl fun y _ => _
    rw[add_mul]
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]


theorem sum_succ_choose_from_1_to_1(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  apply gol

theorem sum_succ_choose_from_1_to_2(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  apply gol

theorem sum_succ_choose_from_1_to_3(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  apply gol

theorem sum_succ_choose_from_1_to_4(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  apply gol

theorem sum_succ_choose_from_1_to_5(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  apply gol

theorem sum_succ_choose_from_1_to_6(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  apply gol

theorem sum_succ_choose_from_1_to_7(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem sum_succ_choose_from_1_to_8(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  apply gol

theorem sum_succ_choose_from_1_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_1_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k)) :
   ∑ k in range (n + 1), (k + 1) * Nat.choose n k = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_2_to_2(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  apply gol

theorem sum_succ_choose_from_2_to_3(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  apply gol

theorem sum_succ_choose_from_2_to_4(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  apply gol

theorem sum_succ_choose_from_2_to_5(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  apply gol

theorem sum_succ_choose_from_2_to_6(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  apply gol

theorem sum_succ_choose_from_2_to_7(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem sum_succ_choose_from_2_to_8(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  apply gol

theorem sum_succ_choose_from_2_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_2_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k)) :
   ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k) = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_3_to_3(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  apply gol

theorem sum_succ_choose_from_3_to_4(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  apply gol

theorem sum_succ_choose_from_3_to_5(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  apply gol

theorem sum_succ_choose_from_3_to_6(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  apply gol

theorem sum_succ_choose_from_3_to_7(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem sum_succ_choose_from_3_to_8(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  apply gol

theorem sum_succ_choose_from_3_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_3_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k)) :
   ∑ x in range (n + 1), x * Nat.choose n x + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_4_to_4(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  simp
  apply gol

theorem sum_succ_choose_from_4_to_5(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  simp
  rw [sum_range_choose]
  apply gol

theorem sum_succ_choose_from_4_to_6(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  apply gol

theorem sum_succ_choose_from_4_to_7(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem sum_succ_choose_from_4_to_8(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  apply gol

theorem sum_succ_choose_from_4_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_4_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), 1 * Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  simp
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_5_to_5(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw [sum_range_choose]
  apply gol

theorem sum_succ_choose_from_5_to_6(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  apply gol

theorem sum_succ_choose_from_5_to_7(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem sum_succ_choose_from_5_to_8(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  apply gol

theorem sum_succ_choose_from_5_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_5_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k)) :
   n * 2 ^ (n - 1) + ∑ x in range (n + 1), Nat.choose n x = 2 ^ (n - 1) * (n + 2) := by
  rw [sum_range_choose]
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_6_to_6(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have n1 : 1 ≤ n := by linarith
  apply gol

theorem sum_succ_choose_from_6_to_7(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem sum_succ_choose_from_6_to_8(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  apply gol

theorem sum_succ_choose_from_6_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_6_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have n1 : 1 ≤ n := by linarith
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_7_to_7(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem sum_succ_choose_from_7_to_8(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  apply gol

theorem sum_succ_choose_from_7_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_7_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
    rw[Nat.sub_add_cancel n1]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_8_to_8(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n)(gol:  n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  apply gol

theorem sum_succ_choose_from_8_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n)(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_8_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_9_to_9(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n)(pow_eq_sub_one_mul : 2 ^ n = 2 ^ (n - 1) * 2)(gol:  n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2)) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  rw[pow_eq_sub_one_mul]
  apply gol

theorem sum_succ_choose_from_9_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n)(pow_eq_sub_one_mul : 2 ^ n = 2 ^ (n - 1) * 2) :
   n * 2 ^ (n - 1) + 2 ^ n = 2 ^ (n - 1) * (n + 2) := by
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]

theorem sum_succ_choose_from_10_to_10(n : ℕ)(hn : 0 < n)(sum_mul_add_distrib :  ∑ k in range (n + 1), (k + 1) * Nat.choose n k = ∑ k in range (n + 1), (k * Nat.choose n k + 1 * Nat.choose n k))(n1 : 1 ≤ n)(h2n : 2 ^ (n - 1 + 1) = 2 ^ n)(pow_eq_sub_one_mul : 2 ^ n = 2 ^ (n - 1) * 2) :
   n * 2 ^ (n - 1) + 2 ^ (n - 1) * 2 = 2 ^ (n - 1) * (n + 2) := by
  rw[mul_comm, mul_add]

