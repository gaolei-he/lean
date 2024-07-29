import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem mul_choose_eq_mul_choose(hn :0 < n) : ∑ k in range (n+1), k * choose n k = ∑ k in Ico 1 (n + 1), n * choose (n-1) (k-1) := by
  have h_succ : 0 < n + 1 := by linarith
  have range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   -- 更改 k 的范围
    rw[range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot h_succ]
    simp
  rw[range_eq_ico_mul_choose]
  refine' sum_congr rfl fun y hy => _
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    linarith
  rw[choose_mul_eq_mul_sub' hyn hy1]  -- 使用定理1.3


theorem mul_choose_eq_mul_choose_from_0_to_0(n : ℕ)(hn : 0 < n)(gol:  ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1)) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) := by
  have h_succ : 0 < n + 1 := by linarith
  apply gol

theorem mul_choose_eq_mul_choose_from_0_to_1(n : ℕ)(hn : 0 < n)(gol:  ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1)) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) := by
  have h_succ : 0 < n + 1 := by linarith
  have range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   rw[range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot h_succ]
    simp
  apply gol

theorem mul_choose_eq_mul_choose_from_0_to_2(n : ℕ)(hn : 0 < n)(gol:  ∑ k in Ico 1 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1)) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) := by
  have h_succ : 0 < n + 1 := by linarith
  have range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   rw[range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot h_succ]
    simp
  rw[range_eq_ico_mul_choose]
  apply gol

theorem mul_choose_eq_mul_choose_from_1_to_1(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(gol:  ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1)) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) := by
  have range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   rw[range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot h_succ]
    simp
  apply gol

theorem mul_choose_eq_mul_choose_from_1_to_2(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(gol:  ∑ k in Ico 1 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1)) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) := by
  have range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   rw[range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot h_succ]
    simp
  rw[range_eq_ico_mul_choose]
  apply gol

theorem mul_choose_eq_mul_choose_from_2_to_2(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(gol:  ∑ k in Ico 1 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1)) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) := by
  rw[range_eq_ico_mul_choose]
  apply gol

theorem mul_choose_eq_mul_choose_from_4_to_4(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1)) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem mul_choose_eq_mul_choose_from_4_to_5(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1)) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
  apply gol

theorem mul_choose_eq_mul_choose_from_4_to_6(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1)) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    linarith
  apply gol

theorem mul_choose_eq_mul_choose_from_4_to_7(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1)) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    linarith
  rw[choose_mul_eq_mul_sub' hyn hy1]

theorem mul_choose_eq_mul_choose_from_5_to_5(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(gol:  y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1)) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
  apply gol

theorem mul_choose_eq_mul_choose_from_5_to_6(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(gol:  y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1)) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    linarith
  apply gol

theorem mul_choose_eq_mul_choose_from_5_to_7(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    linarith
  rw[choose_mul_eq_mul_sub' hyn hy1]

theorem mul_choose_eq_mul_choose_from_6_to_6(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(hy_succ : y < n + 1)(gol:  y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1)) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hyn : y ≤ n := by
    linarith
  apply gol

theorem mul_choose_eq_mul_choose_from_6_to_7(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(hy_succ : y < n + 1) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  have hyn : y ≤ n := by
    linarith
  rw[choose_mul_eq_mul_sub' hyn hy1]

theorem mul_choose_eq_mul_choose_from_7_to_7(n : ℕ)(hn : 0 < n)(h_succ : 0 < n + 1)(range_eq_ico_mul_choose : ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k)(y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(hy_succ : y < n + 1)(hyn : y ≤ n) :
   y * Nat.choose n y = n * Nat.choose (n - 1) (y - 1) := by
  rw[choose_mul_eq_mul_sub' hyn hy1]

