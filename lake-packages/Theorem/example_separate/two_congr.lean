import Theorem.example_separate.Ico_neg_eq_succ


open Nat

open Finset

open BigOperators



theorem two_congr: 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / choose (2 * m) k = 2 + (-1) / (m + 1) := by  -- 第三个等式
  simp

  have neg_pow_div_choose : ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), ((-1) * (-1 : ℝ) ^ (k - 1) ) / Nat.choose (2 * m) k := by
    refine' sum_congr rfl fun y hy => _
    have y_le_one : 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hy_cancel : (-1 : ℝ) ^ y = (-1 : ℝ) ^ (y - 1 + 1) := by
      rw[Nat.sub_add_cancel y_le_one]
    congr 1
    -- rw[hy_cancel]
    -- rw[_root_.pow_succ]
  rw[neg_pow_div_choose]
  have sum_assoc : ∑ k in Ico 1 (2 * m), (-1 : ℝ) * (-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), (-1 : ℝ) * ((-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k) := by  --用mul_div结合律，方便后续提取-1
    refine' sum_congr rfl fun y _ => _
    rw[← mul_div]
  rw[sum_assoc]  -- 使用结合律
  rw[← mul_sum]  -- 提取 -1
  rw[Ico_neg_eq_succ]
  rw[mul_div]
  simp


theorem two_congr_from_0_to_0(m : ℕ)(gol:  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) = -1 / (↑m + 1)) :
   2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) = 2 + -1 / (↑m + 1) := by
  simp
  apply gol

theorem two_congr_from_2_to_2(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(gol:  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) = -1 / (↑m + 1)) :
   ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) = -1 / (↑m + 1) := by
  rw[neg_pow_div_choose]
  apply gol

theorem two_congr_from_4_to_4(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)) = -1 / (↑m + 1)) :
   ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) = -1 / (↑m + 1) := by
  rw[sum_assoc]
  apply gol

theorem two_congr_from_4_to_5(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ (x - 1) / ↑(Nat.choose (2 * m) x) = -1 / (↑m + 1)) :
   ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) = -1 / (↑m + 1) := by
  rw[sum_assoc]
  rw[← mul_sum]
  apply gol

theorem two_congr_from_4_to_6(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * (1 / (↑m + 1)) = -1 / (↑m + 1)) :
   ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) = -1 / (↑m + 1) := by
  rw[sum_assoc]
  rw[← mul_sum]
  rw[Ico_neg_eq_succ]
  apply gol

theorem two_congr_from_4_to_7(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * 1 / (↑m + 1) = -1 / (↑m + 1)) :
   ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) = -1 / (↑m + 1) := by
  rw[sum_assoc]
  rw[← mul_sum]
  rw[Ico_neg_eq_succ]
  rw[mul_div]
  apply gol

theorem two_congr_from_4_to_8(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))) :
   ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) = -1 / (↑m + 1) := by
  rw[sum_assoc]
  rw[← mul_sum]
  rw[Ico_neg_eq_succ]
  rw[mul_div]
  simp

theorem two_congr_from_5_to_5(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ (x - 1) / ↑(Nat.choose (2 * m) x) = -1 / (↑m + 1)) :
   ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)) = -1 / (↑m + 1) := by
  rw[← mul_sum]
  apply gol

theorem two_congr_from_5_to_6(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * (1 / (↑m + 1)) = -1 / (↑m + 1)) :
   ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)) = -1 / (↑m + 1) := by
  rw[← mul_sum]
  rw[Ico_neg_eq_succ]
  apply gol

theorem two_congr_from_5_to_7(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * 1 / (↑m + 1) = -1 / (↑m + 1)) :
   ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)) = -1 / (↑m + 1) := by
  rw[← mul_sum]
  rw[Ico_neg_eq_succ]
  rw[mul_div]
  apply gol

theorem two_congr_from_5_to_8(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))) :
   ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)) = -1 / (↑m + 1) := by
  rw[← mul_sum]
  rw[Ico_neg_eq_succ]
  rw[mul_div]
  simp

theorem two_congr_from_6_to_6(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * (1 / (↑m + 1)) = -1 / (↑m + 1)) :
   -1 * ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ (x - 1) / ↑(Nat.choose (2 * m) x) = -1 / (↑m + 1) := by
  rw[Ico_neg_eq_succ]
  apply gol

theorem two_congr_from_6_to_7(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * 1 / (↑m + 1) = -1 / (↑m + 1)) :
   -1 * ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ (x - 1) / ↑(Nat.choose (2 * m) x) = -1 / (↑m + 1) := by
  rw[Ico_neg_eq_succ]
  rw[mul_div]
  apply gol

theorem two_congr_from_6_to_8(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))) :
   -1 * ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ (x - 1) / ↑(Nat.choose (2 * m) x) = -1 / (↑m + 1) := by
  rw[Ico_neg_eq_succ]
  rw[mul_div]
  simp

theorem two_congr_from_7_to_7(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k)))(gol:  -1 * 1 / (↑m + 1) = -1 / (↑m + 1)) :
   -1 * (1 / (↑m + 1)) = -1 / (↑m + 1) := by
  rw[mul_div]
  apply gol

theorem two_congr_from_7_to_8(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))) :
   -1 * (1 / (↑m + 1)) = -1 / (↑m + 1) := by
  rw[mul_div]
  simp

theorem two_congr_from_8_to_8(m : ℕ)(neg_pow_div_choose :  ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))(sum_assoc :  ∑ k in Ico 1 (2 * m), -1 * (-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k) =    ∑ k in Ico 1 (2 * m), -1 * ((-1 : ℝ) ^ (k - 1) / ↑(Nat.choose (2 * m) k))) :
   -1 * 1 / (↑m + 1) = -1 / (↑m + 1) := by
  simp

