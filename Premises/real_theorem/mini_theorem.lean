import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Parity

open Nat

open Finset

open BigOperators


-- 例2
theorem ex2 (n : ℕ) : ∑ k in range (n+1), choose (2*n) k = 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n := by sorry

-- 题11
theorem t11 (n : ℕ) : ∑ k in range (n+1), k * choose (2*n) k = n * 2^(2*n-1) := by sorry



/-
  自然数相关定理
-/
theorem succ_sub (n : ℕ) (h : 1 < n): succ (n-1) = n := by
  have h1 : 1 ≤ 1 := by linarith
  have h2 : 1 ≤ n := by linarith
  rw [succ_eq_add_one]
  rw [←tsub_tsub_assoc h2 h1]
  simp

-- 习题6：等式6
theorem pow_add_one_sub_one {n : ℕ} (h : n ≠ 0) : 2^n = 2^(n - 1 + 1) := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by exact Iff.mpr one_le_iff_ne_zero h
  rw [←tsub_tsub_assoc hone_le_n hone_le_one]
  simp

-- 习题6：等式7
theorem pow_sub_one_succ {n : ℕ} : 2^(n - 1 + 1) = 2 * 2^(n-1) := by
  rw [add_one]
  rw [_root_.pow_succ 2 (n-1)]

-- 习题10：条件
theorem le_two_mul_sub_one_add_one {n : ℕ} (h : 0 < n) : n ≤ 2 * n - 1 + 1 := by
  have : 1 ≤ 2 * n := by linarith
  rw [Nat.sub_add_cancel this]
  linarith

-- 习题10：条件h2
theorem two_mul_sub_one_add_one_sub {n : ℕ} (h : 0 < n) : 2 * n - 1 + 1 - n = n := by
  have : 1 ≤ 2 * n := by linarith
  rw [Nat.sub_add_cancel this]
  rw [two_mul]
  simp


-- 习题10：条件h3
theorem two_mul_sub_one_add_one_sub_zero {n : ℕ} (h : 0 < n) : 2 * n - 1 + 1 - 0 = 2 * n := by
  simp
  have : 1 ≤ 2 * n := by linarith
  rw [Nat.sub_add_cancel this]


-- 习题17：one_div_two_mul_choose_sub_succ_mul_choose h41
theorem half_sub_eq_neg_two_mul_add_div {n : ℕ}: (((1/2) : ℝ)- (n + 1)) = - ((2*n+1) / 2) :=
  calc
    (((1/2) : ℝ)- (n + 1)) = - (n + 1/2) := by
      {
        rw [add_comm, ←sub_sub]
        norm_num
        congr 1
      }
    _ = - ((2*n+1) / 2) := by
      {
        congr 1
        rw [_root_.add_div, mul_comm]
        norm_num
      }

-- 习题17：one_div_two_mul_choose_sub_succ_mul_choose h42
theorem two_mul_eq_two_mul_sub_add {n : ℕ} (h : 1 ≤ n) : 2*n = 2*n-1+1 := by
  have : 1 ≤ 2*n := by rw [two_mul]; linarith
  rw [Nat.sub_add_cancel this]

-- 习题17：one_div_two_mul_choose_sub_succ_mul_choose h43
theorem sub_one_add_one {n : ℕ} (h : 1 ≤ n) : n = n-1+1 := by rw [Nat.sub_add_cancel h]

-- 习题17：one_div_two_mul_choose_sub_succ_mul_choose h44
theorem factorial_succ_ge_one {n : ℕ} (h : 1 ≤ n) : n * (n-1)! = n ! := by
    rw [sub_one_add_one h, Nat.factorial_succ (n-1)]
    congr 1

-- 习题17：one_div_two_mul_choose_sub_succ_mul_choose h45
theorem sub_one_eq_two_mul_sub_one_sub {n : ℕ} (h : 1 ≤ n) : n-1 = 2*n-1-n := by
    rw [two_mul, Nat.add_sub_assoc h, add_sub_self_left n (n - 1)]


/-
  组合相关定理
-/
-- 定理1.3改写1 succ_mul_choose_eq
theorem succ_mul_choose_eq' {n k : ℕ} (h0 : 1 < n) (h1 : 1 ≤ k): n * choose (n-1) (k-1) = k * choose n k := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h2 : succ (n-1) = n := by
    rw [succ_eq_add_one]
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  have h3 : succ (k-1) = k := by
    rw [succ_eq_add_one]
    rw [←tsub_tsub_assoc h1 hone_le_one]
    simp
  rw [←h2, ←h3]
  simp
  rw [succ_mul_choose_eq]
  rw [mul_comm]

-- 定理1.3改写2 succ_mul_choose_eq
theorem succ_mul_choose_eq'' {n k: ℕ} : (((1/(k+1)) : ℝ) * choose n k) = (1/(n+1)) * choose (n+1) (k+1) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    have h2 : (n + 1) * (k + 1) * ((1 / (n+1)) : ℝ) * (Nat.choose (n + 1) (k + 1))
      = (k + 1) * ((n + 1) * (1 / (n+1)) * (Nat.choose (n + 1) (k + 1))) := by
      rw [←mul_assoc]
      congr 1
      rw [←mul_assoc]
      congr 1
      rw [mul_comm]
    rw [h2]
    rw [←mul_assoc]
    have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h1 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
            = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
            exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h2 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
            = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
            exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h1, h2] at h
  have h3 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h4 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h5 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h3 h4
  rw [mul_right_inj' h5] at h
  assumption

theorem one_div_two_mul_choose_sub_succ_mul_choose (n : ℕ) (h : 1 ≤ n) : ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n
                                      = -(2*n+1) * choose (2*n-1) n := by
  have h41 : (((1/2) : ℝ)- (n + 1)) = - ((2*n+1) / 2) :=
    calc
      (((1/2) : ℝ)- (n + 1)) = - (n + 1/2) := by
        {
          rw [add_comm, ←sub_sub]
          norm_num
          congr 1
        }
      _ = - ((2*n+1) / 2) := by
        {
          congr 1
          rw [_root_.add_div, mul_comm]
          norm_num
        }
  have h42: 2*n = 2*n-1+1 := by
    have : 1 ≤ 2*n := by rw [two_mul]; linarith
    rw [Nat.sub_add_cancel this]
  have h43 : n = n-1+1 := by rw [Nat.sub_add_cancel h]
  have h44 : n * (n-1)! = n ! := by
    rw [h43,Nat.factorial_succ (n-1)]
    congr 1
  have h45 : n-1 = 2*n-1-n := by
    rw [two_mul, Nat.add_sub_assoc h, add_sub_self_left n (n - 1)]
  rw [←sub_mul, h41]
  rw [←neg_one_mul, ←neg_one_mul ((2*n+1) : ℝ), mul_assoc, mul_assoc]
  congr 1
  rw [choose_eq_factorial_div_factorial, cast_div, ←mul_div_assoc]
  rw [h42, Nat.factorial_succ (2*n-1), ←h42]
  norm_num
  rw [two_mul (n:ℕ)]
  norm_num
  rw [←two_mul (n:ℕ), h43, Nat.factorial_succ (n-1), ←h43]
  rw [div_mul, mul_assoc, ←div_div 2, div_self two_ne_zero, ←div_mul, div_one]
  rw [←mul_div, ←div_div, mul_comm (n:ℝ), cast_mul, ←mul_div, ←div_div (n:ℝ), div_self]
  rw [mul_one_div, div_div, ←cast_mul]
  rw [h44, choose_eq_factorial_div_factorial, cast_div, cast_mul]
  congr 2
  rw [mul_comm, h45] -- 第一个目标证明完成
  rw [←h45, two_mul, Nat.add_sub_assoc h]
  exact factorial_mul_factorial_dvd_factorial_add n (n - 1)
  rw [←h45, cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero (n-1))
  linarith
  rw [cast_ne_zero]
  linarith
  rw [two_mul, Nat.add_sub_cancel]
  exact factorial_mul_factorial_dvd_factorial_add n n
  rw [two_mul, Nat.add_sub_cancel, cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero n)
  linarith



-- 习题5：条件h1
theorem sum_range_choose_mul_pow_succ (x : ℕ) (h : 0 < x): 1 / (n + 1) * ∑ k in range (n + 1), Nat.choose (n + 1) (k + 1) * ((x ^ k) : ℝ)
            = 1 / ((n + 1) * x) * ∑ k in range (n + 1), Nat.choose (n + 1) (k + 1) * ((x ^ (k+1)) : ℝ) := by
  rw [mul_sum, mul_sum]
  rw [div_mul_eq_div_mul_one_div]
  refine' sum_congr rfl fun y hy => _
  rw [pow_add,mul_assoc]
  congr 1
  rw [←mul_assoc]
  rw [mul_comm  (1/(x:ℝ))  ((Nat.choose (n + 1) (y + 1)) : ℝ)]
  rw [mul_assoc]
  congr 1
  rw [div_mul,mul_comm]
  simp
  rw [mul_div_right_comm, div_self]
  simp
  have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
  exact Iff.mpr cast_ne_zero this


-- 习题6：等式1
theorem two_mul_sum_ite {n : ℕ} : 2 * (∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) else 0))
        = ∑ k in range (n+1), (if k % 2 = 1 then 2 * ((choose n k) : ℤ) else 0) := by
        rw [mul_sum]
        refine' sum_congr rfl fun y hy => _
        rw [ite_mul_zero_right (y % 2 = 1) 2 ((Nat.choose n y) : ℤ)]

-- 习题6：等式2
theorem ite_two_mul_eq_add_zero_eq_sub {n : ℕ} : ∑ k in range (n+1), (if k % 2 = 1 then 2 * ((choose n k) : ℤ) else 0)
        = ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) + ((choose n k) : ℤ) else ((choose n k) : ℤ) - ((choose n k) : ℤ)) := by
        refine' sum_congr rfl fun y hy => _
        congr 1
        rw [two_mul]
        simp

-- 习题6：等式3
theorem ite_add_eq_sub_neg {n : ℕ} : ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) + ((choose n k) : ℤ) else ((choose n k) : ℤ) - ((choose n k) : ℤ))
        = ∑ k in range (n+1), ((if k % 2 = 1 then choose n k - (-1)^k * choose n k else choose n k - (-1)^k * choose n k) : ℤ) := by
        refine' sum_congr rfl fun y fy => _
        split_ifs with h'
        . rw [←Nat.odd_iff] at h'
          rw [Odd.neg_one_pow h']
          rw [neg_one_mul]
          rw [sub_neg_eq_add]
        . rw [Nat.mod_two_ne_one, ←Nat.even_iff] at h'
          rw [Even.neg_one_pow h']
          simp

-- 习题6：等式4
theorem ite_merge {n : ℕ} : ∑ k in range (n+1), ((if k % 2 = 1 then choose n k - (-1)^k * choose n k else choose n k - (-1)^k * choose n k) : ℤ)
                = ∑ k in range (n+1), ((choose n k - (-1)^k * choose n k) : ℤ) := by simp

-- 习题6：等式5
theorem add_pow_sub_choose_of_ne {n : ℕ} (h : n ≠ 0) : ∑ k in range (n+1), ((choose n k - (-1)^k * choose n k) : ℤ) = 2^n := by
  rw [sum_sub_distrib]
  rw [Int.alternating_sum_range_choose_of_ne h]
  simp
  have := (add_pow (1:ℤ) 1 n).symm
  simpa [one_add_one_eq_two] using this


-- 习题10：条件h1
theorem sum_range_halfway_choose_symm {n : ℕ} (h : 0 < n) : ∑ k in range n, choose (2 * n - 1) k
            = ∑ k in range n, choose (2 * n - 1) (2 * n - 1 - k) := by
  refine' sum_congr rfl fun y hy => _
  have : y ≤ 2 * n - 1 := by
    have h1 : y < n := mem_range.1 hy
    refine le_pred_of_lt ?h
    have h2 : n < 2 * n := by exact lt_two_mul_self h
    exact Nat.lt_trans h1 h2
  rw [choose_symm this]

-- 习题16：等式1
theorem sum_range_mul_eq_neg_mul_sub_sub_mul {n : ℕ} : ∑ k in range (n+1), k * choose (2*n) (n-k)
      = ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n) (n-k) := by
      rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n) (n - x)]
      refine' sum_congr rfl fun k hk => _
      rw [cast_mul]
      congr 1
      norm_num

-- 习题16: 等式2
theorem sum_neg_mul_eq_neg_mul_sum {n : ℕ} : ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n) (n-k)
        = (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n) (n-k) := by
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc]


-- 习题16：等式3
theorem sum_range_add_one_sub_one {n : ℕ} : (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n) (n-k)
      = (-1 : ℝ) * ∑ k in range (n + 1), ((n + 1 - 1 - k) - n) * ((Nat.choose (2 * n) (n + 1 - 1 - k)) : ℝ) := by
  congr 1
  refine' sum_congr rfl fun k hk => _
  congr 1
  simp


-- 习题16：等式5
theorem neg_mul_sum_eq_sum_neg_mul {n : ℕ} : (-1 : ℝ) * ∑ k in range (n+1), (k-(n:ℝ)) * choose (2*n) k
                  = ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n) k := by
  rw [mul_sum]
  refine' sum_congr rfl fun k hk => _
  rw [←neg_one_mul (k-(n:ℝ))]
  rw [mul_assoc]


-- 习题16：等式6
theorem sum_range_neg_sub {n : ℕ} : ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n) k
                  = ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n) k := by
  refine' sum_congr rfl fun k hk => _
  congr 1
  exact neg_sub (k:ℝ) (n:ℝ)


-- 习题16：等式7
theorem sum_range_sub_mul {n : ℕ} : ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n) k
                  = ∑ k in range (n+1), ((n:ℝ) * choose (2*n) k - k * choose (2*n) k) := by
  refine' sum_congr rfl fun k hk => _
  rw [sub_mul]


-- 习题16：等式8
theorem cast_sum_add_distrib {n : ℕ} : ∑ k in range (n+1), ((n:ℝ) * choose (2*n) k - k * choose (2*n) k)
                = ∑ k in range (n+1), (n:ℝ) * choose (2*n) k - ∑ k in range (n+1), k * choose (2*n) k := by
  rw [sum_sub_distrib]
  congr 1
  rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n) x]
  refine' sum_congr rfl fun k hk => _
  rw [cast_mul]

-- 习题16：等式9
theorem cast_sum_mul {n : ℕ} : ∑ k in range (n+1), (n:ℝ) * choose (2*n) k - ∑ k in range (n+1), k * choose (2*n) k
                = (∑ k in range (n+1), n * choose (2*n) k) - (∑ k in range (n+1), k * choose (2*n) k) := by -- 这里是在变换数据类型
  rw [cast_sum (range (n+1)) fun x => n * Nat.choose (2 * n) x]
  congr 1
  refine' sum_congr rfl fun k hk => _
  rw [cast_mul]

-- 习题16：等式10
-- TODO: 改名字
theorem t11_of_sub {n : ℕ} : (∑ k in range (n+1), n * choose (2*n) k) - (∑ k in range (n+1), k * choose (2*n) k)
                  = ∑ k in range (n+1), n * choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
  congr 1
  rw [t11 n]

-- 习题16：等式11
theorem mul_sum_of_sub {n : ℕ} : ∑ k in range (n+1), n * choose (2*n) k - ((n * 2^(2*n-1)) :ℕ)
                  = n * ∑ k in range (n+1), choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
  congr 1
  rw [mul_sum]

-- 习题16：等式12
-- TODO: 改名字
theorem ex2_of_sub {n : ℕ} : n * ∑ k in range (n+1), choose (2*n) k - ((n * 2^(2*n-1)) :ℕ)
                  = n * ((2^(2*n-1)) + (((1/2):ℝ) * choose (2*n) n)) - ((n * 2^(2*n-1)) :ℕ) := by
  congr 2
  rw [ex2 n]

-- 习题16：等式13
theorem mul_add_comm_simp {n : ℕ} : n * ((2^(2*n-1)) + (((1/2):ℝ) * choose (2*n) n)) - ((n * 2^(2*n-1)) :ℕ)
                = n * (((1/2):ℝ) * choose (2*n) n) := by
  rw [mul_add]
  rw [add_comm]
  simp


-- 习题17sum_mul_choose_eq_two_pow'：条件h1
theorem sum_Ico_to_range_add_zero {n : ℕ} : ∑ k in Ico 1 (n + 1), k * choose (2*n) k = ∑ k in range (n+1), k * choose (2*n) k := by
  have h_gt_zero : 0 < n + 1 := by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
  simp

-- 习题17sum_mul_choose_eq_two_pow'：条件h2
theorem sum_Ico_to_range_sub {n : ℕ} : ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1)
          = ∑ k in range (n+1), (k+1) * choose (2*n) k - (n+1) * choose (2*n) n := by
  rw [sum_Ico_eq_sum_range, sum_range_succ]
  simp [add_comm]

-- 习题17sum_mul_choose_eq_two_pow'：条件h3
theorem sum_range_add_mul_distrib {n : ℕ} : ∑ k in range (n+1), (k+1) * choose (2*n) k
          = ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k := by
  rw [←sum_add_distrib]
  refine' sum_congr rfl fun k hk => _
  rw [add_mul]
  simp


-- 习题17sum_mul_choose_eq_two_pow'：等式1
theorem sum_range_eq_Ico_succ_bot {n : ℕ} : ((∑ k in range (n+1), k * choose (2*n+1) k) : ℝ)
            = ∑ k in Ico 1 (n + 1), k * choose (2*n+1) k := by
  have h_gt_zero : 0 < n + 1 := by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
  simp


-- 习题17sum_mul_choose_eq_two_pow'：等式2
theorem sum_choose_succ_succ' {n : ℕ} : ∑ k in Ico 1 (n + 1), k * choose (2*n+1) k
                  = ∑ k in Ico 1 (n + 1), k * (choose (2*n) k + choose (2*n) (k-1)) := by
  refine' sum_congr rfl fun k hk => _
  congr 1
  have : k = k-1+1 := by
    rw [Nat.sub_add_cancel]
    rw [mem_Ico] at hk
    exact hk.left
  rw [this, choose_succ_succ' (2*n) (k-1), ←this, add_comm]


-- 习题17sum_mul_choose_eq_two_pow'：等式3
theorem sum_mul_add {n : ℕ} : ∑ k in Ico 1 (n + 1), k * (choose (2*n) k + choose (2*n) (k-1))
                  = ∑ k in Ico 1 (n + 1), (k * choose (2*n) k + k * choose (2*n) (k-1)) := by
  refine' sum_congr rfl fun k hk => _
  rw [mul_add]


-- 习题17sum_mul_choose_eq_two_pow'：等式5
theorem Ico_eq_range_with_add_zero_and_sub {n : ℕ} : ((∑ k in Ico 1 (n + 1), k * choose (2*n) k + ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1)) : ℝ)
    = ∑ k in range (n+1), k * choose (2*n) k
      + ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k - (n+(1:ℕ)) * choose (2*n) n := by
  rw [sum_Ico_to_range_add_zero, sum_Ico_to_range_sub]
  rw [cast_sub, ←add_sub_assoc]
  congr 1
  rw [add_assoc]
  congr 1
  rw [sum_range_add_mul_distrib, cast_add]
  rw [←cast_add, ←cast_mul]
  rw [sum_range_succ]
  have : 0 ≤ ∑ k in range n, (k + 1) * Nat.choose (2 * n) k := by
    exact Nat.zero_le (∑ k in range n, (k + 1) * Nat.choose (2 * n) k)
  linarith


-- 习题17sum_mul_choose_eq_two_pow'：等式6
-- TODO: 改名字
theorem t11_add_ex2 {n : ℕ} : ∑ k in range (n+1), k * choose (2*n) k
      + ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k - (n+(1:ℕ)) * choose (2*n) n
      = 2*(n:ℝ)*2^(2*n-1) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
  rw [←two_mul, t11, ex2]
  congr 1
  rw [cast_mul, ←mul_assoc, ←add_assoc]
  congr 3
  rw [cast_pow]
  congr 1
  congr 2
  rw [cast_one]


-- 习题17sum_mul_choose_eq_two_pow'：等式7
theorem pow_add'_comm {n : ℕ} (h : 1 ≤ n) : 2*(n:ℝ)*2^(2*n-1) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n
                  = n*2^(2*n) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
  congr 3
  rw [←cast_comm, mul_assoc]
  congr 1
  have : 2*n = 2*n-1+1 := by
    have : 1 ≤ 2*n := by rw [two_mul]; linarith
    rw [Nat.sub_add_cancel this]
  rw [this, pow_add, ←this, pow_one, mul_comm]


-- 习题17sum_mul_choose_eq_two_pow'：等式8
theorem simp_with_one_div_two_mul_choose_sub_succ_mul_choose {n : ℕ} (h : 1 ≤ n) : n*2^(2*n) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n
                = n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n := by
  rw [add_sub_assoc]
  rw [one_div_two_mul_choose_sub_succ_mul_choose n h]
  congr 1
  rw [←neg_one_mul ((2 * n + 1) * (Nat.choose (2 * n - 1) n) : ℝ)]
  rw [←mul_assoc, neg_one_mul]


-- 习题17sum_mul_choose_eq_two_pow'：等式10
theorem simp_sub {n : ℕ} : (n*2^(2*n)) - ((n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n) : ℝ)
                = (2*n+1) * choose (2*n-1) n - 2^(2*n-1) := by
  rw [←add_sub, ←sub_sub, sub_self, ←sub_add, add_comm]
  congr 1
  simp


-- 习题20：等式1
theorem cast_sum_choose_mul {n l : ℕ} {x : ℝ} : ∑ k in Ico l (n+1), (choose n k) * (choose k l) * x^k * (1 - x)^(n - k)
      = ∑ k in Ico l (n+1), (choose n l) * (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k) := by
  refine' sum_congr rfl fun k hk => _
  congr 2
  rw [mem_Ico] at hk
  rw [←cast_mul,←cast_mul]
  rw [choose_mul]
  linarith
  exact hk.left

-- 习题20：等式2
theorem sum_choose_mul_eq_choose_mul_sum {n l : ℕ} {x : ℝ} : ∑ k in Ico l (n+1), (choose n l) * (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k)
  = (choose n l)  * ∑ k in Ico l (n+1), (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k) := by
  rw [mul_sum]
  simp [mul_assoc]

-- 习题20：等式3
theorem sum_Ico_eq_sum_range_simp {n l : ℕ} {x : ℝ} : (choose n l) * ∑ k in Ico l (n+1), (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k)
          = (choose n l) * ∑ k in range (n+1-l), (choose (n-l) k) * x^(l+k) * (1 - x)^(n-(l+k)) := by
  rw [sum_Ico_eq_sum_range]
  simp

-- 习题20：等式4
theorem cast_sum_mul_comm {n l : ℕ} {x : ℝ} : (choose n l) * ∑ k in range (n+1-l), (choose (n-l) k) * x^(l+k) * (1 - x)^(n-(l+k))
        = (choose n l) * ∑ k in range (n+1-l), x^(l+k) * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
  congr 1
  refine' sum_congr rfl fun k hk => _
  congr 1
  rw [mul_comm]

-- 习题20：等式5
theorem sum_pow_add {n l : ℕ} {x : ℝ} : (choose n l) * ∑ k in range (n+1-l), x^(l+k) * (choose (n-l) k) * (1 - x)^(n-(l+k))
        = (choose n l) * ∑ k in range (n+1-l), x^l * x^k * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
  congr 1
  refine' sum_congr rfl fun k hk => _
  rw [pow_add]

-- 习题20：等式6
theorem sum_pow_mul_eq_pow_mul_sum {n l : ℕ} {x : ℝ} : (choose n l) * ∑ k in range (n+1-l), x^l * x^k * (choose (n-l) k) * (1 - x)^(n-(l+k))
                          = (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
  rw [mul_assoc]
  repeat rw [mul_sum]
  simp [mul_assoc]

-- 习题20：等式7
theorem sum_sub_add_eq {n l : ℕ} {x : ℝ} : (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^(n-(l+k))
                          = (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^((n-l)-k) := by
  congr 1
  refine' sum_congr rfl fun k hk => _
  congr 2
  exact sub_add_eq n l k

-- 习题20：等式8
theorem sum_choose_mul_pow_comm {n l : ℕ} {x : ℝ} (h : l ≤ n) : (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^((n-l)-k)
                          = (choose n l) * x^l * ∑ k in range (n-l+1), x^k * (1 - x)^((n-l)-k) * (choose (n-l) k) := by
  have : n+1-l = n-l+1 := by rw [succ_sub h]
  rw [this]
  congr 1
  refine' sum_congr rfl fun k hk => _
  rw [mul_assoc,mul_assoc]
  congr 1
  rw [mul_comm]

-- 习题20：等式9
theorem mul_mul_add_pow {n l : ℕ} {x : ℝ} : (choose n l) * x^l * ∑ k in range (n-l+1), x^k * (1 - x)^((n-l)-k) * (choose (n-l) k)
                          = (choose n l) * x^l * (x + (1-x))^(n-l) := by rw [←add_pow (x:ℝ) (1-x) (n-l)]

-- 习题20：等式10
theorem mul_mul_pow_add_sub {n l : ℕ} {x : ℝ} : (choose n l) * x^l * (x + (1-x))^(n-l) = (choose n l) * x^l * (1)^(n-l) := by
  rw [add_sub]
  congr 2
  rw [add_sub_right_comm x 1 x, sub_self]
  simp


-- 习题20：等式11
theorem mul_mul_one_pow {n l : ℕ} {x : ℝ} : (choose n l) * x^l * (1)^(n-l) = (choose n l) * x^l := by
  rw [one_pow]
  simp






/-
  组合数计算
-/

-- 习题16：等式14
theorem cast_mul_mul_choose_eq_factorial_div_factorial {n : ℕ} : n * (((1/2):ℝ) * choose (2*n) n)
                  = n * ((1/2):ℝ) * ((2*n)! / ((n)! * (2*n -n)!)) := by
  rw [choose_eq_factorial_div_factorial]
  rw [←mul_assoc,←cast_mul, ←cast_div]
  rw [two_mul, Nat.add_sub_cancel]
  exact factorial_mul_factorial_dvd_factorial_add n n
  rw [two_mul, Nat.add_sub_cancel]
  rw [cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero n)
  linarith

-- 习题16：等式15
theorem factorial_succ_of_two_mul_ge_one {n : ℕ} (h : 1 ≤ n) : n * ((1/2):ℝ) * ((2*n)! / ((n)! * (2*n -n)!))
                = n * ((1/2):ℝ) * (((2:ℕ)*n-1+1)*((2:ℕ)*n-1)! / (n ! * n !)) := by
  congr 1
  have : 2*n = 2*n-1+1 := by
    have : 1 ≤ 2*n := by rw [two_mul];linarith
    rw [Nat.sub_add_cancel this]
  rw [this]
  rw [Nat.factorial_succ (2*n-1)]
  rw [←this, cast_mul, ←cast_mul 2 n]
  rw [sub_add_cancel]
  congr 3
  rw [two_mul, Nat.add_sub_cancel]


-- 习题16：等式16
theorem cast_factorial_sub_one_add_one {n : ℕ} : n * ((1/2):ℝ) * (((2:ℕ)*n-1+1)*((2:ℕ)*n-1)! / (n ! * n !))
                = n * (((1/2):ℝ) * ((2:ℕ)*n)*((2:ℕ)*n-1)! / (n ! * n !)) := by
  rw [sub_add_cancel, mul_assoc]
  congr 1
  rw [←cast_mul,←cast_mul,←cast_mul,←mul_div_assoc]
  congr 1
  rw [cast_mul,←mul_assoc]


-- 习题16：等式17
theorem one_div_two_mul_two_of_factorial {n : ℕ} : n * (((1/2):ℝ) * ((2:ℕ)*n)*((2:ℕ)*n-1)! / (n ! * n !))
                  = n * (n * ((2:ℕ)*n-1)! / (n ! * n !)) := by simp


-- 习题16：等式19
theorem factorial_mul_div_simp {n : ℕ} (h : 1 ≤ n) : ((n * (n * ((2:ℕ)*n-1)! / (n ! * (n * (n-1) !)))):ℝ)
                  = n * (((2:ℕ)*n-1)! / (n ! * (n-1) !)) := by
  congr 1
  rw [mul_comm, mul_div_assoc]
  rw [←cast_mul, ←cast_mul, mul_comm (n !) _, cast_mul]
  rw [div_mul_eq_div_div,cast_mul,div_mul_eq_div_div]
  rw [div_self, ←div_mul_eq_div_div, mul_one_div, mul_comm ((n-1)! : ℝ) _]
  rw [cast_ne_zero]
  linarith

-- 习题16：等式20
theorem mul_factorial_div_factorial_eq_choose {n : ℕ} (h : 1 ≤ n) : ((n * (((2:ℕ)*n-1)! / (n ! * (n-1) !))) : ℝ)
                 = n * choose (2*n-1) n := by
  congr 1
  have : n-1 = 2*n-1-n := by
    rw [two_mul, Nat.add_sub_assoc h, add_sub_self_left n (n - 1)]
  rw [this]
  rw [choose_eq_factorial_div_factorial, cast_div, cast_mul]
  all_goals (try rw [←this])
  rw [two_mul, Nat.add_sub_assoc h]
  exact factorial_mul_factorial_dvd_factorial_add n (n-1)
  rw [cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero (n-1))
  rw [two_mul]
  have h1 : n - 1 + n = n + n - 1 := by exact tsub_add_eq_add_tsub h
  rw [←h1]
  exact Nat.le_add_left n (n - 1)
