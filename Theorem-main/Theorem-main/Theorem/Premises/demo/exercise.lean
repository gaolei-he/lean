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


-- 定理1.3
theorem choose_mul_eq_mul_sub' {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
  k * choose n k = n * choose (n - 1) (k - 1) := by
    have t : choose k 1 * choose n k= choose n 1 * choose (n - 1) (k - 1) := by rw[mul_comm, choose_mul hkn hsk]
    rw[choose_one_right, choose_one_right] at t
    rw[t]


-- 定理1.3改写 succ_mul_choose_eq
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


-- 例题3
theorem sum_div_succ_mul_choose {n k: ℕ} : ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k = (1/(n+1)) * (2^(n+1) - 1) := by
  have : ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k
        = ∑ k in range (n+1), ((1/(n+1)) : ℝ) * choose (n+1) (k+1) := by
        refine' sum_congr rfl fun y hy => _
        exact succ_mul_choose_eq''
  rw [this, ←mul_sum]
  congr 1
  rw [←one_add_one_eq_two]
  rw [add_pow 1 1 (n+1)]
  simp
  rw [sum_range_succ' _ (n + 1)]
  simp

-- 例题5
def delta (m n : ℕ) : ℕ :=
  if m = n then 1 else 0

theorem alternating_sum_choose_mul { m n : ℕ } (h : m ≤ n) :
  ( ∑ k in Ico m (n + 1), (-1 : ℤ) ^ k * (choose n k) * (choose k m) ) = (-1) ^ m * delta m n := by
  by_cases h_eq : m = n
  . rw [h_eq]
    simp [delta]
  . rw [delta]
    simp [h_eq]
    have h1 : ∀ m n i: ℕ, i ∈ Ico m (n+1) →
      (-1 : ℤ) ^ i * (choose n i) * (choose i m) = (-1 : ℤ) ^ i * (choose n m * choose (n-m) (i-m)) := by
      intro m n i hi
      simp_rw [mul_assoc, ←cast_mul]
      congr 1
      have h2 : i ≤ n := Nat.le_of_lt_succ (mem_Ico.mp hi).right
      have h3 : m ≤ i := (mem_Ico.mp hi).left
      rw [choose_mul h2 h3]
    rw [sum_congr rfl (h1 m n)]
    rw [sum_Ico_eq_sum_range]
    rw [add_comm, add_tsub_assoc_of_le h, add_comm]
    simp [pow_add,mul_assoc]
    rw [←mul_sum]
    simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum, ←mul_assoc, cast_comm]
    have h2 : 0 < n - m := tsub_pos_of_lt (lt_of_le_of_ne h h_eq)
    rw [pos_iff_ne_zero] at h2
    rw [Int.alternating_sum_range_choose_of_ne h2]
    simp


-- 例题6
theorem sum_Ico_choose_mul { m n : ℕ } (h : m ≤ n) :
  (∑ k in Ico m (n + 1), (choose n k) * (choose k m) = 2^(n-m) * choose n m) := by
  by_cases h_eq : m = n
  . rw [h_eq]
    simp
  case neg =>
    have h1 : ∀ m n i: ℕ, i ∈ Ico m (n+1) → (choose n i) * (choose i m) = (choose n m * choose (n-m) (i-m)) := by
      intro m n i hi
      have h2 : i ≤ n := Nat.le_of_lt_succ (mem_Ico.mp hi).right
      have h3 : m ≤ i := (mem_Ico.mp hi).left
      exact choose_mul h2 h3
    rw [sum_congr rfl (h1 m n)]
    rw [sum_Ico_eq_sum_range]
    simp
    rw [←mul_sum]
    rw [add_comm, add_tsub_assoc_of_le h, add_comm]
    rw [sum_range_choose]
    rw [mul_comm]

-- 题1
theorem sum_two_pow_mul_choose {n : ℕ} : ∑ k in range (n+1), 2^k * choose n k = 3^n := by
  have : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * ↑(Nat.choose n m) = (2 + 1) ^ n :=
    (add_pow _ _ _).symm
  simp at this
  assumption

-- 题4
theorem alternating_sum_mul_mul_choose {n : ℕ} (h0 : 1 < n): ∑ k in range (n+1), (-1 : ℤ)^k * k * choose n k = 0 := by
  rw [range_eq_Ico]
  have hzero_lt_n : 0 < n+1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  simp [mul_assoc]
  have h1 : ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * (k * choose n k)
    = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * (n * choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    rw [←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq' h0 (mem_Ico.mp hy).left]
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]


-- 题5
theorem sum_div_succ_mul_choose_mul {n k : ℕ} (x : ℕ) (h : 0 < x): ∑ k in range (n+1), (((1/(k+1)) : ℝ) * choose n k * ((x^k) : ℝ))
                            = ((((1+x)^(n+1) : ℝ) - 1)) / ((n+1)*x):= by
  have h0 : ∑ k in range (n+1), (((1/(k+1)) : ℝ) * choose n k * ((x^k) : ℝ))
    = ∑ k in range (n+1), ((1/(n+1)) * choose (n+1) (k+1) * ((x^k) : ℝ)) := by
    refine' sum_congr rfl fun y hy => _
    rw [succ_mul_choose_eq'']
  rw [h0]
  simp_rw [mul_assoc]
  rw [←mul_sum]
  have h1 : 1 / (n + 1) * ∑ k in range (n + 1), Nat.choose (n + 1) (k + 1) * ((x ^ k) : ℝ)
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
            have : x ≠ 0 := by linarith
            exact Iff.mpr cast_ne_zero this
  rw [h1, div_eq_mul_one_div ((((1 + x) ^ (n + 1)):ℝ) - 1), mul_comm ((((1 + x) ^ (n + 1)):ℝ) - 1)]
  congr 1
  rw [range_eq_Ico]
  have h2 : ∑ k in Ico 0 (n + 1), (Nat.choose (n + 1) (k + 1)) * ((x ^ (k + 1)) : ℝ)
          = ∑ l in Ico (0 + 1) (n + 1 + 1), (Nat.choose (n + 1) l) * ((x ^ l) : ℝ) := by
          let f : ℕ → ℝ := fun k => ↑(Nat.choose (n + 1) k) * ↑(x ^ k)
          change ∑ k in Ico 0 (n + 1), f (k+1) = ∑ l in Ico (0+1) (n + 1 + 1), f l
          rw [sum_Ico_add']
  rw [h2]
  simp
  have h3 : ∑ k in Ico 1 (n + 1 + 1), (Nat.choose (n + 1) k) * ((x : ℝ) ^ k )
            = ∑ k in Ico 0 (n + 1 + 1), (Nat.choose (n + 1) k) * ((x : ℝ) ^ k) - 1 := by
            have : 0 < n + 2 := by exact succ_pos (n + 1)
            rw [sum_eq_sum_Ico_succ_bot this]
            simp
  rw [h3]
  simp [add_comm]
  rw [add_pow (x:ℝ) 1 (n+1)]
  rw [add_comm]
  refine' sum_congr rfl fun y hy => _
  simp [mul_comm]

-- 题6
theorem odd_sum_range_choose (n : ℕ) (h0 : n ≠ 0) : ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) else 0) = 2^(n-1) :=
  mul_right_injective₀ two_ne_zero <|
    calc
      2 * (∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) else 0))
        = ∑ k in range (n+1), (if k % 2 = 1 then 2 * ((choose n k) : ℤ) else 0) := by
          {
            rw [mul_sum]
            refine' sum_congr rfl fun y hy => _
            rw [ite_mul_zero_right (y % 2 = 1) 2 ((Nat.choose n y) : ℤ)]
          }
      _ = ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) + ((choose n k) : ℤ) else ((choose n k) : ℤ) - ((choose n k) : ℤ)) := by
          {
            refine' sum_congr rfl fun y hy => _
            congr 1
            rw [two_mul]
            simp
          }
      _ = ∑ k in range (n+1), ((if k % 2 = 1 then choose n k - (-1)^k * choose n k else choose n k - (-1)^k * choose n k) : ℤ) := by
          {
            refine' sum_congr rfl fun y fy => _
            split_ifs with h'
            . rw [←Nat.odd_iff] at h'
              rw [Odd.neg_one_pow h']
              rw [neg_one_mul]
              rw [sub_neg_eq_add]
            . rw [Nat.mod_two_ne_one, ←Nat.even_iff] at h'
              rw [Even.neg_one_pow h']
              simp
          }
      _ = ∑ k in range (n+1), ((choose n k - (-1)^k * choose n k) : ℤ) := by simp
      _ = 2^n := by
          {
            rw [sum_sub_distrib]
            rw [Int.alternating_sum_range_choose_of_ne h0]
            simp
            have := (add_pow (1:ℤ) 1 n).symm
            simpa [one_add_one_eq_two] using this
          }
      _ = 2^(n - 1 + 1) := by
          {
            have hone_le_one : 1 ≤ 1 := by linarith
            have hone_le_n : 1 ≤ n := by exact Iff.mpr one_le_iff_ne_zero h0
            rw [←tsub_tsub_assoc hone_le_n hone_le_one]
            simp
          }
      _ = 2 * 2^(n-1) := by
          {
            rw [add_one]
            rw [_root_.pow_succ 2 (n-1)]
          }


-- 题 10
theorem sum_range_choose_halfway_of_lt (n : ℕ) (h0 : 0 < n): ∑ k in range n, choose (2 * n - 1) k = 2^(2 * n - 2) :=
  have : ∑ k in range n, choose (2 * n - 1) k = ∑ k in Ico n (2 * n), choose (2 * n - 1) k := by
    have h1 : ∑ k in range n, choose (2 * n - 1) k
            = ∑ k in range n, choose (2 * n - 1) (2 * n - 1 - k) := by
      refine' sum_congr rfl fun y hy => _
      have : y ≤ 2 * n - 1 := by
        have h1 : y < n := mem_range.1 hy
        refine le_pred_of_lt ?h
        have h2 : n < 2 * n := by exact lt_two_mul_self h0
        simp
        exact Nat.lt_trans h1 h2
      rw [choose_symm this]
    rw [h1, range_eq_Ico]
    have : n ≤ 2 * n - 1 + 1 := by
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
      linarith
    rw [sum_Ico_reflect _ _ this]
    have h2 : 2 * n - 1 + 1 - n = n := by
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
      rw [two_mul]
      simp
    have h3 : 2 * n - 1 + 1 - 0 = 2 * n := by
      simp
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
    rw [h2, h3]
  mul_right_injective₀ two_ne_zero <|
    calc
      2 * (∑ k in range n, choose (2 * n - 1) k)
        = ∑ k in range n, choose (2 * n - 1) k + ∑ k in Ico n (2 * n), choose (2 * n - 1) k := by rw [two_mul, this]
      _ =  ∑ k in range (2 * n), choose (2 * n - 1) k := sum_range_add_sum_Ico _ (by linarith)
      _ = ∑ k in range (2 * n - 1 + 1), choose (2 * n - 1) k := by
          {
            have : 1 ≤ 2 * n := by linarith
            rw [Nat.sub_add_cancel this]
          }
      _ = 2^(2 * n - 1) := sum_range_choose (2 * n - 1)
      _ = 2^(2 * n - 2 + 1)  := by
          {
            congr 1
            rw [←tsub_tsub_assoc]
            linarith
            linarith
          }
      _ = 2 * 2^(2 * n - 2)  := by rw [Nat.pow_succ, mul_comm]


-- 题11：条件1
theorem sum_range_succ_eq_sum_range : ∑ k in range (n+1), (k * choose (2 * n) k) = (2 * n) * ∑ k in range n, (choose (2*n - 1) k) := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]
  simp
  have h1: ∑ k in Ico 1 (n+1), k * (choose (2 * n) k) = ∑ k in Ico 1 (n+1), (2 * n) * (choose (2*n - 1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[choose_mul_eq_mul_sub' hkn hsk]
  rw[h1]
  rw[mul_sum] -- 提出 2 * n + 1
  rw[sum_Ico_eq_sum_range] -- 代换 l = k - 1
  simp --∑ k in range (n+1), (k * choose (2 * n) k) = (2 * n) * ∑ k in range n, (choose (2*n - 1) k)


-- 题11
theorem sum_mul_choose_eq_mul_two_pow (h : 0 < n) : ∑ k in range (n+1), (k * choose (2 * n) k) = n * 2 ^ (2 * n - 1) := by
  rw[sum_range_succ_eq_sum_range]
  rw[sum_range_choose_halfway_of_lt n h] --(2 * n) * 2 ^ (2 * n - 2)
  rw[mul_comm 2 n, mul_assoc]
  congr 1
  rw[mul_comm]
  -- have h1 : 2 ^ (n * 2 - 1) = 2 ^ (n * 2 - 2 + 1) := by
  rw[← Nat.pow_succ]
  congr 1
  rw[Nat.succ_eq_add_one]
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  rw[h21]

-- 题16
theorem sum_mul_choose_eq_mul_choose (n : ℕ) (h : 1 ≤ n): ∑ k in range (n+1), k * choose (2*n) (n-k) = ((n * choose (2*n-1) n) : ℝ) := by
  calc
    ∑ k in range (n+1), k * choose (2*n) (n-k)
      = ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n) (n-k) := by
      {
        rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n) (n - x)]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
        congr 1
        norm_num
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n) (n-k) := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc]
      }
    _ = (-1 : ℝ) * ∑ k in range (n + 1), (↑(n + 1 - 1 - k) - ↑n) * ↑(Nat.choose (2 * n) (n + 1 - 1 - k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        rw [mem_range] at hk
        rw [←cast_sub]
        simp
        linarith
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), (k-(n:ℝ)) * choose (2*n) k := by
      {
        congr 1
        rw [sum_range_reflect (fun x => (x-(n:ℝ)) * choose (2*n) x) (n+1)]
      }
    _ = ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n) k := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [←neg_one_mul (k-(n:ℝ))]
        rw [mul_assoc]
      }
    _ = ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n) k := by
      {
        refine' sum_congr rfl fun k hk => _
        congr 1
        exact neg_sub (k:ℝ) (n:ℝ)
      }
    _ = ∑ k in range (n+1), ((n:ℝ) * choose (2*n) k - k * choose (2*n) k) := by
      {
        refine' sum_congr rfl fun k hk => _
        rw [sub_mul]
      }
    _ = ∑ k in range (n+1), (n:ℝ) * choose (2*n) k - ∑ k in range (n+1), k * choose (2*n) k := by
      {
        rw [sum_sub_distrib]
        congr 1
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n) x]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (∑ k in range (n+1), n * choose (2*n) k) - (∑ k in range (n+1), k * choose (2*n) k) := by -- 这里是在变换数据类型
      {
        rw [cast_sum (range (n+1)) fun x => n * Nat.choose (2 * n) x]
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = ∑ k in range (n+1), n * choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 1
        have : 0 < n := by linarith
        rw [sum_mul_choose_eq_mul_two_pow this]
      }
    _ = n * ∑ k in range (n+1), choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 1
        rw [←cast_mul,mul_sum]
      }
    _ = n * ((2^(2*n-1)) + (((1/2):ℝ) * choose (2*n) n)) - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 2
        rw [ex2 n]
      }
    _ =  n * (((1/2):ℝ) * choose (2*n) n) := by
      {
        rw [mul_add]
        rw [add_comm]
        simp
      }
    _ = n * ((1/2):ℝ) * ((2*n)! / ((n)! * (2*n -n)!)) := by
      {
        rw [choose_eq_factorial_div_factorial]
        rw [←mul_assoc,←cast_mul, ←cast_div]
        rw [two_mul, Nat.add_sub_cancel]
        exact factorial_mul_factorial_dvd_factorial_add n n
        rw [two_mul, Nat.add_sub_cancel]
        rw [cast_ne_zero]
        exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero n)
        linarith
      }
    _ = n * ((1/2):ℝ) * (((2:ℕ)*n-1+1)*((2:ℕ)*n-1)! / (n ! * n !)) := by
      {
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

      }
    _ = n * (((1/2):ℝ) * ((2:ℕ)*n)*((2:ℕ)*n-1)! / (n ! * n !)) := by
      {
        rw [sub_add_cancel, mul_assoc]
        congr 1
        rw [←cast_mul,←cast_mul,←cast_mul,←mul_div_assoc]
        congr 1
        rw [cast_mul,←mul_assoc]
      }
    _ = n * (n * ((2:ℕ)*n-1)! / (n ! * n !)) := by simp
    _ = n * (n * ((2:ℕ)*n-1)! / (n ! * (n * (n-1) !))) := by
      {
        congr 3
        have : n = n-1+1 := by rw [Nat.sub_add_cancel h]
        rw [this,Nat.factorial_succ (n-1)]
        simp [cast_mul]
      }
    _ = n * (((2:ℕ)*n-1)! / (n ! * (n-1) !)) := by
      {
        congr 1
        rw [mul_comm, mul_div_assoc]
        rw [←cast_mul, ←cast_mul, mul_comm (n !) _, cast_mul]
        rw [div_mul_eq_div_div,cast_mul,div_mul_eq_div_div]
        rw [div_self, ←div_mul_eq_div_div, mul_one_div, mul_comm ((n-1)! : ℝ) _]
        rw [cast_ne_zero]
        linarith
      }
    _ = n * choose (2*n-1) n := by
      {
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
      }


-- sum_mul_choose_eq_two_pow' 的替换条件4
theorem one_div_two_mul_choose_sub_succ_mul_choose (n : ℕ) (h : 1 ≤ n) : ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n = -(2*n+1) * choose (2*n-1) n := by
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


theorem sum_mul_choose_eq_two_pow' (n : ℕ) (h : 1 ≤ n) :((∑ k in range (n+1), k * choose (2*n+1) k):ℝ)
                        = ((n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n) : ℝ) :=
  have h_gt_zero : 0 < n + 1 := by linarith
  have h1 : ∑ k in Ico 1 (n + 1), k * choose (2*n) k = ∑ k in range (n+1), k * choose (2*n) k := by
    rw [range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
    simp
  have h2 : ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1)
          = ∑ k in range (n+1), (k+1) * choose (2*n) k - (n+1) * choose (2*n) n := by
    rw [sum_Ico_eq_sum_range, sum_range_succ]
    simp [add_comm]
  have h3 : ∑ k in range (n+1), (k+1) * choose (2*n) k
          = ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k := by
    rw [←sum_add_distrib]
    refine' sum_congr rfl fun k hk => _
    rw [add_mul]
    simp
  calc
    ((∑ k in range (n+1), k * choose (2*n+1) k) : ℝ) = ∑ k in Ico 1 (n + 1), k * choose (2*n+1) k := by
      {
        rw [range_eq_Ico]
        rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
        simp
      }
    _ = ∑ k in Ico 1 (n + 1), k * (choose (2*n) k + choose (2*n) (k-1)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        have : k = k-1+1 := by
          rw [Nat.sub_add_cancel]
          rw [mem_Ico] at hk
          exact hk.left
        rw [this, choose_succ_succ' (2*n) (k-1), ←this, add_comm]
      }
    _ = ∑ k in Ico 1 (n + 1), (k * choose (2*n) k + k * choose (2*n) (k-1)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [mul_add]
      }
    _ = ∑ k in Ico 1 (n + 1), k * choose (2*n) k + ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1) := by
      {
        rw [←cast_add]
        congr 1
        rw [sum_add_distrib]
      }
    _ = ∑ k in range (n+1), k * choose (2*n) k
      + ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k - (n+(1:ℕ)) * choose (2*n) n := by
      {
        rw [h1, h2]
        rw [cast_sub, ←add_sub_assoc]
        congr 1
        rw [add_assoc]
        congr 1
        rw [h3, cast_add]
        rw [←cast_add, ←cast_mul]
        rw [sum_range_succ]
        have : 0 ≤ ∑ k in range n, (k + 1) * Nat.choose (2 * n) k := by
          exact Nat.zero_le (∑ k in range n, (k + 1) * Nat.choose (2 * n) k)
        linarith
      }
    _ = 2*(n:ℝ)*2^(2*n-1) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
      {
        have : 0 < n := by linarith
        rw [←two_mul, sum_mul_choose_eq_mul_two_pow this, ex2]
        congr 1
        rw [cast_mul, ←mul_assoc, ←add_assoc]
        congr 3
        rw [cast_pow]
        congr 1
        congr 2
        rw [cast_one]
      }
    _ = n*2^(2*n) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
      {
        congr 3
        rw [←cast_comm, mul_assoc]
        congr 1
        have : 2*n = 2*n-1+1 := by
          have : 1 ≤ 2*n := by rw [two_mul]; linarith
          rw [Nat.sub_add_cancel this]
        rw [this, pow_add, ←this, pow_one, mul_comm]
      }
    _ = n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n := by
      {
        rw [add_sub_assoc]
        rw [one_div_two_mul_choose_sub_succ_mul_choose n h]
        congr 1
        rw [←neg_one_mul ((2 * n + 1) * (Nat.choose (2 * n - 1) n) : ℝ)]
        rw [←mul_assoc, neg_one_mul]
      }


-- 题17
theorem sum_mul_choose_eq_pow_mul_sub (n : ℕ) (h : 1 ≤ n) : ∑ k in range (n+1), k * choose (2*n+1) (n-k) = (((2*n+1) * choose (2*n-1) n - 2^(2*n-1)) : ℝ) :=
  calc
    ∑ k in range (n+1), k * choose (2*n+1) (n-k)
      = ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n+1) (n-k) := by
      {
        rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n + 1) (n - x)]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
        congr 1
        norm_num
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n+1) (n-k) := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc]
      }
    _ = (-1 : ℝ) * ∑ k in range (n + 1), (↑(n + 1 - 1 - k) - ↑n) * ↑(Nat.choose (2 * n + 1) (n + 1 - 1 - k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        rw [mem_range] at hk
        rw [←cast_sub]
        simp
        linarith
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), (k-(n:ℝ)) * choose (2*n+1) k := by
      {
        congr 1
        rw [sum_range_reflect (fun x => (x-(n:ℝ)) * choose (2*n+1) x) (n+1)]
      }
    _ = ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n+1) k := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [←neg_one_mul (k-(n:ℝ))]
        rw [mul_assoc]
      }
    _ = ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n+1) k := by
      {
        refine' sum_congr rfl fun k hk => _
        congr 1
        exact neg_sub (k:ℝ) (n:ℝ)
      }
    _ = ∑ k in range (n+1), ((n:ℝ) * choose (2*n+1) k - k * choose (2*n+1) k) := by
      {
        refine' sum_congr rfl fun k hk => _
        rw [sub_mul]
      }
    _ = ∑ k in range (n+1), (n:ℝ) * choose (2*n+1) k - ∑ k in range (n+1), k * choose (2*n+1) k := by
      {
        rw [sum_sub_distrib]
        congr 1
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n + 1) x]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (∑ k in range (n+1), n * choose (2*n+1) k) - (∑ k in range (n+1), k * choose (2*n+1) k) := by -- 这里是在变换数据类型
      {
        rw [cast_sum (range (n+1)) fun x => n * Nat.choose (2 * n + 1) x]
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (n*2^(2*n)) - ((n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n) : ℝ) := by
      {
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n + 1) x]
        simp_rw [cast_mul]
        rw [sum_mul_choose_eq_two_pow' n h]
        congr 1
        rw [←mul_sum, sum_range_choose_halfway n]
        have : 4 = 2^2 := by exact rfl
        rw [this, ←pow_mul, cast_mul, cast_pow]
        congr 1
      }
    _ = (2*n+1) * choose (2*n-1) n - 2^(2*n-1) := by
      {
        rw [←add_sub, ←sub_sub, sub_self, ←sub_add, add_comm]
        congr 1
        simp
      }



-- 题20
theorem choose_mul_add_pow (n l : ℕ) (x : ℝ) (h : l ≤ n): ∑ k in Ico l (n+1), (choose n k) * (choose k l) * x^k * (1 - x)^(n - k)
                                        = (choose n l) * x^l :=
  calc
    ∑ k in Ico l (n+1), (choose n k) * (choose k l) * x^k * (1 - x)^(n - k)
      = ∑ k in Ico l (n+1), (choose n l) * (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k) := by
      {
        refine' sum_congr rfl fun k hk => _
        congr 2
        rw [mem_Ico] at hk
        rw [←cast_mul,←cast_mul]
        rw [choose_mul]
        linarith
        exact hk.left
      }
    _ = (choose n l) * ∑ k in Ico l (n+1), (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k) := by
      {
        rw [mul_sum]
        simp [mul_assoc]
      }
    _ = (choose n l) * ∑ k in range (n+1-l), (choose (n-l) k) * x^(l+k) * (1 - x)^(n-(l+k)) := by
      {
        rw [sum_Ico_eq_sum_range]
        simp
      }
    _ = (choose n l) * ∑ k in range (n+1-l), x^(l+k) * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        rw [mul_comm]
      }
    _ = (choose n l) * ∑ k in range (n+1-l), x^l * x^k * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [pow_add]
      }
    _ = (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
      {
        rw [mul_assoc]
        repeat rw [mul_sum]
        simp [mul_assoc]
      }
    _ = (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^((n-l)-k) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 2
        exact sub_add_eq n l k
      }
    _ = (choose n l) * x^l * ∑ k in range (n-l+1), x^k * (1 - x)^((n-l)-k) * (choose (n-l) k) := by
      {
        have : n+1-l = n-l+1 := by rw [succ_sub h]
        rw [this]
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc,mul_assoc]
        congr 1
        rw [mul_comm]
      }
    _ = (choose n l) * x^l * (x + (1-x))^(n-l) := by rw [←add_pow (x:ℝ) (1-x) (n-l)]
    _ = (choose n l) * x^l * (1)^(n-l) := by
      {
        rw [add_sub]
        congr 2
        rw [add_sub_right_comm x 1 x, sub_self]
        simp
      }
    _ = (choose n l) * x^l := by
      {
        rw [one_pow]
        simp
      }
