import Mathlib.Data.Nat.Choose.Sum
import Theorem.mini_separate.succ_mul_choose_eq''

open Nat

open Finset

open BigOperators


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
            have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
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
