import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

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
