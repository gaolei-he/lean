import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.mini_Theorem.one_div_two_mul_choose_sub_succ_mul_choose


open Nat
open Finset
open BigOperators



theorem simp_one_div_two_mul_choose {n : ℕ} (h : 1 ≤ n) : n*2^(2*n) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n
                = n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n := by
  rw [add_sub_assoc]
  rw [one_div_two_mul_choose_sub_succ_mul_choose n h]
  congr 1
  rw [←neg_one_mul ((2 * n + 1) * (Nat.choose (2 * n - 1) n) : ℝ)]
  rw [←mul_assoc, neg_one_mul]
