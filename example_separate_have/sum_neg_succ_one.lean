import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div

open Nat
open Finset
open BigOperators

theorem sum_neg_succ_one : ∑ k in range (n + 1), ((-1:ℝ)^k) * (choose (n+1) (k+1)) = 1 := by sorry
