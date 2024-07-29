import AdaLean.sum_mul_congr
import AdaLean.mul_choose_two_pow
import AdaLean.mul_choose_eq_mul_choose
import AdaLean.icc_eq_ico

open Nat

open Finset

open BigOperators


theorem sum_mul_choose_eq_mul_two_pow_sub
  (n : ℕ)
  (h₀ : 0 < n) :
  ∑ k in Finset.Icc 1 n, (k * Nat.choose n k) = n * 2^(n - 1) := by
  rw [icc_eq_ico]
  rw[← range_eq_Ico]
  rw[mul_choose_eq_mul_choose]
  rw[sum_mul_congr]
  rw[mul_choose_two_pow]
  linarith
  linarith
  linarith
