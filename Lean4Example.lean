import Lean4Repl
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

open Nat
open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_comm b c]

theorem sum_neg_pow_mul_mul (t : ℕ → ℕ → ℕ → ℝ := fun m n k => (-1 : ℝ)^k * (choose n k : ℝ) * (m / (m+k))):
  ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k * (m / (m+k)) + (-1 : ℝ)^k * choose (n-1) (k-1) * (m / (m+k))) : ℝ):= by
    congr 1
    ext1 k
    rw [mul_add]
    rw [add_mul]



-- example (m : Nat):choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m := by
--     rw [choose_eq_factorial_div_factorial (Nat.sub_le _ _)]
--     rw[tsub_tsub_cancel_of_le hk, mul_comm]
--     apply choose_symm_of_eq_add
--     rw [add_comm m 1]
--     rw [add_assoc 1 m m]
--     rw [add_comm (2 * m) 1]
--     rw [two_mul m]
