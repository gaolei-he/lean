import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Finset

open BigOperators

theorem Ico_pow_choose : ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x + 1) * (1 / x) * (Nat.choose (n + 1) x) = (∑ k in range (n + 1), 1 / (k + 1))  := by sorry  --example8


theorem Ico_pow_choose_from_0_to_0(n : ℕ) :
   ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x + 1) * (1 / ↑x) * ↑(Nat.choose (n + 1) x) = ↑(∑ k in range (n + 1), 1 / (k + 1)) := by
  sorry

