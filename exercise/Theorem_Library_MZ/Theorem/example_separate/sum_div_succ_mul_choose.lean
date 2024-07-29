import Mathlib.Data.Nat.Choose.Sum
import Theorem.mini_separate.succ_mul_choose_eq''

open Nat

open Finset

open BigOperators

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


theorem sum_div_succ_mul_choose_from_1_to_1(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  1 / (↑n + 1) * ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = 1 / (↑n + 1) * (2 ^ (n + 1) - 1)) :
   ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) = 1 / (↑n + 1) * (2 ^ (n + 1) - 1) := by
  rw [this, ←mul_sum]
  apply gol

theorem sum_div_succ_mul_choose_from_3_to_3(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = (1 + 1) ^ (n + 1) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = 2 ^ (n + 1) - 1 := by
  rw [←one_add_one_eq_two]
  apply gol

theorem sum_div_succ_mul_choose_from_3_to_4(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ m in range (n + 1 + 1), 1 ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = 2 ^ (n + 1) - 1 := by
  rw [←one_add_one_eq_two]
  rw [add_pow 1 1 (n+1)]
  apply gol

theorem sum_div_succ_mul_choose_from_3_to_5(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 1 + 1), ↑(Nat.choose (n + 1) x) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = 2 ^ (n + 1) - 1 := by
  rw [←one_add_one_eq_two]
  rw [add_pow 1 1 (n+1)]
  simp
  apply gol

theorem sum_div_succ_mul_choose_from_3_to_6(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) + ↑(Nat.choose (n + 1) 0) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = 2 ^ (n + 1) - 1 := by
  rw [←one_add_one_eq_two]
  rw [add_pow 1 1 (n+1)]
  simp
  rw [sum_range_succ' _ (n + 1)]
  apply gol

theorem sum_div_succ_mul_choose_from_3_to_7(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1))) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = 2 ^ (n + 1) - 1 := by
  rw [←one_add_one_eq_two]
  rw [add_pow 1 1 (n+1)]
  simp
  rw [sum_range_succ' _ (n + 1)]
  simp

theorem sum_div_succ_mul_choose_from_4_to_4(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ m in range (n + 1 + 1), 1 ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = (1 + 1) ^ (n + 1) - 1 := by
  rw [add_pow 1 1 (n+1)]
  apply gol

theorem sum_div_succ_mul_choose_from_4_to_5(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 1 + 1), ↑(Nat.choose (n + 1) x) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = (1 + 1) ^ (n + 1) - 1 := by
  rw [add_pow 1 1 (n+1)]
  simp
  apply gol

theorem sum_div_succ_mul_choose_from_4_to_6(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) + ↑(Nat.choose (n + 1) 0) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = (1 + 1) ^ (n + 1) - 1 := by
  rw [add_pow 1 1 (n+1)]
  simp
  rw [sum_range_succ' _ (n + 1)]
  apply gol

theorem sum_div_succ_mul_choose_from_4_to_7(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1))) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = (1 + 1) ^ (n + 1) - 1 := by
  rw [add_pow 1 1 (n+1)]
  simp
  rw [sum_range_succ' _ (n + 1)]
  simp

theorem sum_div_succ_mul_choose_from_5_to_5(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 1 + 1), ↑(Nat.choose (n + 1) x) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ m in range (n + 1 + 1), 1 ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m) - 1 := by
  simp
  apply gol

theorem sum_div_succ_mul_choose_from_5_to_6(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) + ↑(Nat.choose (n + 1) 0) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ m in range (n + 1 + 1), 1 ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m) - 1 := by
  simp
  rw [sum_range_succ' _ (n + 1)]
  apply gol

theorem sum_div_succ_mul_choose_from_5_to_7(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1))) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ m in range (n + 1 + 1), 1 ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m) - 1 := by
  simp
  rw [sum_range_succ' _ (n + 1)]
  simp

theorem sum_div_succ_mul_choose_from_6_to_6(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)))(gol:  ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) + ↑(Nat.choose (n + 1) 0) - 1) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 1 + 1), ↑(Nat.choose (n + 1) x) - 1 := by
  rw [sum_range_succ' _ (n + 1)]
  apply gol

theorem sum_div_succ_mul_choose_from_6_to_7(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1))) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 1 + 1), ↑(Nat.choose (n + 1) x) - 1 := by
  rw [sum_range_succ' _ (n + 1)]
  simp

theorem sum_div_succ_mul_choose_from_7_to_7(n k : ℕ)(this :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1))) :
   ∑ x in range (n + 1), ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) + ↑(Nat.choose (n + 1) 0) - 1 := by
  simp

