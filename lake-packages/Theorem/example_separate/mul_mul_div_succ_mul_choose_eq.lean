import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat


theorem mul_mul_div_succ_mul_choose_eq{n k: ℕ} :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
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


theorem mul_mul_div_succ_mul_choose_eq_from_0_to_0(n k : ℕ)(gol:  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) :
   (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_0_to_1(n k : ℕ)(gol:  ↑(choose n k) * ((↑n + 1) * ((↑k + 1) * (1 / (↑k + 1)))) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) :
   (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
  rw [mul_comm, mul_assoc]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_0_to_2(n k : ℕ)(gol:  ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) :
   (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
  rw [mul_comm, mul_assoc]
  rw [mul_one_div_cancel h1]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_1_to_1(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(gol:  ↑(choose n k) * ((↑n + 1) * ((↑k + 1) * (1 / (↑k + 1)))) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) :
   (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [mul_comm, mul_assoc]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_1_to_2(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(gol:  ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) :
   (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [mul_comm, mul_assoc]
  rw [mul_one_div_cancel h1]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_2_to_2(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(gol:  ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) :
   ↑(choose n k) * ((↑n + 1) * ((↑k + 1) * (1 / (↑k + 1)))) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [mul_one_div_cancel h1]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_4_to_4(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * ((↑n + 1) * 1) = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [h2]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_4_to_5(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [h2]
  rw [←mul_assoc]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_4_to_6(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [h2]
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_4_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * (1 * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [h2]
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_4_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) = (↑k + 1) * ↑(choose (n + 1) (k + 1))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [h2]
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_4_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑((n + 1) * choose n k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [h2]
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_4_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose (succ n) (succ k) * succ k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [h2]
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_4_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) := by
  rw [h2]
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  simp [mul_comm]

theorem mul_mul_div_succ_mul_choose_eq_from_5_to_5(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [←mul_assoc]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_5_to_6(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_5_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * (1 * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_5_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) = (↑k + 1) * ↑(choose (n + 1) (k + 1))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_5_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑((n + 1) * choose n k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_5_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose (succ n) (succ k) * succ k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_5_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * ((↑n + 1) * 1) = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [←mul_assoc]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  simp [mul_comm]

theorem mul_mul_div_succ_mul_choose_eq_from_6_to_6(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_6_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * (1 * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_6_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose n k) * (↑n + 1) = (↑k + 1) * ↑(choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_6_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑((n + 1) * choose n k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_6_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  ↑(choose (succ n) (succ k) * succ k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_6_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  simp [mul_comm]

theorem mul_mul_div_succ_mul_choose_eq_from_7_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * (1 * ↑(choose (n + 1) (k + 1)))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [mul_one_div_cancel h3]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_7_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑(choose n k) * (↑n + 1) = (↑k + 1) * ↑(choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [mul_one_div_cancel h3]
  simp
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_7_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑((n + 1) * choose n k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_7_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑(choose (succ n) (succ k) * succ k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_7_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) := by
  rw [mul_one_div_cancel h3]
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  simp [mul_comm]

theorem mul_mul_div_succ_mul_choose_eq_from_8_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑(choose n k) * (↑n + 1) = (↑k + 1) * ↑(choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * (1 * ↑(choose (n + 1) (k + 1))) := by
  simp
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_8_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑((n + 1) * choose n k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * (1 * ↑(choose (n + 1) (k + 1))) := by
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_8_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑(choose (succ n) (succ k) * succ k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * (1 * ↑(choose (n + 1) (k + 1))) := by
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_8_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0) :
   ↑(choose n k) * (↑n + 1) * 1 = (↑k + 1) * (1 * ↑(choose (n + 1) (k + 1))) := by
  simp
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  simp [mul_comm]

theorem mul_mul_div_succ_mul_choose_eq_from_9_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑((n + 1) * choose n k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) = (↑k + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_9_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑(choose (succ n) (succ k) * succ k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑(choose n k) * (↑n + 1) = (↑k + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_9_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0) :
   ↑(choose n k) * (↑n + 1) = (↑k + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
  rw [succ_mul_choose_eq]
  simp [mul_comm]

theorem mul_mul_div_succ_mul_choose_eq_from_10_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  ↑(choose (succ n) (succ k) * succ k) = ↑((k + 1) * choose (n + 1) (k + 1))) :
   ↑((n + 1) * choose n k) = ↑((k + 1) * choose (n + 1) (k + 1)) := by
  rw [succ_mul_choose_eq]
  apply gol

theorem mul_mul_div_succ_mul_choose_eq_from_10_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0) :
   ↑((n + 1) * choose n k) = ↑((k + 1) * choose (n + 1) (k + 1)) := by
  rw [succ_mul_choose_eq]
  simp [mul_comm]

theorem mul_mul_div_succ_mul_choose_eq_from_11_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0) :
   ↑(choose (succ n) (succ k) * succ k) = ↑((k + 1) * choose (n + 1) (k + 1)) := by
  simp [mul_comm]

