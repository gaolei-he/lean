import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

theorem choose_mul_eq_mul_sub_div {n k: ℕ} :
 (((1/(k+1)) : ℝ) * choose n k) = (1/(n+1)) * choose (n+1) (k+1) := by
  have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
  have h2 : (n + 1) * (k + 1) * ((1 / (n+1)) : ℝ) * (Nat.choose (n + 1) (k + 1))
      = (k + 1) * ((n + 1) * (1 / (n+1)) * (Nat.choose (n + 1) (k + 1))) := by
      rw [←mul_assoc]
      congr 1
      rw [←mul_assoc]
      congr 1
      rw [mul_comm]
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption


theorem choose_mul_eq_mul_sub_div_from_0_to_0(n k : ℕ)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_2(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_3(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_4(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_5(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_6(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_2_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_3_to_3(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  apply gol

theorem choose_mul_eq_mul_sub_div_from_3_to_4(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  apply gol

theorem choose_mul_eq_mul_sub_div_from_3_to_5(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  apply gol

theorem choose_mul_eq_mul_sub_div_from_3_to_6(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_3_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem choose_mul_eq_mul_sub_div_from_3_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem choose_mul_eq_mul_sub_div_from_3_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  apply gol

theorem choose_mul_eq_mul_sub_div_from_3_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_3_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    rw [h2]
    rw [←mul_assoc]
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_4_to_4(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  apply gol

theorem choose_mul_eq_mul_sub_div_from_4_to_5(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  apply gol

theorem choose_mul_eq_mul_sub_div_from_4_to_6(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_4_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem choose_mul_eq_mul_sub_div_from_4_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem choose_mul_eq_mul_sub_div_from_4_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  apply gol

theorem choose_mul_eq_mul_sub_div_from_4_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_4_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h4 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_5_to_5(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  apply gol

theorem choose_mul_eq_mul_sub_div_from_5_to_6(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_5_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem choose_mul_eq_mul_sub_div_from_5_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem choose_mul_eq_mul_sub_div_from_5_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  apply gol

theorem choose_mul_eq_mul_sub_div_from_5_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_5_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h5 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
          = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_6_to_6(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [h4, h5] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_6_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem choose_mul_eq_mul_sub_div_from_6_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem choose_mul_eq_mul_sub_div_from_6_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  apply gol

theorem choose_mul_eq_mul_sub_div_from_6_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_6_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [h4, h5] at h
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_7_to_7(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  apply gol

theorem choose_mul_eq_mul_sub_div_from_7_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem choose_mul_eq_mul_sub_div_from_7_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  apply gol

theorem choose_mul_eq_mul_sub_div_from_7_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_7_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h6 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_8_to_8(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  apply gol

theorem choose_mul_eq_mul_sub_div_from_8_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  apply gol

theorem choose_mul_eq_mul_sub_div_from_8_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_8_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h7 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_9_to_9(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(h7 : ↑k + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  apply gol

theorem choose_mul_eq_mul_sub_div_from_9_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(h7 : ↑k + 1 ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_9_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(h7 : ↑k + 1 ≠ 0) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  have h8 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h6 h7
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_10_to_10(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(h7 : ↑k + 1 ≠ 0)(h8 : (↑n + 1) * (↑k + 1) ≠ 0)(gol:  1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [mul_right_inj' h8] at h
  apply gol

theorem choose_mul_eq_mul_sub_div_from_10_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h :  (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(h7 : ↑k + 1 ≠ 0)(h8 : (↑n + 1) * (↑k + 1) ≠ 0) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  rw [mul_right_inj' h8] at h
  assumption

theorem choose_mul_eq_mul_sub_div_from_11_to_11(n k : ℕ)(h1 : ↑k + 1 ≠ 0)(h2 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑k + 1) * ((↑n + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1))))(h3 : ↑n + 1 ≠ 0)(h : 1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)))(h4 : (↑n + 1) * (↑k + 1) * (1 / (↑k + 1)) * ↑(choose n k) = (↑n + 1) * (↑k + 1) * (1 / (↑k + 1) * ↑(choose n k)))(h5 :  (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(choose (n + 1) (k + 1)) =    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(choose (n + 1) (k + 1))))(h6 : ↑n + 1 ≠ 0)(h7 : ↑k + 1 ≠ 0)(h8 : (↑n + 1) * (↑k + 1) ≠ 0) :
   1 / (↑k + 1) * ↑(choose n k) = 1 / (↑n + 1) * ↑(choose (n + 1) (k + 1)) := by
  assumption

