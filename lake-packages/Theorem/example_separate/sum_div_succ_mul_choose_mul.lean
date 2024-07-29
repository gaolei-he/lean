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
  have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
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


theorem sum_div_succ_mul_choose_mul_from_1_to_1(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) = (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  rw [h0]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_1_to_2(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  ∑ x_1 in range (n + 1), 1 / (↑n + 1) * (↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1)) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) = (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  rw [h0]
  simp_rw [mul_assoc]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_1_to_3(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) = (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  rw [h0]
  simp_rw [mul_assoc]
  rw [←mul_sum]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_1_to_4(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) = (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  rw [h0]
  simp_rw [mul_assoc]
  rw [←mul_sum]
  have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
  apply gol

theorem sum_div_succ_mul_choose_mul_from_2_to_2(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  ∑ x_1 in range (n + 1), 1 / (↑n + 1) * (↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1)) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  simp_rw [mul_assoc]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_2_to_3(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  simp_rw [mul_assoc]
  rw [←mul_sum]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_2_to_4(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  simp_rw [mul_assoc]
  rw [←mul_sum]
  have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
  apply gol

theorem sum_div_succ_mul_choose_mul_from_3_to_3(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ x_1 in range (n + 1), 1 / (↑n + 1) * (↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1)) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  rw [←mul_sum]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_3_to_4(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   ∑ x_1 in range (n + 1), 1 / (↑n + 1) * (↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1)) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  rw [←mul_sum]
  have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
  apply gol

theorem sum_div_succ_mul_choose_mul_from_4_to_4(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(gol:  1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x)) :
   1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
  apply gol

theorem sum_div_succ_mul_choose_mul_from_6_to_6(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(gol:  1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =
    1 / ((↑n + 1) * ↑x) * (↑((1 + x) ^ (n + 1)) - 1)) :
   1 / (↑n + 1) * ∑ x_1 in range (n + 1), ↑(Nat.choose (n + 1) (x_1 + 1)) * ↑(x ^ x_1) =
    (↑((1 + x) ^ (n + 1)) - 1) / ((↑n + 1) * ↑x) := by
  rw [h1, div_eq_mul_one_div ((((1 + x) ^ (n + 1)):ℝ) - 1), mul_comm ((((1 + x) ^ (n + 1)):ℝ) - 1)]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_8_to_8(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(gol:  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1) :
   ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  rw [range_eq_Ico]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_8_to_9(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(gol:  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1) :
   ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  rw [range_eq_Ico]
  have h2 : ∑ k in Ico 0 (n + 1), (Nat.choose (n + 1) (k + 1)) * ((x ^ (k + 1)) : ℝ)
          = ∑ l in Ico (0 + 1) (n + 1 + 1), (Nat.choose (n + 1) l) * ((x ^ l) : ℝ) := by
          let f : ℕ → ℝ := fun k => ↑(Nat.choose (n + 1) k) * ↑(x ^ k)
          change ∑ k in Ico 0 (n + 1), f (k+1) = ∑ l in Ico (0+1) (n + 1 + 1), f l
          rw [sum_Ico_add']
  apply gol

theorem sum_div_succ_mul_choose_mul_from_8_to_10(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(gol:  ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l) = ↑((1 + x) ^ (n + 1)) - 1) :
   ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  rw [range_eq_Ico]
  have h2 : ∑ k in Ico 0 (n + 1), (Nat.choose (n + 1) (k + 1)) * ((x ^ (k + 1)) : ℝ)
          = ∑ l in Ico (0 + 1) (n + 1 + 1), (Nat.choose (n + 1) l) * ((x ^ l) : ℝ) := by
          let f : ℕ → ℝ := fun k => ↑(Nat.choose (n + 1) k) * ↑(x ^ k)
          change ∑ k in Ico 0 (n + 1), f (k+1) = ∑ l in Ico (0+1) (n + 1 + 1), f l
          rw [sum_Ico_add']
  rw [h2]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_8_to_11(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(gol:  ∑ x_1 in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (1 + ↑x) ^ (n + 1) - 1) :
   ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  rw [range_eq_Ico]
  have h2 : ∑ k in Ico 0 (n + 1), (Nat.choose (n + 1) (k + 1)) * ((x ^ (k + 1)) : ℝ)
          = ∑ l in Ico (0 + 1) (n + 1 + 1), (Nat.choose (n + 1) l) * ((x ^ l) : ℝ) := by
          let f : ℕ → ℝ := fun k => ↑(Nat.choose (n + 1) k) * ↑(x ^ k)
          change ∑ k in Ico 0 (n + 1), f (k+1) = ∑ l in Ico (0+1) (n + 1 + 1), f l
          rw [sum_Ico_add']
  rw [h2]
  simp
  apply gol

theorem sum_div_succ_mul_choose_mul_from_9_to_9(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(gol:  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1) :
   ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  have h2 : ∑ k in Ico 0 (n + 1), (Nat.choose (n + 1) (k + 1)) * ((x ^ (k + 1)) : ℝ)
          = ∑ l in Ico (0 + 1) (n + 1 + 1), (Nat.choose (n + 1) l) * ((x ^ l) : ℝ) := by
          let f : ℕ → ℝ := fun k => ↑(Nat.choose (n + 1) k) * ↑(x ^ k)
          change ∑ k in Ico 0 (n + 1), f (k+1) = ∑ l in Ico (0+1) (n + 1 + 1), f l
          rw [sum_Ico_add']
  apply gol

theorem sum_div_succ_mul_choose_mul_from_9_to_10(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(gol:  ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l) = ↑((1 + x) ^ (n + 1)) - 1) :
   ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  have h2 : ∑ k in Ico 0 (n + 1), (Nat.choose (n + 1) (k + 1)) * ((x ^ (k + 1)) : ℝ)
          = ∑ l in Ico (0 + 1) (n + 1 + 1), (Nat.choose (n + 1) l) * ((x ^ l) : ℝ) := by
          let f : ℕ → ℝ := fun k => ↑(Nat.choose (n + 1) k) * ↑(x ^ k)
          change ∑ k in Ico 0 (n + 1), f (k+1) = ∑ l in Ico (0+1) (n + 1 + 1), f l
          rw [sum_Ico_add']
  rw [h2]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_9_to_11(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(gol:  ∑ x_1 in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (1 + ↑x) ^ (n + 1) - 1) :
   ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  have h2 : ∑ k in Ico 0 (n + 1), (Nat.choose (n + 1) (k + 1)) * ((x ^ (k + 1)) : ℝ)
          = ∑ l in Ico (0 + 1) (n + 1 + 1), (Nat.choose (n + 1) l) * ((x ^ l) : ℝ) := by
          let f : ℕ → ℝ := fun k => ↑(Nat.choose (n + 1) k) * ↑(x ^ k)
          change ∑ k in Ico 0 (n + 1), f (k+1) = ∑ l in Ico (0+1) (n + 1 + 1), f l
          rw [sum_Ico_add']
  rw [h2]
  simp
  apply gol

theorem sum_div_succ_mul_choose_mul_from_10_to_10(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(gol:  ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l) = ↑((1 + x) ^ (n + 1)) - 1) :
   ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  rw [h2]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_10_to_11(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(gol:  ∑ x_1 in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (1 + ↑x) ^ (n + 1) - 1) :
   ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) = ↑((1 + x) ^ (n + 1)) - 1 := by
  rw [h2]
  simp
  apply gol

theorem sum_div_succ_mul_choose_mul_from_11_to_11(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(gol:  ∑ x_1 in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (1 + ↑x) ^ (n + 1) - 1) :
   ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l) = ↑((1 + x) ^ (n + 1)) - 1 := by
  simp
  apply gol

theorem sum_div_succ_mul_choose_mul_from_13_to_13(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1 = (1 + ↑x) ^ (n + 1) - 1) :
   ∑ x_1 in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (1 + ↑x) ^ (n + 1) - 1 := by
  rw [h3]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_13_to_14(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (1 + (n + 1)), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (↑x + 1) ^ (n + 1)) :
   ∑ x_1 in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (1 + ↑x) ^ (n + 1) - 1 := by
  rw [h3]
  simp [add_comm]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_13_to_15(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (1 + (n + 1)), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 =
    ∑ m in range (n + 1 + 1), ↑x ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m)) :
   ∑ x_1 in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (1 + ↑x) ^ (n + 1) - 1 := by
  rw [h3]
  simp [add_comm]
  rw [add_pow (x:ℝ) 1 (n+1)]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_13_to_16(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 =
    ∑ m in range (n + 1 + 1), ↑x ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m)) :
   ∑ x_1 in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (1 + ↑x) ^ (n + 1) - 1 := by
  rw [h3]
  simp [add_comm]
  rw [add_pow (x:ℝ) 1 (n+1)]
  rw [add_comm]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_14_to_14(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (1 + (n + 1)), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (↑x + 1) ^ (n + 1)) :
   ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1 = (1 + ↑x) ^ (n + 1) - 1 := by
  simp [add_comm]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_14_to_15(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (1 + (n + 1)), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 =
    ∑ m in range (n + 1 + 1), ↑x ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m)) :
   ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1 = (1 + ↑x) ^ (n + 1) - 1 := by
  simp [add_comm]
  rw [add_pow (x:ℝ) 1 (n+1)]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_14_to_16(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 =
    ∑ m in range (n + 1 + 1), ↑x ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m)) :
   ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1 = (1 + ↑x) ^ (n + 1) - 1 := by
  simp [add_comm]
  rw [add_pow (x:ℝ) 1 (n+1)]
  rw [add_comm]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_15_to_15(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (1 + (n + 1)), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 =
    ∑ m in range (n + 1 + 1), ↑x ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m)) :
   ∑ x_1 in range (1 + (n + 1)), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (↑x + 1) ^ (n + 1) := by
  rw [add_pow (x:ℝ) 1 (n+1)]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_15_to_16(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 =
    ∑ m in range (n + 1 + 1), ↑x ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m)) :
   ∑ x_1 in range (1 + (n + 1)), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 = (↑x + 1) ^ (n + 1) := by
  rw [add_pow (x:ℝ) 1 (n+1)]
  rw [add_comm]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_16_to_16(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(gol:  ∑ x_1 in range (n + 1 + 1), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 =
    ∑ m in range (n + 1 + 1), ↑x ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m)) :
   ∑ x_1 in range (1 + (n + 1)), ↑(Nat.choose (n + 1) x_1) * ↑x ^ x_1 =
    ∑ m in range (n + 1 + 1), ↑x ^ m * 1 ^ (n + 1 - m) * ↑(Nat.choose (n + 1) m) := by
  rw [add_comm]
  apply gol

theorem sum_div_succ_mul_choose_mul_from_18_to_18(n k x : ℕ)(h : 0 < x)(h0 :  ∑ k in range (n + 1), 1 / (↑k + 1) * ↑(Nat.choose n k) * ↑(x ^ k) =    ∑ k in range (n + 1), 1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k))(this : x ≠ 0)(h1 :  1 / (↑n + 1) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ k) =    1 / ((↑n + 1) * ↑x) * ∑ k in range (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)))(h2 :  ∑ k in Ico 0 (n + 1), ↑(Nat.choose (n + 1) (k + 1)) * ↑(x ^ (k + 1)) =    ∑ l in Ico (0 + 1) (n + 1 + 1), ↑(Nat.choose (n + 1) l) * ↑(x ^ l))(h3 :  ∑ k in Ico 1 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k =    ∑ k in Ico 0 (n + 1 + 1), ↑(Nat.choose (n + 1) k) * ↑x ^ k - 1)(y : ℕ)(hy : y ∈ range (n + 1 + 1)) :
   ↑(Nat.choose (n + 1) y) * ↑x ^ y = ↑x ^ y * 1 ^ (n + 1 - y) * ↑(Nat.choose (n + 1) y) := by
  simp [mul_comm]

