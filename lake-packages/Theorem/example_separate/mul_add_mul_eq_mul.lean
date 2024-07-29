import Theorem.example_separate.add_div_two

theorem mul_add_mul_eq_mul(h: 2 ≤ n) : n * (n - 1) + 2 * n = n * (n + 1) := by
  have h1: 1 ≤ n := by linarith
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  rw[sub_add_eq_add]


theorem mul_add_mul_eq_mul_from_0_to_0(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) + 2 * n = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  have h1: 1 ≤ n := by linarith
  apply gol

theorem mul_add_mul_eq_mul_from_0_to_1(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) + n * 2 = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  have h1: 1 ≤ n := by linarith
  rw[Nat.mul_comm 2 n]
  apply gol

theorem mul_add_mul_eq_mul_from_0_to_2(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  have h1: 1 ≤ n := by linarith
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  apply gol

theorem mul_add_mul_eq_mul_from_0_to_3(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  have h1: 1 ≤ n := by linarith
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem mul_add_mul_eq_mul_from_0_to_4(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  have h1: 1 ≤ n := by linarith
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem mul_add_mul_eq_mul_from_0_to_5(n : ℕ)(h : 2 ≤ n) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  have h1: 1 ≤ n := by linarith
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  rw[sub_add_eq_add]

theorem mul_add_mul_eq_mul_from_1_to_1(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) + n * 2 = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  rw[Nat.mul_comm 2 n]
  apply gol

theorem mul_add_mul_eq_mul_from_1_to_2(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  apply gol

theorem mul_add_mul_eq_mul_from_1_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem mul_add_mul_eq_mul_from_1_to_4(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem mul_add_mul_eq_mul_from_1_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n) :
   n * (n - 1) + 2 * n = n * (n + 1) := by
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  rw[sub_add_eq_add]

theorem mul_add_mul_eq_mul_from_2_to_2(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + n * 2 = n * (n + 1) := by
  rw[← Nat.mul_add]
  apply gol

theorem mul_add_mul_eq_mul_from_2_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + n * 2 = n * (n + 1) := by
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem mul_add_mul_eq_mul_from_2_to_4(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1) + n * 2 = n * (n + 1) := by
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem mul_add_mul_eq_mul_from_2_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n) :
   n * (n - 1) + n * 2 = n * (n + 1) := by
  rw[← Nat.mul_add]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  rw[sub_add_eq_add]

theorem mul_add_mul_eq_mul_from_3_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1 + 2) = n * (n + 1) := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem mul_add_mul_eq_mul_from_3_to_4(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1 + 2) = n * (n + 1) := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem mul_add_mul_eq_mul_from_3_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n) :
   n * (n - 1 + 2) = n * (n + 1) := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  rw[sub_add_eq_add]

theorem mul_add_mul_eq_mul_from_4_to_4(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1)(gol:  n * (n - 1 + 2) = n * (n + 1)) :
   n * (n - 1 + 2) = n * (n + 1) := by
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem mul_add_mul_eq_mul_from_4_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1) :
   n * (n - 1 + 2) = n * (n + 1) := by
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  rw[sub_add_eq_add]

theorem mul_add_mul_eq_mul_from_5_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1)(sub_add_eq_add : n - 1 + 2 = n + 1) :
   n * (n - 1 + 2) = n * (n + 1) := by
  rw[sub_add_eq_add]

