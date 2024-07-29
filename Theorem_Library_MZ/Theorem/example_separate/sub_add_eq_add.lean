import Theorem.example_separate.add_div_two

theorem sub_add_eq_add(h: 2 ≤ n) : n - 1 + 2 = n + 1 := by
  have h1: 1 ≤ n := by linarith
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  rw[sub_add_eq_sub_add_add_add]
  rw [Nat.sub_add_cancel h1]


theorem sub_add_eq_add_from_0_to_0(n : ℕ)(h : 2 ≤ n)(gol:  n - 1 + 2 = n + 1) :
   n - 1 + 2 = n + 1 := by
  have h1: 1 ≤ n := by linarith
  apply gol

theorem sub_add_eq_add_from_0_to_1(n : ℕ)(h : 2 ≤ n)(gol:  n - 1 + 2 = n + 1) :
   n - 1 + 2 = n + 1 := by
  have h1: 1 ≤ n := by linarith
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem sub_add_eq_add_from_0_to_2(n : ℕ)(h : 2 ≤ n)(gol:  n - 1 + 1 + 1 = n + 1) :
   n - 1 + 2 = n + 1 := by
  have h1: 1 ≤ n := by linarith
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  rw[sub_add_eq_sub_add_add_add]
  apply gol

theorem sub_add_eq_add_from_0_to_3(n : ℕ)(h : 2 ≤ n) :
   n - 1 + 2 = n + 1 := by
  have h1: 1 ≤ n := by linarith
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  rw[sub_add_eq_sub_add_add_add]
  rw [Nat.sub_add_cancel h1]

theorem sub_add_eq_add_from_1_to_1(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n - 1 + 2 = n + 1) :
   n - 1 + 2 = n + 1 := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem sub_add_eq_add_from_1_to_2(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n - 1 + 1 + 1 = n + 1) :
   n - 1 + 2 = n + 1 := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  rw[sub_add_eq_sub_add_add_add]
  apply gol

theorem sub_add_eq_add_from_1_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n) :
   n - 1 + 2 = n + 1 := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  rw[sub_add_eq_sub_add_add_add]
  rw [Nat.sub_add_cancel h1]

theorem sub_add_eq_add_from_2_to_2(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1)(gol:  n - 1 + 1 + 1 = n + 1) :
   n - 1 + 2 = n + 1 := by
  rw[sub_add_eq_sub_add_add_add]
  apply gol

theorem sub_add_eq_add_from_2_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1) :
   n - 1 + 2 = n + 1 := by
  rw[sub_add_eq_sub_add_add_add]
  rw [Nat.sub_add_cancel h1]

theorem sub_add_eq_add_from_3_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1) :
   n - 1 + 1 + 1 = n + 1 := by
  rw [Nat.sub_add_cancel h1]

