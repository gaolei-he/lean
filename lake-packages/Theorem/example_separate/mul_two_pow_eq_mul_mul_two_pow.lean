import Theorem.example_separate.add_div_two

theorem mul_two_pow_eq_mul_mul_two_pow(h: 2 ≤ n): n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]


theorem mul_two_pow_eq_mul_mul_two_pow_from_0_to_0(n : ℕ)(h : 2 ≤ n)(gol:  n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_0_to_1(n : ℕ)(h : 2 ≤ n)(gol:  n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_0_to_2(n : ℕ)(h : 2 ≤ n)(gol:  n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_0_to_3(n : ℕ)(h : 2 ≤ n)(gol:  n * (2 ^ (n - 2) * 2) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_0_to_4(n : ℕ)(h : 2 ≤ n)(gol:  n * 2 ^ (n - 2) * 2 = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_0_to_5(n : ℕ)(h : 2 ≤ n) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]

theorem mul_two_pow_eq_mul_mul_two_pow_from_1_to_1(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_1_to_2(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_1_to_3(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * (2 ^ (n - 2) * 2) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_1_to_4(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * 2 ^ (n - 2) * 2 = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_1_to_5(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]

theorem mul_two_pow_eq_mul_mul_two_pow_from_2_to_2(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_2_to_3(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  n * (2 ^ (n - 2) * 2) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_2_to_4(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  n * 2 ^ (n - 2) * 2 = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_2_to_5(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]

theorem mul_two_pow_eq_mul_mul_two_pow_from_3_to_3(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  n * (2 ^ (n - 2) * 2) = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  rw[two_pow_eq_two_pow_two]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_3_to_4(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  n * 2 ^ (n - 2) * 2 = 2 * n * 2 ^ (n - 2)) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_3_to_5(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2) :
   n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2) := by
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]

theorem mul_two_pow_eq_mul_mul_two_pow_from_4_to_4(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  n * 2 ^ (n - 2) * 2 = 2 * n * 2 ^ (n - 2)) :
   n * (2 ^ (n - 2) * 2) = 2 * n * 2 ^ (n - 2) := by
  rw[← Nat.mul_assoc]
  apply gol

theorem mul_two_pow_eq_mul_mul_two_pow_from_4_to_5(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2) :
   n * (2 ^ (n - 2) * 2) = 2 * n * 2 ^ (n - 2) := by
  rw[← Nat.mul_assoc]
  rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]

theorem mul_two_pow_eq_mul_mul_two_pow_from_5_to_5(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2) :
   n * 2 ^ (n - 2) * 2 = 2 * n * 2 ^ (n - 2) := by
  rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]

