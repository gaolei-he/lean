import Theorem.example_separate.add_div_two

theorem two_pow_eq_two_pow_two(h: 2 ≤ n) : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
      exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  rw[two_pow_eq_two_pow_sub_add]
  rw[Nat.pow_succ]


theorem two_pow_eq_two_pow_two_from_0_to_0(n : ℕ)(h : 2 ≤ n)(gol:  2 ^ (n - 1) = 2 ^ (n - 2) * 2) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
      exact tsub_add_eq_add_tsub h
  apply gol

theorem two_pow_eq_two_pow_two_from_0_to_1(n : ℕ)(h : 2 ≤ n)(gol:  2 ^ (n - 1) = 2 ^ (n - 2) * 2) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
      exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  apply gol

theorem two_pow_eq_two_pow_two_from_0_to_2(n : ℕ)(h : 2 ≤ n)(gol:  2 ^ (n - 2 + 1) = 2 ^ (n - 2) * 2) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
      exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  rw[two_pow_eq_two_pow_sub_add]
  apply gol

theorem two_pow_eq_two_pow_two_from_0_to_3(n : ℕ)(h : 2 ≤ n) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
      exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  rw[two_pow_eq_two_pow_sub_add]
  rw[Nat.pow_succ]

theorem two_pow_eq_two_pow_two_from_1_to_1(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  2 ^ (n - 1) = 2 ^ (n - 2) * 2) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  apply gol

theorem two_pow_eq_two_pow_two_from_1_to_2(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  2 ^ (n - 2 + 1) = 2 ^ (n - 2) * 2) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  rw[two_pow_eq_two_pow_sub_add]
  apply gol

theorem two_pow_eq_two_pow_two_from_1_to_3(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  rw[two_pow_eq_two_pow_sub_add]
  rw[Nat.pow_succ]

theorem two_pow_eq_two_pow_two_from_2_to_2(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  2 ^ (n - 2 + 1) = 2 ^ (n - 2) * 2) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  rw[two_pow_eq_two_pow_sub_add]
  apply gol

theorem two_pow_eq_two_pow_two_from_2_to_3(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1)) :
   2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
  rw[two_pow_eq_two_pow_sub_add]
  rw[Nat.pow_succ]

theorem two_pow_eq_two_pow_two_from_3_to_3(n : ℕ)(h : 2 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1)) :
   2 ^ (n - 2 + 1) = 2 ^ (n - 2) * 2 := by
  rw[Nat.pow_succ]

