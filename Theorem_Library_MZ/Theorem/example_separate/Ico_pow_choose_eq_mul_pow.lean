import Theorem.example_separate.Ico_pow_choose_eq_pow_add_pow

open Nat

open Finset

open BigOperators

theorem Ico_pow_choose_eq_mul_pow(h: 2 ≤ n):  ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n * (n + 1) * 2 ^ ( n - 2 )  := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]


theorem Ico_pow_choose_eq_mul_pow_from_0_to_0(n : ℕ)(h : 2 ≤ n)(gol:  ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_1(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_2(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_3(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_4(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_5(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_6(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_7(n : ℕ)(h : 2 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_8(n : ℕ)(h : 2 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_9(n : ℕ)(h : 2 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_10(n : ℕ)(h : 2 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_11(n : ℕ)(h : 2 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_0_to_12(n : ℕ)(h : 2 ≤ n) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_1_to_1(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_2(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_4(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_6(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_7(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_8(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_1_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * (n + 1) * 2 ^ (n - 2) := by
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_2_to_2(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_4(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_6(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_7(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_8(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_2_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_3_to_3(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_4(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_6(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_7(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_8(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_3_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    rw[sub_add_eq_sub]
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_4_to_4(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_4_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_4_to_6(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_4_to_7(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_4_to_8(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_4_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_4_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_4_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_4_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_5_to_5(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_5_to_6(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_5_to_7(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_5_to_8(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_5_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_5_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_5_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_5_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_6_to_6(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_eq_mul_mul_two_pow]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_6_to_7(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_6_to_8(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_6_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_6_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_6_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_6_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + n * 2 ^ (n - 1) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_7_to_7(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_7_to_8(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_7_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_7_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_7_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_7_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_8_to_8(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_add_eq_mul_pow ]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_8_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_8_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_8_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_8_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2)) :
   n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_two_pow_add_eq_mul_pow ]
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_9_to_9(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_9_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_9_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_9_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2)) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_10_to_10(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_10_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_10_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_11_to_11(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1)(sub_add_eq_add : n - 1 + 2 = n + 1)(gol:  (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2)) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  apply gol

theorem Ico_pow_choose_eq_mul_pow_from_11_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1)(sub_add_eq_add : n - 1 + 2 = n + 1) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem Ico_pow_choose_eq_mul_pow_from_12_to_12(n : ℕ)(h : 2 ≤ n)(h1 : 1 ≤ n)(sub_add_eq_sub : n - 2 + 1 = n - 1)(two_pow_eq_two_pow_sub_add : 2 ^ (n - 1) = 2 ^ (n - 2 + 1))(two_pow_eq_two_pow_two : 2 ^ (n - 1) = 2 ^ (n - 2) * 2)(mul_two_pow_eq_mul_mul_two_pow : n * 2 ^ (n - 1) = 2 * n * 2 ^ (n - 2))(mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2))(sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1)(sub_add_eq_add : n - 1 + 2 = n + 1)(mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1)) :
   (n * (n - 1) + 2 * n) * 2 ^ (n - 2) = n * (n + 1) * 2 ^ (n - 2) := by
  rw[mul_add_mul_eq_mul]

