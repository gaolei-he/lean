import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Parity
import Theorem.IDT_1to100.IDT_11to20.idt_12

open Nat
open Finset
open BigOperators


def sum_choose_even (n:ℕ) : ℕ := ∑ k in range (n+1), if Even k then choose n k else 0

def sum_choose_odd  (n:ℕ) : ℕ := ∑ k in range (n+1), if Odd k then choose n k else 0


theorem sum_choose_eq_even_add_odd {n:ℕ} :  ∑ a in range (n+1), choose n a = sum_choose_even n + sum_choose_odd n :=by
  rw [sum_choose_even]
  rw [sum_choose_odd]

  rw [←sum_add_distrib]

  rw [sum_bij]

  case i;
    intro a _;
    exact a
  case hi;
    intro a ha;
    exact ha
  case h;
    intro a _;
    cases Nat.even_or_odd a with
    | inl hl=>
      simp [hl]
    | inr hr=>
      simp
      rw [odd_iff_not_even] at hr
      simp [hr]
  intro a b
  simp
  intro a ha
  simp
  exact mem_range.mp ha


theorem sum_choose_eq_even_add_odd_eval {n:ℕ} : sum_choose_even n + sum_choose_odd n  = 2^ n :=by
  rw [←sum_choose_eq_even_add_odd]
  rw [sum_range_choose]


theorem sum_chose_alternating_of_ne (n:ℕ) :  sum_choose_even n - sum_choose_odd n = ∑ a in range (n+1), (-1:ℤ)^a * choose n a := by
  symm
  have h2 {a n :ℕ} :  (-1:ℤ)^a * choose n a = ( if Even a then choose n a else 0) - ( if Odd a then choose n a else 0) :=by
    cases Nat.even_or_odd a with
    | inl hl=>
      simp [hl]
    | inr hr =>
      simp
      rw [odd_iff_not_even] at hr
      simp [hr]

  rw [sum_congr rfl fun k hk=>by
    rw [h2]
  ]
  rw [sum_sub_distrib]
  congr
  rw [←cast_sum]
  rw [sum_choose_even]
  rw [←cast_sum]
  rw [sum_choose_odd]


theorem sum_chose_alternating_of_ne_eval {n:ℕ} (hn: 1≤ n) :  sum_choose_even n - sum_choose_odd n = 0 := by

  have h1 (_: 1≤ n): sum_choose_even n - sum_choose_odd n = (0:ℤ)  → sum_choose_even n - sum_choose_odd n = 0 :=by
    simp
    intro ha
    rw [sub_eq_zero] at ha
    simp [Int.cast] at ha
    rw [ha]
  rw [h1 hn]

  rw [sum_chose_alternating_of_ne]
  rw [Idt12]
  simp
  intro h
  rw [h] at hn
  exact Nat.not_succ_le_zero 0 hn


theorem sum_even_choose_eq_sum_odd_choose {n:ℕ} (hn: 1≤ n) : sum_choose_even n = sum_choose_odd n :=by
  have h1 (_: 1≤ n): sum_choose_even n - sum_choose_odd n = (0:ℤ)  → sum_choose_even n = sum_choose_odd n :=by
    intro ha
    rw [sub_eq_zero] at ha
    simp [Int.cast] at ha
    rw [ha]
  rw [h1 hn]
  rw [sum_chose_alternating_of_ne]
  rw [Idt12]
  simp
  intro h
  rw [h] at hn
  exact Nat.not_succ_le_zero 0 hn




theorem sum_choose_even_eval' {n:ℕ} (hn : 1≤ n) : sum_choose_even n = 2 ^(n-1) :=by
  have h1: sum_choose_even n + sum_choose_odd n  = 2^ n :=by
    exact sum_choose_eq_even_add_odd_eval

  rw [←sum_even_choose_eq_sum_odd_choose] at h1
  rw [←two_mul] at h1


  have h_two_pow_eq (hn: 1 ≤ n ) :  2 ^ n = 2 * 2 ^(n-1) :=by
    have hn_one : n = n-1+1:= by
      rw [tsub_add_cancel_of_le hn]
    rw [hn_one]
    rw [pow_add]
    simp
    rw [mul_comm]

  rw [h_two_pow_eq] at h1
  rw [mul_right_inj'] at h1
  exact h1
  simp [hn]
  exact hn
  exact hn


theorem sum_choose_odd_eval'  {n:ℕ} (hn : 1≤ n) : sum_choose_odd n = 2 ^(n-1) :=by
  rw [←sum_even_choose_eq_sum_odd_choose hn]
  rw [sum_choose_even_eval' hn]


theorem sum_choose_even_eval {n:ℕ} : sum_choose_even n = 2^(n-1) + (1/2)*(if 1 ≤ n then 1 else 0) :=by
  cases Nat.eq_zero_or_pos n with
  | inl hl =>
    simp [hl]

  | inr hr =>
    rw [sum_choose_even_eval']
    simp

    rw [gt_iff_lt,lt_iff_add_one_le,zero_add] at hr
    simp [hr]



theorem sum_choose_odd_eval {n:ℕ} :sum_choose_odd n = 2^(n-1) * (if 1 ≤ n then 1 else 0) :=by
  cases Nat.eq_zero_or_pos n with
  | inl hl =>
    simp [hl]
  | inr hr =>
    rw [sum_choose_odd_eval']
    rw [gt_iff_lt,lt_iff_add_one_le,zero_add] at hr
    simp [hr]
    rw [gt_iff_lt,lt_iff_add_one_le,zero_add] at hr
    exact hr
