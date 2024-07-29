import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem sum_Ico_choose_mul { m n : ℕ } (h : m ≤ n) :
  (∑ k in Ico m (n + 1), (choose n k) * (choose k m) = 2^(n-m) * choose n m) := by
  by_cases h_eq : m = n
  . rw [h_eq]
    simp
  case neg =>
    have h1 : ∀ m n i: ℕ, i ∈ Ico m (n+1) → (choose n i) * (choose i m) = (choose n m * choose (n-m) (i-m)) := by
      intro m n i hi
      have h2 : i ≤ n := Nat.le_of_lt_succ (mem_Ico.mp hi).right
      have h3 : m ≤ i := (mem_Ico.mp hi).left
      exact choose_mul h2 h3
    rw [sum_congr rfl (h1 m n)]
    rw [sum_Ico_eq_sum_range]
    simp
    rw [←mul_sum]
    rw [add_comm, add_tsub_assoc_of_le h, add_comm]
    rw [sum_range_choose]
    rw [mul_comm]


