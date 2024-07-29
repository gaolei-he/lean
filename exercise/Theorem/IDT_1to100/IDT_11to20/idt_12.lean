import Mathlib.Data.Nat.Choose.Sum


open Nat

open Finset

open BigOperators

theorem Idt12 {n : ℕ} :
    (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ)) = if n = 0 then 1 else 0 := by
  cases n; · simp
  case succ n =>
    have h := add_pow (-1 : ℤ) 1 n.succ
    simp only [one_pow, mul_one, add_left_neg] at h
    rw [← h, zero_pow (Nat.succ_pos n), if_neg (Nat.succ_ne_zero n)]
