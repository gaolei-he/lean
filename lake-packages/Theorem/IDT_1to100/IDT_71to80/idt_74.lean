import Mathlib.Data.Nat.Choose.Sum
import Theorem.Lemma.succ_dvd_two

open Nat Finset BigOperators



theorem Idt_74 {n : ℕ} : ∑ k in range (n+1), k^2 = choose (n+1) 2 + 2 * choose (n+1) 3 := by
  induction n
  . exact rfl
  . rename_i n h₁
    rw [sum_range_succ, choose_succ_succ', choose_succ_succ' (n+1)]
    norm_num
    rw [add_comm (choose (n+1) 2) _, mul_add, ←add_assoc, add_assoc (n+1), add_comm (n+1), h₁]
    rw [add_assoc (Nat.choose (n + 1) 2 + 2 * Nat.choose (n + 1) 3)]
    congr 1
    rw [choose_two_right]
    simp
    rw [mul_comm, Nat.div_mul_cancel]
    nth_rw 2 [←mul_one (n+1)]
    rw [←mul_add, add_comm 1 n, pow_two]
    exact succ_dvd_two
