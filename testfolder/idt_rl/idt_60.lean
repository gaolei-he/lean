import Lean4Repl
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Theorem.IDT_1to100.IDT_1to10.idt_1
import Theorem.IDT_1to100.IDT_1to10.idt_2
import Theorem.Lemma.choose_two_mul_n_add_one_eq

import Mathlib.Algebra.Group.Defs

open Nat
open Finset
open BigOperators

def f : ℕ → ℕ := fun n => ∑ k in Ico 0 (n+1), (n+k).choose k * 2 ^(n-k)



theorem idt_60 {n:ℕ} : ∑ k in Ico 0 (n+1), (n+k).choose k * 2 ^(n-k) = 4^ n :=by lean_repl sorry

  induction' n with n hn
  {
    simp
  }
  {
    have hf: f (n+1) =  ∑ k in Ico 0 (succ n + 1), Nat.choose (succ n + k) k * 2 ^ (succ n - k) :=by
      rw [f]


    have h_e: 2 * f (n+1) = 4 * 4 ^ n +  f (n+1) :=by
      nth_rw 1 [hf]

      rw [sum_eq_sum_Ico_succ_bot]
      simp

      rw [sum_congr rfl fun y hy => by
        have h1: 1<= succ n + y:=by
          rw [succ_add]
          rw [Nat.succ_le]
          simp [Nat.zero_lt_succ (n+y)]

        have h2: 1 <= y :=by
          simp [mem_Ico.mp hy]
        rw [idt1_Pascal's_Recurrence h1 h2]
      ]
      simp [add_mul]
      rw [sum_add_distrib]

      rw [← add_assoc]
      rw [add_comm]

      simp [mul_add]
      simp [mul_sum]

      have l₁: ∑ x in Ico 1 (succ n + 1), 2 * (Nat.choose (n + x) x * 2 ^ (succ n - x)) =
       2 * choose (2*n+1) (n+1) + 4^(n+1) - 2 ^ (n+2) :=by
        have h1: 1 ≤ n + 1 :=by norm_num
        rw [Finset.sum_Ico_succ_top h1]
        ring_nf
        rw [succ_eq_add_one]
        nth_rw 3 [add_comm 1 n]
        have h1: n + 1 - (n + 1) = 0:=by norm_num
        rw [h1]
        simp [Nat.pow_zero]
        rw [Nat.add_sub_assoc]
        nth_rw 1 [add_comm]
        congr 1
        rw [←hn]
        symm
        rw [sum_eq_sum_Ico_succ_bot]
        simp
        rw [add_mul]
        simp
        rw [sum_mul]
        rw [add_comm]
        apply sum_congr rfl
        intro x hx
        rw [Nat.add_sub_assoc]
        rw [add_comm 1]
        rw [←succ_eq_add_one]
        rw [Nat.pow_succ]
        ring_nf
        have h_nx:= (mem_Ico.mp hx).right
        rw [←Nat.lt_succ_iff]
        rw [succ_eq_add_one]
        rw [add_comm]
        exact h_nx
        simp
        simp
        apply Nat.pow_le_pow_of_le_left
        norm_num
      have l₂: ∑ x in Ico 1 (succ n + 1), 2 * (Nat.choose (n + x) (x - 1) * 2 ^ (succ n - x)) =
        f (n+1) - choose (2*n+2) (n+1) :=by
        have h1 : ∑ x in Ico 0 (succ n), 2 * Nat.choose (n +(x+1)) (x+1-1) * 2 ^ ((n+1)-(x+1)) =
         ∑ x in Ico 1 (succ n + 1), 2 * (Nat.choose (n + x) (x - 1) * 2 ^ (succ n - x)) :=by
          rw [sum_Ico_add' fun x => 2 * Nat.choose (n + x) (x-1) * 2 ^ ((n+1)-x)]
          simp
          rw [succ_eq_add_one]
          rw [sum_congr rfl]
          intro x hx
          rw [mul_assoc]
        symm at h1
        rw [h1]
        simp
        rw [hf]
        symm
        rw [sum_Ico_succ_top]
        simp
        rw [succ_eq_add_one]
        ring_nf
        simp

        rw [sum_congr rfl]
        intro x hx
        rw [mul_assoc]
        rw [mul_comm 2]
        rw [mul_assoc]
        rw [←Nat.pow_succ 2 (n-x)]
        congr 1
        rw [add_comm]
        rw [←add_assoc]
        rw [add_comm n]
        rw [succ_eq_add_one]
        congr 1
        rw [add_comm _ 1]
        rw [Nat.add_sub_assoc]

        have hxn:= mem_range.mp hx
        apply Nat.le_of_lt_succ
        rw [succ_eq_add_one]
        rw [add_comm]
        exact hxn
        norm_num


      rw [l₁,l₂]
      ring_nf

      have h_2: 2 ^ succ n * 2 =2^n * 4:=by
        rw [Nat.pow_succ]
        ring
      rw [h_2]
      rw [add_assoc]
      rw [Nat.sub_add_cancel]


      have l₃: Nat.choose (2 + n * 2) (1 + n)  = Nat.choose (1 + n * 2) (1 + n) * 2 :=by
        exact choose_two_mul_n_add_one_eq


      rw [l₃]
      rw [←add_assoc]
      rw [Nat.sub_add_cancel]
      swap


      have h_3: 2 ^ n * 4 ≤ 4 ^n *4:=by
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_of_le_left
        simp

      apply Nat.le_trans h_3
      simp
      swap
      norm_num


      have l₂' : ∑ x in Ico 1 (succ n + 1), 2 * (Nat.choose (n + x) (x - 1) * 2 ^ (succ n - x)) + choose (2*n+2) (n+1) = f (n+1) :=by
        rw [l₂]
        rw [Nat.sub_add_cancel]

        rw [hf]
        rw [Finset.sum_Ico_succ_top]
        simp

        have h: succ n + (n + 1) = 2 * n + 2 :=by
          rw [succ_eq_add_one]
          rw [←two_mul]
          rw [mul_add]
          simp
        rw [h]
        simp
        simp


      have h_4:  f (1 + n) ≥ Nat.choose (1 + n * 2) (1 + n) * 2 :=by
        symm at l₂'
        rw [add_comm 1 n]
        rw [l₂']
        nth_rw 1 [add_comm n 1]
        rw [add_comm _ 2]
        rw [mul_comm 2 n]
        rw [choose_two_mul_n_add_one_eq]
        rw [add_comm n 1]
        simp

      exact h_4

    rw [hf] at h_e
    rw [two_mul] at h_e
    simp at h_e
    rw [succ_eq_add_one]
    rw [pow_add]
    simp
    rw [mul_comm]
    rw [h_e]
  }
