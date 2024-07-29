import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub'
import Theorem.IDT_1to100.IDT_1to10.idt_6
import Theorem.Lemma.succ_mul_choose'
import Theorem.Lemma.sum_choose_neg_two_pow

open Nat

open Finset

open BigOperators


theorem idt_28{ n : ℕ}: ∑ k in Ico 0 (n+1), 2 ^ (k-1) * (-1:ℝ) ^ k * k * choose n k  = n * (-1 :ℝ)^ n := by

    cases Nat.eq_zero_or_pos n with
    | inl hl =>
        rw [hl]
        simp
    | inr hr =>
        rw [gt_iff_lt] at hr
        rw [←succ_le_iff] at hr
        rw [succ_eq_add_one] at hr
        rw [zero_add] at hr
        have hn: 0 < n+1:=by
            rw [←succ_eq_add_one]
            simp
        rw [Finset.sum_eq_sum_Ico_succ_bot hn]
        simp
        have h₁: ∑ k in Ico 1 (n + 1), 2 ^ (k - 1) * (-1:ℝ) ^ k * k * (Nat.choose n k) =
            ∑ k in Ico 1 (n + 1), 2 ^ (k - 1) * (-1:ℝ) ^ k * n * (n-1).choose (k-1) :=by
            refine' sum_congr rfl fun k hk => _
            rw [mul_assoc]
            symm
            rw [mul_assoc]
            ring_nf
            congr 2
            let h_ico:= mem_Ico.mp hk
            let h_sk := And.left h_ico
            let h_kn := And.right h_ico
            rw [←succ_eq_add_one,lt_succ_iff] at h_kn
            rw [←succ_mul_choose' h_kn h_sk]
        rw [h₁]
        rw [sum_congr rfl fun k _ => by
            rw [mul_comm,←mul_assoc]
        ]
        rw [←sum_mul]
        rw [mul_comm]
        congr 1
        have h₂ : ∑ x in Ico 1 (n + 1), (Nat.choose (n - 1) (x - 1)) * (2 ^ (x - 1) * (-1:ℝ) ^ x) =
            ∑ x in Ico 0 n, Nat.choose (n-1) (x + 1 -1) * 2 ^ (x + 1 -1) * (-1: ℝ) ^ (x + 1)  :=by
            symm
            let f : ℕ -> ℝ := fun k=> (n-1).choose (k-1) * 2 ^(k-1) * (-1:ℝ) ^ k
            rw [sum_Ico_add' f 0 n 1]
            simp
            refine' sum_congr rfl fun k _ => _
            rw [mul_assoc]
        rw [h₂]
        simp
        have h₃ : ∑ x in range n, (Nat.choose (n - 1) x) * 2 ^ x * (-1:ℝ) ^ (x + 1) =
            ∑ x in range n, ↑(Nat.choose (n - 1) x) * 2 ^ x * (-1:ℝ) ^ x * (-1:ℝ) :=by
            refine' sum_congr rfl fun k _ => _
            rw [pow_add]
            simp
        rw [h₃]
        rw [←sum_mul]
        rw [sum_choose_neg_two_pow]
        nth_rw 2 [←pow_one (-1)]
        rw [←pow_add]
        congr
        rw [nat_sub_add_cancel hr]
        exact hr
