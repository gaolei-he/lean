import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.IDT_1to100.IDT_1to10.idt_1
import Theorem.IDT_1to100.IDT_21to30.idt_23

open Nat Finset BigOperators

theorem idt_25 {n : ℕ} : ∑ k in Ico 1 (n+1), ((choose n k / k):ℝ) = ∑ k in Ico 1 (n+1), (((2^k - 1) / k):ℝ) := by
  induction n with
  | zero => simp
  | succ n nth =>
    have h1 : ∑ k in Ico 1 (succ n + 1), ((Nat.choose (succ n) k / k):ℝ) - ∑ k in Ico 1 (n+1), ((choose n k / k):ℝ)
              = ∑ k in Ico 1 (succ n + 1), ((Nat.choose n (k-1) / k):ℝ) := by
      have h11 : ∑ k in Ico 1 (succ n + 1), ((choose n k / k):ℝ) - choose n (n+1) / (n+1)
                = ∑ k in Ico 1 (n+1), ((choose n k / k):ℝ) := by
                rw [sum_Ico_succ_top]
                simp
                linarith
      rw [←h11, choose_succ_self]
      simp
      rw [←sum_sub_distrib]
      refine' sum_congr rfl fun k hk => _
      have h12 : (k:ℝ) ≠ 0 := by
        have : 1 ≤ k := (mem_Ico.1 hk).left
        rw [cast_ne_zero]
        linarith
      have h13: 1 ≤ succ n := by linarith
      rw [div_sub_div_same, ←cast_sub]
      apply mul_right_cancel₀ h12
      rw [div_mul_cancel, div_mul_cancel]
      congr 1
      rw [←add_left_inj (Nat.choose n k), Nat.sub_add_cancel, add_comm]
      rw [idt1_Pascal's_Recurrence h13 (mem_Ico.1 hk).left]
      simp
      all_goals (try exact h12)
      all_goals (try (rw [idt1_Pascal's_Recurrence h13 (mem_Ico.1 hk).left];simp))
    have h2 : ∑ k in Ico 1 (succ n + 1), ((Nat.choose n (k-1) / k):ℝ)
              = ∑ k in range (n + 1), ((Nat.choose n k / (k+1)):ℝ) := by
              -- rw [range_eq_Ico]
              rw [sum_Ico_eq_sum_range]
              simp
              rw [←add_one]
              refine' sum_congr rfl fun k hk => _
              rw [add_comm]
    have h3 : ∑ k in range (n + 1), ((Nat.choose n k / (k+1)):ℝ)
              = ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k := by
              refine' sum_congr rfl fun k hk => _
              rw [one_div, mul_comm, ←one_div, mul_one_div]
    have h4 : 1 ≤ n+1 := by linarith
    have h5 : 1 / ((n:ℝ)+ 1) = 1 / (n+(1:ℕ)) := by rw [cast_one]
    rw [h3] at h2
    rw [idt_23, h5] at h2
    rw [h2] at h1
    rw [nth] at h1
    rw [←add_left_inj (∑ k in Ico 1 (n + 1), (((2 ^ k - 1) / k):ℝ)), sub_add_cancel,
        one_div, mul_comm, ←one_div, mul_one_div, add_comm (_ / _), ←cast_add, ←sum_Ico_succ_top h4, add_one n] at h1
    assumption
    exact n
