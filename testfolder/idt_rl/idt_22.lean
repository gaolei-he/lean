import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Basic
import Lean4Repl

open Nat

open Finset
-- open Int
open BigOperators
theorem Idt22  {n k: ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
  (∑ k in range (n + 1), ( (-1) ^ k * (k) * ↑ (choose n k) : ℤ)) = (-1)*(if n=1 then 1 else 0) := by lean_repl sorry
cases n with
| zero => simp
| succ n =>
  have idt6_Absorption {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
    k * choose n k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]


  rw [range_eq_Ico]
  have h_succ : 0 < n.succ + 1 := by linarith

  have Ico_choose_simp_0to1: ∑ k in Ico 0 (n.succ + 1), (-1:ℤ) ^ k * ↑k * (choose n.succ k) =
    ∑ k in Ico 1 (n.succ + 1), (-1:ℤ) ^ k * ↑k * (choose n.succ k):= by
      rw [sum_eq_sum_Ico_succ_bot h_succ]
      simp

  rw [Ico_choose_simp_0to1]

  have h1: ∑ k in Ico 1 (n.succ + 1), (-1:ℤ) ^ k * ↑k * ↑(Nat.choose (n.succ) k)
    = ∑ k in Ico 1 (n.succ + 1), (-1:ℤ) ^ k * n.succ * ↑(Nat.choose (n.succ - 1) (k - 1)) := by
      refine' sum_congr rfl fun x hx ↦ _
      have hx_succ: x < n.succ + 1 := by exact (mem_Ico.1 hx).2
      have hx_n: x ≤ n.succ := by linarith
      have hk1: 1 ≤ x := by exact (mem_Ico.1 hx).1
      rw [mul_assoc,mul_assoc]
      simp
      rw [← cast_mul]
      rw [idt6_Absorption hx_n hk1]
      rw [cast_mul]
      rw [← add_one]
      rw [cast_add_one]
      simp

  rw [h1]
  have h2: ∑ k in Ico 1 (succ n + 1), (-1:ℤ ) ^ k * ↑(succ n) * ↑(Nat.choose (succ n - 1) (k - 1))
    =↑(succ n) * ∑ k in Ico 1 (succ n + 1), (-1:ℤ) ^ k *  ↑(Nat.choose (succ n - 1) (k - 1)) := by
    simp
    rw [mul_sum]
    refine' sum_congr rfl fun x hx ↦ _
    rw[mul_comm]
    rw [← mul_assoc,← mul_assoc]
    rw [mul_right_comm,mul_assoc,mul_left_comm,mul_assoc]
    simp
    rw [mul_comm]
    simp

  rw [h2]
  rw [sum_Ico_eq_sum_range]

  have h3:
    ↑(succ n) * ∑ k in range (succ n + 1 - 1), (-1:ℤ) ^ (1 + k) * ↑(Nat.choose (succ n - 1) (1 + k - 1))
    = (-1:ℤ) * ↑(succ n) * ∑ k in range (succ n - 1 + 1), (-1:ℤ) ^ k * ↑(Nat.choose (succ n - 1) (1 + k - 1)) := by
      simp
      rw [add_one]
      rw [mul_sum,mul_sum]
      refine' sum_congr rfl fun x hx ↦ _
      rw [mul_comm,← mul_assoc,mul_right_comm]
      simp
      rw [pow_add,mul_right_comm]
      simp

  rw [h3]
  -- 右边不能simp，故写h4
  have h4: ∑ k in range (n.succ - 1 + 1), (-1:ℤ) ^ k * choose (n.succ - 1) (1 + k - 1) =
    ∑ k in range (n + 1), (-1:ℤ) ^ k * choose n k := by
    simp

  rw [h4]
  have idt_12 {n : ℕ} :
    (∑ k in range (n + 1), ((-1) ^ k * ↑(choose n k ) : ℤ)) = if n = 0 then 1 else 0 := by
      cases n; · simp
      case succ n =>
        have h := add_pow (-1 : ℤ) 1 n.succ
        simp only [one_pow, mul_one, add_left_neg] at h
        rw [← h, zero_pow (Nat.succ_pos n), if_neg (Nat.succ_ne_zero n)]

  rw [idt_12]
  rw [succ_eq_add_one]
  have h6: -1 * ( if n + 1 = 1 then 1 else 0) = -1 * if n = 0 then 1 else 0 := by
    simp
  rw [h6]
  simp
  cases n; · simp
  case succ n => simp
