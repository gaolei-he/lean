import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Real.Basic
import Theorem.IDT_1to100.IDT_21to30.idt_24
import Theorem.IDT_1to100.IDT_41to50.idt_41

open Nat

open Finset

open BigOperators

variable {R : Type*}


theorem idt_53( n : ℕ ) : ∑ k in range (n + 1), (Nat.choose n k) * ((-1 : ℝ )^k / (k+2)) = 1 / (((n+1):ℝ) * ((n+2):ℝ)) := by
  have h1( n : ℕ ) : 1/((n+1):ℝ) - 1/((n+2):ℝ) = 1/((n+1)*(n+2)) := by
    rw[div_sub_div]
    norm_num
    linarith
    linarith
  rw [← h1]
  rw[← idt_24, ← idt_41]

  have h2 : ∑ k in range (n + 1), (Nat.choose n k) * ((-1 : ℝ )^k / (((k+1):ℝ)*((k+2):ℝ))) = ∑ k in range (n + 1), (Nat.choose n k) * ((-1 : ℝ )^k / ((k+1):ℝ)) - ∑ k in range (n + 1), (Nat.choose n k) * ((-1 : ℝ )^k /((k+2):ℝ)) := by
    have h2': ∑ k in range (n + 1), (Nat.choose n k) * ((-1 : ℝ )^k / (((k+1):ℝ)*((k+2):ℝ))) = ∑ k in range (n + 1), (Nat.choose n k) * (-1 : ℝ )^k * (1/((k+1):ℝ)-1/((k+2):ℝ)) := by
      refine' sum_congr rfl fun y hy => _
      rw[mul_assoc]
      congr 1
      rw[← mul_one ((-1 : ℝ) ^ y)]
      rw[mul_div_assoc]
      rw[h1]
      simp
    rw[h2']
    have h2'' : ∑ k in range (n + 1), (Nat.choose n k) * (-1 : ℝ )^k * (1/((k+1):ℝ)-1/((k+2):ℝ)) = ∑ k in range (n + 1), ((Nat.choose n k) * (-1 : ℝ )^k * (1/((k+1):ℝ)) - (Nat.choose n k) * (-1 : ℝ )^k * ( 1/((k+2):ℝ))) := by
      refine' sum_congr rfl fun y hy => _
      rw[mul_sub]
    have h2''' : ∑ k in range (n + 1), (Nat.choose n k) * (-1 : ℝ )^k * (1/((k+1):ℝ)-1/((k+2):ℝ)) = ∑ k in range (n + 1), (Nat.choose n k) * (-1 : ℝ )^k * (1 / ((k+1):ℝ)) - ∑ k in range (n + 1), (Nat.choose n k) * (-1 : ℝ )^k * (1/((k+2):ℝ)):= by
      rw[h2'']
      rw[sum_sub_distrib]
    rw[h2''']
    have h_div1:∑ k in range (n + 1), (Nat.choose n k) * (-1 : ℝ )^k * (1 / ((k+1):ℝ)) = ∑ k in range (n + 1), (Nat.choose n k) * ((-1 : ℝ )^k  / ((k+1):ℝ)) := by
      refine' sum_congr rfl fun y hy => _
      rw[mul_one_div]
      rw[mul_div_assoc]
    have h_div2:∑ k in range (n + 1), (Nat.choose n k) * (-1 : ℝ )^k * (1 / ((k+2):ℝ)) = ∑ k in range (n + 1), (Nat.choose n k) * ((-1 : ℝ )^k  / ((k+2):ℝ)) := by
      refine' sum_congr rfl fun y hy => _
      rw[mul_one_div]
      rw[mul_div_assoc]
    rw[h_div1,h_div2]
  rw[h2]
  simp
