import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Theorem.Lemma.harmonic
import Theorem.IDT_1to100.IDT_21to30.idt_24


open Nat
open Finset
open BigOperators



theorem idt_24' {n:ℕ} : ∑ k in Ico 0 (n+1), n.choose k * (-1:ℝ)^k / (k+1) = 1 / (n+1) :=by
  rw [← idt_24]
  rw [range_eq_Ico]
  refine' sum_congr rfl fun x hx => _
  rw [mul_comm,div_eq_mul_one_div]
  rw [mul_assoc]
  congr 1
  rw [mul_comm]
