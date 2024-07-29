import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

open Nat Finset BigOperators


-- Mathlib\Data\Nat\Choose\Basic.lean：choose_eq_descFactorial_div_factorial

theorem idt_17 (n k : ℕ) : n.choose k = n.descFactorial k / k ! := by lean_repl sorry
  apply mul_left_cancel₀ (factorial_ne_zero k)
  rw [← descFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_div_cancel' <| factorial_dvd_descFactorial _ _).symm
