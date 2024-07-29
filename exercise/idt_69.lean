import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic


open Nat Finset BigOperators


theorem idt_69 (n k : ℕ)(hn: n > 0) : multichoose n k = (n-1).ascFactorial k / k.factorial := by
  rw[multichoose_eq]
  rw[← choose_eq_asc_factorial_div_factorial]
  rw[Nat.sub_add_comm]
  have h1 : 1 ≤ n := by linarith
  exact h1
