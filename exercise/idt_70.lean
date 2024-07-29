import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic


open Nat Finset BigOperators


theorem idt_70 (n k : ℕ)(hn: n > 0)(hk: k > 0) : multichoose n k = n.multichoose (k - 1) + (n - 1).multichoose k := by
  -- rw[multichoose_eq]
  have hn1:1 ≤ n := by linarith
  have hk1:1 ≤ k := by linarith
  rw[← Nat.sub_add_cancel hn1, ← Nat.sub_add_cancel hk1]
  rw[multichoose_succ_succ]
  simp
  rw[add_comm]
