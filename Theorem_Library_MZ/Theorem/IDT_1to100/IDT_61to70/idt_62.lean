import Mathlib.Data.Nat.Choose.Basic


open Nat


theorem idt62_multichoose_eq : ∀ n k : ℕ, multichoose n k = (n + k - 1).choose k
  | _, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    have : n + (k + 1) < (n + 1) + (k + 1) := add_lt_add_right (Nat.lt_succ_self _) _
    have : (n + 1) + k < (n + 1) + (k + 1) := add_lt_add_left (Nat.lt_succ_self _) _
    erw [multichoose_succ_succ, add_comm, Nat.succ_add_sub_one, ← add_assoc, Nat.choose_succ_succ]
    simp [idt62_multichoose_eq n (k+1), idt62_multichoose_eq (n+1) k]
  termination_by idt62_multichoose_eq a b => a + b
  decreasing_by { assumption }
