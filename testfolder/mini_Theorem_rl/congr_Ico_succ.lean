import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem congr_Ico_succ:
  ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1) = ∑ l in Ico 0 n, (l + 1) * choose (n-1) l:= by lean_repl sorry
  rw[sum_Ico_eq_sum_range]
  simp
  refine' sum_congr rfl fun y _ => _
  rw[add_comm]
