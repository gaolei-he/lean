import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by lean_repl sorry
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]
