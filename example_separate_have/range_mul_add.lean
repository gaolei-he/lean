import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators



theorem range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]
