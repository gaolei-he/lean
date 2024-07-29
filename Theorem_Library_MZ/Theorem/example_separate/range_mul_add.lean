import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators



theorem range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]


theorem range_mul_add_from_1_to_1(n y : ℕ)(x✝ : y ∈ range n) :
   (y + 1) * Nat.choose (n - 1) y = y * Nat.choose (n - 1) y + 1 * Nat.choose (n - 1) y := by
  rw[Nat.add_mul]

