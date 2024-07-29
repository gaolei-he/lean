import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
  rw[← range_eq_Ico]
  have range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]
  rw[range_mul_add]
  rw[sum_add_distrib]
  simp


theorem Ico_mul_add_from_0_to_0(n : ℕ)(gol:  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =
    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l := by
  rw[← range_eq_Ico]
  apply gol

theorem Ico_mul_add_from_2_to_2(n : ℕ)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l) =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l) :
   ∑ l in range n, (l + 1) * Nat.choose (n - 1) l =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l := by
  rw[range_mul_add]
  apply gol

theorem Ico_mul_add_from_2_to_3(n : ℕ)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ x in range n, x * Nat.choose (n - 1) x + ∑ x in range n, 1 * Nat.choose (n - 1) x =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l) :
   ∑ l in range n, (l + 1) * Nat.choose (n - 1) l =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l := by
  rw[range_mul_add]
  rw[sum_add_distrib]
  apply gol

theorem Ico_mul_add_from_2_to_4(n : ℕ)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l)) :
   ∑ l in range n, (l + 1) * Nat.choose (n - 1) l =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l := by
  rw[range_mul_add]
  rw[sum_add_distrib]
  simp

theorem Ico_mul_add_from_3_to_3(n : ℕ)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ x in range n, x * Nat.choose (n - 1) x + ∑ x in range n, 1 * Nat.choose (n - 1) x =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l) :
   ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l) =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l := by
  rw[sum_add_distrib]
  apply gol

theorem Ico_mul_add_from_3_to_4(n : ℕ)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l)) :
   ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l) =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l := by
  rw[sum_add_distrib]
  simp

theorem Ico_mul_add_from_4_to_4(n : ℕ)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l)) :
   ∑ x in range n, x * Nat.choose (n - 1) x + ∑ x in range n, 1 * Nat.choose (n - 1) x =
    ∑ l in range n, l * Nat.choose (n - 1) l + ∑ l in range n, Nat.choose (n - 1) l := by
  simp

