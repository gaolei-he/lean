import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators


theorem neg_pow_mul_mul_mul : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ (k - 1) * (-1)* n * (choose (n-1) (k-1))  = ∑ k in Ico 1 (n + 1), (-1 : ℤ)*  ((-1) ^ (k - 1) * n * (choose (n-1) (k-1))) := by
  refine' sum_congr rfl fun y _ => _
  rw[mul_comm ((-1 : ℤ) ^ (y - 1)) (-1)]
  rw[mul_assoc,mul_assoc,mul_assoc]


theorem neg_pow_mul_mul_mul_from_1_to_1(n y : ℕ)(x✝ : y ∈ Ico 1 (n + 1))(gol:  -1 * (-1 : ℝ) ^ (y - 1) * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = -1 * ((-1 : ℝ) ^ (y - 1) * ↑n * ↑(Nat.choose (n - 1) (y - 1)))) :
   (-1 : ℝ) ^ (y - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = -1 * ((-1 : ℝ) ^ (y - 1) * ↑n * ↑(Nat.choose (n - 1) (y - 1))) := by
  rw[mul_comm ((-1 : ℤ) ^ (y - 1)) (-1 : ℝ)]
  apply gol

theorem neg_pow_mul_mul_mul_from_1_to_2(n y : ℕ)(x✝ : y ∈ Ico 1 (n + 1)) :
   (-1 : ℝ) ^ (y - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = -1 * ((-1 : ℝ) ^ (y - 1) * ↑n * ↑(Nat.choose (n - 1) (y - 1))) := by
  rw[mul_comm ((-1 : ℤ) ^ (y - 1)) (-1 : ℝ)]
  rw[mul_assoc,mul_assoc,mul_assoc]

theorem neg_pow_mul_mul_mul_from_2_to_2(n y : ℕ)(x✝ : y ∈ Ico 1 (n + 1)) :
   -1 * (-1 : ℝ) ^ (y - 1) * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = -1 * ((-1 : ℝ) ^ (y - 1) * ↑n * ↑(Nat.choose (n - 1) (y - 1))) := by
  rw[mul_assoc,mul_assoc,mul_assoc]

