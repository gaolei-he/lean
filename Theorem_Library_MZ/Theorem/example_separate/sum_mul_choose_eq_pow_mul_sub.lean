import Theorem.example_separate.sum_mul_choose_eq_two_pow'
import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem sum_mul_choose_eq_pow_mul_sub (n : ℕ) (h : 1 ≤ n) : ∑ k in range (n+1), k * choose (2*n+1) (n-k) = (((2*n+1) * choose (2*n-1) n - 2^(2*n-1)) : ℝ) :=
  calc
    ∑ k in range (n+1), k * choose (2*n+1) (n-k)
      = ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n+1) (n-k) := by
      {
        rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n + 1) (n - x)]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
        congr 1
        norm_num
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n+1) (n-k) := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc]
      }
    _ = (-1 : ℝ) * ∑ k in range (n + 1), (↑(n + 1 - 1 - k) - ↑n) * ↑(Nat.choose (2 * n + 1) (n + 1 - 1 - k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        rw [mem_range] at hk
        rw [←cast_sub]
        simp
        linarith
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), (k-(n:ℝ)) * choose (2*n+1) k := by
      {
        congr 1
        rw [sum_range_reflect (fun x => (x-(n:ℝ)) * choose (2*n+1) x) (n+1)]
      }
    _ = ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n+1) k := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [←neg_one_mul (k-(n:ℝ))]
        rw [mul_assoc]
      }
    _ = ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n+1) k := by
      {
        refine' sum_congr rfl fun k hk => _
        congr 1
        exact neg_sub (k:ℝ) (n:ℝ)
      }
    _ = ∑ k in range (n+1), ((n:ℝ) * choose (2*n+1) k - k * choose (2*n+1) k) := by
      {
        refine' sum_congr rfl fun k hk => _
        rw [sub_mul]
      }
    _ = ∑ k in range (n+1), (n:ℝ) * choose (2*n+1) k - ∑ k in range (n+1), k * choose (2*n+1) k := by
      {
        rw [sum_sub_distrib]
        congr 1
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n + 1) x]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (∑ k in range (n+1), n * choose (2*n+1) k) - (∑ k in range (n+1), k * choose (2*n+1) k) := by -- 这里是在变换数据类型
      {
        rw [cast_sum (range (n+1)) fun x => n * Nat.choose (2 * n + 1) x]
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (n*2^(2*n)) - ((n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n) : ℝ) := by
      {
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n + 1) x]
        simp_rw [cast_mul]
        rw [sum_mul_choose_eq_two_pow' n h]
        congr 1
        rw [←mul_sum, sum_range_choose_halfway n]
        have : 4 = 2^2 := by exact rfl
        rw [this, ←pow_mul, cast_mul, cast_pow]
        congr 1
      }
    _ = (2*n+1) * choose (2*n-1) n - 2^(2*n-1) := by
      {
        rw [←add_sub, ←sub_sub, sub_self, ←sub_add, add_comm]
        congr 1
        simp
      }


theorem sum_mul_choose_eq_pow_mul_sub_from_0_to_0(n : ℕ)(h : 1 ≤ n)(gol:  ∑ x in range (n + 1), ↑(x * Nat.choose (2 * n + 1) (n - x)) =
    ∑ k in range (n + 1), -1 * (↑n - ↑k - ↑n) * ↑(Nat.choose (2 * n + 1) (n - k))) :
   ↑(∑ k in range (n + 1), k * Nat.choose (2 * n + 1) (n - k)) =
    ∑ k in range (n + 1), -1 * (↑n - ↑k - ↑n) * ↑(Nat.choose (2 * n + 1) (n - k)) := by
  rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n + 1) (n - x)]
  apply gol

theorem sum_mul_choose_eq_pow_mul_sub_from_2_to_2(n : ℕ)(h : 1 ≤ n)(k : ℕ)(hk : k ∈ range (n + 1))(gol:  ↑k * ↑(Nat.choose (2 * n + 1) (n - k)) = -1 * (↑n - ↑k - ↑n) * ↑(Nat.choose (2 * n + 1) (n - k))) :
   ↑(k * Nat.choose (2 * n + 1) (n - k)) = -1 * (↑n - ↑k - ↑n) * ↑(Nat.choose (2 * n + 1) (n - k)) := by
  rw [cast_mul]
  apply gol

theorem sum_mul_choose_eq_pow_mul_sub_from_4_to_4(n : ℕ)(h : 1 ≤ n)(k : ℕ)(hk : k ∈ range (n + 1)) :
   ↑k = -1 * (↑n - ↑k - ↑n) := by
  norm_num

