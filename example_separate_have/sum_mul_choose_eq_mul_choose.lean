import Theorem.example_separate.sum_mul_choose_eq_mul_two_pow
import Theorem.example_separate.sum_choose_eq_pow_add'

open Nat

open Finset

open BigOperators


theorem sum_mul_choose_eq_mul_choose (n : ℕ) (h : 1 ≤ n): ∑ k in range (n+1), k * choose (2*n) (n-k) = ((n * choose (2*n-1) n) : ℝ) := by
  calc
    ∑ k in range (n+1), k * choose (2*n) (n-k)
      = ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n) (n-k) := by
      {
        rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n) (n - x)]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
        congr 1
        norm_num
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n) (n-k) := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc]
      }
    _ = (-1 : ℝ) * ∑ k in range (n + 1), (↑(n + 1 - 1 - k) - ↑n) * ↑(Nat.choose (2 * n) (n + 1 - 1 - k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        rw [mem_range] at hk
        rw [←cast_sub]
        simp
        linarith
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), (k-(n:ℝ)) * choose (2*n) k := by
      {
        congr 1
        rw [sum_range_reflect (fun x => (x-(n:ℝ)) * choose (2*n) x) (n+1)]
      }
    _ = ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n) k := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [←neg_one_mul (k-(n:ℝ))]
        rw [mul_assoc]
      }
    _ = ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n) k := by
      {
        refine' sum_congr rfl fun k hk => _
        congr 1
        exact neg_sub (k:ℝ) (n:ℝ)
      }
    _ = ∑ k in range (n+1), ((n:ℝ) * choose (2*n) k - k * choose (2*n) k) := by
      {
        refine' sum_congr rfl fun k hk => _
        rw [sub_mul]
      }
    _ = ∑ k in range (n+1), (n:ℝ) * choose (2*n) k - ∑ k in range (n+1), k * choose (2*n) k := by
      {
        rw [sum_sub_distrib]
        congr 1
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n) x]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (∑ k in range (n+1), n * choose (2*n) k) - (∑ k in range (n+1), k * choose (2*n) k) := by -- 这里是在变换数据类型
      {
        rw [cast_sum (range (n+1)) fun x => n * Nat.choose (2 * n) x]
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = ∑ k in range (n+1), n * choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 1
        have : 0 < n := by linarith
        rw [sum_mul_choose_eq_mul_two_pow this]
      }
    _ = n * ∑ k in range (n+1), choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 1
        rw [←cast_mul,mul_sum]
      }
    _ = n * ((2^(2*n-1)) + (((1/2):ℝ) * choose (2*n) n)) - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 2
        rw [sum_choose_eq_pow_add' n h]
      }
    _ =  n * (((1/2):ℝ) * choose (2*n) n) := by
      {
        rw [mul_add]
        rw [add_comm]
        simp
      }
    _ = n * ((1/2):ℝ) * ((2*n)! / ((n)! * (2*n -n)!)) := by
      {
        rw [choose_eq_factorial_div_factorial]
        rw [←mul_assoc,←cast_mul, ←cast_div]
        rw [two_mul, Nat.add_sub_cancel]
        exact factorial_mul_factorial_dvd_factorial_add n n
        rw [two_mul, Nat.add_sub_cancel]
        rw [cast_ne_zero]
        exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero n)
        linarith
      }
    _ = n * ((1/2):ℝ) * (((2:ℕ)*n-1+1)*((2:ℕ)*n-1)! / (n ! * n !)) := by
      {
        congr 1
        have : 2*n = 2*n-1+1 := by
          have : 1 ≤ 2*n := by rw [two_mul];linarith
          rw [Nat.sub_add_cancel this]
        rw [this]
        rw [Nat.factorial_succ (2*n-1)]
        rw [←this, cast_mul, ←cast_mul 2 n]
        rw [sub_add_cancel]
        congr 3
        rw [two_mul, Nat.add_sub_cancel]

      }
    _ = n * (((1/2):ℝ) * ((2:ℕ)*n)*((2:ℕ)*n-1)! / (n ! * n !)) := by
      {
        rw [sub_add_cancel, mul_assoc]
        congr 1
        rw [←cast_mul,←cast_mul,←cast_mul,←mul_div_assoc]
        congr 1
        rw [cast_mul,←mul_assoc]
      }
    _ = n * (n * ((2:ℕ)*n-1)! / (n ! * n !)) := by simp
    _ = n * (n * ((2:ℕ)*n-1)! / (n ! * (n * (n-1) !))) := by
      {
        congr 3
        have : n = n-1+1 := by rw [Nat.sub_add_cancel h]
        rw [this,Nat.factorial_succ (n-1)]
        simp [cast_mul]
      }
    _ = n * (((2:ℕ)*n-1)! / (n ! * (n-1) !)) := by
      {
        congr 1
        rw [mul_comm, mul_div_assoc]
        rw [←cast_mul, ←cast_mul, mul_comm (n !) _, cast_mul]
        rw [div_mul_eq_div_div,cast_mul,div_mul_eq_div_div]
        rw [div_self, ←div_mul_eq_div_div, mul_one_div, mul_comm ((n-1)! : ℝ) _]
        rw [cast_ne_zero]
        linarith
      }
    _ = n * choose (2*n-1) n := by
      {
        congr 1
        have : n-1 = 2*n-1-n := by
          rw [two_mul, Nat.add_sub_assoc h, add_sub_self_left n (n - 1)]
        rw [this]
        rw [choose_eq_factorial_div_factorial, cast_div, cast_mul]
        all_goals (try rw [←this])
        rw [two_mul, Nat.add_sub_assoc h]
        exact factorial_mul_factorial_dvd_factorial_add n (n-1)
        rw [cast_ne_zero]
        exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero (n-1))
        rw [two_mul]
        have h1 : n - 1 + n = n + n - 1 := by exact tsub_add_eq_add_tsub h
        rw [←h1]
        exact Nat.le_add_left n (n - 1)
      }
