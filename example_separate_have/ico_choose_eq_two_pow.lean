import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators


theorem ico_choose_eq_two_pow(h : 2 ≤ n ) : ∑ s in Ico 0 (n-1), choose (n-2) s = 2 ^ ( n - 2 ) := by
    rw[← range_eq_Ico]
    have range_choose_eq_ico_choose :  ∑ l in range (n-2+1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n-1), choose (n-2) s:= by
      refine' sum_congr _ fun y _ => rfl
      have nn: n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
      rw[nn,range_eq_Ico]
    rw[sum_range_choose] at range_choose_eq_ico_choose
    rw[range_choose_eq_ico_choose,range_eq_Ico]



theorem mul_left_c (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw [← Nat.mul_assoc]
  rw [Nat.mul_comm n m]
  rw [Nat.mul_assoc]


theorem hc(n m k : Nat): n * (m * k) = m * n * k := by
  rw [← Nat.mul_assoc, Nat.mul_comm n m]
theorem mul_left_comm' (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw[hc]
  rw[Nat.mul_assoc]


theorem hn(n m k : Nat): n * m * k = m * (n * k) := by
  rw [Nat.mul_comm n m, Nat.mul_assoc]
theorem mul_left_com (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw [← Nat.mul_assoc]
  rw[hn]


theorem mul_left_c' (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw [← Nat.mul_assoc]
  rw [Nat.mul_assoc]  --候选策略
  rw [Nat.mul_comm n m]
  rw [Nat.mul_assoc]

-- rw[Nat.mul_assoc]
theorem lll(n m k : Nat)(h1:n * m * k = m * (n * k)): n * (m * k) = m * (n * k) := by
  -- rw [← Nat.mul_assoc] at h1
  rw [Nat.mul_assoc] at h1
  rw[h1]

theorem lll'(n m k : Nat)(h1:n * m * k = m * (n * k)): n * (m * k) = m * (n * k) := by
  rw [← Nat.mul_assoc]
  rw[h1]

-- theorem lll''(n m k : Nat)(h1:n * m * k = m * (n * k)): n * (m * k) = m * (n * k) := by
--   rw [← Nat.mul_assoc]
--   rw[h1]
