import Theorem.example_separate.congr_Ico_succ

open Nat

open Finset

open BigOperators

theorem Ico_choose_eq_Ico_choose_add(h : 0 < n): ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1) = ∑ l in Ico 1 n, l * choose (n-1) l + 2 ^ ( n - 1 ):= by   --sum42
  rw[congr_Ico_succ]
  have h': 1 ≤ n := by linarith
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   have range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  have ico_two_pow: ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
    rw[← range_eq_Ico]
    have range_sub_add_cancel :  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
      refine' sum_congr _ fun y _ => rfl
      have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
      rw[nn]
    rw[sum_range_choose] at range_sub_add_cancel
    rw[range_sub_add_cancel]
  rw[h_bot h, ico_two_pow]
