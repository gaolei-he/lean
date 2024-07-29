import Theorem.example_separate.congr_Ico_succ

open Nat

open Finset

open BigOperators

theorem Ico_choose_eq_Ico_choose_add(h : 0 < n): ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1) = ∑ l in Ico 1 n, l * choose (n-1) l + 2 ^ ( n - 1 ):= by   --sum42
  rw[congr_Ico_succ]
  have h': 1 ≤ n := by linarith
  have range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
  have range_sub_add_cancel :  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
      refine' sum_congr _ fun y _ => rfl
      rw[nn]
  have ico_two_pow: ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
    rw[← range_eq_Ico]
    rw[sum_range_choose] at range_sub_add_cancel
    rw[range_sub_add_cancel]
  rw[h_bot h, ico_two_pow]


theorem Ico_choose_eq_Ico_choose_add_from_1_to_1(n : ℕ)(h : 0 < n)(gol:  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have h': 1 ≤ n := by linarith
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_3_to_3(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_3_to_4(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  rw[Ico_mul_add]
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_3_to_5(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_3_to_6(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_3_to_7(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_3_to_8(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_4_to_4(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  rw[Ico_mul_add]
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_4_to_5(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_4_to_6(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_4_to_7(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_4_to_8(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_5_to_5(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_5_to_6(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_5_to_7(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_5_to_8(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_6_to_6(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot :  0 < n → ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  simp at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_6_to_7(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot :  0 < n → ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_6_to_8(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot :  0 < n → ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_7_to_7(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot : 0 < n → ∑ x in range n, x * Nat.choose (n - 1) x = ∑ x in Ico 1 n, x * Nat.choose (n - 1) x)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  rw[range_eq_Ico] at h_bot
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_7_to_8(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot : 0 < n → ∑ x in range n, x * Nat.choose (n - 1) x = ∑ x in Ico 1 n, x * Nat.choose (n - 1) x)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  rw[range_eq_Ico] at h_bot
  have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_8_to_8(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot : 0 < n → ∑ x in Ico 0 n, x * Nat.choose (n - 1) x = ∑ x in Ico 1 n, x * Nat.choose (n - 1) x)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_10_to_10(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot : 0 < n → ∑ x in Ico 0 n, x * Nat.choose (n - 1) x = ∑ x in Ico 1 n, x * Nat.choose (n - 1) x)(nn : n - 1 + 1 = n)(range_sub_add_cancel : ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = ∑ l in range n, Nat.choose (n - 1) l)(gol:  ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have ico_two_pow: ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
    rw[← range_eq_Ico]
    rw[sum_range_choose] at range_sub_add_cancel
    rw[range_sub_add_cancel]
  apply gol

theorem Ico_choose_eq_Ico_choose_add_from_10_to_11(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot : 0 < n → ∑ x in Ico 0 n, x * Nat.choose (n - 1) x = ∑ x in Ico 1 n, x * Nat.choose (n - 1) x)(nn : n - 1 + 1 = n)(range_sub_add_cancel : ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = ∑ l in range n, Nat.choose (n - 1) l) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  have ico_two_pow: ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
    rw[← range_eq_Ico]
    rw[sum_range_choose] at range_sub_add_cancel
    rw[range_sub_add_cancel]
  rw[h_bot h, ico_two_pow]

theorem Ico_choose_eq_Ico_choose_add_from_11_to_11(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(range_mul_add :  ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * Nat.choose (n - 1) l + 1 * Nat.choose (n - 1) l))(Ico_mul_add :  ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l =    ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l)(h_bot : 0 < n → ∑ x in Ico 0 n, x * Nat.choose (n - 1) x = ∑ x in Ico 1 n, x * Nat.choose (n - 1) x)(nn : n - 1 + 1 = n)(range_sub_add_cancel : ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = ∑ l in range n, Nat.choose (n - 1) l)(ico_two_pow : ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n, Nat.choose (n - 1) l =
    ∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1) := by
  rw[h_bot h, ico_two_pow]

