import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat Finset BigOperators


theorem idt25h1: ∑ k in Ico 1 (succ n + 1), ((choose n k / k):ℝ) - choose n (n+1) / (n+1)
                = ∑ k in Ico 1 (n+1), ((choose n k / k):ℝ) := by
                rw [sum_Ico_succ_top]
                simp
                linarith

theorem idt25h2: ∑ k in Ico 1 (succ n + 1), ((Nat.choose n (k-1) / k):ℝ)
              = ∑ k in range (n + 1), ((Nat.choose n k / (k+1)):ℝ) := by
              rw [sum_Ico_eq_sum_range]
              simp
              rw [←add_one]
              refine' sum_congr rfl fun k hk => _
              rw [add_comm]

theorem idt25h3: ∑ k in range (n + 1), ((Nat.choose n k / (k+1)):ℝ)
              = ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k := by
              refine' sum_congr rfl fun k hk => _
              rw [one_div, mul_comm, ←one_div, mul_one_div]


theorem idt_25 {n : ℕ} : ∑ k in Ico 1 (n+1), ((choose n k / k):ℝ) = ∑ k in Ico 1 (n+1), (((2^k - 1) / k):ℝ) := by sorry

theorem idt26h3 : ∑ x in range n, (Nat.choose (n - 1) x) * 2 ^ x * (-1:ℝ) ^ (x + 1) =
            ∑ x in range n, ↑(Nat.choose (n - 1) x) * 2 ^ x * (-1:ℝ) ^ x * (-1:ℝ) :=by
            refine' sum_congr rfl fun k _ => _
            rw [pow_add]
            simp

theorem idt4 (n : ℕ) : (∑ m in range (n + 1), choose n m) = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this


theorem idt6_Absorption_Idt {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
    k * choose n k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]

theorem h_mod:  n + 1 ∣ Nat.choose (n + 1) (k + 1) * (k + 1) := by
      rw[← succ_mul_choose_eq]
      simp

theorem h_choose1: ∑ k in range (n + 1), ((choose n k) * ((1 / (((k + 1):ℝ) * ((k + 2):ℝ))):ℝ)) = ∑ k in range (n + 1), ((1/(n + 1)) * ((((choose (n + 1) (k + 1))) ) * ((1 / (k + 2)):ℝ))) := by sorry

theorem h22: (∑ x in range (n + 1 + 1), (Nat.choose (n + 2) (x + 1): ℝ)) - (choose (n + 2) 1) = ∑ x in range (n + 1), (Nat.choose (n + 2) (x + 2): ℝ) := by
    have zero_lt_succ_succ: 0 < n + 1 + 1 := by linarith
    rw[range_eq_Ico]
    rw[sum_eq_sum_Ico_succ_bot]
    rw[add_assoc,add_comm,add_sub_assoc]
    simp
    rw[one_add_one_eq_two,one_add_one_eq_two]
    rw[range_eq_Ico]
    simp
    rw[sum_Ico_eq_sum_range]
    refine' sum_congr rfl fun y hy ↦ _
    rw[add_comm 1 y]
    exact zero_lt_succ_succ

theorem IDT50h1{ m n k : ℕ } (hnk: k <= n) (hkm : m <=k) : n+1 =  m + (n - m +1) := by
  rw [add_comm m]
  rw [add_assoc]
  rw [add_comm 1]
  rw [←add_assoc]
  rw [tsub_add_cancel_of_le]
  exact Nat.le_trans hkm hnk
