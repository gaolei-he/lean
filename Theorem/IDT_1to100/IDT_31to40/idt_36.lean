import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic


open Nat

open Finset

open BigOperators

theorem idt4 (n : ℕ) : (∑ m in range (n + 1), choose n m) = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this

theorem idt6_Absorption_Idt {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
    k * choose n k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]


theorem Idt36 {n k m : ℕ } (h1: k ≤ n) (h2 : 1 ≤ k - m) (h3 : m ≤ n)(h4 : 1 ≤ m): (∑ k in Icc 0 n,  (choose n k) * (descFactorial k m)) = (descFactorial n m) * 2 ^(n - m):= by
  have h0 : (∑ k in Icc 0 n,  (choose n k) * (descFactorial k m)) = (∑ k in Icc 0 n, (descFactorial n m) * choose (n - m) (k - m)) := by
    have h2 (k : ℕ): (choose n k) * (descFactorial k m) = (descFactorial n m) * choose (n - m) (k - m) := by
      induction' m with m ih
      · simp
      · have d1 : descFactorial k (succ m) = (k - m) * (descFactorial k m ) := by
          apply descFactorial_succ
        have d2 : descFactorial n (succ m) = (n - m) * descFactorial n m := by
          apply descFactorial_succ
        have ih2 : descFactorial k m * Nat.choose n k =  Nat.choose n k * descFactorial k m := by
          exact Nat.mul_comm (descFactorial k m) (Nat.choose n k)
        rw[d1]
        rw[d2]
        rw[mul_comm]
        rw[mul_assoc , mul_comm]
        rw[ih2]
        rw[ih]
        have d3 : (k - m) * Nat.choose (n - m) (k - m) = (n - m) * Nat.choose (n - succ m) (k - succ m) := by
          apply idt6_Absorption_Idt
          · have l1 : k ≤ n := by
              sorry
            exact Nat.sub_le_sub_right l1 m
          · sorry
        have d4 : (k - m) * Nat.choose (n - m) (k - m) =  Nat.choose (n - m) (k - m) * (k - m) := by
          exact Nat.mul_comm (k - m) (Nat.choose (n - m) (k - m))
        rw[d4] at d3
        rw[mul_assoc]
        rw[d3]
        rw[← mul_assoc]
        rw[mul_assoc]
        rw[mul_comm]
        exact Nat.mul_right_comm (n - m) (Nat.choose (n - succ m) (k - succ m)) (descFactorial n m)
        ·sorry
        ·sorry
        ·sorry
    refine' sum_congr _ fun y _ => h2 (y)
    rfl
  have h1 : (∑ k in Icc 0 n,  (choose n k) * (descFactorial k m)) = (∑ k in Icc m n, (descFactorial n m) * choose (n - m) (k - m)) := by
    have s1 : (∑ k in Icc 0 n,  (choose n k) * (descFactorial k m)) = (∑ k in Icc 0 (m - 1),  (choose n k) * (descFactorial k m)) + (∑ k in Icc m n,  (choose n k) * (descFactorial k m)) := by
      have m1 : Icc 0 n = Ico 0 (n + 1) := by
        exact rfl
      rw[m1]
      have m3 : 0 ≤ m := by
        exact Nat.zero_le m
      have m4 : m ≤ n + 1 := by
        exact le_step h3
      have m5 : Icc 0 (m - 1) = Ico 0 (m - 1 + 1) := by
        exact rfl
      have p1 : m - 1 + 1 = m := by
        rw[Nat.sub_add_cancel h4]
      have m6 : Ico 0 (m - 1 + 1) = Ico 0 m := by
        rw[p1]
      have m7 : Icc 0 (m - 1) = Ico 0 m := by
        exact m6
      have m8 : Icc m n = Ico m (n + 1) := by
        exact rfl
      rw[m7, m8]
      have m9 : ∑ k in Ico m (n + 1), Nat.choose n k * descFactorial k m = (∑ k in range (n + 1), Nat.choose n k * descFactorial k m) - (∑ k in range m, Nat.choose n k * descFactorial k m) := by
        rw[range_eq_Ico]
        sorry
      sorry
    have s2 : (∑ k in Icc 0 (m - 1),  (choose n k) * (descFactorial k m)) = 0 := by
      apply Finset.sum_eq_zero
      rintro x Hi
      norm_num
      have j' : Icc 0 (m - 1) = Ico 0 (m - 1 + 1) := by
        exact rfl
      have c : m - 1 + 1 = m := by
        exact Nat.sub_add_cancel h4
      have j'' : Ico 0 (m - 1 + 1) = Ico 0 m := by
        rw[c]
      have f: Ico 0 m = range m := by
        norm_num
      have j : Icc 0 (m - 1) = range m := by
        rw[j''] at j'
        rw[f] at j'
        exact j'
      have j0 : x ∈ range m := by
        rw[j] at Hi
        exact Hi
      have j1 : x < m := by
        exact Iff.mp List.mem_range j0
      exact Or.inr j1
    rw[s1]
    rw[s2]
    simp
    sorry
  rw[h1]
  have h3' : (∑ k in Icc m n, descFactorial n m * Nat.choose (n - m) (k - m)) = descFactorial n m * (∑ k in Icc m n, Nat.choose (n - m) (k - m)) := by
    rw[mul_sum]
  rw[h3']
  have h4 :  (∑ k in Icc m n, Nat.choose (n - m) (k - m)) = 2 ^ (n - m) := by
    -- simp
    have d1 : (∑ k in Icc m n, Nat.choose (n - m) (k - m)) = (∑ k in range ((n - m) + 1), Nat.choose (n-m) k) := by
      have o1 : (∑ k in Icc m n, Nat.choose (n - m) (k - m)) = (∑ k in Ico m (n + 1), Nat.choose (n - m) (k - m)) := by
        exact rfl
      have o2 : (∑ k in Ico m (n + 1), Nat.choose (n - m) (k - m)) = (∑ k in range (n + 1 - m), Nat.choose (n-m) (m + k -m)):= by
        rw[Finset.sum_Ico_eq_sum_range]
      have o3 : (∑ k in range (n + 1 - m), Nat.choose (n-m) (m + k - m)) = (∑ k in range (n + 1 - m), Nat.choose (n-m) k) := by
        refine' sum_congr rfl fun y hy => _
        rw[Nat.add_sub_cancel_left]
      -- have o3 : (∑ k in Ico 0 (n + 1 - m), Nat.choose (n - m) k) = (∑ k in range (n + 1 - m), Nat.choose (n-m) k) := by
      --   rw[← range_eq_Ico]
      have g1 : n + 1 - m = (n - m) + 1 := by
        exact Nat.sub_add_comm h3
      have o4 : (∑ k in range (n + 1 - m), Nat.choose (n-m) k) = (∑ k in range ((n - m) + 1), Nat.choose (n-m) k) := by
        rw[g1]
      rw[o1]
      rw[o2]
      rw[o3]
      rw[o4]
    rw[d1]
    rw[idt4 ((n-m):ℕ)]
  rw[h4]
