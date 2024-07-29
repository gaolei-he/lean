import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div

open Nat
open Finset
open BigOperators

theorem idt_12 {n : ℕ} :(∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ)) = if n = 0 then 1 else 0 := by
  cases n; · simp
  case succ n =>
    have h := add_pow (-1 : ℤ) 1 n.succ
    simp only [one_pow, mul_one, add_left_neg] at h
    rw [← h, zero_pow (Nat.succ_pos n), if_neg (Nat.succ_ne_zero n)]

theorem idt6_Absorption_Idt {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
    k * choose n k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]

theorem two_eq_one_add_one: 2 = 1+1:=by
  simp
theorem tree_eq_two_add_one: 3= 2+1 :=by
  linarith


theorem f_choose_mul_eq_mul_sub_div (n : ℕ) (k :ℕ) : (((1/(k+1)) : ℝ) * choose n k) = (1/(n+1)) * choose (n+1) (k+1) := by
  have h :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    have h2 : (n + 1) * (k + 1) * ((1 / (n+1)) : ℝ) * (Nat.choose (n + 1) (k + 1))
      = (k + 1) * ((n + 1) * (1 / (n+1)) * (Nat.choose (n + 1) (k + 1))) := by
      rw [←mul_assoc]
      congr 1
      rw [←mul_assoc]
      congr 1
      rw [mul_comm]
    rw [h2]
    rw [←mul_assoc]
    have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
  have h1 : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
          = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
          exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
  have h2 : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
    = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
    exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))
  rw [h1, h2] at h
  have h3 : ((n : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero n
  have h4 : ((k : ℝ) + 1) ≠ 0 := by exact cast_add_one_ne_zero k
  have h5 : ((n : ℝ) + 1) * ((k : ℝ) + 1) ≠ 0 := by exact mul_ne_zero h3 h4
  rw [mul_right_inj' h5] at h
  assumption


theorem choose_mul_eq_mul_sub_div_2 {n k: ℕ} : (((1/(k+2)) : ℝ) * choose (n+1) (k+1)) = (1/(n+2)) * choose (n+2) (k+2) := by
  have h1: 1 / (↑(k + 1) + 1) * ↑(Nat.choose (n + 1) (k + 1)) =  (((1/(k+2)) : ℝ) * choose (n+1) (k+1)) :=by
    simp
    left
    rw [add_assoc]
    simp
    ring
  rw [←h1]
  rw [f_choose_mul_eq_mul_sub_div (n+1) (k+1)]
  simp
  left
  rw [add_assoc]
  simp
  ring

theorem binom_identity_n_1 {n k : ℕ} (hkn: k<=n) : (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k :=by
  let t:= k+1
  have h1: t= k+1 :=by
    simp
  simp [←h1]
  have h2: k = t-1 := by
    simp [tsub_add_tsub_comm]
  rw [h2]
  let m:= n+1
  have h3: m= n+1:=by
    simp
  rw [←h3]
  have h4: n = m-1 :=by
    simp [tsub_add_tsub_comm]
  rw [h4]
  have h_tm: t<=m :=by
    simp
    exact hkn
  have h_sk: 1≤ t :=by
    simp
  exact (idt6_Absorption_Idt h_tm h_sk)
theorem lemma_1 { k : ℕ}: (-1:ℝ) ^ k = (-1:ℝ) ^ (k + 2 -2) := by
  congr

theorem lemma_2 {n : ℕ} : ∑ k in Ico 0 (n+1) , (-1:ℝ) ^ (k +2) * choose (n+2) (k+2) = n+1 :=by
  let f: ℕ → ℝ := fun k =>  (-1:ℝ) ^ k * choose (n+2) k
  rw [sum_Ico_add' f]
  ring_nf
  rw [add_comm 3 n]
  have h₁: ∑ x in Ico 0 (n + 3), f x =  f 0 + f 1 + ∑ x in Ico 2 (n + 3), f x :=by
    rw [sum_eq_sum_Ico_succ_bot,sum_eq_sum_Ico_succ_bot]
    simp
    ring
    linarith

    have hh : 0 + 3 ≤ n + 3 := Nat.add_le_add_right (Nat.zero_le n) 3
    rw [Nat.zero_add] at hh
    exact lt_of_lt_of_le (Nat.zero_lt_succ 2) hh
  have h_2: f 0 = 1 :=by
    ring_nf
    rw [choose_zero_right]
    ring

  have h_3 : f 1 = - (n+2) :=by
    ring_nf
    rw [choose_one_right]
    simp
    ring

  have h_4: ∑ x in Ico 0 (n + 3), f x  = 0 := by
    ring_nf
    rw [←range_eq_Ico]
    rw [add_comm 2 n,add_comm 3 n]
    rw [tree_eq_two_add_one,←add_assoc]

    rw [sum_congr rfl fun a ha => by
      rw [mul_comm]
    ]
    have h0: ∑ a in range (n + 2 + 1), (-1:ℝ) ^ a * (Nat.choose (n + 2) a) = ∑ a in range (n + 2 + 1), (-1:ℤ) ^ a * (Nat.choose (n + 2) a) :=by
      simp
    rw [h0]
    have hn2: (n+2) ≠ 0 :=by
      simp
    rw [Int.alternating_sum_range_choose_of_ne hn2]
    simp

  rw [h_4,h_2,h_3] at h₁
  symm at h₁
  rw [add_comm 1] at h₁
  ring_nf at h₁
  rw [add_comm] at h₁

  rw [sub_eq_neg_add,←neg_add,add_neg_eq_iff_eq_add,zero_add,add_comm 3] at h₁
  symm at h₁
  rw [h₁, sum_congr rfl fun a ha => by
    rw [mul_comm]
  ]
theorem neg_one_pow_add {k:ℕ}: (-1:ℝ) ^ k = (-1:ℝ) ^ (k+2):= by
  rw [pow_add]
  rw [neg_one_pow_two]
  ring


theorem idt_41 { n : ℕ }: ∑ k in Ico 0 (n+1),  (-1:ℝ)^k *  (1/ (k+2)) * (1/ (k+1)) * n.choose (k) = 1 / (n +2 ) :=by
  have l₁:  ∑ k in Ico 0 (n+1),  (-1:ℝ)^k *  (1/ (k+2)) * (1/ (k+1)) * n.choose (k) =
     ∑ k in Ico 0 (n+1),  (-1:ℝ)^k * (1/ (n+1)) * (1/ (k+2)) * (n+1).choose (k+1) := by
      refine' sum_congr rfl fun k _ => _
      rw [mul_assoc,choose_mul_eq_mul_sub_div,← mul_assoc]
      congr 1
      ring
  rw [l₁]

  have l₂: ∑ k in Ico 0 (n+1), (-1:ℝ) ^ k * (1 / (n + 1)) * (1 / (k + 2)) * Nat.choose (n + 1) (k + 1) =
    ∑ k in Ico 0 (n+1),  (-1:ℝ)^k *(n+2).choose (k+2) * (1/ (n+1)) * (1/ (n+2)):= by
      refine' sum_congr rfl fun k _ => _
      rw [mul_assoc,choose_mul_eq_mul_sub_div_2]
      ring
  rw [l₂]

  rw [←sum_mul,←sum_mul]

  have l₃: ∑ k in Ico 0 (n+1), (-1:ℝ) ^ k * (Nat.choose (n + 2) (k + 2)) = (n + 1) :=by
    rw [sum_congr rfl fun k _ => by
      rw [neg_one_pow_add]
    ]
    exact lemma_2

  rw [l₃]
  congr
  rw [← mul_div_assoc,mul_one,div_eq_iff_mul_eq]
  ring
  linarith
  rw [one_div]
