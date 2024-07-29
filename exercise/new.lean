import Mathlib.Data.Nat.Factorial.Basic

#align_import data.nat.choose.basic from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"


open Nat

namespace Nat

/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. -/
def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)
#align nat.choose Nat.choose

@[simp]
theorem choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n <;> rfl
#align nat.choose_zero_right Nat.choose_zero_right

@[simp]
theorem choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 :=
  rfl
#align nat.choose_zero_succ Nat.choose_zero_succ

theorem choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) :=
  rfl
#align nat.choose_succ_succ Nat.choose_succ_succ

theorem choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, k + 1, _ => choose_zero_succ _
  | n + 1, k + 1, hk => by
    have hnk : n < k := lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [choose_succ_succ, choose_eq_zero_of_lt hnk, choose_eq_zero_of_lt hnk1]
#align nat.choose_eq_zero_of_lt Nat.choose_eq_zero_of_lt

@[simp]
theorem choose_self (n : ℕ) : choose n n = 1 := by
  induction n <;>
  simp [*, choose]
  simp[choose_eq_zero_of_lt (lt_succ_self _)]
#align nat.choose_self Nat.choose_self

@[simp]
theorem choose_succ_self (n : ℕ) : choose n (succ n) = 0 :=
  choose_eq_zero_of_lt (lt_succ_self _)
#align nat.choose_succ_self Nat.choose_succ_self

@[simp]
theorem choose_one_right (n : ℕ) : choose n 1 = n := by 
  induction n <;> 
  simp [*, choose]
  simp [add_comm]
#align nat.choose_one_right Nat.choose_one_right

-- The `n+1`-st triangle number is `n` more than the `n`-th triangle number
theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rw [← add_mul_div_left, mul_comm 2 n, ← mul_add, add_tsub_cancel_right, mul_comm]
  cases n <;> rfl; apply zero_lt_succ
#align nat.triangle_succ Nat.triangle_succ

/-- `choose n 2` is the `n`-th triangle number. -/
theorem choose_two_right (n : ℕ) : choose n 2 = n * (n - 1) / 2 := by
  induction' n with n ih
  · simp
  · rw [triangle_succ n, choose, ih]
    simp [add_comm]
#align nat.choose_two_right Nat.choose_two_right

theorem choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
  | 0, _, hk => by rw [Nat.eq_zero_of_le_zero hk]; decide
  | n + 1, 0, _ => by simp
  | n + 1, k + 1, hk => by
    rw [choose_succ_succ]
    exact add_pos_of_pos_of_nonneg (choose_pos (le_of_succ_le_succ hk)) (Nat.zero_le _)
#align nat.choose_pos Nat.choose_pos

theorem choose_eq_zero_iff {n k : ℕ} : n.choose k = 0 ↔ n < k :=
  ⟨fun h => lt_of_not_ge (mt Nat.choose_pos h.symm.not_lt), Nat.choose_eq_zero_of_lt⟩
#align nat.choose_eq_zero_iff Nat.choose_eq_zero_iff

theorem succ_mul_choose_eq : ∀ n k, succ n * choose n k = choose (succ n) (succ k) * succ k
  | 0, 0 => by decide
  | 0, k + 1 => by simp [choose]
  | n + 1, 0 => by simp [choose, mul_succ, succ_eq_add_one, add_comm]
  | n + 1, k + 1 => by
    rw [choose_succ_succ (succ n) (succ k), add_mul, ← succ_mul_choose_eq n, mul_succ, ←
      succ_mul_choose_eq n, add_right_comm, ← mul_add, ← choose_succ_succ, ← succ_mul]
#align nat.succ_mul_choose_eq Nat.succ_mul_choose_eq

theorem choose_mul_factorial_mul_factorial : ∀ {n k}, k ≤ n → choose n k * k ! * (n - k)! = n !
  | 0, _, hk => by simp [Nat.eq_zero_of_le_zero hk]
  | n + 1, 0, _ => by simp
  | n + 1, succ k, hk => by
    cases' lt_or_eq_of_le hk with hk₁ hk₁
    · have h : choose n k * k.succ ! * (n - k)! = (k + 1) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk)]
        simp [factorial_succ, mul_comm, mul_left_comm, mul_assoc]
      have h₁ : (n - k)! = (n - k) * (n - k.succ)! := by
        rw [← succ_sub_succ, succ_sub (le_of_lt_succ hk₁), factorial_succ]
      have h₂ : choose n (succ k) * k.succ ! * ((n - k) * (n - k.succ)!) = (n - k) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁)]
        simp [factorial_succ, mul_comm, mul_left_comm, mul_assoc]
      have h₃ : k * n ! ≤ n * n ! := Nat.mul_le_mul_right _ (le_of_succ_le_succ hk)
      rw [choose_succ_succ, add_mul, add_mul, succ_sub_succ, h, h₁, h₂, add_mul, tsub_mul,
        factorial_succ, ← add_tsub_assoc_of_le h₃, add_assoc, ← add_mul, add_tsub_cancel_left,
        add_comm]
    · rw [hk₁]; simp [hk₁, mul_comm, choose, tsub_self]
#align nat.choose_mul_factorial_mul_factorial Nat.choose_mul_factorial_mul_factorial

theorem choose_mul {n k s : ℕ} (hkn : k ≤ n) (hsk : s ≤ k) :
    n.choose k * k.choose s = n.choose s * (n - s).choose (k - s) :=
  have h : (n - k)! * (k - s)! * s ! ≠ 0 := by apply_rules [factorial_ne_zero, mul_ne_zero]
  mul_right_cancel₀ h <|
  calc
    n.choose k * k.choose s * ((n - k)! * (k - s)! * s !) =
        n.choose k * (k.choose s * s ! * (k - s)!) * (n - k)! :=
      by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc _ s !, mul_assoc, mul_comm (n - k)!,
        mul_comm s !]
    _ = n ! :=
      by rw [choose_mul_factorial_mul_factorial hsk, choose_mul_factorial_mul_factorial hkn]
    _ = n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) :=
      by rw [choose_mul_factorial_mul_factorial (tsub_le_tsub_right hkn _),
        choose_mul_factorial_mul_factorial (hsk.trans hkn)]
    _ = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s !) :=
      by rw [tsub_tsub_tsub_cancel_right hsk, mul_assoc, mul_left_comm s !, mul_assoc,
        mul_comm (k - s)!, mul_comm s !, mul_right_comm, ← mul_assoc]
#align nat.choose_mul Nat.choose_mul

theorem choose_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
    choose n k = n ! / (k ! * (n - k)!) := by
  rw [← choose_mul_factorial_mul_factorial hk, mul_assoc]
  exact (mul_div_left _ (mul_pos (factorial_pos _) (factorial_pos _))).symm
#align nat.choose_eq_factorial_div_factorial Nat.choose_eq_factorial_div_factorial

theorem add_choose (i j : ℕ) : (i + j).choose j = (i + j)! / (i ! * j !) := by
  rw [choose_eq_factorial_div_factorial (Nat.le_add_left j i), add_tsub_cancel_right, mul_comm]
#align nat.add_choose Nat.add_choose

theorem add_choose_mul_factorial_mul_factorial (i j : ℕ) :
    (i + j).choose j * i ! * j ! = (i + j)! := by
  rw [← choose_mul_factorial_mul_factorial (Nat.le_add_left _ _), add_tsub_cancel_right,
    mul_right_comm]
#align nat.add_choose_mul_factorial_mul_factorial Nat.add_choose_mul_factorial_mul_factorial

@[simp]
theorem choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := by
  rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial (Nat.sub_le _ _),
    tsub_tsub_cancel_of_le hk, mul_comm]
#align nat.choose_symm Nat.choose_symm

theorem choose_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : Nat.choose n a = Nat.choose n b := by
  suffices choose n (n - b) = choose n b by
    rw [h, add_tsub_cancel_right] at this; rwa [h]
  exact choose_symm (h ▸ le_add_left _ _)
#align nat.choose_symm_of_eq_add Nat.choose_symm_of_eq_add

theorem choose_symm_add {a b : ℕ} : choose (a + b) a = choose (a + b) b :=
  choose_symm_of_eq_add rfl
#align nat.choose_symm_add Nat.choose_symm_add

theorem choose_symm_half (m : ℕ) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m := by
  apply choose_symm_of_eq_add
  rw [add_comm m 1, add_assoc 1 m m, add_comm (2 * m) 1, two_mul m]
#align nat.choose_symm_half Nat.choose_symm_half



theorem factorial_mul_factorial_dvd_factorial {n k : ℕ} (hk : k ≤ n) : k ! * (n - k)! ∣ n ! := by
  rw [← choose_mul_factorial_mul_factorial hk, mul_assoc]; exact dvd_mul_left _ _
#align nat.factorial_mul_factorial_dvd_factorial Nat.factorial_mul_factorial_dvd_factorial


end Nat
