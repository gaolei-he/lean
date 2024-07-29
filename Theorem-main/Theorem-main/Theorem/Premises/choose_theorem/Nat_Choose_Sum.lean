/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.NatAntidiagonal

#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.

-/

open Nat

open Finset

open BigOperators

variable {R : Type*}

namespace Commute

variable [Semiring R] {x y : R}

/-- A version of the **binomial theorem** for commuting elements in noncommutative semirings. -/
theorem add_pow (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m := by
  let t : ℕ → ℕ → R := fun n m ↦ x ^ m * y ^ (n - m) * choose n m
  change (x + y) ^ n = ∑ m in range (n + 1), t n m
  have h_first : ∀ n, t n 0 = y ^ n := fun n ↦ by
    simp only [choose_zero_right, _root_.pow_zero, Nat.cast_one, mul_one, one_mul, tsub_zero]
  have h_last : ∀ n, t n n.succ = 0 := fun n ↦ by
    simp only [ge_iff_le, choose_succ_self, cast_zero, mul_zero]
  have h_middle :
    ∀ n i : ℕ, i ∈ range n.succ → (t n.succ ∘ Nat.succ) i =
      x * t n i + y * t n i.succ := by
    intro n i h_mem
    have h_le : i ≤ n := Nat.le_of_lt_succ (mem_range.mp h_mem)
    dsimp only
    rw [Function.comp_apply, choose_succ_succ, Nat.cast_add, mul_add]
    congr 1
    · rw [pow_succ x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc]
    · rw [← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).eq]
      by_cases h_eq : i = n
      · rw [h_eq, choose_succ_self, Nat.cast_zero, mul_zero, mul_zero]
      · rw [succ_sub (lt_of_le_of_ne h_le h_eq)]
        rw [pow_succ y, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  induction' n with n ih
  · rw [_root_.pow_zero, sum_range_succ, range_zero, sum_empty, zero_add]
    dsimp only
    rw [_root_.pow_zero, _root_.pow_zero, choose_self, Nat.cast_one, mul_one, mul_one]
  · rw [sum_range_succ', h_first]
    erw [sum_congr rfl (h_middle n), sum_add_distrib, add_assoc]
    rw [pow_succ (x + y), ih, add_mul, mul_sum, mul_sum]
    congr 1
    rw [sum_range_succ', sum_range_succ, h_first, h_last, mul_zero, add_zero, _root_.pow_succ]
#align commute.add_pow Commute.add_pow

/-- A version of `Commute.add_pow` that avoids ℕ-subtraction by summing over the antidiagonal and
also with the binomial coefficient applied via scalar action of ℕ. -/
theorem add_pow' (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m in antidiagonal n, choose n m.fst • (x ^ m.fst * y ^ m.snd) := by
  simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun m p ↦ choose n m • (x ^ m * y ^ p),
    _root_.nsmul_eq_mul, cast_comm, h.add_pow]
#align commute.add_pow' Commute.add_pow'

end Commute

/-- The **binomial theorem** -/
theorem add_pow [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
  (Commute.all x y).add_pow n
#align add_pow add_pow

namespace Nat

/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) : (∑ m in range (n + 1), choose n m) = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this
#align nat.sum_range_choose Nat.sum_range_choose

theorem sum_range_choose_halfway (m : Nat) : (∑ i in range (m + 1), choose (2 * m + 1) i) = 4 ^ m :=
  have : (∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i)) =
      ∑ i in range (m + 1), choose (2 * m + 1) i :=
    sum_congr rfl fun i hi ↦ choose_symm <| by linarith [mem_range.1 hi]
  mul_right_injective₀ two_ne_zero <|
    calc
      (2 * ∑ i in range (m + 1), choose (2 * m + 1) i) =
          (∑ i in range (m + 1), choose (2 * m + 1) i) +
            ∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i) := by rw [two_mul, this]
      _ = (∑ i in range (m + 1), choose (2 * m + 1) i) +
            ∑ i in Ico (m + 1) (2 * m + 2), choose (2 * m + 1) i := by
        { rw [range_eq_Ico, sum_Ico_reflect]
          · congr
            have A : m + 1 ≤ 2 * m + 1 := by linarith
            rw [add_comm, add_tsub_assoc_of_le A, ← add_comm]
            congr
            rw [tsub_eq_iff_eq_add_of_le A]
            ring
          · linarith }
      _ = ∑ i in range (2 * m + 2), choose (2 * m + 1) i := sum_range_add_sum_Ico _ (by linarith)
      _ = 2 ^ (2 * m + 1) := sum_range_choose (2 * m + 1)
      _ = 2 * 4 ^ m := by rw [pow_succ, pow_mul, mul_comm]; rfl
#align nat.sum_range_choose_halfway Nat.sum_range_choose_halfway

theorem choose_middle_le_pow (n : ℕ) : choose (2 * n + 1) n ≤ 4 ^ n := by
  have t : choose (2 * n + 1) n ≤ ∑ i in range (n + 1), choose (2 * n + 1) i :=
    single_le_sum (fun x _ ↦ by linarith) (self_mem_range_succ n)
  simpa [sum_range_choose_halfway n] using t
#align nat.choose_middle_le_pow Nat.choose_middle_le_pow

theorem four_pow_le_two_mul_add_one_mul_central_binom (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * choose (2 * n) n :=
  calc
    4 ^ n = (1 + 1) ^ (2 * n) := by norm_num [pow_mul]
    _ = ∑ m in range (2 * n + 1), choose (2 * n) m := by simp [add_pow]
    _ ≤ ∑ m in range (2 * n + 1), choose (2 * n) (2 * n / 2) := by gcongr; apply choose_le_middle
    _ = (2 * n + 1) * choose (2 * n) n := by simp
#align nat.four_pow_le_two_mul_add_one_mul_central_binom Nat.four_pow_le_two_mul_add_one_mul_central_binom

end Nat

theorem Int.alternating_sum_range_choose {n : ℕ} :
    (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ)) = if n = 0 then 1 else 0 := by
  cases n; · simp
  case succ n =>
    have h := add_pow (-1 : ℤ) 1 n.succ
    simp only [one_pow, mul_one, add_left_neg] at h
    rw [← h, zero_pow (Nat.succ_pos n), if_neg (Nat.succ_ne_zero n)]
#align int.alternating_sum_range_choose Int.alternating_sum_range_choose

theorem Int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
    (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ)) = 0 := by
  rw [Int.alternating_sum_range_choose, if_neg h0]
#align int.alternating_sum_range_choose_of_ne Int.alternating_sum_range_choose_of_ne