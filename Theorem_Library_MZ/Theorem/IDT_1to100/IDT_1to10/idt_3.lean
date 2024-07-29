import Mathlib.Algebra.BigOperators.NatAntidiagonal

open Nat

open Finset

open BigOperators


variable [Semiring R] {x y : R}

theorem idt3_Binomial(h : Commute x y) (n : ℕ) :
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
