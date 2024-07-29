import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.Lemma.neg_two_one_pow_add_n_prev
import Theorem.Lemma.neg_two_pow_nat


open Nat

open Finset

open BigOperators

lemma sum_choose_neg_two_pow {n:ℕ} (hn : 1<=n) : ∑ x in range n, (Nat.choose (n - 1) x) * 2 ^ x * (-1:ℝ) ^ x = (-1:ℝ)^(n-1) :=by
    rw [← neg_two_one_pow_add_n_prev]
    ring_nf
    refine' sum_congr rfl fun x _ ↦ _
    rw[neg_two_pow_nat]
    simp
    symm
    rw [mul_comm]
    rw [mul_assoc]
    exact hn
