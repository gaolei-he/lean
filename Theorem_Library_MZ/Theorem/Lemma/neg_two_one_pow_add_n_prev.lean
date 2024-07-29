import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.Lemma.nat_sub_add_cancel
import Theorem.Lemma.neg_two_one_pow_add_n



open Nat

open Finset

open BigOperators

lemma neg_two_one_pow_add_n_prev {n:ℕ} (hn: 1 ≤ n) :∑ m in range n,   (-2:ℝ) ^ (m) *(1) ^ ((n-1)-m) * ↑(Nat.choose (n-1) m) = (-1:ℝ)^(n-1) :=by
    have hn_one : n = n-1+1:= by
        rw [←nat_sub_add_cancel hn]
        simp
    nth_rw 1 [hn_one]
    rw [neg_two_one_pow_add_n (n-1)]
