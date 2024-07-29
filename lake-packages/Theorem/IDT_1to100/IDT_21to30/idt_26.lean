import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity
open Nat

open Finset

open BigOperators

theorem choose_eq_zero_iff_26(k n : ℕ) (h1: n < k): choose n k = 0 := by
  exact choose_eq_zero_iff.mpr h1

theorem mul_one_26(a:ℤ): a * 1 * 1 = a := by
  have a1:a * 1 = a:=by
    exact mul_one a
  rw[a1]
  rw[a1]

theorem Identity_26(h1 : n = m):
∑ k in range (n + 1), ((-1) ^ k * ↑ (choose n k) : ℤ) * choose k m = (-1) ^ m := by
  have c0:n = m := by
    exact h1
  have c1:∑ k in range (n + 1), ((-1) ^ k * ↑(choose n k) : ℤ) * choose k m = ((-1) ^ n * ↑(choose n n) : ℤ) * choose n m + ∑ k in range n, ((-1) ^ k * ↑(choose n k) : ℤ) * choose k m := by
    exact sum_range_succ_comm (fun x => ((-1) ^ x * ↑(Nat.choose n x) : ℤ) * ↑(Nat.choose x m)) n
  rw[c1]
  have c2: ∑ k in range n, ((-1) ^ k * ↑(choose n k) : ℤ) * choose k m = ∑ k in range n, ((-1) ^ k * ↑(choose n k) : ℤ) * 0 := by
    have d1(k : ℕ)(h2: k < n)(h3: n = m): choose k m = 0 := by
      have e1: k < n := by
        exact h2
      have e2: n = m := by
        exact h3
      have e3: k < m := by
        exact Nat.lt_of_lt_of_eq h2 h3
      exact choose_eq_zero_iff_26 m k e3
    have d2: n = m := by
      exact h1
    refine' sum_congr rfl fun y hy => _
    have d3: y < n := by
      exact List.mem_range.mp hy
    rw[d1]
    exact rfl
    · exact d3
    · exact d2
  rw[c2]
  have c3: ∑ k in range n, ((-1) ^ k * ↑(choose n k) : ℤ) * 0 = 0 := by
    have d4(k : ℕ): ((-1) ^ k * ↑(choose n k) : ℤ) * 0 = 0 := by
      exact Int.mul_zero ((-1) ^ k * ↑(Nat.choose n k))
    have d5:∑ k in range n, ((-1) ^ k * ↑(choose n k) : ℤ) * 0 = ∑ k in range n,0:= by
      refine' sum_congr rfl fun y hy => _
      rw[d4]
    rw[d5]
    have d6:∑ k in range n, 0  =  ∑ k in range n, k * 0:= by
      have e4(k:ℕ): 0 = k * 0 := by
        exact rfl
      refine' sum_congr rfl fun y hy => _
      exact e4 y
    have d7: ∑ k in range n, k * 0 = 0:=by
      exact sum_range_induction (fun k => k * 0) (fun {n} => 0) rfl (congrFun rfl) n
    linarith
  rw[c3]
  have c4(h4:n = m): ((-1) ^ n * ↑(choose n n) : ℤ) * choose n m = (-1) ^ m := by
    have d10(h6:n = m):((-1) ^ n * ↑(choose n n) : ℤ) * choose n m = ((-1) ^ n * 1) * 1 := by
      have d8: choose n n = 1 := by
        exact choose_self n
      have d9(h5:n = m): choose n m = 1 := by
        have e5: n = m := by
          exact h5
        have e6: choose m m = 1 := by
          exact choose_self m
        have e7: choose n m = choose m m := by
          exact (Nat.bit1_inj (congrArg bit1 (congrFun (congrArg Nat.choose (id h1.symm)) m))).symm
        linarith
      have d11: (↑(choose n n) : ℤ) = 1 := by
        exact congrArg Nat.cast d8
      rw[d11]
      rw[d9]
      exact rfl
      exact h6
    rw[d10]
    have d11(h7:n = m):((-1:ℤ) ^ n * 1) * 1 = (-1) ^ m := by
      have e8: n = m:= by
        exact h7
      rw[e8]
      exact mul_one_26 ((-1) ^ m)
    exact d11 h1
    exact h1
  rw[c4]
  linarith
  apply c0
