import Lean4Repl
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Associated
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupPower.Identities
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Parity
import Mathlib.Data.List.Intervals
import Mathlib.Data.List.Palindrome
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.Data.PNat.Basic
import Mathlib.Data.PNat.Prime
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LocallyFinite
import Mathlib.Order.WellFounded
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.NNReal
import Mathlib.Algebra.Associated
import Mathlib.Algebra.Parity
import Mathlib.Data.Int.Dvd.Basic
import Mathlib.Data.Int.Units
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Real.Basic

set_option trace.aesop true
set_option trace.aesop.proof true
set_option maxHeartbeats 999999999999999999999999
open Nat Real Rat BigOperators Function Finset Bool


theorem hk1 (k : ℕ) (h0 : 2 ≤ k) : k-2+1 = k-1 := by
  rw [←one_add_one_eq_two, ←Nat.sub_sub, Nat.sub_add_cancel]
  exact le_sub_one_of_lt h0

theorem hh02 (k : ℕ) (h0 : 2 ≤ k) : k*(k-1)*(k-2)! = k ! := by
  rw [←h21 k h0, mul_assoc]
  rw [←Nat.factorial_succ (k-2), h22 k h0]
  nth_rw 1 [←h23 k h0]
  rw [←Nat.factorial_succ (k-1)]
  rw [←add_one, h23 k h0]

theorem hk25 : n - 2 = k - 2 + (n - k) := by
    rw [←Nat.sub_add_comm, ←Nat.add_sub_assoc h1]
    norm_num

theorem idt2 {n k : ℕ} (hk : k ≤ n) :
    choose n k = n ! / (k ! * (n - k)!) := by
  rw [← choose_mul_factorial_mul_factorial hk, mul_assoc]
  exact (mul_div_left _ (mul_pos (factorial_pos _) (factorial_pos _))).symm


theorem idt20 {n k : ℕ} (hk : k ≤ n):Nat.choose n k = Nat.choose n k * (k ! * (n - k)!) / (k ! * (n - k)!):= by sorry

theorem idt4 (n : ℕ) : (∑ m in range (n + 1), choose n m) = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this


theorem idt5_Symm {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := by
  rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial (Nat.sub_le _ _),
    tsub_tsub_cancel_of_le hk, mul_comm]


theorem idt6_Absorption_Idt {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
    k * choose n k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]

theorem choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]

theorem choose_mul_right : k * Nat.choose n k = n * Nat.choose (n - 1) (k - 1) := by sorry

theorem idt7_Trinomial_Revi {n k s : ℕ} (hkn : k ≤ n) (hsk : s ≤ k) :
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

theorem h7 : (n - k)! * (k - s)! * s ! ≠ 0 := by apply_rules [factorial_ne_zero, mul_ne_zero]

theorem h70 : n.choose k * k.choose s * ((n - k)! * (k - s)! * s !) =
        n.choose k * (k.choose s * s ! * (k - s)!) * (n - k)! :=
      by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc _ s !, mul_assoc, mul_comm (n - k)!,
        mul_comm s !]

theorem h71 {n k s : ℕ}(hkn : k ≤ n) (hsk : s ≤ k) :
        n.choose k * (k.choose s * s ! * (k - s)!) * (n - k)! = n ! :=
      by rw [choose_mul_factorial_mul_factorial hsk, choose_mul_factorial_mul_factorial hkn]

theorem h72 {n k s : ℕ}(hkn : k ≤ n) (hsk : s ≤ k) :
        n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) = n ! :=
      by rw [choose_mul_factorial_mul_factorial (tsub_le_tsub_right hkn _),
        choose_mul_factorial_mul_factorial (hsk.trans hkn)]

theorem h73 {n k s : ℕ}(hkn : k ≤ n) (hsk : s ≤ k) :
        n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s !) :=
      by rw [tsub_tsub_tsub_cancel_right hsk, mul_assoc, mul_left_comm s !, mul_assoc,
        mul_comm (k - s)!, mul_comm s !, mul_right_comm, ← mul_assoc]


theorem idt8 {n k : ℕ} (hk : k ≤ n) (hk1 :1 ≤ k):
 (n-k)*choose n k = n * choose (n-1) k  := by
  have h₁:1 ≤ n := by linarith
  rw [idt1_Pascal's_Recurrence h₁ hk1]
  rw [mul_add]
  have h₂ :(n - k)  =((n-1)- (k-1)) := by
    rw [tsub_tsub_tsub_cancel_right]
    linarith
  rw [h₂,mul_comm (n - 1 - (k - 1)) (choose (n - 1) (k - 1)),← choose_succ_right_eq (n-1) (k-1)]
  rw [Nat.sub_add_cancel hk1]
  rw [← h₂]
  rw [tsub_mul]
  rw [mul_comm (choose (n - 1) k)]
  rw [tsub_add_cancel_of_le]
  exact Nat.mul_le_mul_right _ hk

theorem h82 {n k : ℕ} (hk : k ≤ n) (hk1 :1 ≤ k):(n - k)  =((n-1)- (k-1)) := by
    rw [tsub_tsub_tsub_cancel_right]
    linarith

theorem Idt21 (n : ℕ) : ∑ k in range (n + 1), k * choose n k = n * 2 ^ (n - 1) := by
  have h1 : ∑ k in range (n + 1), k * choose n k = ∑ k in range (n + 1), (n - k) * choose n k := by
    rw [← sum_range_reflect, add_tsub_cancel_right]
    congr! 2 with k h
    exact choose_symm (mem_range_succ_iff.mp h)
  have h2 : 2 * ∑ k in range (n + 1), k * choose n k = n * 2 ^ n := by
    nth_rw 1 [two_mul, h1, ← sum_add_distrib]
    simp_rw [← add_mul]
    rw [sum_congr (g := fun x => n * n.choose x) rfl fun x h => by
      congr 1; exact tsub_add_cancel_iff_le.mpr (mem_range_succ_iff.mp h),
      ← mul_sum, sum_range_choose]
  apply mul_right_injective₀ (show 2 ≠ 0 by norm_num)
  dsimp only
  rw [h2, mul_comm _ (_ * _), mul_assoc]
  cases' n.eq_zero_or_pos with h h
  · simp [h]
  · have d1 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      induction n
      · linarith
      · exact rfl
    exact congrArg (HMul.hMul n) d1

theorem idt21h1(n : ℕ) : ∑ k in range (n + 1), k * choose n k = ∑ k in range (n + 1), (n - k) * choose n k := by
    rw [← sum_range_reflect, add_tsub_cancel_right]
    congr! 2 with k h
    exact choose_symm (mem_range_succ_iff.mp h)

theorem idt21d1 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      induction n
      · linarith
      · exact rfl

theorem idt21h2(n : ℕ) : 2 * ∑ k in range (n + 1), k * choose n k = n * 2 ^ n := by
    nth_rw 1 [two_mul, h1, ← sum_add_distrib]
    simp_rw [← add_mul]
    rw [sum_congr (g := fun x => n * n.choose x) rfl fun x h => by
      congr 1; exact tsub_add_cancel_iff_le.mpr (mem_range_succ_iff.mp h),
      ← mul_sum, sum_range_choose]

theorem idt21h3(n : ℕ) :n * 2 ^ n = n * (2 ^ (n - 1) * 2) := by sorry

theorem  Ico_choose_simp_0to1{n k: ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k): ∑ k in Ico 0 (n.succ + 1), (-1:ℤ) ^ k * ↑k * (choose n.succ k) =
    ∑ k in Ico 1 (n.succ + 1), (-1:ℤ) ^ k * ↑k * (choose n.succ k):= by
      rw [sum_eq_sum_Ico_succ_bot h_succ]
      simp

theorem idt22h1{n k: ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k): ∑ k in Ico 1 (n.succ + 1), (-1:ℤ) ^ k * ↑k * ↑(Nat.choose (n.succ) k)
    = ∑ k in Ico 1 (n.succ + 1), (-1:ℤ) ^ k * n.succ * ↑(Nat.choose (n.succ - 1) (k - 1)) := by
      refine' sum_congr rfl fun x hx ↦ _
      have hx_succ: x < n.succ + 1 := by exact (mem_Ico.1 hx).2
      have hx_n: x ≤ n.succ := by linarith
      have hk1: 1 ≤ x := by exact (mem_Ico.1 hx).1
      rw [mul_assoc,mul_assoc]
      simp
      rw [← cast_mul]
      rw [idt6_Absorption hx_n hk1]
      rw [cast_mul]
      rw [← add_one]
      rw [cast_add_one]
      simp


theorem idt22h2: ∑ k in Ico 1 (succ n + 1), (-1:ℤ ) ^ k * ↑(succ n) * ↑(Nat.choose (succ n - 1) (k - 1))
    =↑(succ n) * ∑ k in Ico 1 (succ n + 1), (-1:ℤ) ^ k *  ↑(Nat.choose (succ n - 1) (k - 1)) := by
    simp
    rw [mul_sum]
    refine' sum_congr rfl fun x hx ↦ _
    rw[mul_comm]
    rw [← mul_assoc,← mul_assoc]
    rw [mul_right_comm,mul_assoc,mul_left_comm,mul_assoc]
    simp
    rw [mul_comm]
    simp

theorem idt22h3:
    ↑(succ n) * ∑ k in range (succ n + 1 - 1), (-1:ℤ) ^ (1 + k) * ↑(Nat.choose (succ n - 1) (1 + k - 1))
    = (-1:ℤ) * ↑(succ n) * ∑ k in range (succ n - 1 + 1), (-1:ℤ) ^ k * ↑(Nat.choose (succ n - 1) (1 + k - 1)) := by
      simp
      rw [add_one]
      rw [mul_sum,mul_sum]
      refine' sum_congr rfl fun x hx ↦ _
      rw [mul_comm,← mul_assoc,mul_right_comm]
      simp
      rw [pow_add,mul_right_comm]
      simp


theorem Identity_22_2{n : ℕ} (h2 : n ≠ 0) :  (∑ k in range (n + 1), ((-1) ^ k * ↑(choose n k) : ℤ)) * k = 0 := by
  have c1:(∑ k in range (n + 1), ((-1) ^ k * ↑(choose n k) : ℤ)) = 0 := by
    rw [Int.alternating_sum_range_choose, if_neg h2]
  have c2: 0 * k = 0 :=by
    linarith
  exact mul_eq_zero_of_left c1 k

theorem Identity_22_1(h1 : n = 1): ∑ k in range (n + 1), ((-1) ^ k * k *↑ (choose n k) : ℤ) = -1 := by sorry

theorem idt_24 {n: ℕ}:
 ∑ k in range (n+1), ((-1:ℝ)^k)*(((1/(k+1)) : ℝ) * choose n k)= 1/(n+1) := by
  sorry

theorem idt24l1: ∑ k in range (n+1), ((-1:ℝ)^k)*(((1/(k+1)) : ℝ) * choose n k) =
   ∑ k in range (n+1), ((-1:ℝ)^k)*(((1/(n+1)) : ℝ) * choose (n+1) (k+1)):= by
    refine' sum_congr rfl fun k hk => _
    rw [choose_mul_eq_mul_sub_div]

theorem idt24l2: ∑ k in range (n+1), ((-1:ℝ)^k)*(((1/(n+1)) : ℝ) * choose (n+1) (k+1)) =
    ∑ k in range (n+1), (((1/(n+1)) : ℝ) *(((-1:ℝ)^k)* choose (n+1) (k+1))) := by
    refine' sum_congr rfl fun k hk => _
    rw [← mul_assoc,← mul_assoc]
    congr 1
    rw [mul_comm]


theorem idt_23 {n k: ℕ} :
 ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k =
  (1/(n+1)) * (2^(n+1) - 1) := by
  have : ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k
        = ∑ k in range (n+1), ((1/(n+1)) : ℝ) * choose (n+1) (k+1) := by
        refine' sum_congr rfl fun y hy => _
        exact choose_mul_eq_mul_sub_div
  rw [this, ←mul_sum]
  congr 1
  rw [←one_add_one_eq_two]
  rw [add_pow 1 1 (n+1)]
  simp
  rw [sum_range_succ' _ (n + 1)]
  simp
