import Theorem.Premises.real_theorem.mini_theorem

import Mathlib.Data.Nat.Choose.Basic
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
#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"


open Nat

open Finset

open BigOperators

variable {R : Type*}

-- namespace Commute

variable [Semiring R] {x y : R}

variable {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : Finset α} {a : α} {g f : α → β}

variable [CommMonoid β]

--1.7
theorem sum_eq_two (n : Nat):
  2 ^ ( 2 * n ) = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by
   have h : n + 1 ≤ 2 * n + 1 := by linarith
   rw [Finset.sum_range_add_sum_Ico _ (h)]
   rw [← sum_range_choose]


theorem sum_choose_eq: ∑ k in Ico 0 n, Nat.choose (2 * n) k = ∑ k in Ico 0 n, Nat.choose (2 * n) (2 * n - k) := by
    refine' sum_congr rfl fun y hy ↦ _
    have yn : y < n := by exact (mem_Ico.1 hy).2
    have y2n : y ≤ 2 * n := by linarith
    rw[← choose_symm y2n]


theorem two_mul_succ_sub(hn: n ≤ 2 * n): 2 * n + 1 - n = n + 1 := by
  have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  simp


theorem two_mul_add_sub (hn: n ≤ 2 * n): 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]


theorem two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp


theorem sum_choose_eq_Ico (hn: n ≤ 2 * n): ∑ k in range n, choose (2 * n) k = ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by
  rw [range_eq_Ico]
  have h1 : ∑ k in Ico 0 n, Nat.choose (2 * n) k = ∑ k in Ico 0 n, Nat.choose (2 * n) (2 * n - k) := by
    refine' sum_congr rfl fun y hy ↦ _
    have yn : y < n := by exact (mem_Ico.1 hy).2
    have y2n : y ≤ 2 * n := by linarith
    rw[← choose_symm y2n]
  rw[h1]
  rw[sum_Ico_reflect]
  simp
  have two_mul_succ_sub : 2 * n + 1 - n = n + 1 := by
    have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
      rw[add_comm]
      rw[Nat.add_sub_assoc hn]
      rw[add_comm]
    rw[two_mul_add_sub]
    simp
    have h23: 2 * n - n = 2 * n - 1 * n := by simp
    rw[h23]
    rw[← Nat.mul_sub_right_distrib]
    simp
  rw[two_mul_succ_sub]
  linarith

theorem sum_choose_sub_eq_add : ∑ k in range (n + 1), choose (2 * n) k - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k) := by
  rw[Finset.sum_range_succ]
  simp

theorem Ico_choose_range_choose:  ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k)  = (∑ k in range (n + 1), choose (2 * n) k) - choose (2 * n) n := by  -- bn = an - choose (2 * n) n
  have sum_choose_sub_eq_add_sub : ∑ k in range (n + 1), choose (2 * n) k - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k) + (choose (2 * n) n) - (choose (2 * n) n) := by rw[Finset.sum_range_succ] -- an - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k)
  rw[← sum_choose_eq_Ico]
  simp at sum_choose_sub_eq_add_sub
  rw[sum_choose_sub_eq_add_sub]
  linarith


theorem two_mod_two_pow( hn : n ≠ 0 ) : 2 ∣ (2 ^ (2 * n)) := by
  have h20: 2 ≠ 0 := by simp
  have h2: 2 * n ≠ 0 := by exact Nat.mul_ne_zero_iff.mpr ⟨h20, hn⟩
  exact dvd_pow_self _ h2

theorem two_pow_sub_add_cancel(h : 1 ≤ 2 * n) :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h]

theorem two_pow_div_two(hn : n ≠ 0): (2 ^ ( 2 * n )) / 2 = 2 ^ (( 2 * n ) - 1) := by
  have h2 : 2 ∣ (2 ^ (2 * n)) := by exact two_mod_two_pow hn
  have h1 : 1 ≤ 2 * n := by
    have h1n: 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr hn
    linarith
  have h02 : 0 < 2 := by simp
  rw[Nat.div_eq_iff_eq_mul_right h02 h2]
  have two_pow_sub_add_cancel :  2 ^ (2 * n - 1 + 1) = 2 ^ (2 * n) := by rw[Nat.sub_add_cancel h1]
  rw[← two_pow_sub_add_cancel]
  rw[Nat.pow_succ, mul_comm]


theorem choose_add_div_distrib( hn : n ≠ 0 ) : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
    have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
    rw[Nat.add_div_of_dvd_left h_mod]


theorem add_div_two(hn : n ≠ 0 ):((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = 2 ^ ( 2 * n - 1 ) + (choose (2 * n) n) / 2:= by
  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
    have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
    rw[Nat.add_div_of_dvd_left h_mod]
  rw[choose_add_div_distrib]
  rw[two_pow_div_two hn, add_comm]

------------------------------------------------------
theorem two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]

theorem range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]

theorem range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by
  rw[← range_sub_choose, Nat.add_comm]
  rw[←two_pow_eq_range_add_ico]

theorem choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
      rw[sum_range_succ]
      simp

theorem sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   -- an + an = 2 ^ ( 2 * n ) + choose (2 * n) n
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
      rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
      simp
      rw [Nat.sub_add_cancel choose_le_sum]
  rw[←sum_sub_sum_add,sum_add_eq_add]

theorem sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]

theorem sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
    rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]

theorem two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  -- 2 * an = 2 ^ ( 2 * n ) + choose (2 * n) n
  rw[← sum_add_eq_two_pow, two_mul]

theorem sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]  -- an = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2

theorem add_div_two_eq_distrib(hn : n ≠ 0) : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]


theorem sum_choose_eq_pow_add (n : ℕ)(hn : n ≠ 0) :
  ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by
    have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]  -- 2 ^ ( 2 * n ) = an + bn
    have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]   -- bn = an - choose (2 * n) n
    have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       --  2 ^ ( 2 * n ) = bn + an =  an - choose (2 * n) n + an
      rw[← range_sub_choose, Nat.add_comm]
      rw[← two_pow_eq_range_add_ico]
    have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
      rw[sum_range_succ]
      simp
    have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   -- an + an = 2 ^ ( 2 * n ) + choose (2 * n) n
      have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]  -- an - choose (2 * n) n + an + choose (2 * n) n = 2 ^ ( 2 * n ) + choose (2 * n) n
      have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by -- an - choose (2 * n) n + an + choose (2 * n) n = an + an
          rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
          simp
          rw [Nat.sub_add_cancel choose_le_sum]
      rw[←sum_sub_sum_add,sum_add_eq_add]
    have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  -- 2 * an = 2 ^ ( 2 * n ) + choose (2 * n) n
      rw[← sum_add_eq_two_pow, two_mul]
    have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]  -- an = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2
    have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
    rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

-- theorem sum_choose_eq_pow_add' (n : ℕ)(hn : n ≠ 0) :
--   ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / (2:ℝ) := by
--     have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]  -- 2 ^ ( 2 * n ) = an + bn
--     have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]   -- bn = an - choose (2 * n) n
--     have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       --  2 ^ ( 2 * n ) = bn + an =  an - choose (2 * n) n + an
--       rw[← range_sub_choose, Nat.add_comm]
--       rw[← two_pow_eq_range_add_ico]
--     have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
--       rw[sum_range_succ]
--       simp
--     have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   -- an + an = 2 ^ ( 2 * n ) + choose (2 * n) n
--       have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]  -- an - choose (2 * n) n + an + choose (2 * n) n = 2 ^ ( 2 * n ) + choose (2 * n) n
--       have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by -- an - choose (2 * n) n + an + choose (2 * n) n = an + an
--           rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
--           simp
--           rw [Nat.sub_add_cancel choose_le_sum]
--       rw[←sum_sub_sum_add,sum_add_eq_add]
--     have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  -- 2 * an = 2 ^ ( 2 * n ) + choose (2 * n) n
--       rw[← sum_add_eq_two_pow, two_mul]
--     have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]  -- an = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2
--     have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / (2:ℝ) = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / (2:ℝ) := by rw[add_div_two hn]
--     rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem choose_mul_eq_choose_mul(hkn : k ≤ n) (hsk : 1 ≤ k) : choose n k * choose k 1 = choose n 1 * choose (n - 1) (k - 1)  := by rw[choose_mul hkn hsk]

theorem choose_mul_eq_mul_sub {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :  -- 定理1.3
    choose n k * k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul : choose n k * choose k 1 = choose n 1 * choose (n - 1) (k - 1)  := by rw[choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]

theorem choose_mul_eq_mul_sub' {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :
    k * choose n k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]

theorem mul_same(hkn : k ≤ n)(hsk : 1 ≤ k) : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]

theorem choose_mul_pow_eq_mul(hkn : k ≤ n)(hsk : 1 ≤ k): choose n k * (k ^ 2)  = n * k * choose (n - 1) (k - 1)  := by
  have mul_same : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]
  rw[Nat.mul_assoc] at mul_same
  rw[pow_two, mul_same]

theorem pow_mul_choose {n k : ℕ}(hkn : k ≤ n)(hsk : 1 ≤ k) :
  k ^ 2 * choose n k = n * k * choose (n-1) (k-1)  := by
    have mul_same : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by   -- 两边同时*k
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]  -- n * Nat.choose (n - 1) (k - 1) * k = n * Nat.choose (n - 1) (k - 1) * k
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]  --choose n k * k * k  = n * k * choose (n - 1) (k - 1)
    have choose_mul_pow_eq_mul : choose n k * (k ^ 2)  = n * k * choose (n - 1) (k - 1)  := by
      rw[Nat.mul_assoc] at mul_same
      rw[pow_two, mul_same]
    rw[mul_comm, choose_mul_pow_eq_mul]


theorem Ico_pow_mul_choose :   --sum41
  ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n * ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1)  := by
    rw[mul_sum]
    refine' sum_congr rfl fun y hy ↦ _
    have hyn : y ≤ n := by
      have yn_succ : y < n + 1 := by exact (mem_Ico.1 hy).2
      exact Nat.le_of_lt_succ yn_succ
    have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[pow_mul_choose (hyn) (hy1)]
    rw[mul_assoc]


theorem congr_Ico_succ:
  ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1) = ∑ l in Ico 0 n, (l + 1) * choose (n-1) l:= by
  rw[sum_Ico_eq_sum_range]
  simp
  refine' sum_congr rfl fun y _ => _
  rw[add_comm]

theorem Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
  rw[← range_eq_Ico]
  have range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]
  rw[range_mul_add]
  rw[sum_add_distrib]
  simp

theorem range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]

theorem ico_two_pow(h : 0 < n): ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have h': 1 ≤ n := by linarith
  rw[← range_eq_Ico]
  have range_sub_add_cancel :  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
    refine' sum_congr _ fun y _ => rfl
    have nn: n - 1 + 1 = n := by
      exact Nat.sub_add_cancel h'
    rw[nn]
  rw[sum_range_choose] at range_sub_add_cancel
  rw[range_sub_add_cancel]

theorem range_sub_add_cancel(h : 0 < n):  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
  have h': 1 ≤ n := by linarith
  refine' sum_congr _ fun y _ => rfl
  have nn: n - 1 + 1 = n := by
    exact Nat.sub_add_cancel h'
  rw[nn]

theorem Ico_choose_eq_Ico_choose_add(h : 0 < n): ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1) = ∑ l in Ico 1 n, l * choose (n-1) l + 2 ^ ( n - 1 ):= by   --sum42
  rw[congr_Ico_succ]
  have h': 1 ≤ n := by linarith
  have Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
   rw[← range_eq_Ico]
   have range_mul_add : ∑ l in range n, (l + 1) * Nat.choose (n - 1) l = ∑ l in range n, (l * (choose (n - 1) l) + 1 * (choose (n - 1) l)) := by
    refine' sum_congr rfl fun y _ => _
    rw[Nat.add_mul]
   rw[range_mul_add]
   rw[sum_add_distrib]
   simp
  rw[Ico_mul_add]
  have h_bot(hn0: 0 < n) : ∑ l in Ico 0 n, l * Nat.choose (n - 1) l = 0 * Nat.choose (n - 1) 0 + ∑ l in Ico 1 n, l * Nat.choose (n - 1) l := by
    rw[sum_eq_sum_Ico_succ_bot hn0]
  simp at h_bot
  rw[range_eq_Ico] at h_bot
  have ico_two_pow: ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
    rw[← range_eq_Ico]
    have range_sub_add_cancel :  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
      refine' sum_congr _ fun y _ => rfl
      have nn: n - 1 + 1 = n := by
        exact Nat.sub_add_cancel h'
      rw[nn]
    rw[sum_range_choose] at range_sub_add_cancel
    rw[range_sub_add_cancel]
  rw[h_bot h, ico_two_pow]

theorem mul_choose_sub {l : ℕ }(hh1: l ≤ n - 1)(hh2: 1 ≤ l) :
  l * choose ( n - 1 ) l = (n - 1) * choose (n-2) (l-1) := by
    rw[mul_comm]
    rw[choose_mul_eq_mul_sub (hh1) (hh2)]
    rw[Nat.sub_sub, Nat.sub_one]

theorem ico_mul_choose_sub(hn0 : 0 < n) : ∑ l in Ico 1 n ,l * choose (n-1) l  = ∑ l in Ico 1 n, (n - 1) * choose (n-2) (l-1) := by
  refine' sum_congr rfl fun y hy ↦ _
  have hyn : y < n := by exact (mem_Ico.1 hy).2
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[mul_choose_sub hy_sub_1 hy1]

theorem lt_eq_le_sub{y:ℕ}(hn0 : 0 < n) : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a

theorem Ico_choose_add_eq_mul_pred(hn0 : 0 < n) : ∑ l in Ico 1 n, l * choose (n-1) l + 2 ^ ( n - 1 ) = (n - 1) * ∑ l in Ico 1 (n), choose (n-2) (l-1) + 2 ^ ( n - 1 ):= by --sum43
    have mul_choose_sub {l : ℕ }(hh1: l ≤ n - 1)(hh2: 1 ≤ l) :
    l * choose ( n - 1 ) l = (n - 1) * choose (n-2) (l-1) := by
      rw[mul_comm]
      rw[choose_mul_eq_mul_sub (hh1) (hh2)]
      rw[Nat.sub_sub, Nat.sub_one]
    have ico_mul_choose_sub : ∑ l in Ico 1 n ,l * choose (n-1) l  = ∑ l in Ico 1 n, (n - 1) * choose (n-2) (l-1) := by
      refine' sum_congr rfl fun y hy ↦ _
      have hyn : y < n := by exact (mem_Ico.1 hy).2
      have lt_eq_le_sub : y < n → y ≤ n - 1 := by
        rw[Nat.lt_iff_le_pred hn0]
        intro a
        exact a
      have hy_sub_1 : y ≤ n - 1 := by
        exact lt_eq_le_sub hyn
      have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
      rw[mul_choose_sub hy_sub_1 hy1]
    rw[ico_mul_choose_sub]
    rw[← mul_sum]

theorem ico_succ: ∑ s in Ico 0 (n-1), choose (n-2) s = ∑ l in Ico 1 n, choose (n-2) (l-1) := by
    rw[sum_Ico_eq_sum_range]
    simp
    rw[sum_Ico_eq_sum_range]
    refine' sum_congr rfl fun y _ => _
    simp

theorem pred_Ico_choose : (n - 1) * ∑ l in Ico 1 n, choose (n-2) (l-1) + 2 ^ ( n - 1 ) = (n - 1) * ∑ s in Ico 0 (n-1), choose (n-2) s + 2 ^ ( n - 1 ) := by  --sum44
  have ico_succ: ∑ s in Ico 0 (n-1), choose (n-2) s = ∑ l in Ico 1 n, choose (n-2) (l-1) := by
    rw[sum_Ico_eq_sum_range]
    simp
    rw[sum_Ico_eq_sum_range]
    refine' sum_congr rfl fun y _ => _
    simp
  rw[ico_succ]

theorem ico_choose_eq_two_pow(h : 2 ≤ n ) : ∑ s in Ico 0 (n-1), choose (n-2) s = 2 ^ ( n - 2 ) := by
    rw[← range_eq_Ico]
    have range_choose_eq_ico_choose :  ∑ l in range (n-2+1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n-1), choose (n-2) s:= by
      refine' sum_congr _ fun y _ => rfl
      have nn: n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
      rw[nn,range_eq_Ico]
    rw[sum_range_choose] at range_choose_eq_ico_choose
    rw[range_choose_eq_ico_choose,range_eq_Ico]

theorem range_choose_eq_ico_choose(h : 2 ≤ n )  :  ∑ l in range (n-2+1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n-1), choose (n-2) s:= by
      refine' sum_congr _ fun y _ => rfl
      have sub_two_add_one: n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
      rw[sub_two_add_one,range_eq_Ico]

theorem sub_two_add_one(h : 2 ≤ n ): n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h

theorem pred_Ico_choose_eq_pred_pow(h : 2 ≤ n ) :  (n - 1) * ∑ s in Ico 0 (n-1), choose (n-2) s + 2 ^ ( n - 1 ) = (n - 1) * 2 ^ (n-2)  + 2 ^ ( n - 1 ) := by  --sum45
  have ico_choose_eq_two_pow: ∑ s in Ico 0 (n-1), choose (n-2) s = 2 ^ ( n - 2 ) := by
    rw[← range_eq_Ico]
    have range_choose_eq_ico_choose :  ∑ l in range (n-2+1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n-1), choose (n-2) s:= by
      refine' sum_congr _ fun y _ => rfl
      have nn: n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
      rw[nn,range_eq_Ico]
    rw[sum_range_choose] at range_choose_eq_ico_choose
    rw[range_choose_eq_ico_choose,range_eq_Ico]
  rw[ico_choose_eq_two_pow]

theorem sum_eq_mul_mul_add_pow(h: 2 ≤ n) : ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n *((n - 1) * 2 ^ (n-2)  + 2 ^ ( n - 1 )) := by
    have h0: 0 < n:= by linarith
    rw[Ico_pow_mul_choose]
    rw[Ico_choose_eq_Ico_choose_add h0]
    rw[Ico_choose_add_eq_mul_pred h0,pred_Ico_choose, pred_Ico_choose_eq_pred_pow h]

theorem Ico_pow_choose_eq_pow_add_pow(h: 2 ≤ n):  ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n * (n - 1) * 2 ^ (n-2)  + n * 2 ^ ( n - 1 )  := by
  have h0: 0 < n:= by linarith
  have sum_eq_mul_mul_add_pow : ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n *((n - 1) * 2 ^ (n-2)  + 2 ^ ( n - 1 )) := by
    rw[Ico_pow_mul_choose]
    rw[Ico_choose_eq_Ico_choose_add h0]
    rw[Ico_choose_add_eq_mul_pred h0,pred_Ico_choose, pred_Ico_choose_eq_pred_pow h]
  rw[Nat.mul_add] at sum_eq_mul_mul_add_pow
  rw[sum_eq_mul_mul_add_pow, Nat.mul_assoc]

theorem mul_two_pow_eq_mul_mul_two_pow(h: 2 ≤ n): n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
  have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
    have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
      have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
      rw[sub_add_eq_sub]
    rw[two_pow_eq_two_pow_sub_add]
    rw[Nat.pow_succ]
  rw[two_pow_eq_two_pow_two]
  rw[← Nat.mul_assoc]
  rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]

theorem two_pow_eq_two_pow_two(h: 2 ≤ n) : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
  have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
    have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
      exact tsub_add_eq_add_tsub h
    rw[sub_add_eq_sub]
  rw[two_pow_eq_two_pow_sub_add]
  rw[Nat.pow_succ]

theorem two_pow_eq_two_pow_sub_add(h: 2 ≤ n) : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  rw[sub_add_eq_sub]

theorem mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
  rw[← Nat.add_mul]

theorem mul_add_mul_eq_mul(h: 2 ≤ n) : n * (n - 1) + 2 * n = n * (n + 1) := by
  have h1: 1 ≤ n := by linarith
  rw[Nat.mul_comm 2 n]
  rw[← Nat.mul_add]
  have sub_add_eq_add : n - 1 + 2 = n + 1 := by
    have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
    rw[sub_add_eq_sub_add_add_add]
    rw [Nat.sub_add_cancel h1]
  rw[sub_add_eq_add]

theorem sub_add_eq_add(h: 2 ≤ n) : n - 1 + 2 = n + 1 := by
  have h1: 1 ≤ n := by linarith
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  rw[sub_add_eq_sub_add_add_add]
  rw [Nat.sub_add_cancel h1]

theorem Ico_pow_choose_eq_mul_pow(h: 2 ≤ n):  ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n * (n + 1) * 2 ^ ( n - 2 )  := by
  have h1: 1 ≤ n := by linarith
  rw[Ico_pow_choose_eq_pow_add_pow h]
  have mul_two_pow_eq_mul_mul_two_pow: n * 2 ^ ( n - 1 ) = 2 * n * 2 ^ ( n - 2 ) := by
    have two_pow_eq_two_pow_two : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 ) * 2  := by
      have two_pow_eq_two_pow_sub_add : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
        have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
          exact tsub_add_eq_add_tsub h
        rw[sub_add_eq_sub]
      rw[two_pow_eq_two_pow_sub_add]
      rw[Nat.pow_succ]
    rw[two_pow_eq_two_pow_two]
    rw[← Nat.mul_assoc]
    rw[Nat.mul_comm (n * 2 ^ (n - 2)), ← Nat.mul_assoc]
  rw[mul_two_pow_eq_mul_mul_two_pow]
  have mul_two_pow_add_eq_mul_pow : n * (n - 1) * 2 ^ (n - 2) + 2 * n * 2 ^ (n - 2) = (n * (n - 1) + 2 * n) * 2 ^ (n - 2) := by
    rw[← Nat.add_mul]
  rw[mul_two_pow_add_eq_mul_pow ]
  have mul_add_mul_eq_mul : n * (n - 1) + 2 * n = n * (n + 1) := by
    rw[Nat.mul_comm 2 n]
    rw[← Nat.mul_add]
    have sub_add_eq_add : n - 1 + 2 = n + 1 := by
      have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
      rw[sub_add_eq_sub_add_add_add]
      rw [Nat.sub_add_cancel h1]
    rw[sub_add_eq_add]
  rw[mul_add_mul_eq_mul]

theorem choose_eq_choose_sub_add(h1:1 ≤ n)(h2:1 ≤ k) :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]

theorem choose_sub_eq_choose_sub_add(h1:1 ≤ n)(h2:1 ≤ k) : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]

theorem choose_eq_choose_add(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]

theorem Real_choose_eq_choose_add(h1:1 ≤ n)(h2:1 ≤ k) : (choose n k : ℝ) = (choose (n-1) k : ℝ)  + (choose (n-1) (k-1): ℝ) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add : ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  simp

theorem neg_pow_choose(h1:1 ≤ n):
  ∑ k in Ico 1 n, (-1 : ℝ) ^ k * (choose n k : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k : ℝ) + (choose (n-1) (k-1) : ℝ)) * (m / (m+k)) := by
    refine' sum_congr rfl fun y hy => _
    congr 1
    have hab: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[choose_eq_choose_add h1 hab]
    simp


theorem sum_neg_pow_mul_distrib: ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k + (-1 : ℝ)^k * choose (n-1) (k-1)) : ℝ) * (m / (m+k)) := by
    refine' sum_congr rfl fun y _ => _
    rw[mul_add]

theorem sum_neg_pow_mul_mul (t : ℕ → ℕ → ℕ → ℝ := fun m n k => (-1 : ℝ)^k * (choose n k : ℝ) * (m / (m+k))):
  ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k * (m / (m+k)) + (-1 : ℝ)^k * choose (n-1) (k-1) * (m / (m+k))) : ℝ):= by
  have sum_neg_pow_mul_distrib: ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k + (-1 : ℝ)^k * choose (n-1) (k-1)) : ℝ) * (m / (m+k)) := by
    refine' sum_congr rfl fun y _ => _
    rw[mul_add]
  rw[sum_neg_pow_mul_distrib]
  refine' sum_congr rfl fun y _ => _
  rw[add_mul]

theorem sum_neg_pow_mul_eq_sum_distrib(t : ℕ → ℕ → ℕ → ℝ := fun m n k => (-1 : ℝ)^k * (choose n k : ℝ) * (m / (m+k))):
  ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, ((-1 : ℝ)^k * choose (n-1) k * (m / (m+k))) + ∑ k in Ico 1 n, ((-1 : ℝ)^k * choose (n-1) (k-1) * (m / (m+k)) : ℝ):= by
  rw[sum_neg_pow_mul_mul]
  rw[sum_add_distrib]

theorem h_pow_zero_mul_add: ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))) = ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico (0+1) n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))):= by
    congr 1

theorem pow_zero_mul_add_sum( hn: 0 < n):
((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico 1 n, (-1 : ℝ)^k * (choose (n-1) k : ℝ) * (m / (m+k))) =
∑ k in range n, (-1 : ℝ)^k * (choose (n-1) k : ℝ) * (m / (m+k)) := by
  have h_pow_zero_mul_add: ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))) = ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico (0+1) n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))):= by
    congr 1
  rw[h_pow_zero_mul_add, range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
  simp

theorem sum_neg_pow_mul_add( hn: 0 < n):
∑ k in Ico 1 n, (-1 : ℝ) ^ k * ((Nat.choose (n - 1) (k - 1)) : ℝ) * (m / (m + k)) + (-1 : ℝ)^n * (choose n n : ℝ) * (m / (m+n)) = ∑ k in Ico 1 (n+1), (-1 : ℝ) ^ k * ((Nat.choose (n - 1) (k - 1)) : ℝ) * (m / (m + k)) := by
  have h1:  1 ≤ n := by linarith
  rw[sum_Ico_succ_top h1]
  simp

------------------------------------习题
theorem Ico_pow_choose : ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x + 1) * (1 / x) * (Nat.choose (n + 1) x) = (∑ k in range (n + 1), 1 / (k + 1))  := by sorry  --example8
theorem choose_eq_pow_add: ∑ k in range (n+1), ((choose (2*n) k) :ℝ) = 2 ^ ( 2 * n - 1 ) + ((choose ( 2 * n ) n / 2) :ℝ) := by sorry  --example2

theorem range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   -- 更改 k 的范围
  rw[range_eq_Ico]
  have h_succ : 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  simp

theorem mul_choose_eq_mul_choose(hn :0 < n) : ∑ k in range (n+1), k * choose n k = ∑ k in Ico 1 (n + 1), n * choose (n-1) (k-1) := by
  have range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   -- 更改 k 的范围
    rw[range_eq_Ico]
    have h_succ : 0 < n + 1 := by linarith
    rw [sum_eq_sum_Ico_succ_bot h_succ]
    simp
  rw[range_eq_ico_mul_choose]
  refine' sum_congr rfl fun y hy => _
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  have hyn : y ≤ n := by
    have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
    linarith
  rw[choose_mul_eq_mul_sub' hyn hy1]  -- 使用定理1.3


theorem sum_mul_congr : ∑ k in Ico 1 (n + 1), n * choose (n-1) (k-1) = n * ∑ l in range n, choose (n-1) l := by
  rw[mul_sum]   --先把 n 提出来
  rw[sum_Ico_eq_sum_range]  -- 代换 l = k - 1
  simp


theorem mul_choose_two_pow(hn : 0 < n) : n * ∑ l in range n, choose (n-1) l = n * 2 ^ (n-1) := by
  congr 1
  have n1 : 1 ≤ n := by linarith
  have hn1 : ∑ l in range n, choose (n-1) l = ∑ l in range (n - 1 + 1), choose (n-1) l   := by
    rw[Nat.sub_add_cancel n1]
  rw[hn1]
  rw [sum_range_choose]


theorem sum_mul_choose_eq_mul_two_pow_sub(hn :0 < n) : ∑ k in range (n+1), k * choose n k = n * 2 ^(n-1) := by
  rw[mul_choose_eq_mul_choose hn]
  rw[sum_mul_congr]
  rw[mul_choose_two_pow hn]


theorem sum_mul_add_distrib : ∑ k in range (n+1), (k+1) * choose n k = ∑ k in range (n+1), (k * choose n k + 1 * choose n k) := by
  refine' sum_congr rfl fun y _ => _
  rw[add_mul]

theorem pow_eq_sub_one_mul(hn :0 < n) :  2 ^ n = 2 ^ (n - 1) * 2  := by
    have n1 : 1 ≤ n := by linarith
    have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
      rw[Nat.sub_add_cancel n1]
    rw[← h2n]
    rw[Nat.pow_succ]

theorem sum_succ_choose(hn :0 < n) :  ∑ k in range (n+1), (k+1) * choose n k = 2 ^ (n - 1) * (n + 2) := by
  have sum_mul_add_distrib : ∑ k in range (n+1), (k+1) * choose n k = ∑ k in range (n+1), (k * choose n k + 1 * choose n k) := by
    refine' sum_congr rfl fun y _ => _
    rw[add_mul]
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    have n1 : 1 ≤ n := by linarith
    have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
      rw[Nat.sub_add_cancel n1]
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]


theorem sum_neg_pow_mul_mul_choose : ∑ k in range (n+1), (-1 : ℤ)^k * k * (choose n k)  = (-1 : ℤ)^0 * 0 * (choose n 0) + ∑ k in Ico 1 (n+1), (-1 : ℤ)^k * k * (choose n k) := by
    rw[range_eq_Ico]
    have n_succ: 0 < n + 1 := by linarith
    rw[sum_eq_sum_Ico_succ_bot n_succ]
    simp


theorem neg_pow_mul_choose_mul_eq_mul_sub:  ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * k * (choose n k) = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hyn : y ≤ n := by
      have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
      linarith
    rw[mul_assoc, mul_assoc]
    congr 1
    rw[← cast_mul,← cast_mul]
    rw[choose_mul_eq_mul_sub' hyn hy1]


theorem neg_pow_cancel : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ k * n * (choose (n-1) (k-1)) =  ∑ k in Ico 1 (n + 1), (-1) ^ (k - 1) * (-1 : ℤ)* n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hnegy : (-1 : ℤ ) ^ y = (-1) ^ (y - 1 + 1)  := by
      rw[Nat.sub_add_cancel hy1]
    congr 2


theorem neg_pow_mul_mul_mul : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ (k - 1) * (-1)* n * (choose (n-1) (k-1))  = ∑ k in Ico 1 (n + 1), (-1 : ℤ)*  ((-1) ^ (k - 1) * n * (choose (n-1) (k-1))) := by
  refine' sum_congr rfl fun y _ => _
  rw[mul_comm ((-1 : ℤ) ^ (y - 1)) (-1)]
  rw[mul_assoc,mul_assoc,mul_assoc]


theorem sum_neg_comm : ∑ x in range n, (-1 : ℤ) ^ x * n * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x):= by
    refine' sum_congr rfl fun y _ => _
    congr 1
    rw[mul_comm]

theorem sum_neg_assoc: ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * ((-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x)) := by
  refine' sum_congr rfl fun y _ => _
  rw[mul_assoc]

theorem sum_neg_cancel(hn : 1 < n) : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
  have zero_lt_n : 0 < n := by linarith
  rw[Nat.sub_add_cancel zero_lt_n]


theorem sum_neg_pow_mul(hn : 1 < n): ∑ k in range (n+1), (-1 : ℤ)^k * k * (choose n k)  = 0 := by
  have zero_lt_n : 0 < n := by linarith
  have n_sub_one : n - 1 ≠ 0 := by exact Nat.sub_ne_zero_of_lt hn
  have hk : ∑ k in range (n+1), (-1 : ℤ)^k * k * (choose n k)  = (-1 : ℤ)^0 * 0 * (choose n 0) + ∑ k in Ico 1 (n+1), (-1 : ℤ)^k * k * (choose n k) := by
    rw[range_eq_Ico]
    have n_succ: 0 < n + 1 := by linarith
    rw[sum_eq_sum_Ico_succ_bot n_succ]
    simp
  rw[hk]
  simp
  have neg_pow_mul_choose_mul_eq_mul_sub:  ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * k * (choose n k) = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hyn : y ≤ n := by
      have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
      linarith
    rw[mul_assoc, mul_assoc]
    congr 1
    rw[← cast_mul,← cast_mul]
    rw[choose_mul_eq_mul_sub' hyn hy1]
  rw[neg_pow_mul_choose_mul_eq_mul_sub]
  have neg_pow_cancel : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ k * n * (choose (n-1) (k-1)) =  ∑ k in Ico 1 (n + 1), (-1) ^ (k - 1) * (-1 : ℤ)* n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hnegy : (-1 : ℤ ) ^ y = (-1) ^ (y - 1 + 1)  := by
      rw[Nat.sub_add_cancel hy1]
    congr 2
  have neg_pow_mul_mul_mul : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ (k - 1) * (-1)* n * (choose (n-1) (k-1))  = ∑ k in Ico 1 (n + 1), (-1 : ℤ)*  ((-1) ^ (k - 1) * n * (choose (n-1) (k-1)) ) := by
    refine' sum_congr rfl fun y hy => _
    rw[mul_comm ((-1 : ℤ) ^ (y - 1)) (-1)]
    rw[mul_assoc,mul_assoc,mul_assoc]
  rw[neg_pow_cancel,neg_pow_mul_mul_mul]
  rw[← mul_sum]
  simp
  rw[sum_Ico_eq_sum_range]
  simp
  have sum_neg_comm : ∑ x in range n, (-1 : ℤ) ^ x * n * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x):= by
    refine' sum_congr rfl fun y hy => _
    congr 1
    rw[mul_comm]
  have sum_neg_assoc: ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * ((-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x)) := by
    refine' sum_congr rfl fun y hy => _
    rw[mul_assoc]
  rw[sum_neg_comm, sum_neg_assoc, ← mul_sum]
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  simp

------------------
-- theorem Int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
--     (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ)) = 0 := by
--   rw [Int.alternating_sum_range_choose, if_neg h0]
------------------

theorem mul_mul_div_succ_mul_choose_eq{n k: ℕ} :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
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


theorem mul_mul_div_succ_mul_choose{n k: ℕ} : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
  = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
  exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)


theorem mul_mul_div_succ_mul_choose_eq_succ{n k: ℕ} : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
  = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
  exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))


-- 定理1.3改写2 succ_mul_choose_eq
----------------------------------
theorem choose_mul_eq_mul_sub_div {n k: ℕ} : (((1/(k+1)) : ℝ) * choose n k) = (1/(n+1)) * choose (n+1) (k+1) := by
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


theorem neg_pow_mul_div_mul: ∑ k in range (n+1), ((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * ((1 / ((k + 1)) : ℝ )) * choose n k = ∑ k in range (n+1), (1/(n+1)) * (((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * choose (n+1) (k+1)) := by
    refine' sum_congr rfl fun y hy => _
    rw[mul_assoc, choose_mul_eq_mul_sub_div, ← mul_assoc]
    rw[mul_comm ((-1 : ℝ) ^ y * (1 / (↑y + 1))) (1 / (n + 1))]
    rw[← mul_assoc]
    rw[mul_assoc, mul_assoc,mul_assoc]


theorem sum_neg_pow_div_congr : ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x+1) * (1 / x) * (Nat.choose (n + 1) x) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
    rw[sum_Ico_eq_sum_range]
    simp

theorem sum_neg_pow_mul_div_succ_congr : ∑ x in range (n + 1), (-1 : ℝ) ^ x * (1 / (x + 1)) * (Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
  simp
  refine' sum_congr rfl fun y _ => _
  congr 2
  have h1: (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
    rw[add_comm, ← add_assoc]
    norm_num
    rw[pow_add]
    simp
  exact h1
  have h2: ((y + 1): ℝ)⁻¹ = ((1 + y): ℝ)⁻¹ := by rw[add_comm]
  exact h2
  have h3: Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y) := by rw[add_comm y 1]
  exact h3

theorem pow_neg_succ_succ{ y : ℕ }: (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
  rw[add_comm, ← add_assoc]
  norm_num
  rw[pow_add]
  simp

theorem sum_neg_pow_mul_div_mul_div {n k: ℕ}: ∑ k in range (n+1), ((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * ((1 / ((k + 1)) : ℝ )) * choose n k = 1 / (n+1) * ∑ k in range (n+1), 1 / (k+1)  := by
  have t13: ∑ k in range (n+1), ((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * ((1 / ((k + 1)) : ℝ )) * choose n k = ∑ k in range (n+1), (1/(n+1)) * (((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * choose (n+1) (k+1)) := by
    refine' sum_congr rfl fun y hy => _
    rw[mul_assoc, choose_mul_eq_mul_sub_div, ← mul_assoc]
    rw[mul_comm ((-1 : ℝ) ^ y * (1 / (↑y + 1))) (1 / (n + 1))]
    rw[← mul_assoc]
    rw[mul_assoc, mul_assoc,mul_assoc]
  rw[t13]
  rw[← mul_sum]
  congr 1
  have sum_neg_pow_div_congr : ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x+1) * (1 / x) * (Nat.choose (n + 1) x) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
    rw[sum_Ico_eq_sum_range]
    simp
  have pow_neg_succ_succ : ∑ x in range (n + 1), (-1 : ℝ) ^ x * (1 / (x + 1)) * (Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
    simp
    refine' sum_congr rfl fun y _ => _
    congr 2
    have h1: (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
      rw[add_comm, ← add_assoc]
      norm_num
      rw[pow_add]
      simp
    exact h1
    have h2: ((y + 1): ℝ)⁻¹ = ((1 + y): ℝ)⁻¹ := by rw[add_comm]
    exact h2
    have h3: Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y) := by rw[add_comm y 1]
    exact h3
  rw[pow_neg_succ_succ, ← sum_neg_pow_div_congr]
  rw[Ico_pow_choose]


theorem div_mul_Ico_eq_zero : 1 / (2 * m + 1) * ∑ l in Ico 0 (2 * m), (l+1) * (-1 : ℝ ) ^ (l+1) / choose (2 * m) l = 0 := by sorry
theorem Ico_neg_eq_succ : ∑ k in Ico 1 (2 * n), (-1 : ℝ) ^ (k - 1) / choose (2 * n) k = 1 / (n + 1) := by sorry


theorem two_even_congr(hnm: n = 2 * m)(hm : 0 < m) : ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / choose (2 * m) k := by
  rw[hnm]  -- 用 2 * m 替换 n
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  norm_num

theorem neg_pow_div_choose : ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), ((-1) * (-1 : ℝ) ^ (k - 1) ) / Nat.choose (2 * m) k := by
    refine' sum_congr rfl fun y hy => _
    congr 1
    have y_le_one : 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hy_cancel : (-1 : ℝ) ^ y = (-1 : ℝ) ^ (y - 1 + 1) := by
      rw[Nat.sub_add_cancel y_le_one]
    rw[hy_cancel]
    rw[_root_.pow_succ]

theorem sum_assoc : ∑ k in Ico 1 (2 * m), (-1 : ℝ) * (-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), (-1 : ℝ) * ((-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k) := by  --用mul_div结合律，方便后续提取-1
  refine' sum_congr rfl fun y _ => _
  rw[← mul_div]

theorem two_congr: 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / choose (2 * m) k = 2 + (-1) / (m + 1) := by  -- 第三个等式
  simp
  have neg_pow_div_choose : ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), ((-1) * (-1 : ℝ) ^ (k - 1) ) / Nat.choose (2 * m) k := by
    refine' sum_congr rfl fun y hy => _
    congr 1
    have y_le_one : 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hy_cancel : (-1 : ℝ) ^ y = (-1 : ℝ) ^ (y - 1 + 1) := by
      rw[Nat.sub_add_cancel y_le_one]
    rw[hy_cancel]
    rw[_root_.pow_succ]
  rw[neg_pow_div_choose]
  have sum_assoc : ∑ k in Ico 1 (2 * m), (-1 : ℝ) * (-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), (-1 : ℝ) * ((-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k) := by  --用mul_div结合律，方便后续提取-1
    refine' sum_congr rfl fun y _ => _
    rw[← mul_div]
  rw[sum_assoc]  -- 使用结合律
  rw[← mul_sum]  -- 提取 -1
  rw[Ico_neg_eq_succ]
  rw[mul_div]
  simp


theorem two_mul_div_add{m : ℕ }(hm : 0 < m) : 2 * (m + 1) / (m + 1)  + (-1 : ℝ) / (m + 1) = 2 + (-1 : ℝ) / (m + 1) := by
    congr 1
    rw[mul_div_assoc]
    simp
    have m_r : 0 < (m : ℝ) := by
      simp
      exact hm
    have hm_z : (m : ℝ) + 1 ≠ 0  := by
      linarith
    rw[div_self hm_z]


theorem add_neg_div {m : ℕ }(hm : 0 < m): 2 + (-1 : ℝ) / (m + 1) = (2 * m + 1) / (m + 1) := by   -- 第四个等式
  have two_m_div_add : 2 * (m + 1) / (m + 1)  + (-1 : ℝ) / (m + 1) = 2 + (-1 : ℝ) / (m + 1) := by
    congr 1
    rw[mul_div_assoc]
    simp
    have m_r : 0 < (m : ℝ) := by
      simp
      exact hm
    have hm_z : (m : ℝ) + 1 ≠ 0  := by
      linarith
    rw[div_self hm_z]
  rw[← two_m_div_add]
  rw[div_add_div_same]  -- 除法分配律
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  rw[mul_comm]

theorem mul_two_div_mul(hnm: n = 2 * m): (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  rw[hnm]


theorem even_choose(hnm: n = 2 * m)(hm : 0 < m) : ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = 2 * (n + 1) / (n + 2) := by
  rw[two_even_congr hnm hm]
  rw[two_congr]
  rw[add_neg_div hm]
  have mul_two_div_mul : (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
      rw[← div_eq_mul_one_div]
      rw[div_div]
      rw[add_mul, mul_comm (m : ℝ) 2]
      simp
      rw[← mul_div]
      rw[mul_right_comm]
      simp
      rw[hnm]
      rw[cast_mul]
      simp
  simp at mul_two_div_mul
  rw[mul_two_div_mul]


theorem odd_choose_sum(hnm: n = 2 * m + 1): ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ ) ^ k / choose (2 * m + 1) k := by
  rw[hnm]
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  norm_num

theorem Ico_odd_div_choose : ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ ) ^ k / choose (2 * m + 1) k = ∑ k in Ico 1 (2 * m + 1), k * (-1 : ℝ ) ^ k / (k * choose (2 * m + 1) k) := by
  refine' sum_congr rfl fun y hy => _
  have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy0 :  y ≠  0 := by linarith
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  rw[mul_div_mul_left]
  exact hy

theorem inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
  rw[div_eq_mul_one_div]
  rw[mul_comm, mul_assoc]


theorem Ico_even_odd: ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ ) ^ k / choose (2 * m + 1) k = 1 / (2 * m + 1) * ∑ k in Ico 1 (2 * m + 1), k * (-1 : ℝ ) ^ k / choose (2 * m) (k-1) := by  --第三个等式
  rw[mul_sum]  -- 改写目标右侧，将 1 / (2 * m + 1) 放入 ∑
  refine' sum_congr rfl fun y hy => _
  -- hk : 目标左侧分子分母同乘 k
  have hk :  (-1 : ℝ ) ^ y / choose (2 * m + 1) y = y * (-1 : ℝ ) ^ y / (y * choose (2 * m + 1) y) := by
    have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
    have hy0 :  y ≠ 0 := by linarith
    have hy : (y : ℝ) ≠ 0 := by
      simp
      exact hy0
    rw[mul_div_mul_left]  -- 核心定理
    exact hy
  rw[hk]
  --
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]  -- 核心定理， 改写目标左侧式子的分母
  simp
  rw[← div_div]  -- 运用结合律，将目标左侧式子分母拆开
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp


theorem Ico_div : 1 / (2 * m + 1) * ∑ k in Ico 1 (2 * m + 1), k * (-1 : ℝ ) ^ k / choose (2 * m) (k-1) = 1 / (2 * m + 1) * ∑ l in Ico 0 (2 * m), (l+1) * (-1 : ℝ ) ^ (l+1) / choose (2 * m) l := by
  rw[sum_Ico_eq_sum_range]
  simp
  rw[range_eq_Ico]
  apply Or.inl
  refine' sum_congr rfl fun y _ => _
  rw[add_comm]
  congr 2
  rw[add_comm]


theorem odd_choose (hnm: n = 2 * m + 1) : ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = 0 := by
    rw[odd_choose_sum hnm , Ico_even_odd, Ico_div]
    rw[div_mul_Ico_eq_zero]


theorem choose_even_odd(h: 0 < n): ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = (n + 1)/(n + 2) * (1 + (-1)^n) := by
  rcases Nat.even_or_odd' n with ⟨m, h1 | h2⟩
  · have hm : 0 < m := by linarith
    rw[even_choose h1 hm]
    have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
    rw[m_two]
    rw[Even.neg_one_pow ⟨m, rfl⟩]
    norm_num
    rw[mul_div_assoc, mul_comm]
  · rw[odd_choose h2]
    rw[h2, Odd.neg_one_pow ⟨m, rfl⟩]
    norm_num


theorem Ico_succ_mul_choose_eq: ∑ k in Ico 1 (n+1), k * (choose (2 * n) k) = ∑ k in Ico 1 (n+1), (2 * n) * (choose (2*n - 1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n  := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[choose_mul_eq_mul_sub' hkn hsk]


theorem Ico_choose: ∑ k in Ico 1 (n+1), k * ((choose (2*n + 1) k):ℝ) = ∑ k in Ico 1 (n+1), (2 * n + 1) * ((choose (2*n) (k-1)):ℝ) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n + 1 := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[← cast_mul]
    rw[choose_mul_eq_mul_sub' hkn hsk]
    simp

theorem bot_sum_mul_congr : ∑ k in range (n+1), ((k * choose (2 * n + 1) k):ℝ) = (2 * n + 1) * ∑ k in range n, ((choose (2*n) k):ℝ) := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]  -- 提出 f 0
  simp
  have h1: ∑ k in Ico 1 (n+1), k * ((choose (2*n + 1) k):ℝ) = ∑ k in Ico 1 (n+1), (2 * n + 1) * ((choose (2*n) (k-1)):ℝ) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n + 1 := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[← cast_mul]
    rw[choose_mul_eq_mul_sub' hkn hsk]
    simp
  rw[h1]
  rw[mul_sum]  -- 提出 2 * n + 1
  rw[sum_Ico_eq_sum_range]  -- 代换 l = k - 1
  simp


theorem mul_sum_choose : (2 * n + 1) * ∑ k in range n, ((choose (2*n) k):ℝ) = (2 * n + 1) * ((∑ k in range (n+1), ((choose (2*n) k):ℝ)) - ((choose (2*n) n):ℝ) ) := by
  congr 1
  rw[sum_range_succ]
  simp

theorem mul_sum_choose_sub_choose : (2 * n + 1) * ((∑ k in range (n+1), ((choose (2*n) k):ℝ)) - ((choose (2*n) n:ℝ))) = (2 * n + 1) * (2 ^ ( 2 * n - 1 ) - ((choose (2*n) n/ 2:ℝ))) := by
  rw[choose_eq_pow_add]
  congr 1
  rw[← add_sub]
  rw[div_two_sub_self]
  rw[← sub_eq_add_neg]


theorem sum_mul_choose_eq_mul_sub : ∑ k in range (n+1), ((k * choose (2 * n + 1) k):ℝ) = (2 * n + 1) * (2 ^ ( 2 * n - 1 ) - ((choose (2*n) n/ 2:ℝ))) := by
  rw[bot_sum_mul_congr, mul_sum_choose, mul_sum_choose_sub_choose]


/-
  例题 by oishi
-/
-- 例2
theorem sum_choose_eq_pow_add' (n : ℕ)(h : 1 ≤ n) : ∑ k in range (n+1), choose (2*n) k = 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n := by
  have h1 : ∑ k in range (n+1), choose (2*n) k + ∑ k in Ico (n+1) (2*n+1), choose (2*n) k = ((2^(2*n)) : ℝ) := by
    rw [←cast_add]
    rw [sum_range_add_sum_Ico, sum_range_choose (2*n), cast_pow]
    congr 1
    linarith
  have h2 : ∑ k in Ico (n+1) (2*n+1), choose (2*n) k = ∑ k in range (n+1), choose (2*n) k - choose (2*n) n := by
    have : 0 ≤ n := by exact Nat.zero_le n
    rw [range_eq_Ico, sum_Ico_succ_top this]
    simp
    rw [sum_Ico_eq_sum_range, two_mul]
    simp
    rw [←two_mul]
    have h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x)
            = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x) := by
      refine' sum_congr rfl fun k hk => _
      rw [←choose_symm, add_assoc, ←Nat.sub_sub, two_mul]
      simp
      rw [Nat.sub_sub]
      rw [mem_range] at hk
      linarith
    rw [h3, sum_range_reflect (fun x => choose (2*n) x) (n)]
  rw [h2, cast_sub, add_sub, ←two_mul] at h1
  have h3 : 2 * ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) = ((2 ^ (2 * n)) : ℝ) + ↑(Nat.choose (2 * n) n):= by
    rw [←h1, sub_add, sub_self, sub_zero]
  have h4 : ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) = ((1/2):ℝ) * (((2 ^ (2 * n)) : ℝ) + ↑(Nat.choose (2 * n) n)) := by
    rw [←h3,one_div,←mul_assoc]
    simp
  rw [h4, one_div, mul_add]
  congr 1
  have : 2 * n - 1 + 1 = 2*n := by
    rw [Nat.sub_add_cancel]
    linarith
  rw [←this, pow_add, pow_one, mul_comm]
  simp
  rw [sum_range_succ]
  have h6 : 0 ≤ ∑ x in range n, Nat.choose (2 * n) x := by
    exact Nat.zero_le (∑ x in range n, Nat.choose (2 * n) x)
  linarith

-- 定理1.3改写2 succ_mul_choose_eq



-- 例题3
theorem sum_div_succ_mul_choose {n k: ℕ} : ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k = (1/(n+1)) * (2^(n+1) - 1) := by
  have : ∑ k in range (n+1), ((1/(k+1)) : ℝ) * choose n k
        = ∑ k in range (n+1), ((1/(n+1)) : ℝ) * choose (n+1) (k+1) := by
        refine' sum_congr rfl fun y hy => _
        exact succ_mul_choose_eq''
  rw [this, ←mul_sum]
  congr 1
  rw [←one_add_one_eq_two]
  rw [add_pow 1 1 (n+1)]
  simp
  rw [sum_range_succ' _ (n + 1)]
  simp

-- 例题5
def delta (m n : ℕ) : ℕ :=
  if m = n then 1 else 0

theorem alternating_sum_choose_mul { m n : ℕ } (h : m ≤ n) :
  ( ∑ k in Ico m (n + 1), (-1 : ℤ) ^ k * (choose n k) * (choose k m) ) = (-1) ^ m * delta m n := by
  by_cases h_eq : m = n
  . rw [h_eq]
    simp [delta]
  . rw [delta]
    simp [h_eq]
    have h1 : ∀ m n i: ℕ, i ∈ Ico m (n+1) →
      (-1 : ℤ) ^ i * (choose n i) * (choose i m) = (-1 : ℤ) ^ i * (choose n m * choose (n-m) (i-m)) := by
      intro m n i hi
      simp_rw [mul_assoc, ←cast_mul]
      congr 1
      have h2 : i ≤ n := Nat.le_of_lt_succ (mem_Ico.mp hi).right
      have h3 : m ≤ i := (mem_Ico.mp hi).left
      rw [choose_mul h2 h3]
    rw [sum_congr rfl (h1 m n)]
    rw [sum_Ico_eq_sum_range]
    rw [add_comm, add_tsub_assoc_of_le h, add_comm]
    simp [pow_add,mul_assoc]
    rw [←mul_sum]
    simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum, ←mul_assoc, cast_comm]
    have h2 : 0 < n - m := tsub_pos_of_lt (lt_of_le_of_ne h h_eq)
    rw [pos_iff_ne_zero] at h2
    rw [Int.alternating_sum_range_choose_of_ne h2]
    simp


-- 例题6
theorem sum_Ico_choose_mul { m n : ℕ } (h : m ≤ n) :
  (∑ k in Ico m (n + 1), (choose n k) * (choose k m) = 2^(n-m) * choose n m) := by
  by_cases h_eq : m = n
  . rw [h_eq]
    simp
  case neg =>
    have h1 : ∀ m n i: ℕ, i ∈ Ico m (n+1) → (choose n i) * (choose i m) = (choose n m * choose (n-m) (i-m)) := by
      intro m n i hi
      have h2 : i ≤ n := Nat.le_of_lt_succ (mem_Ico.mp hi).right
      have h3 : m ≤ i := (mem_Ico.mp hi).left
      exact choose_mul h2 h3
    rw [sum_congr rfl (h1 m n)]
    rw [sum_Ico_eq_sum_range]
    simp
    rw [←mul_sum]
    rw [add_comm, add_tsub_assoc_of_le h, add_comm]
    rw [sum_range_choose]
    rw [mul_comm]

/-
  习题 by oishi

-/

-- 题1
theorem sum_two_pow_mul_choose {n : ℕ} : ∑ k in range (n+1), 2^k * choose n k = 3^n := by
  have : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * ↑(Nat.choose n m) = (2 + 1) ^ n :=
    (add_pow _ _ _).symm
  simp at this
  assumption

-- 题4
theorem alternating_sum_mul_mul_choose {n : ℕ} (h0 : 1 < n): ∑ k in range (n+1), (-1 : ℤ)^k * k * choose n k = 0 := by
  rw [range_eq_Ico]
  have hzero_lt_n : 0 < n+1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  simp [mul_assoc]
  have h1 : ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * (k * choose n k)
    = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * (n * choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    rw [←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq' h0 (mem_Ico.mp hy).left]
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]


-- 题5
theorem sum_div_succ_mul_choose_mul {n k : ℕ} (x : ℕ) (h : 0 < x): ∑ k in range (n+1), (((1/(k+1)) : ℝ) * choose n k * ((x^k) : ℝ))
                            = ((((1+x)^(n+1) : ℝ) - 1)) / ((n+1)*x):= by
  have h0 : ∑ k in range (n+1), (((1/(k+1)) : ℝ) * choose n k * ((x^k) : ℝ))
    = ∑ k in range (n+1), ((1/(n+1)) * choose (n+1) (k+1) * ((x^k) : ℝ)) := by
    refine' sum_congr rfl fun y hy => _
    rw [succ_mul_choose_eq'']
  rw [h0]
  simp_rw [mul_assoc]
  rw [←mul_sum]
  have h1 : 1 / (n + 1) * ∑ k in range (n + 1), Nat.choose (n + 1) (k + 1) * ((x ^ k) : ℝ)
            = 1 / ((n + 1) * x) * ∑ k in range (n + 1), Nat.choose (n + 1) (k + 1) * ((x ^ (k+1)) : ℝ) := by
            rw [mul_sum, mul_sum]
            rw [div_mul_eq_div_mul_one_div]
            refine' sum_congr rfl fun y hy => _
            rw [pow_add,mul_assoc]
            congr 1
            rw [←mul_assoc]
            rw [mul_comm  (1/(x:ℝ))  ((Nat.choose (n + 1) (y + 1)) : ℝ)]
            rw [mul_assoc]
            congr 1
            rw [div_mul,mul_comm]
            simp
            rw [mul_div_right_comm, div_self]
            simp
            have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
            exact Iff.mpr cast_ne_zero this
  rw [h1, div_eq_mul_one_div ((((1 + x) ^ (n + 1)):ℝ) - 1), mul_comm ((((1 + x) ^ (n + 1)):ℝ) - 1)]
  congr 1
  rw [range_eq_Ico]
  have h2 : ∑ k in Ico 0 (n + 1), (Nat.choose (n + 1) (k + 1)) * ((x ^ (k + 1)) : ℝ)
          = ∑ l in Ico (0 + 1) (n + 1 + 1), (Nat.choose (n + 1) l) * ((x ^ l) : ℝ) := by
          let f : ℕ → ℝ := fun k => ↑(Nat.choose (n + 1) k) * ↑(x ^ k)
          change ∑ k in Ico 0 (n + 1), f (k+1) = ∑ l in Ico (0+1) (n + 1 + 1), f l
          rw [sum_Ico_add']
  rw [h2]
  simp
  have h3 : ∑ k in Ico 1 (n + 1 + 1), (Nat.choose (n + 1) k) * ((x : ℝ) ^ k )
            = ∑ k in Ico 0 (n + 1 + 1), (Nat.choose (n + 1) k) * ((x : ℝ) ^ k) - 1 := by
            have : 0 < n + 2 := by exact succ_pos (n + 1)
            rw [sum_eq_sum_Ico_succ_bot this]
            simp
  rw [h3]
  simp [add_comm]
  rw [add_pow (x:ℝ) 1 (n+1)]
  rw [add_comm]
  refine' sum_congr rfl fun y hy => _
  simp [mul_comm]

-- 题6
theorem odd_sum_range_choose (n : ℕ) (h0 : n ≠ 0) : ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) else 0) = 2^(n-1) :=
  mul_right_injective₀ two_ne_zero <|
    calc
      2 * (∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) else 0))
        = ∑ k in range (n+1), (if k % 2 = 1 then 2 * ((choose n k) : ℤ) else 0) := by
          {
            rw [mul_sum]
            refine' sum_congr rfl fun y hy => _
            rw [ite_mul_zero_right (y % 2 = 1) 2 ((Nat.choose n y) : ℤ)]
          }
      _ = ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) + ((choose n k) : ℤ) else ((choose n k) : ℤ) - ((choose n k) : ℤ)) := by
          {
            refine' sum_congr rfl fun y hy => _
            congr 1
            rw [two_mul]
            simp
          }
      _ = ∑ k in range (n+1), ((if k % 2 = 1 then choose n k - (-1)^k * choose n k else choose n k - (-1)^k * choose n k) : ℤ) := by
          {
            refine' sum_congr rfl fun y fy => _
            split_ifs with h'
            . rw [←Nat.odd_iff] at h'
              rw [Odd.neg_one_pow h']
              rw [neg_one_mul]
              rw [sub_neg_eq_add]
            . rw [Nat.mod_two_ne_one, ←Nat.even_iff] at h'
              rw [Even.neg_one_pow h']
              simp
          }
      _ = ∑ k in range (n+1), ((choose n k - (-1)^k * choose n k) : ℤ) := by simp
      _ = 2^n := by
          {
            rw [sum_sub_distrib]
            rw [Int.alternating_sum_range_choose_of_ne h0]
            simp
            have := (add_pow (1:ℤ) 1 n).symm
            simpa [one_add_one_eq_two] using this
          }
      _ = 2^(n - 1 + 1) := by
          {
            have hone_le_one : 1 ≤ 1 := by linarith
            have hone_le_n : 1 ≤ n := by exact Iff.mpr one_le_iff_ne_zero h0
            rw [←tsub_tsub_assoc hone_le_n hone_le_one]
            simp
          }
      _ = 2 * 2^(n-1) := by
          {
            rw [add_one]
            rw [_root_.pow_succ 2 (n-1)]
          }


-- 题 10
theorem sum_range_choose_halfway_of_lt (n : ℕ) (h0 : 0 < n): ∑ k in range n, choose (2 * n - 1) k = 2^(2 * n - 2) :=
  have : ∑ k in range n, choose (2 * n - 1) k = ∑ k in Ico n (2 * n), choose (2 * n - 1) k := by
    have h1 : ∑ k in range n, choose (2 * n - 1) k
            = ∑ k in range n, choose (2 * n - 1) (2 * n - 1 - k) := by
      refine' sum_congr rfl fun y hy => _
      have : y ≤ 2 * n - 1 := by
        have h1 : y < n := mem_range.1 hy
        refine le_pred_of_lt ?h
        have h2 : n < 2 * n := by exact lt_two_mul_self h0
        exact Nat.lt_trans h1 h2
      rw [choose_symm this]
    rw [h1, range_eq_Ico]
    have : n ≤ 2 * n - 1 + 1 := by
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
      linarith
    rw [sum_Ico_reflect _ _ this]
    have h2 : 2 * n - 1 + 1 - n = n := by
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
      rw [two_mul]
      simp
    have h3 : 2 * n - 1 + 1 - 0 = 2 * n := by
      simp
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
    rw [h2, h3]
  mul_right_injective₀ two_ne_zero <|
    calc
      2 * (∑ k in range n, choose (2 * n - 1) k)
        = ∑ k in range n, choose (2 * n - 1) k + ∑ k in Ico n (2 * n), choose (2 * n - 1) k := by rw [two_mul, this]
      _ =  ∑ k in range (2 * n), choose (2 * n - 1) k := sum_range_add_sum_Ico _ (by linarith)
      _ = ∑ k in range (2 * n - 1 + 1), choose (2 * n - 1) k := by
          {
            have : 1 ≤ 2 * n := by linarith
            rw [Nat.sub_add_cancel this]
          }
      _ = 2^(2 * n - 1) := sum_range_choose (2 * n - 1)
      _ = 2^(2 * n - 2 + 1)  := by
          {
            congr 1
            rw [←tsub_tsub_assoc]
            linarith
            linarith
          }
      _ = 2 * 2^(2 * n - 2)  := by rw [Nat.pow_succ, mul_comm]


-- 题11：条件1
theorem sum_range_succ_eq_sum_range : ∑ k in range (n+1), (k * choose (2 * n) k) = (2 * n) * ∑ k in range n, (choose (2*n - 1) k) := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]
  simp
  have h1: ∑ k in Ico 1 (n+1), k * (choose (2 * n) k) = ∑ k in Ico 1 (n+1), (2 * n) * (choose (2*n - 1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[choose_mul_eq_mul_sub' hkn hsk]
  rw[h1]
  rw[mul_sum] -- 提出 2 * n + 1
  rw[sum_Ico_eq_sum_range] -- 代换 l = k - 1
  simp --∑ k in range (n+1), (k * choose (2 * n) k) = (2 * n) * ∑ k in range n, (choose (2*n - 1) k)


-- 题11
theorem sum_mul_choose_eq_mul_two_pow (h : 0 < n) : ∑ k in range (n+1), (k * choose (2 * n) k) = n * 2 ^ (2 * n - 1) := by
  rw[sum_range_succ_eq_sum_range]
  rw[sum_range_choose_halfway_of_lt n h] --(2 * n) * 2 ^ (2 * n - 2)
  rw[mul_comm 2 n, mul_assoc]
  congr 1
  rw[mul_comm]
  -- have h1 : 2 ^ (n * 2 - 1) = 2 ^ (n * 2 - 2 + 1) := by
  rw[← Nat.pow_succ]
  congr 1
  rw[Nat.succ_eq_add_one]
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  rw[h21]

-- 题16
theorem sum_mul_choose_eq_mul_choose (n : ℕ) (h : 1 ≤ n): ∑ k in range (n+1), k * choose (2*n) (n-k) = ((n * choose (2*n-1) n) : ℝ) := by
  calc
    ∑ k in range (n+1), k * choose (2*n) (n-k)
      = ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n) (n-k) := by
      {
        rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n) (n - x)]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
        congr 1
        norm_num
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n) (n-k) := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc]
      }
    _ = (-1 : ℝ) * ∑ k in range (n + 1), (↑(n + 1 - 1 - k) - ↑n) * ↑(Nat.choose (2 * n) (n + 1 - 1 - k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        rw [mem_range] at hk
        rw [←cast_sub]
        simp
        linarith
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), (k-(n:ℝ)) * choose (2*n) k := by
      {
        congr 1
        rw [sum_range_reflect (fun x => (x-(n:ℝ)) * choose (2*n) x) (n+1)]
      }
    _ = ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n) k := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [←neg_one_mul (k-(n:ℝ))]
        rw [mul_assoc]
      }
    _ = ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n) k := by
      {
        refine' sum_congr rfl fun k hk => _
        congr 1
        exact neg_sub (k:ℝ) (n:ℝ)
      }
    _ = ∑ k in range (n+1), ((n:ℝ) * choose (2*n) k - k * choose (2*n) k) := by
      {
        refine' sum_congr rfl fun k hk => _
        rw [sub_mul]
      }
    _ = ∑ k in range (n+1), (n:ℝ) * choose (2*n) k - ∑ k in range (n+1), k * choose (2*n) k := by
      {
        rw [sum_sub_distrib]
        congr 1
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n) x]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (∑ k in range (n+1), n * choose (2*n) k) - (∑ k in range (n+1), k * choose (2*n) k) := by -- 这里是在变换数据类型
      {
        rw [cast_sum (range (n+1)) fun x => n * Nat.choose (2 * n) x]
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = ∑ k in range (n+1), n * choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 1
        have : 0 < n := by linarith
        rw [sum_mul_choose_eq_mul_two_pow this]
      }
    _ = n * ∑ k in range (n+1), choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 1
        rw [←cast_mul,mul_sum]
      }
    _ = n * ((2^(2*n-1)) + (((1/2):ℝ) * choose (2*n) n)) - ((n * 2^(2*n-1)) :ℕ) := by
      {
        congr 2
        rw [sum_choose_eq_pow_add' n h]
      }
    _ =  n * (((1/2):ℝ) * choose (2*n) n) := by
      {
        rw [mul_add]
        rw [add_comm]
        simp
      }
    _ = n * ((1/2):ℝ) * ((2*n)! / ((n)! * (2*n -n)!)) := by
      {
        rw [choose_eq_factorial_div_factorial]
        rw [←mul_assoc,←cast_mul, ←cast_div]
        rw [two_mul, Nat.add_sub_cancel]
        exact factorial_mul_factorial_dvd_factorial_add n n
        rw [two_mul, Nat.add_sub_cancel]
        rw [cast_ne_zero]
        exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero n)
        linarith
      }
    _ = n * ((1/2):ℝ) * (((2:ℕ)*n-1+1)*((2:ℕ)*n-1)! / (n ! * n !)) := by
      {
        congr 1
        have : 2*n = 2*n-1+1 := by
          have : 1 ≤ 2*n := by rw [two_mul];linarith
          rw [Nat.sub_add_cancel this]
        rw [this]
        rw [Nat.factorial_succ (2*n-1)]
        rw [←this, cast_mul, ←cast_mul 2 n]
        rw [sub_add_cancel]
        congr 3
        rw [two_mul, Nat.add_sub_cancel]

      }
    _ = n * (((1/2):ℝ) * ((2:ℕ)*n)*((2:ℕ)*n-1)! / (n ! * n !)) := by
      {
        rw [sub_add_cancel, mul_assoc]
        congr 1
        rw [←cast_mul,←cast_mul,←cast_mul,←mul_div_assoc]
        congr 1
        rw [cast_mul,←mul_assoc]
      }
    _ = n * (n * ((2:ℕ)*n-1)! / (n ! * n !)) := by simp
    _ = n * (n * ((2:ℕ)*n-1)! / (n ! * (n * (n-1) !))) := by
      {
        congr 3
        have : n = n-1+1 := by rw [Nat.sub_add_cancel h]
        rw [this,Nat.factorial_succ (n-1)]
        simp [cast_mul]
      }
    _ = n * (((2:ℕ)*n-1)! / (n ! * (n-1) !)) := by
      {
        congr 1
        rw [mul_comm, mul_div_assoc]
        rw [←cast_mul, ←cast_mul, mul_comm (n !) _, cast_mul]
        rw [div_mul_eq_div_div,cast_mul,div_mul_eq_div_div]
        rw [div_self, ←div_mul_eq_div_div, mul_one_div, mul_comm ((n-1)! : ℝ) _]
        rw [cast_ne_zero]
        linarith
      }
    _ = n * choose (2*n-1) n := by
      {
        congr 1
        have : n-1 = 2*n-1-n := by
          rw [two_mul, Nat.add_sub_assoc h, add_sub_self_left n (n - 1)]
        rw [this]
        rw [choose_eq_factorial_div_factorial, cast_div, cast_mul]
        all_goals (try rw [←this])
        rw [two_mul, Nat.add_sub_assoc h]
        exact factorial_mul_factorial_dvd_factorial_add n (n-1)
        rw [cast_ne_zero]
        exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero (n-1))
        rw [two_mul]
        have h1 : n - 1 + n = n + n - 1 := by exact tsub_add_eq_add_tsub h
        rw [←h1]
        exact Nat.le_add_left n (n - 1)
      }



theorem sum_mul_choose_eq_two_pow' (n : ℕ) (h : 1 ≤ n) :((∑ k in range (n+1), k * choose (2*n+1) k):ℝ)
                        = ((n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n) : ℝ) :=
  have h_gt_zero : 0 < n + 1 := by linarith
  have h1 : ∑ k in Ico 1 (n + 1), k * choose (2*n) k = ∑ k in range (n+1), k * choose (2*n) k := by
    rw [range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
    simp
  have h2 : ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1)
          = ∑ k in range (n+1), (k+1) * choose (2*n) k - (n+1) * choose (2*n) n := by
    rw [sum_Ico_eq_sum_range, sum_range_succ]
    simp [add_comm]
  have h3 : ∑ k in range (n+1), (k+1) * choose (2*n) k
          = ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k := by
    rw [←sum_add_distrib]
    refine' sum_congr rfl fun k hk => _
    rw [add_mul]
    simp
  calc
    ((∑ k in range (n+1), k * choose (2*n+1) k) : ℝ) = ∑ k in Ico 1 (n + 1), k * choose (2*n+1) k := by
      {
        rw [range_eq_Ico]
        rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
        simp
      }
    _ = ∑ k in Ico 1 (n + 1), k * (choose (2*n) k + choose (2*n) (k-1)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        have : k = k-1+1 := by
          rw [Nat.sub_add_cancel]
          rw [mem_Ico] at hk
          exact hk.left
        rw [this, choose_succ_succ' (2*n) (k-1), ←this, add_comm]
      }
    _ = ∑ k in Ico 1 (n + 1), (k * choose (2*n) k + k * choose (2*n) (k-1)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [mul_add]
      }
    _ = ∑ k in Ico 1 (n + 1), k * choose (2*n) k + ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1) := by
      {
        rw [←cast_add]
        congr 1
        rw [sum_add_distrib]
      }
    _ = ∑ k in range (n+1), k * choose (2*n) k
      + ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k - (n+(1:ℕ)) * choose (2*n) n := by
      {
        rw [h1, h2]
        rw [cast_sub, ←add_sub_assoc]
        congr 1
        rw [add_assoc]
        congr 1
        rw [h3, cast_add]
        rw [←cast_add, ←cast_mul]
        rw [sum_range_succ]
        have : 0 ≤ ∑ k in range n, (k + 1) * Nat.choose (2 * n) k := by
          exact Nat.zero_le (∑ k in range n, (k + 1) * Nat.choose (2 * n) k)
        linarith
      }
    _ = 2*(n:ℝ)*2^(2*n-1) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
      {
        have : 0 < n := by linarith
        have h1 : n ≠ 0 := by linarith
        rw [←two_mul, sum_mul_choose_eq_mul_two_pow this, sum_choose_eq_pow_add' n h]
        congr 1
        rw [cast_mul, ←mul_assoc, ←add_assoc]
        congr 3
        rw [cast_pow]
        congr 1
        congr 2
        rw [cast_one]
      }
    _ = n*2^(2*n) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
      {
        congr 3
        rw [←cast_comm, mul_assoc]
        congr 1
        have : 2*n = 2*n-1+1 := by
          have : 1 ≤ 2*n := by rw [two_mul]; linarith
          rw [Nat.sub_add_cancel this]
        rw [this, pow_add, ←this, pow_one, mul_comm]
      }
    _ = n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n := by
      {
        rw [add_sub_assoc]
        rw [one_div_two_mul_choose_sub_succ_mul_choose n h]
        congr 1
        rw [←neg_one_mul ((2 * n + 1) * (Nat.choose (2 * n - 1) n) : ℝ)]
        rw [←mul_assoc, neg_one_mul]
      }


-- 题17
theorem sum_mul_choose_eq_pow_mul_sub (n : ℕ) (h : 1 ≤ n) : ∑ k in range (n+1), k * choose (2*n+1) (n-k) = (((2*n+1) * choose (2*n-1) n - 2^(2*n-1)) : ℝ) :=
  calc
    ∑ k in range (n+1), k * choose (2*n+1) (n-k)
      = ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n+1) (n-k) := by
      {
        rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n + 1) (n - x)]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
        congr 1
        norm_num
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n+1) (n-k) := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc]
      }
    _ = (-1 : ℝ) * ∑ k in range (n + 1), (↑(n + 1 - 1 - k) - ↑n) * ↑(Nat.choose (2 * n + 1) (n + 1 - 1 - k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        rw [mem_range] at hk
        rw [←cast_sub]
        simp
        linarith
      }
    _ = (-1 : ℝ) * ∑ k in range (n+1), (k-(n:ℝ)) * choose (2*n+1) k := by
      {
        congr 1
        rw [sum_range_reflect (fun x => (x-(n:ℝ)) * choose (2*n+1) x) (n+1)]
      }
    _ = ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n+1) k := by
      {
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [←neg_one_mul (k-(n:ℝ))]
        rw [mul_assoc]
      }
    _ = ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n+1) k := by
      {
        refine' sum_congr rfl fun k hk => _
        congr 1
        exact neg_sub (k:ℝ) (n:ℝ)
      }
    _ = ∑ k in range (n+1), ((n:ℝ) * choose (2*n+1) k - k * choose (2*n+1) k) := by
      {
        refine' sum_congr rfl fun k hk => _
        rw [sub_mul]
      }
    _ = ∑ k in range (n+1), (n:ℝ) * choose (2*n+1) k - ∑ k in range (n+1), k * choose (2*n+1) k := by
      {
        rw [sum_sub_distrib]
        congr 1
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n + 1) x]
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (∑ k in range (n+1), n * choose (2*n+1) k) - (∑ k in range (n+1), k * choose (2*n+1) k) := by -- 这里是在变换数据类型
      {
        rw [cast_sum (range (n+1)) fun x => n * Nat.choose (2 * n + 1) x]
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [cast_mul]
      }
    _ = (n*2^(2*n)) - ((n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n) : ℝ) := by
      {
        rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n + 1) x]
        simp_rw [cast_mul]
        rw [sum_mul_choose_eq_two_pow' n h]
        congr 1
        rw [←mul_sum, sum_range_choose_halfway n]
        have : 4 = 2^2 := by exact rfl
        rw [this, ←pow_mul, cast_mul, cast_pow]
        congr 1
      }
    _ = (2*n+1) * choose (2*n-1) n - 2^(2*n-1) := by
      {
        rw [←add_sub, ←sub_sub, sub_self, ←sub_add, add_comm]
        congr 1
        simp
      }



-- 题20
theorem choose_mul_add_pow (n l : ℕ) (x : ℝ) (h : l ≤ n): ∑ k in Ico l (n+1), (choose n k) * (choose k l) * x^k * (1 - x)^(n - k)
                                        = (choose n l) * x^l :=
  calc
    ∑ k in Ico l (n+1), (choose n k) * (choose k l) * x^k * (1 - x)^(n - k)
      = ∑ k in Ico l (n+1), (choose n l) * (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k) := by
      {
        refine' sum_congr rfl fun k hk => _
        congr 2
        rw [mem_Ico] at hk
        rw [←cast_mul,←cast_mul]
        rw [choose_mul]
        linarith
        exact hk.left
      }
    _ = (choose n l) * ∑ k in Ico l (n+1), (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k) := by
      {
        rw [mul_sum]
        simp [mul_assoc]
      }
    _ = (choose n l) * ∑ k in range (n+1-l), (choose (n-l) k) * x^(l+k) * (1 - x)^(n-(l+k)) := by
      {
        rw [sum_Ico_eq_sum_range]
        simp
      }
    _ = (choose n l) * ∑ k in range (n+1-l), x^(l+k) * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        rw [mul_comm]
      }
    _ = (choose n l) * ∑ k in range (n+1-l), x^l * x^k * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [pow_add]
      }
    _ = (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
      {
        rw [mul_assoc]
        repeat rw [mul_sum]
        simp [mul_assoc]
      }
    _ = (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^((n-l)-k) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 2
        exact sub_add_eq n l k
      }
    _ = (choose n l) * x^l * ∑ k in range (n-l+1), x^k * (1 - x)^((n-l)-k) * (choose (n-l) k) := by
      {
        have : n+1-l = n-l+1 := by rw [succ_sub h]
        rw [this]
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc,mul_assoc]
        congr 1
        rw [mul_comm]
      }
    _ = (choose n l) * x^l * (x + (1-x))^(n-l) := by rw [←add_pow (x:ℝ) (1-x) (n-l)]
    _ = (choose n l) * x^l * (1)^(n-l) := by
      {
        rw [add_sub]
        congr 2
        rw [add_sub_right_comm x 1 x, sub_self]
        simp
      }
    _ = (choose n l) * x^l := by
      {
        rw [one_pow]
        simp
      }


open Nat

open Finset

open BigOperators

variable {R : Type*}

namespace Commute

variable [Semiring R] {x y : R}{β : Type v}
variable [CommMonoid β]

namespace exp_test

theorem add_two_sub: 2 * n + 1 - n = n + 1 := by
 rw[two_mul]
 rw[add_assoc]
 rw[add_comm]
 simp

theorem add_two_subY(n y : ℕ): n - (2 * n - y) =(-1:ℝ)*(n - y) := by
 simp
 rw[two_mul]
 rw[sub_eq_neg_add]
 rw[neg_sub]
 rw[sub_eq_neg_add]
 rw[neg_add]
 rw[sub_eq_neg_add]
 rw[add_assoc]
 rw[add_comm]
 rw[← add_assoc]
 rw[add_comm]
 congr 1
 rw[add_assoc]
 simp

theorem Transit_item: ∑ k in Ico (2*n + 1 - n) (2 * n + 1 - 1), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) =
        ∑ k in Ico (n+1) (2 * n), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) := by
        rw[add_two_sub]
        simp

theorem prod_Ico_reflect_two (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ 2*n + 1) :
    (∏ j in Ico k m, f (2*n - j)) = ∏ j in Ico (2*n + 1 - m) (2*n + 1 - k), f j := by
  have : ∀ i < m, i ≤ 2*n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  cases' lt_or_le k m with hkm hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine' (prod_image _).symm
    simp only [mem_Ico]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
  · have : 2*n + 1 - k ≤ 2*n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [ge_iff_le, hkm, Ico_eq_empty_of_le, prod_empty, tsub_le_iff_right, Ico_eq_empty_of_le
      this]

theorem sum_Ico_reflect_two {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ 2 * n + 1) : (∑ j in Ico k m, f (2 * n - j)) = ∑ j in Ico (2 * n + 1 - m) (2 * n + 1 - k), f j :=
  @prod_Ico_reflect_two (Multiplicative δ) _ f k m n h


theorem Ico_simpn (hn : 1 ≤ n): ∑ k in Ico 1 (n+1), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) =
   ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ) ) := by
    rw [sum_Ico_succ_top hn]
    simp
