import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.example_separate.choose_mul_eq_mul_sub'


open Nat

open Finset

open BigOperators

-- theorem idt6_Absorption_Idt{n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) : k * (choose n k)  = n * choose (n - 1) (k - 1) := by
--     have choose_mul_eq_choose_mul :  choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by rw[mul_comm, choose_mul hkn hsk]
--     rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
--     rw[choose_mul_eq_choose_mul]


theorem succ_mul_choose'{n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :k * (choose n k)  = (n:ℝ) * choose (n - 1) (k - 1) :=by
    rw [← cast_mul, ← cast_mul]
    rw [choose_mul_eq_mul_sub' hkn hsk]
