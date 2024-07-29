import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Real.Basic


open Nat


theorem Real_choose_eq_choose_add(h1:1 ≤ n)(h2:1 ≤ k) : (choose n k : ℝ) = (choose (n-1) k : ℝ)  + (choose (n-1) (k-1): ℝ) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  simp


theorem Real_choose_eq_choose_add_from_0_to_0(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  apply gol

theorem Real_choose_eq_choose_add_from_0_to_1(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  apply gol

theorem Real_choose_eq_choose_add_from_0_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  apply gol

theorem Real_choose_eq_choose_add_from_0_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  ↑(choose (n - 1) (k - 1) + choose (n - 1) (succ (k - 1))) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  apply gol

theorem Real_choose_eq_choose_add_from_0_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  ↑(choose (n - 1) (succ (k - 1)) + choose (n - 1) (k - 1)) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  apply gol

theorem Real_choose_eq_choose_add_from_0_to_5(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  simp

theorem Real_choose_eq_choose_add_from_1_to_1(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  rw[choose_eq_choose_sub_add]
  apply gol

theorem Real_choose_eq_choose_add_from_1_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  apply gol

theorem Real_choose_eq_choose_add_from_1_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1) (k - 1) + choose (n - 1) (succ (k - 1))) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  apply gol

theorem Real_choose_eq_choose_add_from_1_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1) (succ (k - 1)) + choose (n - 1) (k - 1)) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  apply gol

theorem Real_choose_eq_choose_add_from_1_to_5(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1))) :
   ↑(choose n k) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  simp

theorem Real_choose_eq_choose_add_from_2_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  apply gol

theorem Real_choose_eq_choose_add_from_2_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1) (k - 1) + choose (n - 1) (succ (k - 1))) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  apply gol

theorem Real_choose_eq_choose_add_from_2_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1) (succ (k - 1)) + choose (n - 1) (k - 1)) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  apply gol

theorem Real_choose_eq_choose_add_from_2_to_5(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1))) :
   ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  have choose_sub_eq_choose_sub_add :
   ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  simp

theorem Real_choose_eq_choose_add_from_3_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(choose_sub_eq_choose_sub_add : ↑(choose (n - 1) k) = ↑(choose (n - 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1) (k - 1) + choose (n - 1) (succ (k - 1))) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  apply gol

theorem Real_choose_eq_choose_add_from_3_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(choose_sub_eq_choose_sub_add : ↑(choose (n - 1) k) = ↑(choose (n - 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1) (succ (k - 1)) + choose (n - 1) (k - 1)) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  apply gol

theorem Real_choose_eq_choose_add_from_3_to_5(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(choose_sub_eq_choose_sub_add : ↑(choose (n - 1) k) = ↑(choose (n - 1) (k - 1 + 1))) :
   ↑(choose (n - 1 + 1) (k - 1 + 1)) = ↑(choose (n - 1) k) + ↑(choose (n - 1) (k - 1)) := by
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  simp

theorem Real_choose_eq_choose_add_from_4_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(choose_sub_eq_choose_sub_add : ↑(choose (n - 1) k) = ↑(choose (n - 1) (k - 1 + 1)))(gol:  ↑(choose (n - 1) (succ (k - 1)) + choose (n - 1) (k - 1)) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1))) :
   ↑(choose (n - 1) (k - 1) + choose (n - 1) (succ (k - 1))) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1)) := by
  rw[add_comm]
  apply gol

theorem Real_choose_eq_choose_add_from_4_to_5(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(choose_sub_eq_choose_sub_add : ↑(choose (n - 1) k) = ↑(choose (n - 1) (k - 1 + 1))) :
   ↑(choose (n - 1) (k - 1) + choose (n - 1) (succ (k - 1))) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1)) := by
  rw[add_comm]
  simp

theorem Real_choose_eq_choose_add_from_5_to_5(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(choose_eq_choose_sub_add : ↑(choose n k) = ↑(choose (n - 1 + 1) (k - 1 + 1)))(choose_sub_eq_choose_sub_add : ↑(choose (n - 1) k) = ↑(choose (n - 1) (k - 1 + 1))) :
   ↑(choose (n - 1) (succ (k - 1)) + choose (n - 1) (k - 1)) = ↑(choose (n - 1) (k - 1 + 1)) + ↑(choose (n - 1) (k - 1)) := by
  simp

