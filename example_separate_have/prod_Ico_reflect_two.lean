import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

variable [CommMonoid β]



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
