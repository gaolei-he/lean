
import Mathlib.Data.Finset.LocallyFinite

#align_import data.nat.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"



open Finset Nat

instance : LocallyFiniteOrder ℕ where
  finsetIcc a b := ⟨List.range' a (b + 1 - a), List.nodup_range' _ _⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range' _ _⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range' _ _⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range' _ _⟩
  finset_mem_Icc a b x := by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]
    cases le_or_lt a b with
    | inl h => rw [add_tsub_cancel_of_le (Nat.lt_succ_of_le h).le, Nat.lt_succ_iff]
    | inr h =>
      rw [tsub_eq_zero_iff_le.2 (succ_le_of_lt h), add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)
  finset_mem_Ico a b x := by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]
    cases le_or_lt a b with
    | inl h => rw [add_tsub_cancel_of_le h]
    | inr h =>
      rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2.le)
  finset_mem_Ioc a b x := by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]
    cases le_or_lt a b with
    | inl h =>
      rw [← succ_sub_succ, add_tsub_cancel_of_le (succ_le_succ h), Nat.lt_succ_iff, Nat.succ_le_iff]
    | inr h =>
      rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.le.trans hx.2)
  finset_mem_Ioo a b x := by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1, ← tsub_add_eq_tsub_tsub]
    cases le_or_lt (a + 1) b with
    | inl h => rw [add_tsub_cancel_of_le h, Nat.succ_le_iff]
    | inr h =>
      rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)

variable (a b c : ℕ)

namespace Nat

theorem Iio_eq_range : Iio = range := by
  ext b x
  rw [mem_Iio, mem_range]
#align nat.Iio_eq_range Nat.Iio_eq_range

@[simp]
theorem Ico_zero_eq_range : Ico 0 = range := by rw [← bot_eq_zero, ← Iio_eq_Ico, Iio_eq_range]
#align nat.Ico_zero_eq_range Nat.Ico_zero_eq_range

theorem _root_.Finset.range_eq_Ico : range = Ico 0 :=
  Ico_zero_eq_range.symm
#align finset.range_eq_Ico Finset.range_eq_Ico

end Nat
