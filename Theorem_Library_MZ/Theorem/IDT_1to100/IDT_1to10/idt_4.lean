import Mathlib.Data.Nat.Choose.Sum


#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"


open Nat

open Finset

open BigOperators



theorem idt4 (n : ℕ) : (∑ m in range (n + 1), choose n m) = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this
