import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import AdaLean.two_mod_two_pow


open Nat

theorem choose_add_div_distrib(hn : n ≠ 0) : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
  rw[Nat.add_div_of_dvd_left]
  exact two_mod_two_pow hn
