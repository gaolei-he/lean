import Theorem.example_separate.two_mod_two_pow
import Mathlib.Data.Nat.ModEq


open Nat

theorem choose_add_div_distrib( hn : n ≠ 0 ) : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
    have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
    rw[Nat.add_div_of_dvd_left h_mod]
