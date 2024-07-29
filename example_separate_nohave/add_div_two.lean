import Theorem.example_separate.two_pow_div_two
import Mathlib.Data.Nat.ModEq


open Nat

theorem add_div_two(hn : n ≠ 0 ):((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = 2 ^ ( 2 * n - 1 ) + (choose (2 * n) n) / 2:= by
  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
    have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
    rw[Nat.add_div_of_dvd_left h_mod]
  rw[choose_add_div_distrib]
  rw[two_pow_div_two hn, add_comm]
