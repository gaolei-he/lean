import AdaLean.two_pow_div_two
import Mathlib.Data.Nat.ModEq
import AdaLean.two_mod_two_pow

open Nat

theorem add_div_two(hn : n ≠ 0 ):((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = 2 ^ ( 2 * n - 1 ) + (choose (2 * n) n) / 2:= by
  rw[Nat.add_div_of_dvd_left]
  rw[two_pow_div_two hn, add_comm]
  exact two_mod_two_pow hn
