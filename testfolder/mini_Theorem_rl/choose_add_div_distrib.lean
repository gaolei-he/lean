import Theorem.example_separate.two_mod_two_pow
import Mathlib.Data.Nat.ModEq
import Lean4Repl

open Nat

set_option maxHeartbeats 999999999999999999999999
theorem choose_add_div_distrib( hn : n ≠ 0 ) : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by lean_repl sorry
    rw[Nat.add_div_of_dvd_left]
    exact two_mod_two_pow hn
