import Theorem.example_separate.add_div_two
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem add_div_two_eq_distrib(hn : n ≠ 0) : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by lean_repl sorry
