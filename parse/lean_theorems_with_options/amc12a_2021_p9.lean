import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12a_2021_p9 :
  ∏ k in Finset.range 7, (2^(2^k) + 3^(2^k)) = 3^128 - 2^128 := by lean_repl sorry
