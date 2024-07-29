import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1990_p2 :
  (52 + 6 * Real.sqrt 43)^(3 / 2) - (52 - 6 * Real.sqrt 43)^(3 / 2) = 828 := by lean_repl sorry
