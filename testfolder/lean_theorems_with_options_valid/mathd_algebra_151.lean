import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_151 :
  Int.ceil (Real.sqrt 27) - Int.floor (Real.sqrt 26) = 1 := by lean_repl sorry
