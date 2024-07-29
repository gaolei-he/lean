import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem numbertheory_sqmod4in01d
  (a : ℤ) :
  (a^2 % 4) = 0 ∨ (a^2 % 4) = 1 := by lean_repl sorry
