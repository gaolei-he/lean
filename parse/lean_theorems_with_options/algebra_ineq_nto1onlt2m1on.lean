import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem algebra_ineq_nto1onlt2m1on
  (n : ℕ) :
  n^(1 / n) < 2 - 1 / n := by lean_repl sorry
