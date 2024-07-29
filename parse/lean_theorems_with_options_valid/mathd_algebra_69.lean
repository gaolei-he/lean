import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_69
  (rows seats : ℕ)
  (h₀ : rows * seats = 450)
  (h₁ : (rows + 5) * (seats - 3) = 450) :
  rows = 25 := by lean_repl sorry
