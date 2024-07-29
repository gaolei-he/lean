import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_48
  (q e : ℂ)
  (h₀ : q = 9 - 4 * Complex.I)
  (h₁ : e = -3 - 4 * Complex.I) : q - e = 12 := by lean_repl sorry
