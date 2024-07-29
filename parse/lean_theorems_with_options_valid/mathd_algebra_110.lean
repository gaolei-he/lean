import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_110
  (q e : ℂ)
  (h₀ : q = 2 - 2 * Complex.I)
  (h₁ : e = 5 + 5 * Complex.I) :
  q * e = 20 := by lean_repl sorry
