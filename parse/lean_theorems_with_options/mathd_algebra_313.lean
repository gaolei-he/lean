import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_313
  (v i z : ℂ)
  (h₀ : v = i * z)
  (h₁ : v = 1 + Complex.I)
  (h₂ : z = 2 - Complex.I) :
  i = 1/5 + 3/5 * Complex.I := by lean_repl sorry
