import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_192
  (q e d : ℂ)
  (h₀ : q = 11 - (5 * Complex.I))
  (h₁ : e = 11 + (5 * Complex.I))
  (h₂ : d = 2 * Complex.I) :
  q * e * d = 292 * Complex.I := by lean_repl sorry
