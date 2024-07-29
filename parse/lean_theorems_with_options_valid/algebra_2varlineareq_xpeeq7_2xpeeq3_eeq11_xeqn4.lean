import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4
  (x e : ℂ)
  (h₀ : x + e = 7)
  (h₁ : 2 * x + e = 3) :
  e = 11 ∧ x = -4 := by lean_repl sorry
