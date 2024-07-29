import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_756
  (a b : ℝ)
  (h₀ : 2^a = (32 : ℝ))
  (h₁ : a^b = 125) :
  b^a = 243 := by lean_repl sorry
