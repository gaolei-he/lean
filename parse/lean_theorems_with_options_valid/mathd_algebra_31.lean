import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_31
  (x : NNReal)
  (u : ℕ → NNReal)
  (h₀ : ∀ n, u (n + 1) = NNReal.sqrt (x + u n))
  (h₁ : Filter.Tendsto u Filter.atTop (𝓝 9)) :
  9 = NNReal.sqrt (x + 9) := by lean_repl sorry
