import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_314
  (n : ℕ)
  (h₀ : n = 11) :
  (1 / 4)^(n + 1) * 2^(2 * n) = 1 / 4 := by lean_repl sorry
