import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem induction_nfactltnexpnm1ngt3
  (n : ℕ)
  (h₀ : 3 ≤ n) :
  n! < n^(n - 1) := by lean_repl sorry
