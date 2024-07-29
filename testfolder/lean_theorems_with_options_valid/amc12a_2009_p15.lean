import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12a_2009_p15
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∑ k in Finset.Icc 1 n, (↑k * (Complex.I^k)) = 48 + 49 * Complex.I) :
  n = 97 := by lean_repl sorry
