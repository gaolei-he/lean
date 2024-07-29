import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem induction_sum_odd
  (n : ℕ) :
  ∑ k in (Finset.range n), 2 * k + 1 = n^2 := by lean_repl sorry
