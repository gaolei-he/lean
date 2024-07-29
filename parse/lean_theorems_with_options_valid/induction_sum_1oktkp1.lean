import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem induction_sum_1oktkp1
  (n : ℕ) :
  ∑ k in (Finset.range n), (1 : ℝ) / ((k + 1) * (k + 2)) = n / (n + 1) := by lean_repl sorry
