import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem induction_sum2kp1npqsqm1
  (n : ℕ) :
  ∑ k in (Finset.range n), 2 * k + 3 = (n + 1)^2 - 1 := by lean_repl sorry
