import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem induction_sumkexp3eqsumksq
  (n : ℕ) :
  ∑ k in Finset.range n, k^3 = (∑ k in Finset.range n, k)^2 := by lean_repl sorry
