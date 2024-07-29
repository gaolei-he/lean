import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem induction_pord1p1on2powklt5on2
  (n : ℕ)
  (h₀ : 0 < n) :
  ∏ k in Finset.Icc 1 n, (1 + (1:ℝ) / 2^k) < 5 / 2 := by lean_repl sorry
