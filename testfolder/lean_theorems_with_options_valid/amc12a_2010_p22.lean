import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12a_2010_p22
  (x : ℝ) :
  49 ≤ ∑ k in Finset.Icc (1:ℕ) 119, abs (↑k * x - 1) := by lean_repl sorry
