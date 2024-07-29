import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem amc12b_2020_p22
  (t : ℝ) :
  ((2^t - 3 * t) * t) / (4^t) ≤ 1 / 12 := by lean_repl sorry
