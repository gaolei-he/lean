import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem algebra_sqineq_2at2pclta2c2p41pc
  (a c : ℝ) :
  2 * a * (2 + c) ≤ a^2 + c^2 + 4 * (1 + c) := by lean_repl sorry
