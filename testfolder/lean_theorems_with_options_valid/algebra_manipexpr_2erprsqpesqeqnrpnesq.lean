import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem algebra_manipexpr_2erprsqpesqeqnrpnesq
  (e r : ℂ) :
  2 * (e * r) + (e^2 + r^2) = (-r + (-e))^2 := by lean_repl sorry
