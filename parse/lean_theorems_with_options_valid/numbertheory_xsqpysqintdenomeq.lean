import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem numbertheory_xsqpysqintdenomeq
  (x y : ℚ)
  (h₀ : (x^2 + y^2).den = 1) :
  x.den = y.den := by lean_repl sorry
