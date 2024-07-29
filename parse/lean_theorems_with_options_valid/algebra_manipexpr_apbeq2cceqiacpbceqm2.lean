import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem algebra_manipexpr_apbeq2cceqiacpbceqm2
  (a b c : ℂ)
  (h₀ : a + b = 2 * c)
  (h₁ : c = Complex.I) :
  a * c + b * c = -2 := by lean_repl sorry
