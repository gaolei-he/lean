import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_96
  (x y z a : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : Real.log x - Real.log y = a)
  (h₂ : Real.log y - Real.log z = 15)
  (h₃ : Real.log z - Real.log x = -7) :
  a = -8 := by lean_repl sorry
