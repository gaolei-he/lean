import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_227
  (x y n : ℕ+)
  (h₀ : ↑x / (4:ℝ) + y / 6 = (x + y) / n) :
  n = 5 := by lean_repl sorry
