import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1997_p11
  (x : ℝ)
  (h₀ : x = (∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * Real.pi / 180)) / (∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * Real.pi / 180))) :
  Int.floor (100 * x) = 241 := by lean_repl sorry
