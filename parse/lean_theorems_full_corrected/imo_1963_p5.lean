import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem imo_1963_p5 :
  Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7) = 1 / 2 := by lean_repl sorry
