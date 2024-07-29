import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem amc12_2000_p12
  (a m c : ℕ)
  (h₀ : a + m + c = 12) :
  a*m*c + a*m + m*c + a*c ≤ 112 := by lean_repl sorry
