import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_239 :
  (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by lean_repl sorry