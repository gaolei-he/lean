import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_3 :
  (∑ x in Finset.range 10, ((x + 1)^2)) % 10 = 5 := by lean_repl sorry
