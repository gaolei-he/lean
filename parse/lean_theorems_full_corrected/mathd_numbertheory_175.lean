import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_175 :
  (2^2010) % 10 = 4 := by lean_repl sorry
