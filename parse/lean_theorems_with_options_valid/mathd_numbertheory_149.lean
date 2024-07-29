import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_149 :
  ∑ k in (Finset.filter (λ x => x % 8 = 5 ∧ x % 6 = 3) (Finset.range 50)), k = 66 := by lean_repl sorry
