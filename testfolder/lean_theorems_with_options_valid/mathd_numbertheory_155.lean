import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_155 :
  Finset.card (Finset.filter (λ x => x % 19 = 7) (Finset.Icc 100 999)) = 48 := by lean_repl sorry
