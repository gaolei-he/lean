import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_211 :
  Finset.card (Finset.filter (λ n => 6 ∣ (4 * ↑n - (2 : ℤ))) (Finset.range 60)) = 20 := by lean_repl sorry
