import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_43 :
  IsGreatest {n : ℕ | 15^n ∣ 942! } 233 := by lean_repl sorry
