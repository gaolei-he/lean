import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_64 :
  IsLeast {x : ℕ | 30 * x ≡ 42 [MOD 47]} 39 := by lean_repl sorry
