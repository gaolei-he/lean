import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_629 :
  IsLeast {t : ℕ | 0 < t ∧ (Nat.lcm 12 t)^3 = (12 * t)^2} 18 := by lean_repl sorry
