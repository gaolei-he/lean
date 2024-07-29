import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_461
  (n : ℕ)
  (h₀ : n = Finset.card (Finset.filter (λ x => Nat.gcd x 8 = 1) (Finset.Icc 1 7))) :
  (3^n) % 8 = 1 := by lean_repl sorry
