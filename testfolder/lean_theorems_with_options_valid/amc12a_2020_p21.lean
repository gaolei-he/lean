import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12a_2020_p21
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 5 ∣ n ∧ Nat.lcm 5! n = 5 * Nat.gcd 10! n) :
  S.card = 48 := by lean_repl sorry
