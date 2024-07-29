import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem induction_seq_mul2pnp1
  (n : ℕ)
  (u : ℕ → ℕ)
  (h₀ : u 0 = 0)
  (h₁ : ∀ n, u (n + 1) = 2 * u n + (n + 1)) :
  u n = 2^(n + 1) - (n + 2) := by lean_repl sorry
