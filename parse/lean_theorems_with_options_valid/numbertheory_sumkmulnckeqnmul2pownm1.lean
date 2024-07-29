import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem numbertheory_sumkmulnckeqnmul2pownm1
  (n : ℕ)
  (h₀ : 0 < n) :
  ∑ k in Finset.Icc 1 n, (k * Nat.choose n k) = n * 2^(n - 1) := by lean_repl sorry
