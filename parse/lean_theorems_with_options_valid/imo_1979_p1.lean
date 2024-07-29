import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem imo_1979_p1
  (p q : ℕ)
  (h₀ : 0 < q)
  (h₁ : ∑ k in Finset.Icc (1 : ℕ) 1319, ((-1:ℤ)^(k + 1) * ((1)/k)) = p/q) :
  1979 ∣ p := by lean_repl sorry
