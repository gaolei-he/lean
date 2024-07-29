import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_76
  (f : ℤ → ℤ)
  (h₀ : ∀n, Odd n → f n = n^2)
  (h₁ : ∀ n, Even n → f n = n^2 - 4*n -1) :
  f 4 = -1 := by lean_repl sorry
