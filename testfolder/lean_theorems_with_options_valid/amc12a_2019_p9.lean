import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12a_2019_p9
  (a : ℕ → ℚ)
  (h₀ : a 1 = 1)
  (h₁ : a 2 = 3 / 7)
  (h₂ : ∀ n, a (n + 2) = (a n * a (n + 1)) / (2 * a n - a (n + 1))) :
  ↑(a 2019).den + (a 2019).num = 8078 := by lean_repl sorry