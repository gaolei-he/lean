import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∑ k in (Finset.Icc (2 : ℕ) 10000), (1 / Real.sqrt k) < 198 := by lean_repl sorry
