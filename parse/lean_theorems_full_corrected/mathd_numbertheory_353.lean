import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_353
  (s : ℕ)
  (h₀ : s = ∑ k in Finset.Icc 2010 4018, k) :
  s % 2009 = 0 := by lean_repl sorry
