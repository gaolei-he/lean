import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem amc12_2001_p5 :
  Finset.prod (Finset.filter (λ x => ¬ Even x) (Finset.range 10000)) (id : ℕ → ℕ) = (10000!) / ((2^5000) * 5000!) := by lean_repl sorry
