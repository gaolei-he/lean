import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by lean_repl sorry
