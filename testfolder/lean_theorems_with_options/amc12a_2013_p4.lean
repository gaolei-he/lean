import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12a_2013_p4 :
  (2^2014 + 2^2012) / (2^2014 - 2^2012) = (5:ℝ) / 3 := by lean_repl sorry
