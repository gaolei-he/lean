import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1983_p1
  (x y z w : ℕ)
  (ht : 1 < x ∧ 1 < y ∧ 1 < z)
  (hw : 0 ≤ w)
  (h0 : Real.log w / Real.log x = 24)
  (h1 : Real.log w / Real.log y = 40)
  (h2 : Real.log w / Real.log (x * y * z) = 12):
  Real.log w / Real.log z = 60 := by lean_repl sorry
