import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

set_option maxHeartbeats 999999999999999999999999
theorem two_mod_two_pow( hn : n ≠ 0 ) : 2 ∣ (2 ^ (2 * n)) := by lean_repl sorry
  exact dvd_pow_self _ (Nat.mul_ne_zero_iff.mpr ⟨by simp, hn⟩)
