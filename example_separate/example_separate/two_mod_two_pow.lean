import Mathlib.Data.Nat.Choose.Sum



theorem two_mod_two_pow( hn : n ≠ 0 ) : 2 ∣ (2 ^ (2 * n)) := by
  have h20: 2 ≠ 0 := by simp
  have h2: 2 * n ≠ 0 := by exact Nat.mul_ne_zero_iff.mpr ⟨h20, hn⟩
  exact dvd_pow_self _ h2
