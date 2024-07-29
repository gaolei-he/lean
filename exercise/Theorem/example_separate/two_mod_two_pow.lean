import Mathlib.Data.Nat.Choose.Sum



theorem two_mod_two_pow( hn : n ≠ 0 ) : 2 ∣ (2 ^ (2 * n)) := by
  have h20: 2 ≠ 0 := by simp
  have h2: 2 * n ≠ 0 := by exact Nat.mul_ne_zero_iff.mpr ⟨h20, hn⟩
  exact dvd_pow_self _ h2


theorem two_mod_two_pow_from_0_to_0(n : ℕ)(hn : n ≠ 0)(gol:  2 ∣ 2 ^ (2 * n)) :
   2 ∣ 2 ^ (2 * n) := by
  have h20: 2 ≠ 0 := by simp
  apply gol

theorem two_mod_two_pow_from_0_to_1(n : ℕ)(hn : n ≠ 0)(gol:  2 ∣ 2 ^ (2 * n)) :
   2 ∣ 2 ^ (2 * n) := by
  have h20: 2 ≠ 0 := by simp
  have h2: 2 * n ≠ 0 := by exact Nat.mul_ne_zero_iff.mpr ⟨h20, hn⟩
  apply gol

theorem two_mod_two_pow_from_0_to_2(n : ℕ)(hn : n ≠ 0) :
   2 ∣ 2 ^ (2 * n) := by
  have h20: 2 ≠ 0 := by simp
  have h2: 2 * n ≠ 0 := by exact Nat.mul_ne_zero_iff.mpr ⟨h20, hn⟩
  exact dvd_pow_self _ h2

theorem two_mod_two_pow_from_1_to_1(n : ℕ)(hn : n ≠ 0)(h20 : 2 ≠ 0)(gol:  2 ∣ 2 ^ (2 * n)) :
   2 ∣ 2 ^ (2 * n) := by
  have h2: 2 * n ≠ 0 := by exact Nat.mul_ne_zero_iff.mpr ⟨h20, hn⟩
  apply gol

theorem two_mod_two_pow_from_1_to_2(n : ℕ)(hn : n ≠ 0)(h20 : 2 ≠ 0) :
   2 ∣ 2 ^ (2 * n) := by
  have h2: 2 * n ≠ 0 := by exact Nat.mul_ne_zero_iff.mpr ⟨h20, hn⟩
  exact dvd_pow_self _ h2

theorem two_mod_two_pow_from_2_to_2(n : ℕ)(hn : n ≠ 0)(h20 : 2 ≠ 0)(h2 : 2 * n ≠ 0) :
   2 ∣ 2 ^ (2 * n) := by
  exact dvd_pow_self _ h2

