import Theorem.example_separate.two_mod_two_pow
import Mathlib.Data.Nat.ModEq


open Nat

theorem choose_add_div_distrib( hn : n ≠ 0 ) :
 ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 =
  (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
    have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
    rw[Nat.add_div_of_dvd_left h_mod]


theorem choose_add_div_distrib_from_0_to_0(n : ℕ)(hn : n ≠ 0)(gol:  (choose (2 * n) n + 2 ^ (2 * n)) / 2 = choose (2 * n) n / 2 + 2 ^ (2 * n) / 2) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = choose (2 * n) n / 2 + 2 ^ (2 * n) / 2 := by
  have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
  apply gol

theorem choose_add_div_distrib_from_0_to_1(n : ℕ)(hn : n ≠ 0) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = choose (2 * n) n / 2 + 2 ^ (2 * n) / 2 := by
  have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
  rw[Nat.add_div_of_dvd_left h_mod]

theorem choose_add_div_distrib_from_1_to_1(n : ℕ)(hn : n ≠ 0)(h_mod : 2 ∣ 2 ^ (2 * n)) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = choose (2 * n) n / 2 + 2 ^ (2 * n) / 2 := by
  rw[Nat.add_div_of_dvd_left h_mod]

