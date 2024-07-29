import Theorem.example_separate.two_pow_div_two
import Mathlib.Data.Nat.ModEq


open Nat

theorem add_div_two(hn : n ≠ 0 ):
 ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 = 2 ^ ( 2 * n - 1 ) + (choose (2 * n) n) / 2:= by
  have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn

  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 =
   (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
   rw[Nat.add_div_of_dvd_left h_mod]
  rw[choose_add_div_distrib]
  rw[two_pow_div_two hn, add_comm]


theorem add_div_two_from_0_to_0(n : ℕ)(hn : n ≠ 0)(gol:  (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
  apply gol

theorem add_div_two_from_0_to_1(n : ℕ)(hn : n ≠ 0)(gol:  (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 =
   (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
   rw[Nat.add_div_of_dvd_left h_mod]
  apply gol

theorem add_div_two_from_0_to_2(n : ℕ)(hn : n ≠ 0)(gol:  choose (2 * n) n / 2 + 2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 =
   (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
   rw[Nat.add_div_of_dvd_left h_mod]
  rw[choose_add_div_distrib]
  apply gol

theorem add_div_two_from_0_to_3(n : ℕ)(hn : n ≠ 0) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  have h_mod : 2∣(2 ^ ( 2 * n )) := two_mod_two_pow hn
  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 =
   (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
   rw[Nat.add_div_of_dvd_left h_mod]
  rw[choose_add_div_distrib]
  rw[two_pow_div_two hn, add_comm]

theorem add_div_two_from_1_to_1(n : ℕ)(hn : n ≠ 0)(h_mod : 2 ∣ 2 ^ (2 * n))(gol:  (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 =
   (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
   rw[Nat.add_div_of_dvd_left h_mod]
  apply gol

theorem add_div_two_from_1_to_2(n : ℕ)(hn : n ≠ 0)(h_mod : 2 ∣ 2 ^ (2 * n))(gol:  choose (2 * n) n / 2 + 2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 =
   (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
   rw[Nat.add_div_of_dvd_left h_mod]
  rw[choose_add_div_distrib]
  apply gol

theorem add_div_two_from_1_to_3(n : ℕ)(hn : n ≠ 0)(h_mod : 2 ∣ 2 ^ (2 * n)) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  have choose_add_div_distrib : ((choose (2 * n) n) + (2 ^ ( 2 * n ))) / 2 =
   (choose (2 * n) n) / 2 + (2 ^ ( 2 * n )) / 2 := by
   rw[Nat.add_div_of_dvd_left h_mod]
  rw[choose_add_div_distrib]
  rw[two_pow_div_two hn, add_comm]

theorem add_div_two_from_2_to_2(n : ℕ)(hn : n ≠ 0)(h_mod : 2 ∣ 2 ^ (2 * n))(choose_add_div_distrib : (choose (2 * n) n + 2 ^ (2 * n)) / 2 = choose (2 * n) n / 2 + 2 ^ (2 * n) / 2)(gol:  choose (2 * n) n / 2 + 2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  rw[choose_add_div_distrib]
  apply gol

theorem add_div_two_from_2_to_3(n : ℕ)(hn : n ≠ 0)(h_mod : 2 ∣ 2 ^ (2 * n))(choose_add_div_distrib : (choose (2 * n) n + 2 ^ (2 * n)) / 2 = choose (2 * n) n / 2 + 2 ^ (2 * n) / 2) :
   (choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  rw[choose_add_div_distrib]
  rw[two_pow_div_two hn, add_comm]

theorem add_div_two_from_3_to_3(n : ℕ)(hn : n ≠ 0)(h_mod : 2 ∣ 2 ^ (2 * n))(choose_add_div_distrib : (choose (2 * n) n + 2 ^ (2 * n)) / 2 = choose (2 * n) n / 2 + 2 ^ (2 * n) / 2) :
   choose (2 * n) n / 2 + 2 ^ (2 * n) / 2 = 2 ^ (2 * n - 1) + choose (2 * n) n / 2 := by
  rw[two_pow_div_two hn, add_comm]

