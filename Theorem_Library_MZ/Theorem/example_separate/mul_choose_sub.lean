import Theorem.example_separate.choose_mul_eq_mul_sub

open Nat


theorem mul_choose_sub {l : ℕ }(hh1: l ≤ n - 1)(hh2: 1 ≤ l) :
  l * choose ( n - 1 ) l = (n - 1) * choose (n-2) (l-1) := by
    rw[mul_comm]
    rw[choose_mul_eq_mul_sub (hh1) (hh2)]
    rw[Nat.sub_sub, Nat.sub_one]


theorem mul_choose_sub_from_0_to_0(n l : ℕ)(hh1 : l ≤ n - 1)(hh2 : 1 ≤ l)(gol:  choose (n - 1) l * l = (n - 1) * choose (n - 2) (l - 1)) :
   l * choose (n - 1) l = (n - 1) * choose (n - 2) (l - 1) := by
  rw[mul_comm]
  apply gol

theorem mul_choose_sub_from_0_to_1(n l : ℕ)(hh1 : l ≤ n - 1)(hh2 : 1 ≤ l)(gol:  (n - 1) * choose (n - 1 - 1) (l - 1) = (n - 1) * choose (n - 2) (l - 1)) :
   l * choose (n - 1) l = (n - 1) * choose (n - 2) (l - 1) := by
  rw[mul_comm]
  rw[choose_mul_eq_mul_sub (hh1) (hh2)]
  apply gol

theorem mul_choose_sub_from_0_to_2(n l : ℕ)(hh1 : l ≤ n - 1)(hh2 : 1 ≤ l) :
   l * choose (n - 1) l = (n - 1) * choose (n - 2) (l - 1) := by
  rw[mul_comm]
  rw[choose_mul_eq_mul_sub (hh1) (hh2)]
  rw[Nat.sub_sub, Nat.sub_one]

theorem mul_choose_sub_from_1_to_1(n l : ℕ)(hh1 : l ≤ n - 1)(hh2 : 1 ≤ l)(gol:  (n - 1) * choose (n - 1 - 1) (l - 1) = (n - 1) * choose (n - 2) (l - 1)) :
   choose (n - 1) l * l = (n - 1) * choose (n - 2) (l - 1) := by
  rw[choose_mul_eq_mul_sub (hh1) (hh2)]
  apply gol

theorem mul_choose_sub_from_1_to_2(n l : ℕ)(hh1 : l ≤ n - 1)(hh2 : 1 ≤ l) :
   choose (n - 1) l * l = (n - 1) * choose (n - 2) (l - 1) := by
  rw[choose_mul_eq_mul_sub (hh1) (hh2)]
  rw[Nat.sub_sub, Nat.sub_one]

theorem mul_choose_sub_from_2_to_2(n l : ℕ)(hh1 : l ≤ n - 1)(hh2 : 1 ≤ l) :
   (n - 1) * choose (n - 1 - 1) (l - 1) = (n - 1) * choose (n - 2) (l - 1) := by
  rw[Nat.sub_sub, Nat.sub_one]

