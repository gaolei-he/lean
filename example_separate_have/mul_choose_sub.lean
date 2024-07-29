import Theorem.example_separate.choose_mul_eq_mul_sub

open Nat


theorem mul_choose_sub {l : ℕ }(hh1: l ≤ n - 1)(hh2: 1 ≤ l) :
  l * choose ( n - 1 ) l = (n - 1) * choose (n-2) (l-1) := by
    rw[mul_comm]
    rw[choose_mul_eq_mul_sub (hh1) (hh2)]
    rw[Nat.sub_sub, Nat.sub_one]
