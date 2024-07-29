import Theorem.example_separate.add_div_two

theorem lt_eq_le_sub{y:ℕ}(hn0 : 0 < n) : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a


theorem lt_eq_le_sub_from_0_to_0(n y : ℕ)(hn0 : 0 < n)(gol:  y ≤ n - 1 → y ≤ n - 1) :
   y < n → y ≤ n - 1 := by
  rw[Nat.lt_iff_le_pred hn0]
  apply gol

theorem lt_eq_le_sub_from_0_to_1(n y : ℕ)(hn0 : 0 < n)(gol:  y ≤ n - 1) :
   y < n → y ≤ n - 1 := by
  rw[Nat.lt_iff_le_pred hn0]
  intro a
  apply gol

theorem lt_eq_le_sub_from_0_to_2(n y : ℕ)(hn0 : 0 < n) :
   y < n → y ≤ n - 1 := by
  rw[Nat.lt_iff_le_pred hn0]
  intro a
  exact a

theorem lt_eq_le_sub_from_1_to_1(n y : ℕ)(hn0 : 0 < n)(gol:  y ≤ n - 1) :
   y ≤ n - 1 → y ≤ n - 1 := by
  intro a
  apply gol

theorem lt_eq_le_sub_from_1_to_2(n y : ℕ)(hn0 : 0 < n) :
   y ≤ n - 1 → y ≤ n - 1 := by
  intro a
  exact a

theorem lt_eq_le_sub_from_2_to_2(n y : ℕ)(hn0 : 0 < n)(a : y ≤ n - 1) :
   y ≤ n - 1 := by
  exact a

