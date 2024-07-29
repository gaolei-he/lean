import Theorem.example_separate.add_div_two

theorem lt_eq_le_sub{y:ℕ}(hn0 : 0 < n) : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
