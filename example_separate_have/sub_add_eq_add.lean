import Theorem.example_separate.add_div_two

theorem sub_add_eq_add(h: 2 ≤ n) : n - 1 + 2 = n + 1 := by
  have h1: 1 ≤ n := by linarith
  have sub_add_eq_sub_add_add_add : n - 1 + 2 = n - 1 + 1 + 1 := by norm_num
  rw[sub_add_eq_sub_add_add_add]
  rw [Nat.sub_add_cancel h1]
