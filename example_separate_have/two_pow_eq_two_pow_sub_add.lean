import Theorem.example_separate.add_div_two


theorem two_pow_eq_two_pow_sub_add(h: 2 ≤ n) : 2 ^ ( n - 1 ) = 2 ^ ( n - 2 + 1 ) := by
  have sub_add_eq_sub: n - 2 + 1 = n - 1 := by
    exact tsub_add_eq_add_tsub h
  rw[sub_add_eq_sub]
