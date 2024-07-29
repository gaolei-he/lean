import Theorem.example_separate.add_div_two


theorem pow_eq_sub_one_mul(hn :0 < n) :  2 ^ n = 2 ^ (n - 1) * 2  := by
    have n1 : 1 ≤ n := by linarith
    have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
      rw[Nat.sub_add_cancel n1]
    rw[← h2n]
    rw[Nat.pow_succ]
