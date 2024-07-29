import Theorem.example_separate.add_div_two



theorem sub_two_add_one(h : 2 ≤ n ): n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
