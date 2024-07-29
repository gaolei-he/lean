import Mathlib.Data.Nat.Choose.Basic

theorem nat_sub_add_cancel {n:ℕ} (hn: 1<=n) : n -1 +1 = n :=by
    rw [tsub_add_cancel_of_le]
    exact hn
