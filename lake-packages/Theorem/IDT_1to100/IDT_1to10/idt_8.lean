import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
-- import Mathlib.Algebra.GroupWithZero.Defs


open Nat

-- theorem idt8 {n k : ℕ} (hk : k ≤ n) :
--  (n-k)*choose n k = k * choose (n-1) k  := by
--  rw [←nat.succ_sub hk, nat.succ_mul, ←choose_succ_self_right, mul_comm k]
--  rw [choose_zero, zero_mul]







--   cases k,
--   { rw [choose_zero, zero_mul],
--     refl },
-- --   { rw [←nat.succ_sub hk, nat.succ_mul, ←choose_succ_self_right, mul_comm k],
-- --     congr' 1,
--     ring }



--  induction' k with n ih
--  · simp
--  rw [sub_mul]
--  have h1: k ≤ n-1 := by linarith
--  rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial]
--  rw [mul_div]
-- --  rw [mul_assoc]
--  rw [mul_comm]
--  rw [mul_factorial_pred]
--  have h : k ! * (n - k)! ≠ 0 := by apply_rules [factorial_ne_zero, mul_ne_zero]
--  mul_right_cancel₀ h <|
--  calc
--    (n-k) * choose n k * (k ! * (n - k)!) =
--       (n-k) * n ! / (k ! * (n - k)!) * (k ! * (n - k)!):=
--     by rw [mul_assoc, mul_assoc,choose_eq_factorial_div_factorial hk]
-- -- --  rw [mul_]
--    _ =
--    -- k * choose (n-1) k * (k ! * (n - k)!) := by
