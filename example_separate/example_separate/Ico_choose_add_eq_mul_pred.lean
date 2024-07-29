import AdaLean.add_div_two
import AdaLean.choose_mul_eq_mul_sub
import AdaLean.mul_choose_sub
import AdaLean.ico_mul_choose_sub

open Nat

open Finset

open BigOperators

theorem Ico_choose_add_eq_mul_pred(hn0 : 0 < n) : ∑ l in Ico 1 n, l * choose (n-1) l + 2 ^ ( n - 1 ) = (n - 1) * ∑ l in Ico 1 (n), choose (n-2) (l-1) + 2 ^ ( n - 1 ):= by
    rw[ico_mul_choose_sub hn0]
    rw[← mul_sum]
