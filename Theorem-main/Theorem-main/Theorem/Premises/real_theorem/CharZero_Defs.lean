import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.NormCast.Tactic
import Mathlib.Tactic.Cases
import Mathlib.Algebra.NeZero

#align_import algebra.char_zero.defs from "leanprover-community/mathlib"@"d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d"

set_option autoImplicit true

class CharZero (R) [AddMonoidWithOne R] : Prop where
  /-- An additive monoid with one has characteristic zero if the canonical map `ℕ → R` is
  injective. -/
  cast_injective : Function.Injective (Nat.cast : ℕ → R)
#align char_zero CharZero

namespace Nat

variable [AddMonoidWithOne R] [CharZero R]

theorem cast_injective : Function.Injective (Nat.cast : ℕ → R) :=
  CharZero.cast_injective
#align nat.cast_injective Nat.cast_injective

@[simp, norm_cast]
theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n :=
  cast_injective.eq_iff
#align nat.cast_inj Nat.cast_inj

@[simp, norm_cast]
theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]
#align nat.cast_eq_zero Nat.cast_eq_zero

@[norm_cast]
theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
#align nat.cast_ne_zero Nat.cast_ne_zero

theorem cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 := by
  -- porting note: old proof was `exact_mod_cast n.succ_ne_zero`
  norm_cast
  exact n.succ_ne_zero
#align nat.cast_add_one_ne_zero Nat.cast_add_one_ne_zero

@[simp, norm_cast]
theorem cast_eq_one {n : ℕ} : (n : R) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]
#align nat.cast_eq_one Nat.cast_eq_one

@[norm_cast]
theorem cast_ne_one {n : ℕ} : (n : R) ≠ 1 ↔ n ≠ 1 :=
  cast_eq_one.not
#align nat.cast_ne_one Nat.cast_ne_one

end Nat
