
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SplitIfs

#align_import data.nat.cast.defs from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

protected def Nat.unaryCast {R : Type u} [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1
#align nat.unary_cast Nat.unaryCast

#align has_nat_cast NatCast
#align has_nat_cast.nat_cast NatCast.natCast

#align nat.cast Nat.cast


class Nat.AtLeastTwo (n : ℕ) : Prop where
  prop : n ≥ 2

instance instNatAtLeastTwo : Nat.AtLeastTwo (n + 2) where
  prop := Nat.succ_le_succ $ Nat.succ_le_succ $ Nat.zero_le _


@[nolint unusedArguments]
instance instOfNat [NatCast R] [Nat.AtLeastTwo n] : OfNat R n where
  ofNat := n.cast


class AddMonoidWithOne (R : Type u) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl
#align add_monoid_with_one AddMonoidWithOne
#align add_monoid_with_one.to_has_nat_cast AddMonoidWithOne.toNatCast
#align add_monoid_with_one.to_add_monoid AddMonoidWithOne.toAddMonoid
#align add_monoid_with_one.to_has_one AddMonoidWithOne.toOne
#align add_monoid_with_one.nat_cast_zero AddMonoidWithOne.natCast_zero
#align add_monoid_with_one.nat_cast_succ AddMonoidWithOne.natCast_succ

/-- An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`.  -/
class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R
#align add_comm_monoid_with_one AddCommMonoidWithOne
#align add_comm_monoid_with_one.to_add_monoid_with_one AddCommMonoidWithOne.toAddMonoidWithOne
#align add_comm_monoid_with_one.to_add_comm_monoid AddCommMonoidWithOne.toAddCommMonoid


namespace Nat
variable [AddMonoidWithOne R]

@[simp, norm_cast]
theorem cast_zero : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero
#align nat.cast_zero Nat.cast_zero

@[simp 500, norm_cast 500]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOne.natCast_succ _
#align nat.cast_succ Nat.cast_succ

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succ _
#align nat.cast_add_one Nat.cast_add_one

end Nat

namespace Nat

@[simp, norm_cast]
theorem cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by
  rw [cast_succ, Nat.cast_zero, zero_add]
#align nat.cast_one Nat.cast_oneₓ

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne R] (m n : ℕ) : ((m + n : ℕ) : R) = m + n := by
  induction n <;> simp [add_succ, add_assoc, Nat.add_zero, Nat.cast_one, Nat.cast_zero, *]
#align nat.cast_add Nat.cast_addₓ

theorem cast_two [AddMonoidWithOne R] : ((2 : ℕ) : R) = (2 : R) := rfl
#align nat.cast_two Nat.cast_two

attribute [simp, norm_cast] Int.natAbs_ofNat

end Nat


theorem one_add_one_eq_two [AddMonoidWithOne α] : 1 + 1 = (2 : α) := by
  rw [←Nat.cast_one, ←Nat.cast_add]
  apply congrArg
  decide
#align one_add_one_eq_two one_add_one_eq_two

theorem two_add_one_eq_three [AddMonoidWithOne α] : 2 + 1 = (3 : α) := by
  rw [←one_add_one_eq_two, ←Nat.cast_one, ←Nat.cast_add, ←Nat.cast_add]
  apply congrArg
  decide

theorem three_add_one_eq_four [AddMonoidWithOne α] : 3 + 1 = (4 : α) := by
  rw [←two_add_one_eq_three, ←one_add_one_eq_two, ←Nat.cast_one,
    ←Nat.cast_add, ←Nat.cast_add, ←Nat.cast_add]
  apply congrArg
  decide
