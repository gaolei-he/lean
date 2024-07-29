import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Ring.Commute

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers: lemmas about `Commute`

-/

variable {α β : Type*}

namespace Nat

section Commute

theorem cast_commute [NonAssocSemiring α] (n : ℕ) (x : α) : Commute (n : α) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)
#align nat.cast_commute Nat.cast_commute

theorem cast_comm [NonAssocSemiring α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).eq
#align nat.cast_comm Nat.cast_comm


end Commute
