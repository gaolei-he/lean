import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Nat.Basic

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

variable {α β : Type*}

namespace Nat

@[simp, norm_cast]
theorem cast_mul [NonAssocSemiring α] (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_succ, mul_add, *]

#align nat.cast_mul Nat.cast_mul
