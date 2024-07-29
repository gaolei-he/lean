import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Powerset

#align_import algebra.big_operators.ring from "leanprover-community/mathlib"@"b2c89893177f66a48daf993b7ba5ef7cddeff8c9"

universe u v w

open BigOperators

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {b : β} {f g : α → β}

section Semiring

variable [NonUnitalNonAssocSemiring β]

theorem sum_mul : (∑ x in s, f x) * b = ∑ x in s, f x * b :=
  map_sum (AddMonoidHom.mulRight b) _ s
#align finset.sum_mul Finset.sum_mul

theorem mul_sum : (b * ∑ x in s, f x) = ∑ x in s, b * f x :=
  map_sum (AddMonoidHom.mulLeft b) _ s
#align finset.mul_sum Finset.mul_sum

end Semiring

theorem sum_div [DivisionSemiring β] {s : Finset α} {f : α → β} {b : β} :
    (∑ x in s, f x) / b = ∑ x in s, f x / b := by simp only [div_eq_mul_inv, sum_mul]
#align finset.sum_div Finset.sum_div


end Finset
