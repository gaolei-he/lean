-- This module serves as the root of the `Theorem` library.
-- Import modules here that should be built as part of the library.
-- import «Theorem».Basic
import Theorem.Basic

-- 自写定理所在位置
import Theorem.Premises.real_theorem.mini_theorem
import Theorem.Premises.example

-- Choose Theorem
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum

-- Nat Theorem
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Nat.Cast.Defs
import Init.Data.Nat.Basic

-- Real Theorem
import Mathlib.Algebra.Order.Sub.Canonical
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.Defs

-- Sum Theorem
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring

-- Extra Theorem
import Mathlib.Data.Nat.Interval
import Mathlib.Order.LocallyFinite
