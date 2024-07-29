/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.RingTheory.Localization.Basic

#align_import ring_theory.localization.away.basic from "leanprover-community/mathlib"@"a7c017d750512a352b623b1824d75da5998457d0"

/-!
# Localizations away from an element

## Main definitions

 * `IsLocalization.Away (x : R) S` expresses that `S` is a localization away from `x`, as an
   abbreviation of `IsLocalization (Submonoid.powers x) S`.
 * `exists_reduced_fraction' (hb : b ≠ 0)` produces a reduced fraction of the form `b = a * x^n` for
   some `n : ℤ` and some `a : R` that is not divisible by `x`.

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section Away

variable (x : R)

/-- Given `x : R`, the typeclass `IsLocalization.Away x S` states that `S` is
isomorphic to the localization of `R` at the submonoid generated by `x`. -/
abbrev Away (S : Type*) [CommSemiring S] [Algebra R S] :=
  IsLocalization (Submonoid.powers x) S
#align is_localization.away IsLocalization.Away

namespace Away

variable [IsLocalization.Away x S]

/-- Given `x : R` and a localization map `F : R →+* S` away from `x`, `invSelf` is `(F x)⁻¹`. -/
noncomputable def invSelf : S :=
  mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩
#align is_localization.away.inv_self IsLocalization.Away.invSelf

@[simp]
theorem mul_invSelf : algebraMap R S x * invSelf x = 1 := by
  convert IsLocalization.mk'_mul_mk'_eq_one (M := Submonoid.powers x) (S := S) _ 1
  symm
  apply IsLocalization.mk'_one
#align is_localization.away.mul_inv_self IsLocalization.Away.mul_invSelf

variable {g : R →+* P}

/-- Given `x : R`, a localization map `F : R →+* S` away from `x`, and a map of `CommSemiring`s
`g : R →+* P` such that `g x` is invertible, the homomorphism induced from `S` to `P` sending
`z : S` to `g y * (g x)⁻ⁿ`, where `y : R, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def lift (hg : IsUnit (g x)) : S →+* P :=
  IsLocalization.lift fun y : Submonoid.powers x =>
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, g.map_pow]
      exact IsUnit.map (powMonoidHom n : P →* P) hg
#align is_localization.away.lift IsLocalization.Away.lift

@[simp]
theorem AwayMap.lift_eq (hg : IsUnit (g x)) (a : R) : lift x hg ((algebraMap R S) a) = g a :=
  IsLocalization.lift_eq _ _
#align is_localization.away.away_map.lift_eq IsLocalization.Away.AwayMap.lift_eq

@[simp]
theorem AwayMap.lift_comp (hg : IsUnit (g x)) : (lift x hg).comp (algebraMap R S) = g :=
  IsLocalization.lift_comp _
#align is_localization.away.away_map.lift_comp IsLocalization.Away.AwayMap.lift_comp

/-- Given `x y : R` and localizations `S`, `P` away from `x` and `x * y`
respectively, the homomorphism induced from `S` to `P`. -/
noncomputable def awayToAwayRight (y : R) [Algebra R P] [IsLocalization.Away (x * y) P] : S →+* P :=
  lift x <|
    show IsUnit ((algebraMap R P) x) from
      isUnit_of_mul_eq_one ((algebraMap R P) x) (mk' P y ⟨x * y, Submonoid.mem_powers _⟩) <| by
        rw [mul_mk'_eq_mk'_of_mul, mk'_self]
#align is_localization.away.away_to_away_right IsLocalization.Away.awayToAwayRight

variable (S) (Q : Type*) [CommSemiring Q] [Algebra P Q]

/-- Given a map `f : R →+* S` and an element `r : R`, we may construct a map `Rᵣ →+* Sᵣ`. -/
noncomputable def map (f : R →+* P) (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (f r) Q] : S →+* Q :=
  IsLocalization.map Q f
    (show Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f by
      rintro x ⟨n, rfl⟩
      use n
      simp)
#align is_localization.away.map IsLocalization.Away.map

end Away

end Away

variable [IsLocalization M S]

section AtUnits

variable (R) (S)

/-- The localization away from a unit is isomorphic to the ring. -/
noncomputable def atUnit (x : R) (e : IsUnit x) [IsLocalization.Away x S] : R ≃ₐ[R] S :=
  atUnits R (Submonoid.powers x)
    (by rwa [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff])
#align is_localization.at_unit IsLocalization.atUnit

/-- The localization at one is isomorphic to the ring. -/
noncomputable def atOne [IsLocalization.Away (1 : R) S] : R ≃ₐ[R] S :=
  @atUnit R _ S _ _ (1 : R) isUnit_one _
#align is_localization.at_one IsLocalization.atOne

theorem away_of_isUnit_of_bijective {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] {r : R} (hr : IsUnit r) (H : Function.Bijective (algebraMap R S)) :
    IsLocalization.Away r S :=
  { map_units' := by
      rintro ⟨_, n, rfl⟩
      exact (algebraMap R S).isUnit_map (hr.pow _)
    surj' := fun z => by
      obtain ⟨z', rfl⟩ := H.2 z
      exact ⟨⟨z', 1⟩, by simp⟩
    exists_of_eq := fun {x y} => by
      erw [H.1.eq_iff]
      rintro rfl
      exact ⟨1, rfl⟩ }
#align is_localization.away_of_is_unit_of_bijective IsLocalization.away_of_isUnit_of_bijective

end AtUnits

end IsLocalization

namespace Localization

open IsLocalization

variable {M}

/-- Given a map `f : R →+* S` and an element `r : R`, such that `f r` is invertible,
  we may construct a map `Rᵣ →+* S`. -/
noncomputable abbrev awayLift (f : R →+* P) (r : R) (hr : IsUnit (f r)) :
    Localization.Away r →+* P :=
  IsLocalization.Away.lift r hr
#align localization.away_lift Localization.awayLift

/-- Given a map `f : R →+* S` and an element `r : R`, we may construct a map `Rᵣ →+* Sᵣ`. -/
noncomputable abbrev awayMap (f : R →+* P) (r : R) :
    Localization.Away r →+* Localization.Away (f r) :=
  IsLocalization.Away.map _ _ f r
#align localization.away_map Localization.awayMap

end Localization

end CommSemiring

open Localization

variable {R : Type*} [CommRing R]

section NumDen

open IsLocalization

variable (x : R)
variable (B : Type*) [CommRing B] [Algebra R B] [IsLocalization.Away x B]

/-- `selfZPow x (m : ℤ)` is `x ^ m` as an element of the localization away from `x`. -/
noncomputable def selfZPow (m : ℤ) : B :=
  if _ : 0 ≤ m then algebraMap _ _ x ^ m.natAbs else mk' _ (1 : R) (Submonoid.pow x m.natAbs)
#align self_zpow selfZPow

theorem selfZPow_of_nonneg {n : ℤ} (hn : 0 ≤ n) : selfZPow x B n = algebraMap R B x ^ n.natAbs :=
  dif_pos hn
#align self_zpow_of_nonneg selfZPow_of_nonneg

@[simp]
theorem selfZPow_natCast (d : ℕ) : selfZPow x B d = algebraMap R B x ^ d :=
  selfZPow_of_nonneg _ _ (Int.natCast_nonneg d)
#align self_zpow_coe_nat selfZPow_natCast

@[simp]
theorem selfZPow_zero : selfZPow x B 0 = 1 := by
  simp [selfZPow_of_nonneg _ _ le_rfl]
#align self_zpow_zero selfZPow_zero

theorem selfZPow_of_neg {n : ℤ} (hn : n < 0) :
    selfZPow x B n = mk' _ (1 : R) (Submonoid.pow x n.natAbs) :=
  dif_neg hn.not_le
#align self_zpow_of_neg selfZPow_of_neg

theorem selfZPow_of_nonpos {n : ℤ} (hn : n ≤ 0) :
    selfZPow x B n = mk' _ (1 : R) (Submonoid.pow x n.natAbs) := by
  by_cases hn0 : n = 0
  · simp [hn0, selfZPow_zero, Submonoid.pow_apply]
  · simp [selfZPow_of_neg _ _ (lt_of_le_of_ne hn hn0)]
#align self_zpow_of_nonpos selfZPow_of_nonpos

@[simp]
theorem selfZPow_neg_natCast (d : ℕ) : selfZPow x B (-d) = mk' _ (1 : R) (Submonoid.pow x d) := by
  simp [selfZPow_of_nonpos _ _ (neg_nonpos.mpr (Int.natCast_nonneg d))]
#align self_zpow_neg_coe_nat selfZPow_neg_natCast

@[simp]
theorem selfZPow_sub_natCast {n m : ℕ} :
    selfZPow x B (n - m) = mk' _ (x ^ n) (Submonoid.pow x m) := by
  by_cases h : m ≤ n
  · rw [IsLocalization.eq_mk'_iff_mul_eq, Submonoid.pow_apply, Subtype.coe_mk, ← Int.ofNat_sub h,
      selfZPow_natCast, ← map_pow, ← map_mul, ← pow_add, Nat.sub_add_cancel h]
  · rw [← neg_sub, ← Int.ofNat_sub (le_of_not_le h), selfZPow_neg_natCast,
      IsLocalization.mk'_eq_iff_eq]
    simp [Submonoid.pow_apply, ← pow_add, Nat.sub_add_cancel (le_of_not_le h)]
#align self_zpow_sub_cast_nat selfZPow_sub_natCast

@[deprecated (since := "2024-04-05")] alias selfZPow_coe_nat := selfZPow_natCast
@[deprecated (since := "2024-04-05")] alias selfZPow_neg_coe_nat := selfZPow_neg_natCast
@[deprecated (since := "2024-04-05")] alias selfZPow_sub_cast_nat := selfZPow_sub_natCast

@[simp]
theorem selfZPow_add {n m : ℤ} : selfZPow x B (n + m) = selfZPow x B n * selfZPow x B m := by
  rcases le_or_lt 0 n with hn | hn <;> rcases le_or_lt 0 m with hm | hm
  · rw [selfZPow_of_nonneg _ _ hn, selfZPow_of_nonneg _ _ hm,
      selfZPow_of_nonneg _ _ (add_nonneg hn hm), Int.natAbs_add_of_nonneg hn hm, pow_add]
  · have : n + m = n.natAbs - m.natAbs := by
      rw [Int.natAbs_of_nonneg hn, Int.ofNat_natAbs_of_nonpos hm.le, sub_neg_eq_add]
    rw [selfZPow_of_nonneg _ _ hn, selfZPow_of_neg _ _ hm, this, selfZPow_sub_natCast,
      IsLocalization.mk'_eq_mul_mk'_one, map_pow]
  · have : n + m = m.natAbs - n.natAbs := by
      rw [Int.natAbs_of_nonneg hm, Int.ofNat_natAbs_of_nonpos hn.le, sub_neg_eq_add, add_comm]
    rw [selfZPow_of_nonneg _ _ hm, selfZPow_of_neg _ _ hn, this, selfZPow_sub_natCast,
      IsLocalization.mk'_eq_mul_mk'_one, map_pow, mul_comm]
  · rw [selfZPow_of_neg _ _ hn, selfZPow_of_neg _ _ hm, selfZPow_of_neg _ _ (add_neg hn hm),
      Int.natAbs_add_of_nonpos hn.le hm.le, ← mk'_mul, one_mul]
    congr
    ext
    simp [pow_add]
#align self_zpow_add selfZPow_add

theorem selfZPow_mul_neg (d : ℤ) : selfZPow x B d * selfZPow x B (-d) = 1 := by
  by_cases hd : d ≤ 0
  · erw [selfZPow_of_nonpos x B hd, selfZPow_of_nonneg, ← map_pow, Int.natAbs_neg,
      IsLocalization.mk'_spec, map_one]
    apply nonneg_of_neg_nonpos
    rwa [neg_neg]
  · erw [selfZPow_of_nonneg x B (le_of_not_le hd), selfZPow_of_nonpos, ← map_pow, Int.natAbs_neg,
      @IsLocalization.mk'_spec' R _ (Submonoid.powers x) B _ _ _ 1 (Submonoid.pow x d.natAbs),
      map_one]
    refine nonpos_of_neg_nonneg (le_of_lt ?_)
    rwa [neg_neg, ← not_le]
#align self_zpow_mul_neg selfZPow_mul_neg

theorem selfZPow_neg_mul (d : ℤ) : selfZPow x B (-d) * selfZPow x B d = 1 := by
  rw [mul_comm, selfZPow_mul_neg x B d]
#align self_zpow_neg_mul selfZPow_neg_mul

theorem selfZPow_pow_sub (a : R) (b : B) (m d : ℤ) :
    selfZPow x B (m - d) * mk' B a (1 : Submonoid.powers x) = b ↔
      selfZPow x B m * mk' B a (1 : Submonoid.powers x) = selfZPow x B d * b := by
  rw [sub_eq_add_neg, selfZPow_add, mul_assoc, mul_comm _ (mk' B a 1), ← mul_assoc]
  constructor
  · intro h
    have := congr_arg (fun s : B => s * selfZPow x B d) h
    simp only at this
    rwa [mul_assoc, mul_assoc, selfZPow_neg_mul, mul_one, mul_comm b _] at this
  · intro h
    have := congr_arg (fun s : B => s * selfZPow x B (-d)) h
    simp only at this
    rwa [mul_comm _ b, mul_assoc b _ _, selfZPow_mul_neg, mul_one] at this
#align self_zpow_pow_sub selfZPow_pow_sub

variable [IsDomain R] [WfDvdMonoid R]

theorem exists_reduced_fraction' {b : B} (hb : b ≠ 0) (hx : Irreducible x) :
    ∃ (a : R) (n : ℤ), ¬x ∣ a ∧ selfZPow x B n * algebraMap R B a = b := by
  obtain ⟨⟨a₀, y⟩, H⟩ := surj (Submonoid.powers x) b
  obtain ⟨d, hy⟩ := (Submonoid.mem_powers_iff y.1 x).mp y.2
  have ha₀ : a₀ ≠ 0 := by
    haveI :=
      @isDomain_of_le_nonZeroDivisors B _ R _ _ _ (Submonoid.powers x) _
        (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    simp only [map_zero, ← hy, map_pow] at H
    apply ((injective_iff_map_eq_zero' (algebraMap R B)).mp _ a₀).mpr.mt
    · rw [← H]
      apply mul_ne_zero hb (pow_ne_zero _ _)
      exact
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors B
          (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero)
    · exact IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  simp only [← hy] at H
  obtain ⟨m, a, hyp1, hyp2⟩ := WfDvdMonoid.max_power_factor ha₀ hx
  refine ⟨a, m - d, ?_⟩
  rw [← mk'_one (M := Submonoid.powers x) B, selfZPow_pow_sub, selfZPow_natCast, selfZPow_natCast,
    ← map_pow _ _ d, mul_comm _ b, H, hyp2, map_mul, map_pow _ _ m]
  exact ⟨hyp1, congr_arg _ (IsLocalization.mk'_one _ _)⟩
#align exists_reduced_fraction' exists_reduced_fraction'

end NumDen