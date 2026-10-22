/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Divisors.AffinePrincipalDivisor

/-!
# The affine count and fractional-lattice bridge

This module builds the finite-chart fractional ideal whose height-one-prime
counts are prescribed by a divisor, then proves the exact membership/order
comparison needed for chart containment.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero nonZeroDivisors

namespace AffinePlace

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance : Algebra k F := constantAlgebra k F

abbrev affineRing : Type _ := _root_.FunctionField.ringOfIntegers k F

abbrev affineFractionalIdeal : Type _ :=
  FractionalIdeal (affineRing k F)⁰ F

/-- The finite-chart lattice whose prime exponent at `P` is `-D P`. -/
noncomputable def chartFractionalLattice (D : Divisor (carrier k F)) :
    affineFractionalIdeal k F :=
  (-D).prod (fun P exponent => (P.asIdeal : affineFractionalIdeal k F) ^ exponent)

/-- The count of the chart lattice is its prescribed prime exponent. -/
theorem count_chartFractionalLattice (D : Divisor (carrier k F)) (P : carrier k F) :
    FractionalIdeal.count F P (chartFractionalLattice k F D) = -D P := by
  simpa only [chartFractionalLattice, Finsupp.neg_apply] using
    (FractionalIdeal.count_finsuppProd F P (-D))

/-- The finite chart lattice is nonzero: it is a finite product of nonzero
height-one-prime powers. -/
theorem chartFractionalLattice_ne_zero (D : Divisor (carrier k F)) :
    chartFractionalLattice k F D ≠ 0 := by
  classical
  rw [chartFractionalLattice, Finsupp.prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot)

/-- The exact nonzero principal bridge.  The numerator and denominator chosen
by `IsLocalization.sec` are used both by `FractionalIdeal.count` and the
normalized affine principal coefficient. -/
theorem count_spanSingleton_eq_affinePrincipalCoefficient (P : carrier k F)
    {f : F} (hf : f ≠ 0) :
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) =
      affinePrincipalCoefficient k F P (Units.mk0 f hf) := by
  classical
  let B : Type _ := affineRing k F
  let q := IsLocalization.sec B⁰ f
  have hspan : FractionalIdeal.spanSingleton B⁰ f =
      FractionalIdeal.spanSingleton B⁰
          ((algebraMap B F) (q.2 : B))⁻¹ * (Ideal.span {q.1} : Ideal B) := by
    have hq : IsLocalization.mk' F q.1 q.2 = f := by
      dsimp [q]
      exact IsLocalization.mk'_sec (M := B⁰) F f
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [← hq, IsFractionRing.mk'_eq_div,
      div_eq_mul_inv, mul_comm]
  have hspan_ne_zero : FractionalIdeal.spanSingleton B⁰ f ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
  rw [FractionalIdeal.count_well_defined F P hspan_ne_zero hspan]
  change _ = -((P.valuationOfNeZeroToFun (Units.mk0 f hf)).toAdd)
  dsimp [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun, q]
  ring

/-- The exact normalized affine-order form of the principal-count bridge. -/
theorem count_spanSingleton_eq_order (P : carrier k F) {f : F} (hf : f ≠ 0) :
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) =
      GlobalPlace.order (globalPlace k F P) f := by
  calc
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) =
        affinePrincipalCoefficient k F P (Units.mk0 f hf) :=
      count_spanSingleton_eq_affinePrincipalCoefficient k F P hf
    _ = GlobalPlace.order (globalPlace k F P) f := by
      simpa only [Units.val_mk0] using
        (affinePrincipalCoefficient_eq_order k F P (Units.mk0 f hf))

/-- For a nonzero element, an affine valuation bound is exactly the matching
lower normalized-order bound. -/
theorem order_lowerBound_iff_valuation_le (P : carrier k F) {f : F} (hf : f ≠ 0)
    (n : ℤ) :
    -n ≤ GlobalPlace.order (globalPlace k F P) f ↔
      valuation k F P f ≤ WithZero.exp n := by
  change -n ≤ -WithZero.log (valuation k F P f) ↔
    valuation k F P f ≤ WithZero.exp n
  rw [neg_le_neg_iff]
  exact WithZero.log_le_iff_le_exp ((valuation k F P).ne_zero_iff.mpr hf)

/-- Prime-count inequalities reverse to fractional-ideal inclusion. -/
theorem le_of_all_count_le {I J : affineFractionalIdeal k F}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (hcount : ∀ P : carrier k F,
      FractionalIdeal.count F P J ≤ FractionalIdeal.count F P I) :
    I ≤ J := by
  classical
  let B : Type _ := affineRing k F
  let D : FractionalIdeal B⁰ F := I * J⁻¹
  have hD : D ≠ 0 := by
    dsimp [D]
    exact mul_ne_zero hI (inv_ne_zero hJ)
  have hDcount (P : carrier k F) :
      FractionalIdeal.count F P D =
        FractionalIdeal.count F P I - FractionalIdeal.count F P J := by
    dsimp [D]
    rw [FractionalIdeal.count_mul F P hI (inv_ne_zero hJ),
      FractionalIdeal.count_inv]
    ring
  have hDnonneg (P : carrier k F) : 0 ≤ FractionalIdeal.count F P D := by
    rw [hDcount]
    exact sub_nonneg.mpr (hcount P)
  let H : Ideal B := ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum B,
    P.asIdeal ^ Int.toNat (FractionalIdeal.count F P D)
  have hH : (H : FractionalIdeal B⁰ F) = D := by
    calc
      (H : FractionalIdeal B⁰ F) = ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum B,
          (P.asIdeal : FractionalIdeal B⁰ F) ^
            Int.toNat (FractionalIdeal.count F P D) := by
        dsimp [H]
        rw [FractionalIdeal.coeIdeal_finprod B⁰ F (le_refl _)]
        apply finprod_congr
        intro P
        exact FractionalIdeal.coeIdeal_pow (S := B⁰) (P := F) P.asIdeal
          (Int.toNat (FractionalIdeal.count F P D))
      _ = ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum B,
          (P.asIdeal : FractionalIdeal B⁰ F) ^ FractionalIdeal.count F P D := by
        apply finprod_congr
        intro P
        conv_rhs => rw [← Int.toNat_of_nonneg (hDnonneg P), zpow_natCast]
      _ = D := FractionalIdeal.finprod_heightOneSpectrum_factorization'
        (R := B) (K := F) hD
  have hDle : D ≤ (1 : FractionalIdeal B⁰ F) := by
    rw [← hH]
    exact FractionalIdeal.coeIdeal_le_one
  have hIeq : I = D * J := by
    calc
      I = I * 1 := (mul_one I).symm
      _ = I * (J⁻¹ * J) := by rw [inv_mul_cancel₀ hJ]
      _ = (I * J⁻¹) * J := (mul_assoc I J⁻¹ J).symm
      _ = D * J := rfl
  calc
    I = D * J := hIeq
    _ ≤ 1 * J := mul_le_mul_left hDle J
    _ = J := one_mul J

/-- Membership in the finite-chart lattice is exactly the valuation bound at
every actual affine height-one prime. -/
theorem mem_chartFractionalLattice_iff (D : Divisor (carrier k F)) (f : F) :
    f ∈ chartFractionalLattice k F D ↔
      ∀ P : carrier k F, valuation k F P f ≤ WithZero.exp (D P) := by
  constructor
  · intro hfmem P
    by_cases hf : f = 0
    · simpa only [hf, map_zero] using
        (zero_le' : (0 : ℤᵐ⁰) ≤ WithZero.exp (D P))
    · have hspan_ne_zero :
        FractionalIdeal.spanSingleton (affineRing k F)⁰ f ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
      have hspan_le : FractionalIdeal.spanSingleton (affineRing k F)⁰ f ≤
          chartFractionalLattice k F D :=
        FractionalIdeal.spanSingleton_le_iff_mem.mpr hfmem
      have hcounts := FractionalIdeal.count_mono F P hspan_ne_zero hspan_le
      have horder : -D P ≤ GlobalPlace.order (globalPlace k F P) f := by
        rw [count_chartFractionalLattice, count_spanSingleton_eq_order k F P hf] at hcounts
        exact hcounts
      exact (order_lowerBound_iff_valuation_le k F P hf (D P)).mp horder
  · intro h
    by_cases hf : f = 0
    · simpa only [hf] using (chartFractionalLattice k F D).zero_mem
    · have hspan_ne_zero :
        FractionalIdeal.spanSingleton (affineRing k F)⁰ f ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
      have hcounts : ∀ P : carrier k F,
          FractionalIdeal.count F P (chartFractionalLattice k F D) ≤
            FractionalIdeal.count F P
              (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) := by
        intro P
        rw [count_chartFractionalLattice, count_spanSingleton_eq_order k F P hf]
        exact (order_lowerBound_iff_valuation_le k F P hf (D P)).mpr (h P)
      exact FractionalIdeal.spanSingleton_le_iff_mem.mp
        (le_of_all_count_le k F hspan_ne_zero
          (chartFractionalLattice_ne_zero k F D) hcounts)

end AffinePlace

end QEC.Coding.AlgebraicGeometry
