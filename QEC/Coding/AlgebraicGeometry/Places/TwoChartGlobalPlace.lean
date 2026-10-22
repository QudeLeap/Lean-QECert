/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import QEC.Coding.AlgebraicGeometry.Places.AffinePlaceDegree
import QEC.Coding.AlgebraicGeometry.Divisors.AffinePrincipalDivisor
import QEC.Coding.AlgebraicGeometry.Places.GlobalPlace
import QEC.Coding.AlgebraicGeometry.Places.InverseInfinityFibre
import QEC.Coding.AlgebraicGeometry.Places.RationalPlace

/-!
# Global places from the two affine charts

This module constructs the two-chart carrier of normalized global places for
a finite separable one-variable function field.  The construction is
valuation-first: a regular-coordinate valuation has a genuine height-one
centre in the integral closure, while a valuation at the complementary chart
is placed in the actual fibre over `(X)`.  The resulting equivalence supports
the finite-support principal divisor below; it does not assert a finite global
place carrier or a Riemann--Roch theorem.
-/

open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom

namespace QEC.Coding.AlgebraicGeometry

/-! ## Normalized valuation rigidity -/

private theorem rankOneDiscrete_of_surjective
    {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : v.IsRankOneDiscrete := by
  let γ : ℤᵐ⁰ˣ := Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp)
  refine ⟨γ, ?_, ?_⟩
  · apply Subgroup.ext
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hv x.1
      have ha0 : v a ≠ 0 := by simpa only [ha] using x.ne_zero
      have hunit : Units.mk0 (v a) ha0 = x := Units.ext ha
      rw [← hunit]
      exact MonoidWithZeroHom.mem_valueGroup (MonoidWithZeroHom.ofClass v)
        (show (Units.mk0 (v a) ha0 : ℤᵐ⁰ˣ).1 ∈ Set.range v from ⟨a, rfl⟩)
    · intro hx
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨-WithZero.log x.1, ?_⟩
      apply Units.ext
      rw [Units.val_zpow_eq_zpow_val]
      change (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ (-WithZero.log x.1) = x.1
      rw [← WithZero.exp_zsmul]
      simpa only [Int.zsmul_eq_mul, neg_mul_neg, one_mul, mul_one] using
        (WithZero.exp_log x.ne_zero)
  · change (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1
    simpa using (WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by decide))

private noncomputable def normalizedValueGroupOrderIso
    {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] : ValueGroup₀ (MonoidWithZeroHom.ofClass v) ≃*o ℤᵐ⁰ :=
  Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v

private noncomputable def normalizedCodomainOrderAuto
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (h : v.IsEquiv w) : ℤᵐ⁰ ≃*o ℤᵐ⁰ :=
  (normalizedValueGroupOrderIso v).symm.trans
    ((h.orderMonoidIso).trans (normalizedValueGroupOrderIso w))

private noncomputable def normalizedUnitOrderAuto
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) : Multiplicative ℤ ≃*o Multiplicative ℤ :=
  OrderMonoidIso.withZero.symm φ

private theorem normalizedUnitOrderAuto_toMulEquiv
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) :
    (normalizedUnitOrderAuto φ).toMulEquiv = φ.toMulEquiv.unzero := rfl

private noncomputable def normalizedIntOrderAuto
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) : ℤ ≃+o ℤ :=
  (OrderMonoidIso.toAdditiveRight (normalizedUnitOrderAuto φ)).trans
    (OrderAddMonoidIso.toAdditive_toMultiplicative (G := ℤ))

private theorem normalizedIntOrderAuto_eq_refl
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) :
    normalizedIntOrderAuto φ = OrderAddMonoidIso.refl ℤ :=
  Subsingleton.elim _ _

private theorem normalizedCodomainOrderAuto_eq_id
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) : φ = OrderMonoidIso.refl ℤᵐ⁰ := by
  have hunit : normalizedUnitOrderAuto φ = OrderMonoidIso.refl (Multiplicative ℤ) :=
    Subsingleton.elim _ _
  calc
    φ = OrderMonoidIso.withZero (normalizedUnitOrderAuto φ) :=
      (OrderMonoidIso.withZero.apply_symm_apply φ).symm
    _ = OrderMonoidIso.withZero (OrderMonoidIso.refl (Multiplicative ℤ)) :=
      congrArg OrderMonoidIso.withZero hunit
    _ = OrderMonoidIso.refl ℤᵐ⁰ := by
      apply OrderMonoidIso.toMulEquiv_injective
      apply MulEquiv.ext
      intro x
      cases x <;> rfl

private theorem normalizedCodomainOrderAuto_apply_restrict
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (h : v.IsEquiv w) (a : F) :
    normalizedCodomainOrderAuto v w h
        (normalizedValueGroupOrderIso v (v.restrict a)) =
      normalizedValueGroupOrderIso w (w.restrict a) := by
  change normalizedValueGroupOrderIso w
      (h.orderMonoidIso
        ((normalizedValueGroupOrderIso v).symm
          (normalizedValueGroupOrderIso v (v.restrict a)))) =
    normalizedValueGroupOrderIso w (w.restrict a)
  rw [(normalizedValueGroupOrderIso v).symm_apply_apply]
  rw [h.orderMonoidIso_spec]

private theorem normalizedCodomainOrderAuto_value_eq
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (h : v.IsEquiv w)
    (hφ : normalizedCodomainOrderAuto v w h = OrderMonoidIso.refl ℤᵐ⁰)
    (a : F) : v a = w a := by
  calc
    v a = normalizedValueGroupOrderIso v (v.restrict a) :=
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (v := v) hv a).symm
    _ = normalizedCodomainOrderAuto v w h
          (normalizedValueGroupOrderIso v (v.restrict a)) := by
      rw [hφ]
      rfl
    _ = normalizedValueGroupOrderIso w (w.restrict a) :=
      normalizedCodomainOrderAuto_apply_restrict v w h a
    _ = w a :=
      Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (v := w) hw a

private theorem valuation_eq_of_surjective_isEquiv_withZeroMulInt
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (h : v.IsEquiv w) : v = w := by
  letI : v.IsRankOneDiscrete := rankOneDiscrete_of_surjective v hv
  letI : w.IsRankOneDiscrete := rankOneDiscrete_of_surjective w hw
  let φ := normalizedCodomainOrderAuto v w h
  have hφ : φ = OrderMonoidIso.refl ℤᵐ⁰ := normalizedCodomainOrderAuto_eq_id φ
  apply Valuation.ext
  intro a
  exact normalizedCodomainOrderAuto_value_eq v w hv hw h hφ a

/-- Equivalent surjective valuations with the fixed `ℤᵐ⁰` normalization are equal.
This is the rigidity bridge from valuation classes to the normalized global-place
carrier. -/
theorem normalizedValuation_eq_of_isEquiv
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (h : v.IsEquiv w) : v = w :=
  valuation_eq_of_surjective_isEquiv_withZeroMulInt v w hv hw h

/-! ## Regular-coordinate centres -/

private theorem polynomial_map_mem_valuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F]
    (ι : k[X] →+* F) (v : Valuation F ℤᵐ⁰)
    (hX : v (ι Polynomial.X) ≤ 1) (p : k[X]) :
    ι p ∈ v.valuationSubring := by
  letI : Algebra k F := (ι.comp Polynomial.C).toAlgebra
  rw [Valuation.mem_valuationSubring_iff]
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [ι.map_add]
    exact (v.map_add (ι p) (ι q)).trans (max_le hp hq)
  · intro n a
    have hC : v (ι (Polynomial.C a)) ≤ 1 := by
      change v (algebraMap k F a) ≤ 1
      exact FiniteField.valuation_algebraMap_le_one v a
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ι.map_mul, ι.map_pow,
      v.map_mul, v.map_pow]
    exact mul_le_one₀ hC zero_le' (pow_le_one₀ zero_le' hX)

private theorem affineIntegralClosureComposite_eq_chartMap
    {k F : Type*} [Field k] [Field F] [Algebra k[X] F] :
    (algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F)) =
    algebraMap k[X] F := by
  exact IsScalarTower.algebraMap_eq k[X] (FunctionField.ringOfIntegers k F) F

private theorem ringOfIntegers_le_valuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k[X] F]
    (v : Valuation F ℤᵐ⁰)
    (ht : v (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (FunctionField.ringOfIntegers k F).toSubring ≤ v.valuationSubring.toSubring := by
  let B := FunctionField.ringOfIntegers k F
  let ι : k[X] →+* F := (algebraMap B F).comp (algebraMap k[X] B)
  have hX : v (ι Polynomial.X) ≤ 1 := ht
  have hpoly : ∀ p : k[X], ι p ∈ v.valuationSubring :=
    fun p ↦ polynomial_map_mem_valuationSubring ι v hX p
  change (integralClosure k[X] F).toSubring ≤ v.integer
  letI : IsIntegrallyClosedIn v.integer F :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn F).mp inferInstance
  rw [Subring.integralClosure_le_iff]
  intro p
  rw [← affineIntegralClosureComposite_eq_chartMap (k := k) (F := F)]
  exact hpoly p

private noncomputable def ringOfIntegersToValuationRing
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k[X] F]
    (v : Valuation F ℤᵐ⁰)
    (ht : v (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    FunctionField.ringOfIntegers k F →+* v.valuationSubring := by
  let hB := ringOfIntegers_le_valuationSubring (v := v) ht
  exact (algebraMap (FunctionField.ringOfIntegers k F) F).codRestrict
    v.valuationSubring fun b => by
      change (b : F) ∈ v.valuationSubring
      exact hB b.property

private noncomputable def regularCentreIdeal
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    Ideal (FunctionField.ringOfIntegers k F) :=
  (IsLocalRing.maximalIdeal P.valuation.valuationSubring).comap
    (ringOfIntegersToValuationRing (v := P.valuation) ht)

private theorem regularCentreIdeal_isPrime
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (regularCentreIdeal P ht).IsPrime := by
  dsimp [regularCentreIdeal]
  exact (IsLocalRing.maximalIdeal P.valuation.valuationSubring).comap_isPrime _

private theorem regularCentreIdeal_ne_top
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreIdeal P ht ≠ ⊤ :=
  (regularCentreIdeal_isPrime P ht).ne_top

private theorem exists_nonzero_mem_regularCentreIdeal
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    ∃ a : FunctionField.ringOfIntegers k F,
      a ≠ 0 ∧ a ∈ regularCentreIdeal P ht := by
  let B := FunctionField.ringOfIntegers k F
  obtain ⟨a, s, hs, hfrac⟩ :=
    IsFractionRing.div_surjective B P.uniformizer
  have hs0 : algebraMap B F s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hu0 : P.uniformizer ≠ 0 := by
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hu_lt_one : P.valuation P.uniformizer < 1 := by
    rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hB := ringOfIntegers_le_valuationSubring (v := P.valuation) ht
  have hs_mem : algebraMap B F s ∈ P.valuation.valuationSubring := by
    change (s : F) ∈ P.valuation.valuationSubring
    exact hB s.property
  have hs_le_one : P.valuation (algebraMap B F s) ≤ 1 :=
    (P.valuation.mem_valuationSubring_iff _).mp hs_mem
  have hprod : algebraMap B F a =
      P.uniformizer * algebraMap B F s := by
    calc
      algebraMap B F a =
          (algebraMap B F a / algebraMap B F s) * algebraMap B F s :=
        (div_mul_cancel₀ _ hs0).symm
      _ = P.uniformizer * algebraMap B F s := by rw [hfrac]
  have ha0 : a ≠ 0 := by
    intro ha
    have hzero : P.uniformizer * algebraMap B F s = 0 := by
      simpa [ha] using hprod.symm
    exact (mul_ne_zero hu0 hs0) hzero
  have ha_lt_one : P.valuation (algebraMap B F a) < 1 := by
    calc
      P.valuation (algebraMap B F a) =
          P.valuation P.uniformizer * P.valuation (algebraMap B F s) := by
        rw [hprod, P.valuation.map_mul]
      _ ≤ P.valuation P.uniformizer * 1 :=
        mul_le_mul_of_nonneg_left hs_le_one
          (le_of_lt (by rw [P.valuation_uniformizer]; exact WithZero.exp_pos))
      _ = P.valuation P.uniformizer := mul_one _
      _ < 1 := hu_lt_one
  have ha_maximal :
      ringOfIntegersToValuationRing (v := P.valuation) ht a ∈
        IsLocalRing.maximalIdeal P.valuation.valuationSubring := by
    rw [Valuation.mem_maximalIdeal_iff]
    exact ha_lt_one
  refine ⟨a, ha0, ?_⟩
  change ringOfIntegersToValuationRing (v := P.valuation) ht a ∈
    IsLocalRing.maximalIdeal P.valuation.valuationSubring
  exact ha_maximal

private theorem regularCentreIdeal_ne_bot
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreIdeal P ht ≠ ⊥ := by
  obtain ⟨a, ha0, haCentre⟩ := exists_nonzero_mem_regularCentreIdeal P ht
  intro hbot
  exact ha0 (Ideal.mem_bot.mp (hbot ▸ haCentre))

private noncomputable def regularCentreHeightOne
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k F) :=
  ⟨regularCentreIdeal P ht, regularCentreIdeal_isPrime P ht,
    regularCentreIdeal_ne_bot P ht⟩

private theorem regularCentre_primeCompl_maps_to_unit
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1)
    (s : (regularCentreHeightOne P ht).asIdeal.primeCompl) :
    IsUnit (ringOfIntegersToValuationRing (v := P.valuation) ht s) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hs
  apply s.property
  change ringOfIntegersToValuationRing (v := P.valuation) ht (s :
    FunctionField.ringOfIntegers k F) ∈
      IsLocalRing.maximalIdeal P.valuation.valuationSubring
  exact hs

private noncomputable abbrev regularCentreCanonicalLocalization
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    ValuationSubring F :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
    (regularCentreHeightOne P ht)

private noncomputable def regularCentreLocalizationToValuationRing
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreCanonicalLocalization P ht →+*
      P.valuation.valuationSubring :=
  IsLocalization.lift
    (M := (regularCentreHeightOne P ht).asIdeal.primeCompl)
    (g := ringOfIntegersToValuationRing (v := P.valuation) ht)
    (regularCentre_primeCompl_maps_to_unit P ht)

private theorem regularCentreLocalizationToValuationRing_comp
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (regularCentreLocalizationToValuationRing P ht).comp
      (algebraMap (FunctionField.ringOfIntegers k F)
        (regularCentreCanonicalLocalization P ht)) =
      ringOfIntegersToValuationRing (v := P.valuation) ht := by
  simpa [regularCentreLocalizationToValuationRing] using
    (IsLocalization.lift_comp (regularCentre_primeCompl_maps_to_unit P ht))

private theorem regularCentreLocalization_coe_triangle
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (ValuationSubring.subtype P.valuation.valuationSubring).comp
      (regularCentreLocalizationToValuationRing P ht) =
      ValuationSubring.subtype (regularCentreCanonicalLocalization P ht) := by
  apply IsLocalization.ringHom_ext
    (regularCentreHeightOne P ht).asIdeal.primeCompl
  ext b
  change ((regularCentreLocalizationToValuationRing P ht
      (algebraMap (FunctionField.ringOfIntegers k F)
        (regularCentreCanonicalLocalization P ht) b) :
        P.valuation.valuationSubring) : F) = algebraMap
      (FunctionField.ringOfIntegers k F) F b
  rw [← RingHom.comp_apply, regularCentreLocalizationToValuationRing_comp]
  rfl

private theorem regularCentreCanonicalLocalization_le_placeValuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreCanonicalLocalization P ht ≤ P.valuation.valuationSubring := by
  intro x hx
  let xC : regularCentreCanonicalLocalization P ht := ⟨x, hx⟩
  have htriangle := RingHom.congr_fun
    (regularCentreLocalization_coe_triangle P ht) xC
  have hxF :
      ((regularCentreLocalizationToValuationRing P ht xC :
        P.valuation.valuationSubring) : F) = x := by
    simpa only [RingHom.comp_apply, ValuationSubring.coe_subtype] using htriangle
  rw [← hxF]
  exact (regularCentreLocalizationToValuationRing P ht xC).property

private theorem globalPlace_valuation_isNontrivial
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : GlobalPlace k F) : P.valuation.IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨P.uniformizer, ?_, ?_⟩
  · apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)

private theorem globalPlace_valuationSubring_ne_top
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : GlobalPlace k F) : P.valuation.valuationSubring ≠ ⊤ := by
  intro htop
  exact ((Valuation.valuationSubring_eq_top_iff (v := P.valuation)).mp htop)
    (globalPlace_valuation_isNontrivial P)

private theorem regularCentreCanonicalLocalization_eq_placeValuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreCanonicalLocalization P ht = P.valuation.valuationSubring :=
  ValuationSubring.eq_of_le_of_ne_top _
    (regularCentreCanonicalLocalization_le_placeValuationSubring P ht)
    (globalPlace_valuationSubring_ne_top P)

/-- A global place at which the chosen affine coordinate is regular has a
height-one centre whose canonical localization is exactly its valuation ring. -/
theorem GlobalPlace.exists_heightOne_valuationSubringAtPrime_eq
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    ∃ C : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k F),
      C.valuationSubringAtPrime F = P.valuationRing := by
  exact ⟨regularCentreHeightOne P ht,
    regularCentreCanonicalLocalization_eq_placeValuationSubring P ht⟩

private theorem placeValuation_isEquiv_regularCentreAdicValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    P.valuation.IsEquiv ((regularCentreHeightOne P ht).valuation F) := by
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact (regularCentreCanonicalLocalization_eq_placeValuationSubring P ht).symm.trans
    ((regularCentreHeightOne P ht).valuationSubringAtPrime_eq_valuationSubring)

/-! ## Equality of places from their raw valuations -/

private theorem placeValuation_eq_regularCentreAdicValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    P.valuation = (regularCentreHeightOne P ht).valuation F := by
  exact valuation_eq_of_surjective_isEquiv_withZeroMulInt
    P.valuation
    ((regularCentreHeightOne P ht).valuation F)
    P.normalized
    ((regularCentreHeightOne P ht).valuation_surjective F)
    (placeValuation_isEquiv_regularCentreAdicValuation P ht)

private abbrev regularCoordinatePlaces
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra k[X] F] : Type _ :=
  { P : GlobalPlace k F //
    P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1 }

private noncomputable def regularCentreHeightOneOnRegularCoordinatePlaces
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] :
    regularCoordinatePlaces k F →
      IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k F) :=
  fun P ↦ regularCentreHeightOne P.1 P.2

private theorem regularCentreHeightOne_eq_implies_valuation_eq
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    {P Q : regularCoordinatePlaces k F}
    (hcentre : regularCentreHeightOne P.1 P.2 = regularCentreHeightOne Q.1 Q.2) :
    P.1.valuation = Q.1.valuation := by
  calc
    P.1.valuation = (regularCentreHeightOne P.1 P.2).valuation F :=
      placeValuation_eq_regularCentreAdicValuation P.1 P.2
    _ = (regularCentreHeightOne Q.1 Q.2).valuation F := by
      exact congrArg (fun C : IsDedekindDomain.HeightOneSpectrum
        (FunctionField.ringOfIntegers k F) ↦ C.valuation F) hcentre
    _ = Q.1.valuation :=
      (placeValuation_eq_regularCentreAdicValuation Q.1 Q.2).symm

private theorem globalPlace_eq_of_valuation_eq
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    {P Q : GlobalPlace k F} (hvaluation : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases hvaluation
  rfl

private theorem regularCentreHeightOneOnRegularCoordinatePlaces_injective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] :
    Function.Injective (regularCentreHeightOneOnRegularCoordinatePlaces
      (k := k) (F := F)) := by
  intro P Q hcentre
  apply Subtype.ext
  exact globalPlace_eq_of_valuation_eq
    (regularCentreHeightOne_eq_implies_valuation_eq hcentre)

/-! ## The corrected two-chart carrier -/

private noncomputable def originalCoordinate
    {k F : Type*} [Field k] [Field F] (ρ : Algebra k⟮X⟯ F) : F :=
  ρ.algebraMap RatFunc.X

private noncomputable def originalInverseCoordinate
    {k F : Type*} [Field k] [Field F] (ρ : Algebra k⟮X⟯ F) : F :=
  (originalCoordinate ρ)⁻¹

private theorem originalCoordinate_ne_zero
    {k F : Type*} [Field k] [Finite k] [Field F]
    [ρ : Algebra k⟮X⟯ F] [_root_.FunctionField k F] :
    originalCoordinate ρ ≠ 0 := by
  exact (map_ne_zero_iff ρ.algebraMap ρ.algebraMap.injective).mpr RatFunc.X_ne_zero

private theorem original_coordinate_dichotomy
    {k F : Type*} [Field k] [Finite k] [Field F]
    [ρ : Algebra k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    P.valuation (originalCoordinate ρ) ≤ 1 ∨
      P.valuation (originalInverseCoordinate ρ) < 1 := by
  by_cases h : P.valuation (originalCoordinate ρ) ≤ 1
  · exact Or.inl h
  · right
    rw [originalInverseCoordinate, P.valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ (lt_of_not_ge h)

private noncomputable def repackageRawGlobalPlace
    {k F : Type*} [Field k] [Finite k] [Field F]
    (A : Algebra k F) {A₀ : Algebra k F}
    (P : @GlobalPlace k F _ _ _ A₀) : @GlobalPlace k F _ _ _ A := by
  exact @GlobalPlace.mk k F _ _ _ A
    (@GlobalPlace.valuation k F _ _ _ A₀ P)
    (@GlobalPlace.normalized k F _ _ _ A₀ P)

private theorem repackageRawGlobalPlace_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    (A : Algebra k F) {A₀ : Algebra k F}
    (P : @GlobalPlace k F _ _ _ A₀) :
    @GlobalPlace.valuation k F _ _ _ A (repackageRawGlobalPlace A P) =
      @GlobalPlace.valuation k F _ _ _ A₀ P := rfl

private theorem directIntegralCoordinate_eq_originalCoordinate
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] :
    algebraMap (_root_.FunctionField.ringOfIntegers k F) F
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) =
        originalCoordinate ρ := by
  change ((algebraMap (_root_.FunctionField.ringOfIntegers k F) F).comp
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))) Polynomial.X =
      ρ.algebraMap RatFunc.X
  calc
    _ = (algebraMap k[X] F) Polynomial.X := by
      rw [← IsScalarTower.algebraMap_eq k[X]
        (_root_.FunctionField.ringOfIntegers k F) F]
    _ = ρ.algebraMap ((algebraMap k[X] k⟮X⟯) Polynomial.X) := by
      rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F]
    _ = ρ.algebraMap RatFunc.X := rfl

private theorem inverseIntegralCoordinate_eq_originalInverseCoordinate
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    algebraMap (_root_.FunctionField.ringOfIntegers k F) F
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) =
        originalInverseCoordinate ρ := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  change ((algebraMap (_root_.FunctionField.ringOfIntegers k F) F).comp
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))) Polynomial.X =
      originalInverseCoordinate ρ
  calc
    _ = (algebraMap k[X] F) Polynomial.X := by
      rw [← IsScalarTower.algebraMap_eq k[X]
        (_root_.FunctionField.ringOfIntegers k F) F]
    _ = InverseAffinePlace.transportedPolynomialMap (oldRationalAlgebra := ρ) k F Polynomial.X := rfl
    _ = InverseAffinePlace.transportedRationalMap (oldRationalAlgebra := ρ) k F RatFunc.X := by
      rfl
    _ = originalInverseCoordinate ρ := by
      change ρ.algebraMap (InverseAffinePlace.rationalInvolution k RatFunc.X) =
        (ρ.algebraMap RatFunc.X)⁻¹
      rw [InverseAffinePlace.rationalInvolution_X, map_inv₀]

private theorem regularCentreHeightOne_mem_of_lt_one
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (hbound : P.valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1)
    (a : _root_.FunctionField.ringOfIntegers k F)
    (ha : P.valuation (algebraMap (_root_.FunctionField.ringOfIntegers k F) F a) < 1) :
    a ∈ (regularCentreHeightOne P hbound).asIdeal := by
  change ringOfIntegersToValuationRing (v := P.valuation) hbound a ∈
    IsLocalRing.maximalIdeal P.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff]
  change P.valuation (algebraMap (_root_.FunctionField.ringOfIntegers k F) F a) < 1
  exact ha

private noncomputable def inverseCentreInInfinityFibre
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ)
    (hinv : P.valuation (originalInverseCoordinate ρ) < 1) :
    InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  let Pinv : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) :=
    repackageRawGlobalPlace (AffinePlace.constantAlgebra k F) P
  let hbound : Pinv.valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 :=
    le_of_lt (by
      rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv)
  let C := regularCentreHeightOne Pinv hbound
  refine ⟨C, ?_⟩
  apply Ideal.dvd_iff_le.mpr
  change Ideal.map (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
      (Polynomial.idealX k).asIdeal ≤ C.asIdeal
  rw [Ideal.map_le_iff_le_comap, Polynomial.idealX_span, Ideal.span_le,
    Set.singleton_subset_iff]
  exact Ideal.mem_comap.mpr (regularCentreHeightOne_mem_of_lt_one Pinv hbound
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) (by
      rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv))

private noncomputable def inverseFibreRawValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) : Valuation F ℤᵐ⁰ := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  exact @GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F)
    (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
      (oldFunctionField := φ) (oldSeparable := σ) k F D)

/-- The raw inverse-fibre valuation is the ambient height-one-prime valuation.
Making this normalization explicit keeps subsequent comparisons independent of
the transported chart instances used to construct the inverse place. -/
private theorem inverseFibreRawValuation_eq_ambient
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    inverseFibreRawValuation (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D =
      D.1.valuation F := by
  unfold inverseFibreRawValuation
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  rw [@InverseAffinePlace.globalPlace_valuation k F _ _ _ π ρ τ φ σ D]
  rfl

private noncomputable def inverseFibreGlobalPlaceAt
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (κ : Algebra k F)
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    @GlobalPlace k F _ _ _ κ :=
  repackageRawGlobalPlace κ
    (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
      (oldFunctionField := φ) (oldSeparable := σ) k F D)

private theorem inverseFibreGlobalPlaceAt_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (κ : Algebra k F)
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D) =
      inverseFibreRawValuation D := rfl

private theorem inverseCentre_rawValuation_eq_ambient
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ)
    (hinv : P.valuation (originalInverseCoordinate ρ) < 1) :
    P.valuation = inverseFibreRawValuation
      (inverseCentreInInfinityFibre P hinv) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  let Pinv : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) :=
    repackageRawGlobalPlace (AffinePlace.constantAlgebra k F) P
  let hbound : Pinv.valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 :=
    le_of_lt (by
      rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv)
  let D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F :=
    inverseCentreInInfinityFibre (π := π) (ρ := ρ) (τ := τ) (φ := φ)
      (σ := σ) (κ := κ) P hinv
  calc
    @GlobalPlace.valuation k F _ _ _ κ P =
        @GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F) Pinv :=
      (repackageRawGlobalPlace_valuation (AffinePlace.constantAlgebra k F) P).symm
    _ = (regularCentreHeightOne Pinv hbound).valuation F :=
      placeValuation_eq_regularCentreAdicValuation Pinv hbound
    _ = inverseFibreRawValuation (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D := by
      rw [inverseFibreRawValuation_eq_ambient
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      rfl

private theorem inverseFibreRawValuation_surjective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    Function.Surjective (inverseFibreRawValuation D) := by
  unfold inverseFibreRawValuation
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  exact @GlobalPlace.normalized k F _ _ _ (AffinePlace.constantAlgebra k F)
    (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
      (oldFunctionField := φ) (oldSeparable := σ) k F D)

private theorem inverseFibreRawValuation_injective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D E : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F)
    (h : inverseFibreRawValuation D = inverseFibreRawValuation E) : D = E := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  apply Subtype.ext
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
  apply Valuation.IsEquiv.of_eq
  rw [inverseFibreRawValuation_eq_ambient
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D,
    inverseFibreRawValuation_eq_ambient
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) E] at h
  exact h

private theorem inverseFibreRawValuation_originalInverse_lt_one
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    inverseFibreRawValuation D (originalInverseCoordinate ρ) < 1 := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  rw [inverseFibreRawValuation_eq_ambient
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
  rw [← inverseIntegralCoordinate_eq_originalInverseCoordinate
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
  exact InverseAffinePlace.globalPlace_coordinate_valuation_lt_one
    (oldPolynomialAlgebra := π) (oldRationalAlgebra := ρ) (oldScalarTower := τ)
    (oldFunctionField := φ) (oldSeparable := σ) k F D

private noncomputable abbrev CorrectedTwoChartPlace
    (k F : Type*) [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] : Type _ :=
  Sum (AffinePlace.carrier k F) (InverseAffinePlace.infinityFibre k F)

private noncomputable def correctedTwoChartValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] :
    CorrectedTwoChartPlace k F → Valuation F ℤᵐ⁰
  | .inl C => C.valuation F
  | .inr D => inverseFibreRawValuation D

private noncomputable def correctedTwoChartToGlobalPlace
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F] :
    CorrectedTwoChartPlace k F → @GlobalPlace k F _ _ _ κ
  | .inl C => ⟨C.valuation F, C.valuation_surjective F⟩
  | .inr D => ⟨inverseFibreRawValuation D, inverseFibreRawValuation_surjective D⟩

private theorem correctedTwoChartToGlobalPlace_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : CorrectedTwoChartPlace k F) :
    (correctedTwoChartToGlobalPlace C).valuation = correctedTwoChartValuation C := by
  cases C <;> rfl

private theorem everyGlobalPlace_has_correctedTwoChartWitness
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    ∃ C : CorrectedTwoChartPlace k F,
      P.valuation = correctedTwoChartValuation C := by
  rcases original_coordinate_dichotomy P with hdirect | hinverse
  · let hbound : P.valuation
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
          (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 := by
      rw [directIntegralCoordinate_eq_originalCoordinate]
      exact hdirect
    exact ⟨Sum.inl (regularCentreHeightOne P hbound),
      placeValuation_eq_regularCentreAdicValuation P hbound⟩
  · let D := inverseCentreInInfinityFibre P hinverse
    exact ⟨Sum.inr D, inverseCentre_rawValuation_eq_ambient P hinverse⟩

private theorem directImage_ne_inverseFibreImage
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : AffinePlace.carrier k F) (D : InverseAffinePlace.infinityFibre k F) :
    correctedTwoChartToGlobalPlace (Sum.inl C : CorrectedTwoChartPlace k F) ≠
      correctedTwoChartToGlobalPlace (Sum.inr D : CorrectedTwoChartPlace k F) := by
  intro h
  have hval : C.valuation F = inverseFibreRawValuation D := by
    change (correctedTwoChartToGlobalPlace
      (Sum.inl C : CorrectedTwoChartPlace k F)).valuation =
      (correctedTwoChartToGlobalPlace (Sum.inr D : CorrectedTwoChartPlace k F)).valuation
    exact congrArg (@GlobalPlace.valuation k F _ _ _ κ) h
  have hdirect : C.valuation F (originalCoordinate ρ) ≤ 1 := by
    rw [← directIntegralCoordinate_eq_originalCoordinate]
    exact C.valuation_le_one _
  have hinverse : 1 < inverseFibreRawValuation D (originalCoordinate ρ) := by
    have hy := inverseFibreRawValuation_originalInverse_lt_one (ρ := ρ) D
    rw [originalInverseCoordinate, (inverseFibreRawValuation D).map_inv] at hy
    exact (inv_lt_one₀ ((inverseFibreRawValuation D).pos_iff.mpr
      (originalCoordinate_ne_zero (ρ := ρ)))).mp hy
  apply (not_lt_of_ge hdirect)
  rw [hval.symm] at hinverse
  exact hinverse

private theorem correctedTwoChartToGlobalPlace_bijective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F] :
    Function.Bijective (correctedTwoChartToGlobalPlace (k := k) (F := F)) := by
  constructor
  · intro C D h
    cases C <;> cases D
    · exact congrArg Sum.inl (by
        apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
        exact Valuation.IsEquiv.of_eq (congrArg (@GlobalPlace.valuation k F _ _ _ κ) h))
    · exact False.elim (directImage_ne_inverseFibreImage _ _ h)
    · exact False.elim (directImage_ne_inverseFibreImage _ _ h.symm)
    · exact congrArg Sum.inr
        (inverseFibreRawValuation_injective (ρ := ρ) _ _
          (congrArg (@GlobalPlace.valuation k F _ _ _ κ) h))
  · intro P
    obtain ⟨C, hC⟩ := everyGlobalPlace_has_correctedTwoChartWitness P
    refine ⟨C, ?_⟩
    apply globalPlace_eq_of_valuation_eq
    rw [correctedTwoChartToGlobalPlace_valuation]
    exact hC.symm

private noncomputable def correctedTwoChartGlobalPlaceEquiv
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F] :
    CorrectedTwoChartPlace k F ≃ @GlobalPlace k F _ _ _ κ :=
  Equiv.ofBijective (correctedTwoChartToGlobalPlace (k := k) (F := F))
    (correctedTwoChartToGlobalPlace_bijective (k := k) (F := F))

/-! ## The all-place principal divisor -/

private theorem order_eq_of_rawValuation_eq
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    {κ₁ κ₂ : Algebra k F}
    (P : @GlobalPlace k F _ _ _ κ₁) (Q : @GlobalPlace k F _ _ _ κ₂)
    (hvaluation : @GlobalPlace.valuation k F _ _ _ κ₁ P =
      @GlobalPlace.valuation k F _ _ _ κ₂ Q) (f : F) :
    @GlobalPlace.order k F _ _ _ κ₁ P f =
      @GlobalPlace.order k F _ _ _ κ₂ Q f := by
  change -WithZero.log (@GlobalPlace.valuation k F _ _ _ κ₁ P f) =
    -WithZero.log (@GlobalPlace.valuation k F _ _ _ κ₂ Q f)
  rw [hvaluation]

private noncomputable def inverseFibrePrincipalDivisor
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) : Divisor (InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Fintype (InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :=
    InverseAffinePlace.infinityFibreFintype (oldRationalAlgebra := ρ) k F
  exact Finsupp.onFinset Finset.univ
    (fun D => -WithZero.log (inverseFibreRawValuation
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D (f : F)))
    (by intro D _; exact Finset.mem_univ D)

private theorem inverseFibrePrincipalDivisor_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    inverseFibrePrincipalDivisor (k := k) (F := F) f D =
      -WithZero.log (inverseFibreRawValuation
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D (f : F)) := by
  unfold inverseFibrePrincipalDivisor
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Fintype (InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :=
    InverseAffinePlace.infinityFibreFintype (oldRationalAlgebra := ρ) k F
  simpa only [Finsupp.onFinset_apply]

private noncomputable def twoChartPrincipalDivisor
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) : Divisor (CorrectedTwoChartPlace k F) :=
  Finsupp.mapDomain Sum.inl (AffinePlace.affinePrincipalDivisor k F f) +
    Finsupp.mapDomain Sum.inr (inverseFibrePrincipalDivisor (k := k) (F := F) f)

private theorem mapDomain_inl_apply
    {α β M : Type*} [AddCommMonoid M] (u : α →₀ M) (a : α) :
    Finsupp.mapDomain Sum.inl u (Sum.inl a : Sum α β) = u a :=
  Finsupp.mapDomain_apply Sum.inl_injective u a

private theorem mapDomain_inr_apply
    {α β M : Type*} [AddCommMonoid M] (v : β →₀ M) (b : β) :
    Finsupp.mapDomain Sum.inr v (Sum.inr b : Sum α β) = v b :=
  Finsupp.mapDomain_apply Sum.inr_injective v b

private theorem mapDomain_inr_at_inl
    {α β M : Type*} [AddCommMonoid M] (v : β →₀ M) (a : α) :
    Finsupp.mapDomain Sum.inr v (Sum.inl a : Sum α β) = 0 := by
  apply Finsupp.mapDomain_notin_range
  intro h
  rcases h with ⟨b, h⟩
  cases h

private theorem mapDomain_inl_at_inr
    {α β M : Type*} [AddCommMonoid M] (u : α →₀ M) (b : β) :
    Finsupp.mapDomain Sum.inl u (Sum.inr b : Sum α β) = 0 := by
  apply Finsupp.mapDomain_notin_range
  intro h
  rcases h with ⟨a, h⟩
  cases h

private theorem correctedTwoChartToGlobalPlace_inl_raw
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : AffinePlace.carrier k F) :
    (correctedTwoChartToGlobalPlace (Sum.inl C : CorrectedTwoChartPlace k F)).valuation =
      (repackageRawGlobalPlace κ (AffinePlace.globalPlace k F C)).valuation := rfl

private theorem correctedTwoChartToGlobalPlace_inr_raw
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    (correctedTwoChartToGlobalPlace (Sum.inr D : CorrectedTwoChartPlace k F)).valuation =
      @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D) := by
  change inverseFibreRawValuation D =
    @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D)
  rw [inverseFibreGlobalPlaceAt_valuation]

private theorem twoChartPrincipalDivisor_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) (C : CorrectedTwoChartPlace k F) :
    twoChartPrincipalDivisor (k := k) (F := F) f C =
      GlobalPlace.order (correctedTwoChartToGlobalPlace C) (f : F) := by
  cases C with
  | inl C =>
      change Finsupp.mapDomain Sum.inl (AffinePlace.affinePrincipalDivisor k F f)
          (Sum.inl C) +
          Finsupp.mapDomain Sum.inr (inverseFibrePrincipalDivisor (k := k) (F := F) f)
            (Sum.inl C) = _
      rw [mapDomain_inl_apply, mapDomain_inr_at_inl, add_zero,
        AffinePlace.affinePrincipalDivisor_apply]
      exact order_eq_of_rawValuation_eq _ _
        (correctedTwoChartToGlobalPlace_inl_raw (k := k) (F := F) C).symm (f : F)
  | inr D =>
      change Finsupp.mapDomain Sum.inl (AffinePlace.affinePrincipalDivisor k F f)
          (Sum.inr D) +
          Finsupp.mapDomain Sum.inr (inverseFibrePrincipalDivisor (k := k) (F := F) f)
            (Sum.inr D) = _
      rw [mapDomain_inl_at_inr, zero_add, mapDomain_inr_apply,
        inverseFibrePrincipalDivisor_apply]
      exact order_eq_of_rawValuation_eq _ _
        (correctedTwoChartToGlobalPlace_inr_raw (k := k) (F := F) D).symm (f : F)

private noncomputable def chartGlobalPlaceEquiv
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F] :
    CorrectedTwoChartPlace k F ≃ @GlobalPlace k F _ _ _ κ :=
  correctedTwoChartGlobalPlaceEquiv (k := k) (F := F)

private theorem chartGlobalPlaceEquiv_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : CorrectedTwoChartPlace k F) :
    chartGlobalPlaceEquiv (k := k) (F := F) C = correctedTwoChartToGlobalPlace C := rfl

/-- The finite-support principal divisor transported from the complete two-chart
carrier.  Its coefficient at each actual global place is the normalized
valuation order. -/
noncomputable def GlobalPlace.principalDivisor
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) : Divisor (@GlobalPlace k F _ _ _ κ) :=
  Finsupp.equivMapDomain (chartGlobalPlaceEquiv (k := k) (F := F))
    (twoChartPrincipalDivisor (k := k) (F := F) f)

/-- A principal-divisor coefficient is the constructed normalized valuation
order at the actual global place. -/
theorem GlobalPlace.principalDivisor_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) (P : @GlobalPlace k F _ _ _ κ) :
    GlobalPlace.principalDivisor (k := k) (F := F) f P = GlobalPlace.order P (f : F) := by
  rw [GlobalPlace.principalDivisor, Finsupp.equivMapDomain_apply]
  have hpoint := twoChartPrincipalDivisor_apply (k := k) (F := F) f
    ((chartGlobalPlaceEquiv (k := k) (F := F)).symm P)
  rw [← chartGlobalPlaceEquiv_apply] at hpoint
  simpa using hpoint

private theorem chartGlobalPrincipalDivisor_mul
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f g : Fˣ) :
    GlobalPlace.principalDivisor (k := k) (F := F) (f * g) =
      GlobalPlace.principalDivisor (k := k) (F := F) f +
        GlobalPlace.principalDivisor (k := k) (F := F) g := by
  ext P
  change GlobalPlace.principalDivisor (k := k) (F := F) (f * g) P =
    GlobalPlace.principalDivisor (k := k) (F := F) f P +
      GlobalPlace.principalDivisor (k := k) (F := F) g P
  rw [GlobalPlace.principalDivisor_apply, GlobalPlace.principalDivisor_apply,
    GlobalPlace.principalDivisor_apply]
  simpa using GlobalPlace.order_mul P (f := (f : F)) (g := (g : F))
    f.ne_zero g.ne_zero

private theorem chartGlobalPrincipalDivisor_inv
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) :
    GlobalPlace.principalDivisor (k := k) (F := F) f⁻¹ =
      -GlobalPlace.principalDivisor (k := k) (F := F) f := by
  ext P
  change GlobalPlace.principalDivisor (k := k) (F := F) f⁻¹ P =
    -GlobalPlace.principalDivisor (k := k) (F := F) f P
  rw [GlobalPlace.principalDivisor_apply, GlobalPlace.principalDivisor_apply]
  simpa using GlobalPlace.order_inv P (f : F)

private noncomputable def inverseFibreResidueDegree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) : ℕ := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  exact AffinePlace.residueDegree k F D.1

private noncomputable def twoChartResidueDegree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] :
    CorrectedTwoChartPlace k F → ℕ
  | .inl C => AffinePlace.residueDegree k F C
  | .inr D => inverseFibreResidueDegree (k := k) (F := F) D

/-! ## Public divisor-degree boundary

The corrected carrier and its equivalence deliberately remain private.  The
following names expose only the finite-fibre data, a one-way inverse-fibre
classifier, and the transported degree identity needed by the global layers;
they neither expose a new all-place carrier nor construct a second all-place
`Finsupp` divisor.
-/

/-- Repackage a normalized global valuation for another constant-field
algebra on the same ambient field.  The valuation and its normalization are
unchanged. -/
noncomputable def GlobalPlace.repackage
    {k F : Type*} [Field k] [Finite k] [Field F]
    {oldAlgebra : Algebra k F} (newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) :
    @GlobalPlace k F _ _ _ newAlgebra :=
  repackageRawGlobalPlace newAlgebra P

@[simp]
theorem GlobalPlace.repackage_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    {oldAlgebra : Algebra k F} (newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) :
    @GlobalPlace.valuation k F _ _ _ newAlgebra
        (GlobalPlace.repackage newAlgebra P) =
      @GlobalPlace.valuation k F _ _ _ oldAlgebra P :=
  rfl

/-- Repackaging global places between two constant-field algebras is an
equivalence; both directions retain the identical normalized valuation. -/
noncomputable def GlobalPlace.repackageEquiv
    {k F : Type*} [Field k] [Finite k] [Field F]
    (oldAlgebra newAlgebra : Algebra k F) :
    @GlobalPlace k F _ _ _ oldAlgebra ≃
      @GlobalPlace k F _ _ _ newAlgebra where
  toFun := GlobalPlace.repackage newAlgebra
  invFun := GlobalPlace.repackage oldAlgebra
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

@[simp]
theorem GlobalPlace.repackageEquiv_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    (oldAlgebra newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) :
    @GlobalPlace.valuation k F _ _ _ newAlgebra
        (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
      @GlobalPlace.valuation k F _ _ _ oldAlgebra P :=
  rfl

@[simp]
theorem GlobalPlace.repackageEquiv_order
    {k F : Type*} [Field k] [Finite k] [Field F]
    (oldAlgebra newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) (x : F) :
    @GlobalPlace.order k F _ _ _ newAlgebra
        (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) x =
      @GlobalPlace.order k F _ _ _ oldAlgebra P x :=
  rfl

/-- An inverse-chart infinity-fibre point, repackaged as a global place for the
ambient constant-field algebra. -/
noncomputable def InverseAffinePlace.infinityFibreGlobalPlace
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    @GlobalPlace k F _ _ _ κ :=
  inverseFibreGlobalPlaceAt
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D

private theorem affineGlobalPlace_injective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra (RatFunc k) F]
    [IsScalarTower k[X] (RatFunc k) F]
    [_root_.FunctionField k F] [Algebra.IsSeparable (RatFunc k) F] :
    Function.Injective (AffinePlace.globalPlace k F) := by
  intro C D hCD
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
    (K := F)
  exact Valuation.IsEquiv.of_eq
    (congrArg
      (@GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F)) hCD)

private theorem infinityFibreGlobalPlace_injective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower k[X] (RatFunc k) F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable (RatFunc k) F] :
    Function.Injective
      (InverseAffinePlace.infinityFibreGlobalPlace
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
        (κ := AffinePlace.constantAlgebra k F)) := by
  intro C D hCD
  apply inverseFibreRawValuation_injective (ρ := ρ)
  exact congrArg
    (@GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F)) hCD

/-- Restriction of an actual all-place `Finsupp` to the direct affine chart.
The ambient constant algebra is the one canonically induced by the affine
function-field presentation. -/
noncomputable def GlobalPlace.affineFinsupp
    {k F M : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra (RatFunc k) F]
    [IsScalarTower k[X] (RatFunc k) F]
    [_root_.FunctionField k F] [Algebra.IsSeparable (RatFunc k) F]
    [Zero M]
    (f : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) →₀ M) :
    AffinePlace.carrier k F →₀ M :=
  Finsupp.comapDomain (AffinePlace.globalPlace k F) f
    (affineGlobalPlace_injective (k := k) (F := F)).injOn

/-- Restriction of an actual all-place `Finsupp` to the finite inverse-chart
fibre above infinity. -/
noncomputable def GlobalPlace.infinityFibreFinsupp
    {k F M : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower k[X] (RatFunc k) F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable (RatFunc k) F]
    [Zero M]
    (f : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) →₀ M) :
    InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F →₀ M :=
  Finsupp.comapDomain
    (InverseAffinePlace.infinityFibreGlobalPlace
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
      (κ := AffinePlace.constantAlgebra k F)) f
    (infinityFibreGlobalPlace_injective
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)).injOn

/-- A finite-support sum over all normalized global places splits into the
direct affine chart and the actual finite inverse-chart fibre over infinity.
This exposes only restrictions of the supplied `Finsupp`; the corrected
two-chart carrier and its equivalence remain private. -/
theorem GlobalPlace.finsupp_sum_eq_affine_add_infinityFibre
    {k F M : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower k[X] (RatFunc k) F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable (RatFunc k) F]
    [AddCommMonoid M]
    (f : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) →₀ M) :
    f.sum (fun _ value => value) =
      (GlobalPlace.affineFinsupp (k := k) (F := F) f).sum
          (fun _ value => value) +
        (GlobalPlace.infinityFibreFinsupp
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
          (k := k) (F := F) f).sum (fun _ value => value) := by
  let e := chartGlobalPlaceEquiv
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
    (κ := AffinePlace.constantAlgebra k F)
  let c : CorrectedTwoChartPlace k F →₀ M :=
    Finsupp.equivMapDomain e.symm f
  have hc : c =
      (GlobalPlace.affineFinsupp (k := k) (F := F) f).sumElim
        (GlobalPlace.infinityFibreFinsupp
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
          (k := k) (F := F) f) := by
    ext C
    rcases C with C | D
    · rfl
    · change f (e (Sum.inr D)) =
        f (InverseAffinePlace.infinityFibreGlobalPlace
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
          (κ := AffinePlace.constantAlgebra k F) D)
      rfl
  calc
    f.sum (fun _ value => value) = c.sum (fun _ value => value) := by
      symm
      exact Finsupp.sum_equivMapDomain e.symm f (fun _ value => value)
    _ = ((GlobalPlace.affineFinsupp (k := k) (F := F) f).sumElim
          (GlobalPlace.infinityFibreFinsupp
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
            (k := k) (F := F) f)).sum (fun _ value => value) := by rw [hc]
    _ = _ := by
      simp only [Finsupp.sum, Finsupp.sumElim_support, Finset.sum_disjSum,
        Finsupp.sumElim_inl, Finsupp.sumElim_inr]

/-- A global place where the original inverse coordinate has positive order
comes from an actual point of the inverse-chart infinity fibre. -/
theorem GlobalPlace.exists_infinityFibreGlobalPlace_of_inverseCoordinate_lt_one
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ)
    (hinv : P.valuation ((algebraMap (RatFunc k) F RatFunc.X)⁻¹) < 1) :
    ∃ D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F,
      P = InverseAffinePlace.infinityFibreGlobalPlace
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) D := by
  have hinv' : P.valuation (originalInverseCoordinate ρ) < 1 := by
    simpa only [originalInverseCoordinate, originalCoordinate] using hinv
  let D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F :=
    inverseCentreInInfinityFibre
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) P hinv'
  refine ⟨D, ?_⟩
  apply globalPlace_eq_of_valuation_eq
  change P.valuation =
    @GlobalPlace.valuation k F _ _ _ κ
      (inverseFibreGlobalPlaceAt
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D)
  calc
    P.valuation = inverseFibreRawValuation
        (inverseCentreInInfinityFibre
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) P hinv') :=
      inverseCentre_rawValuation_eq_ambient
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) P hinv'
    _ = inverseFibreRawValuation D := by rfl
    _ = @GlobalPlace.valuation k F _ _ _ κ
        (inverseFibreGlobalPlaceAt
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D) :=
      (inverseFibreGlobalPlaceAt_valuation
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D).symm

/-- The finite-support principal divisor on the actual inverse-chart infinity
fibre. -/
noncomputable def InverseAffinePlace.infinityFibrePrincipalDivisor
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) : Divisor (InverseAffinePlace.infinityFibre k F) :=
  inverseFibrePrincipalDivisor (k := k) (F := F) f

/-- A coefficient of the inverse-fibre principal divisor is the normalized
order of its corresponding inverse-chart global place. -/
theorem InverseAffinePlace.infinityFibrePrincipalDivisor_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) (D : InverseAffinePlace.infinityFibre k F) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    InverseAffinePlace.infinityFibrePrincipalDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (k := k) (F := F) f D =
      GlobalPlace.order (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
        (oldFunctionField := φ) (oldSeparable := σ) k F D) (f : F) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  change inverseFibrePrincipalDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (k := k) (F := F) f D =
    GlobalPlace.order (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
      (oldFunctionField := φ) (oldSeparable := σ) k F D) (f : F)
  rw [inverseFibrePrincipalDivisor_apply
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
  rfl

/-- The actual affine residue degree on an inverse-chart infinity-fibre
point, evaluated in the transported chart. -/
noncomputable def InverseAffinePlace.infinityFibreResidueDegree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre k F) : ℕ :=
  inverseFibreResidueDegree (k := k) (F := F) D

/-- The finite residue degree of an actual global place, transported from the
private direct/inverse chart decomposition. -/
noncomputable def GlobalPlace.residueDegree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) : ℕ :=
  twoChartResidueDegree (k := k) (F := F)
    ((chartGlobalPlaceEquiv (k := k) (F := F)).symm P)

/-- Repackaging a global place for another constant-field algebra preserves
the residue degree transported from the complete two-chart decomposition. -/
theorem GlobalPlace.residueDegree_repackage
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (oldAlgebra newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) :
    @GlobalPlace.residueDegree k F _ _ _ π ρ τ φ σ newAlgebra
        (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
      @GlobalPlace.residueDegree k F _ _ _ π ρ τ φ σ oldAlgebra P := by
  let oldEquiv : CorrectedTwoChartPlace k F ≃
      @GlobalPlace k F _ _ _ oldAlgebra :=
    @chartGlobalPlaceEquiv k F _ _ _ π ρ τ φ σ oldAlgebra
  let newEquiv : CorrectedTwoChartPlace k F ≃
      @GlobalPlace k F _ _ _ newAlgebra :=
    @chartGlobalPlaceEquiv k F _ _ _ π ρ τ φ σ newAlgebra
  have hpreimage :
      newEquiv.symm
          (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
        oldEquiv.symm P := by
    apply newEquiv.injective
    rw [newEquiv.apply_symm_apply]
    apply globalPlace_eq_of_valuation_eq
    have hvaluation := congrArg
      (@GlobalPlace.valuation k F _ _ _ oldAlgebra)
      (oldEquiv.apply_symm_apply P)
    have hsame (C : CorrectedTwoChartPlace k F) :
        @GlobalPlace.valuation k F _ _ _ newAlgebra (newEquiv C) =
          @GlobalPlace.valuation k F _ _ _ oldAlgebra (oldEquiv C) := by
      calc
        @GlobalPlace.valuation k F _ _ _ newAlgebra (newEquiv C) =
            correctedTwoChartValuation C := by
          exact @correctedTwoChartToGlobalPlace_valuation
            k F _ _ _ π ρ τ φ σ newAlgebra C
        _ = @GlobalPlace.valuation k F _ _ _ oldAlgebra (oldEquiv C) := by
          symm
          exact @correctedTwoChartToGlobalPlace_valuation
            k F _ _ _ π ρ τ φ σ oldAlgebra C
    calc
      @GlobalPlace.valuation k F _ _ _ newAlgebra
          (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
          @GlobalPlace.valuation k F _ _ _ oldAlgebra P := rfl
      _ = @GlobalPlace.valuation k F _ _ _ oldAlgebra
          (oldEquiv (oldEquiv.symm P)) := hvaluation.symm
      _ = @GlobalPlace.valuation k F _ _ _ newAlgebra
          (newEquiv (oldEquiv.symm P)) := (hsame _).symm
  change twoChartResidueDegree (k := k) (F := F)
      (newEquiv.symm
        (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P)) =
    twoChartResidueDegree (k := k) (F := F) (oldEquiv.symm P)
  rw [hpreimage]

/-- The residue field of every global place in a finite separable
one-variable function field is finite.  The proof transports the actual
finite affine residue field through the complete two-chart decomposition; it
does not add finiteness to the bare `GlobalPlace` structure. -/
theorem GlobalPlace.finite_residueField
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) : Finite (GlobalPlace.residueField P) := by
  let C := (chartGlobalPlaceEquiv (k := k) (F := F)).symm P
  have hP : chartGlobalPlaceEquiv (k := k) (F := F) C = P :=
    (chartGlobalPlaceEquiv (k := k) (F := F)).apply_symm_apply P
  rw [← hP, chartGlobalPlaceEquiv_apply]
  rcases C with C | D
  · letI : Finite (AffinePlace.residueField k F C) :=
      AffinePlace.finite_residueField k F C
    let e₁ : Localization.AtPrime C.asIdeal ≃+*
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C :=
      (Localization.algEquiv C.asIdeal.primeCompl
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C)).toRingEquiv
    let e₂ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C ≃+*
        (C.valuation F).valuationSubring := by
      rw [C.valuationSubringAtPrime_eq_valuationSubring]
    exact Finite.of_equiv (AffinePlace.residueField k F C)
      (IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)).toEquiv
  · letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    letI : Finite (AffinePlace.residueField k F D.1) :=
      AffinePlace.finite_residueField k F D.1
    let e₁ : Localization.AtPrime D.1.asIdeal ≃+*
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F D.1 :=
      (Localization.algEquiv D.1.asIdeal.primeCompl
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F D.1)).toRingEquiv
    let e₂ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F D.1 ≃+*
        (inverseFibreRawValuation (π := π) (ρ := ρ) (τ := τ) (φ := φ)
          (σ := σ) D).valuationSubring := by
      rw [D.1.valuationSubringAtPrime_eq_valuationSubring,
        inverseFibreRawValuation_eq_ambient (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (σ := σ)]
    exact Finite.of_equiv (AffinePlace.residueField k F D.1)
      (IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)).toEquiv

/-- The actual residue field of every global place is finite-dimensional over
the constant field through its canonical constant-reduction algebra. -/
theorem GlobalPlace.residueField_finiteDimensional
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
    FiniteDimensional k (GlobalPlace.residueField P) := by
  letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
  letI : Finite (GlobalPlace.residueField P) := GlobalPlace.finite_residueField P
  exact (Module.finite_iff_finite).mpr inferInstance

private theorem affineResidueDegree_eq_globalResidueField_finrank
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) (C : AffinePlace.carrier k F)
    (hvaluation : P.valuation = C.valuation F) :
    letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
    letI : FiniteDimensional k (GlobalPlace.residueField P) :=
      GlobalPlace.residueField_finiteDimensional P
    AffinePlace.residueDegree k F C =
      Module.finrank k (GlobalPlace.residueField P) := by
  letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  letI : Algebra k (AffinePlace.residueField k F C) :=
    AffinePlace.residueAlgebra k F C
  letI : FiniteDimensional k (AffinePlace.residueField k F C) :=
    AffinePlace.residueField_finiteDimensional k F C
  let e₁ : Localization.AtPrime C.asIdeal ≃+*
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C :=
    (Localization.algEquiv C.asIdeal.primeCompl
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C)).toRingEquiv
  let e₂ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C ≃+*
      P.valuation.valuationSubring := by
    rw [C.valuationSubringAtPrime_eq_valuationSubring, hvaluation]
  let e : AffinePlace.residueField k F C ≃+* GlobalPlace.residueField P :=
    IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)
  unfold AffinePlace.residueDegree
  apply Nat.pow_right_injective (a := Nat.card k) (by
    letI : Fintype k := Fintype.ofFinite k
    simpa only [Nat.card_eq_fintype_card] using
      (Nat.succ_le_of_lt (Fintype.one_lt_card : 1 < Fintype.card k)))
  change Nat.card k ^ Module.finrank k (AffinePlace.residueField k F C) =
    Nat.card k ^ Module.finrank k (GlobalPlace.residueField P)
  rw [← Module.natCard_eq_pow_finrank (K := k)
      (V := AffinePlace.residueField k F C),
    ← Module.natCard_eq_pow_finrank (K := k)
      (V := GlobalPlace.residueField P)]
  exact Nat.card_congr e.toEquiv

/-- The canonical all-place residue degree of a global place whose valuation
is an inverse-fibre valuation is the residue degree constructed at that
inverse-fibre point. -/
theorem GlobalPlace.residueDegree_eq_inverseFibre
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) (D : InverseAffinePlace.infinityFibre k F)
    (hvaluation : @GlobalPlace.valuation k F _ _ _ κ P =
      @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D)) :
    GlobalPlace.residueDegree P =
      InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F) D := by
  unfold GlobalPlace.residueDegree
  have hpreimage : (chartGlobalPlaceEquiv (k := k) (F := F)).symm P = Sum.inr D := by
    apply (chartGlobalPlaceEquiv (k := k) (F := F)).injective
    rw [(chartGlobalPlaceEquiv (k := k) (F := F)).apply_symm_apply,
      chartGlobalPlaceEquiv_apply]
    apply globalPlace_eq_of_valuation_eq
    exact hvaluation.trans
      (correctedTwoChartToGlobalPlace_inr_raw (k := k) (F := F) D).symm
  rw [hpreimage]
  rfl

/-- The canonical all-place residue degree of a global place whose valuation
is an affine-place valuation is the residue degree constructed at that affine
point.  This is the direct-chart public transport out of the private two-chart
carrier. -/
theorem GlobalPlace.residueDegree_eq_affine
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) (C : AffinePlace.carrier k F)
    (hvaluation : P.valuation =
      @GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F)
        (AffinePlace.globalPlace k F C)) :
    GlobalPlace.residueDegree P = AffinePlace.residueDegree k F C := by
  unfold GlobalPlace.residueDegree
  have hpreimage : (chartGlobalPlaceEquiv (k := k) (F := F)).symm P = Sum.inl C := by
    apply (chartGlobalPlaceEquiv (k := k) (F := F)).injective
    rw [(chartGlobalPlaceEquiv (k := k) (F := F)).apply_symm_apply,
      chartGlobalPlaceEquiv_apply]
    apply globalPlace_eq_of_valuation_eq
    exact hvaluation.trans
      (correctedTwoChartToGlobalPlace_inl_raw (k := k) (F := F) C).symm
  rw [hpreimage]
  rfl

/-- The all-place residue degree transported from the complete two-chart
construction is the dimension of the place's actual residue field over the
constant field. -/
theorem GlobalPlace.residueDegree_eq_finrank
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
    letI : FiniteDimensional k (GlobalPlace.residueField P) :=
      GlobalPlace.residueField_finiteDimensional P
    GlobalPlace.residueDegree P = Module.finrank k (GlobalPlace.residueField P) := by
  letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  let C := (chartGlobalPlaceEquiv (k := k) (F := F)).symm P
  have hP : chartGlobalPlaceEquiv (k := k) (F := F) C = P :=
    (chartGlobalPlaceEquiv (k := k) (F := F)).apply_symm_apply P
  rcases C with C | D
  · have hvaluation : P.valuation = C.valuation F := by
      rw [← hP, chartGlobalPlaceEquiv_apply]
      rfl
    rw [GlobalPlace.residueDegree_eq_affine P C hvaluation]
    exact affineResidueDegree_eq_globalResidueField_finrank P C hvaluation
  · have hvaluationRaw : P.valuation =
        inverseFibreRawValuation
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D := by
      rw [← hP, chartGlobalPlaceEquiv_apply]
      rfl
    have hvaluationGlobal : P.valuation =
        @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D) :=
      hvaluationRaw.trans
        (inverseFibreGlobalPlaceAt_valuation
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D).symm
    rw [GlobalPlace.residueDegree_eq_inverseFibre P D hvaluationGlobal]
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    have hvaluationAffine : P.valuation = D.1.valuation F :=
      hvaluationRaw.trans
        (inverseFibreRawValuation_eq_ambient
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D)
    change AffinePlace.residueDegree k F D.1 =
      Module.finrank k (GlobalPlace.residueField P)
    exact affineResidueDegree_eq_globalResidueField_finrank P D.1 hvaluationAffine

private theorem divisor_degree_equivMapDomain
    {α β : Type*} (e : α ≃ β) (weight : β → ℕ) (D : Divisor α) :
    Divisor.degree weight (Finsupp.equivMapDomain e D) =
      Divisor.degree (fun a => weight (e a)) D := by
  change (Finsupp.equivMapDomain e D).sum
      (fun b coefficient => coefficient * (weight b : ℤ)) =
    D.sum (fun a coefficient => coefficient * (weight (e a) : ℤ))
  rw [Finsupp.sum_equivMapDomain]

private theorem divisor_degree_sum_mapDomain
    {α β : Type*} (left : Divisor α) (right : Divisor β)
    (weight : Sum α β → ℕ) :
    Divisor.degree weight
        (Finsupp.mapDomain Sum.inl left + Finsupp.mapDomain Sum.inr right) =
      Divisor.degree (fun a => weight (Sum.inl a)) left +
        Divisor.degree (fun b => weight (Sum.inr b)) right := by
  rw [Divisor.degree_add]
  change (Finsupp.mapDomain Sum.inl left).sum
      (fun q coefficient => coefficient * (weight q : ℤ)) +
    (Finsupp.mapDomain Sum.inr right).sum
      (fun q coefficient => coefficient * (weight q : ℤ)) =
    left.sum (fun a coefficient => coefficient * (weight (Sum.inl a) : ℤ)) +
      right.sum (fun b coefficient => coefficient * (weight (Sum.inr b) : ℤ))
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]

private theorem principalDivisor_degree_eq_twoChart_degree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (GlobalPlace.principalDivisor (k := k) (F := F) f) =
      Divisor.degree (twoChartResidueDegree (k := k) (F := F))
        (twoChartPrincipalDivisor (k := k) (F := F) f) := by
  unfold GlobalPlace.principalDivisor
  let e := chartGlobalPlaceEquiv (k := k) (F := F)
  have hweight : ∀ C : CorrectedTwoChartPlace k F,
      GlobalPlace.residueDegree (e C) = twoChartResidueDegree (k := k) (F := F) C := by
    intro C
    change twoChartResidueDegree (k := k) (F := F) (e.symm (e C)) =
      twoChartResidueDegree (k := k) (F := F) C
    rw [e.symm_apply_apply]
  calc
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (Finsupp.equivMapDomain e (twoChartPrincipalDivisor (k := k) (F := F) f)) =
      Divisor.degree (fun C => GlobalPlace.residueDegree (e C))
        (twoChartPrincipalDivisor (k := k) (F := F) f) :=
      divisor_degree_equivMapDomain e (GlobalPlace.residueDegree (k := k) (F := F))
        (twoChartPrincipalDivisor (k := k) (F := F) f)
    _ = Divisor.degree (twoChartResidueDegree (k := k) (F := F))
        (twoChartPrincipalDivisor (k := k) (F := F) f) := by
      rw [show (fun C => GlobalPlace.residueDegree (e C)) =
        twoChartResidueDegree (k := k) (F := F) from funext hweight]

private theorem twoChart_principalDivisor_degree_split
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) :
    Divisor.degree (twoChartResidueDegree (k := k) (F := F))
        (twoChartPrincipalDivisor (k := k) (F := F) f) =
      Divisor.degree (AffinePlace.residueDegree k F)
        (AffinePlace.affinePrincipalDivisor k F f) +
      Divisor.degree (inverseFibreResidueDegree (k := k) (F := F))
        (inverseFibrePrincipalDivisor (k := k) (F := F) f) := by
  unfold twoChartPrincipalDivisor
  exact divisor_degree_sum_mapDomain
    (AffinePlace.affinePrincipalDivisor k F f)
    (inverseFibrePrincipalDivisor (k := k) (F := F) f)
    (twoChartResidueDegree (k := k) (F := F))

/-- The all-place principal-divisor degree is the sum of the genuine direct
affine and finite inverse-fibre contributions. -/
theorem GlobalPlace.principalDivisor_degree_eq_chartContributions
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (GlobalPlace.principalDivisor (k := k) (F := F) f) =
      Divisor.degree (AffinePlace.residueDegree k F)
        (AffinePlace.affinePrincipalDivisor k F f) +
      Divisor.degree (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
        (InverseAffinePlace.infinityFibrePrincipalDivisor (k := k) (F := F) f) := by
  rw [principalDivisor_degree_eq_twoChart_degree,
    twoChart_principalDivisor_degree_split]
  rfl

end QEC.Coding.AlgebraicGeometry
