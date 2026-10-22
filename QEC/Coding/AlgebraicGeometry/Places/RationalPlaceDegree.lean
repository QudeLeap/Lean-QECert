/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Places.RationalPlace
import QEC.Coding.AlgebraicGeometry.Places.TwoChartGlobalPlace

/-!
# Rational global places have global residue degree one

The all-place degree is transported through the private two-chart carrier in
`TwoChartGlobalPlace`. This module reconstructs a chart centre from a
normalized global valuation and transports its actual local residue field.
-/

open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom

namespace QEC.Coding.AlgebraicGeometry

/-! ## Normalized valuation comparison -/

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

/-! ## A global valuation centre in an affine chart -/

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
  obtain ⟨a, s, hs, hfrac⟩ := IsFractionRing.div_surjective B P.uniformizer
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
  have hprod : algebraMap B F a = P.uniformizer * algebraMap B F s := by
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

/-! ## Transport of the actual residue field -/

private noncomputable def affineResidueFieldEquiv
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F) (C : AffinePlace.carrier k F)
    (hvaluation : P.valuation = C.valuation F) :
    AffinePlace.residueField k F C ≃+* GlobalPlace.residueField P := by
  change IsLocalRing.ResidueField (Localization.AtPrime C.asIdeal) ≃+*
    IsLocalRing.ResidueField P.valuation.valuationSubring
  let e₁ : Localization.AtPrime C.asIdeal ≃+*
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C :=
    (Localization.algEquiv C.asIdeal.primeCompl
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C)).toRingEquiv
  let e₂ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C ≃+*
      P.valuation.valuationSubring := by
    rw [C.valuationSubringAtPrime_eq_valuationSubring, hvaluation]
  exact IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)

private theorem affineResidueDegree_eq_one_of_rationalGlobal
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (Q : RationalPlace k F) (C : AffinePlace.carrier k F)
    (hvaluation : Q.place.valuation = C.valuation F) :
    AffinePlace.residueDegree k F C = 1 := by
  classical
  let e := affineResidueFieldEquiv Q.place C hvaluation
  unfold AffinePlace.residueDegree
  letI : Algebra k (AffinePlace.residueField k F C) := AffinePlace.residueAlgebra k F C
  letI : FiniteDimensional k (AffinePlace.residueField k F C) :=
    AffinePlace.residueField_finiteDimensional k F C
  apply Module.finrank_of_bijective_algebraMap
  rw [AffinePlace.residueAlgebra_algebraMap]
  letI : Fintype k := Fintype.ofFinite k
  letI : Finite (GlobalPlace.residueField Q.place) :=
    Finite.of_equiv k Q.constantsEquiv.toEquiv
  letI : Fintype (GlobalPlace.residueField Q.place) := Fintype.ofFinite _
  letI : Finite (AffinePlace.residueField k F C) :=
    Finite.of_equiv (GlobalPlace.residueField Q.place) e.toEquiv.symm
  letI : Fintype (AffinePlace.residueField k F C) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card
    (AffinePlace.constantsToResidue k F C)).mpr
  refine ⟨(AffinePlace.constantsToResidue k F C).injective, ?_⟩
  calc
      Fintype.card k = Fintype.card (GlobalPlace.residueField Q.place) :=
        Fintype.card_congr Q.constantsEquiv.toEquiv
      _ = Fintype.card (AffinePlace.residueField k F C) :=
        Fintype.card_congr e.toEquiv.symm

/-! ## The two chart cases -/

private noncomputable def originalCoordinate
    {k F : Type*} [Field k] [Field F] (ρ : Algebra k⟮X⟯ F) : F :=
  ρ.algebraMap RatFunc.X

private noncomputable def originalInverseCoordinate
    {k F : Type*} [Field k] [Field F] (ρ : Algebra k⟮X⟯ F) : F :=
  (originalCoordinate ρ)⁻¹

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
  let hbound : P.valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 :=
    le_of_lt (by
      rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv)
  let C := regularCentreHeightOne P hbound
  refine ⟨C, ?_⟩
  apply Ideal.dvd_iff_le.mpr
  change Ideal.map (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
      (Polynomial.idealX k).asIdeal ≤ C.asIdeal
  rw [Ideal.map_le_iff_le_comap, Polynomial.idealX_span, Ideal.span_le,
    Set.singleton_subset_iff]
  exact Ideal.mem_comap.mpr (regularCentreHeightOne_mem_of_lt_one P hbound
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) (by
      rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv))

/-- A rational global place has degree one for the all-place degree used by
global divisors. -/
theorem RationalPlace.globalResidueDegree_eq_one
    {k F : Type*} [Field k] [Finite k] [Field F] [κ : Algebra k F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (Q : RationalPlace k F) :
    GlobalPlace.residueDegree Q.place = 1 := by
  rcases original_coordinate_dichotomy Q.place with hdirect | hinverse
  · let hbound : Q.place.valuation
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
          (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 := by
      rw [directIntegralCoordinate_eq_originalCoordinate]
      exact hdirect
    let C := regularCentreHeightOne Q.place hbound
    have hvaluation : Q.place.valuation = C.valuation F :=
      placeValuation_eq_regularCentreAdicValuation Q.place hbound
    rw [GlobalPlace.residueDegree_eq_affine Q.place C hvaluation]
    exact affineResidueDegree_eq_one_of_rationalGlobal Q C hvaluation
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
    let hbound : Q.place.valuation
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
          (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 :=
      le_of_lt (by
        rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
        exact hinverse)
    let D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F :=
      inverseCentreInInfinityFibre (π := π) (ρ := ρ) (τ := τ) (φ := φ)
        (σ := σ) Q.place hinverse
    have hvaluation : Q.place.valuation = D.1.valuation F := by
      change Q.place.valuation = (regularCentreHeightOne Q.place hbound).valuation F
      exact placeValuation_eq_regularCentreAdicValuation Q.place hbound
    rw [GlobalPlace.residueDegree_eq_inverseFibre
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) Q.place D (by
      change Q.place.valuation = D.1.valuation F
      exact hvaluation)]
    change AffinePlace.residueDegree k F D.1 = 1
    exact affineResidueDegree_eq_one_of_rationalGlobal Q D.1 hvaluation

end QEC.Coding.AlgebraicGeometry
