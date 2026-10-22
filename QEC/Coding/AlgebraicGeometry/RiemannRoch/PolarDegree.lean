import QEC.Coding.AlgebraicGeometry.Divisors.InverseFibrePrincipalDegree
import QEC.Coding.AlgebraicGeometry.Divisors.RationalBaseInfinityCancellation
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PolarFamily

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The exact degree of the chart-variable pole divisor

This file first transports the weighted degree of any actual all-place divisor
through the public direct/inverse chart restrictions.  It then proves that the
direct chart contributes no pole of the original coordinate, while every
inverse-fibre coefficient is the negative of its principal-divisor order.
The existing inverse-fibre norm formula therefore computes the pole degree as
the rational-function extension degree.

No genus, canonical divisor, specialty, duality, or Riemann--Roch identity is
assumed or proved here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators Polynomial RatFunc WithZero

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance riemannRochPolarDegreeAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

namespace GlobalPlace

private noncomputable def weightedDivisor
    {P : Type*} (weight : P → ℕ) (D : Divisor P) : P →₀ ℤ :=
  Finsupp.onFinset D.support
    (fun P => D P * (weight P : ℤ))
    (by
      intro P hP
      exact Finsupp.mem_support_iff.mpr fun hzero => hP (by simp [hzero]))

@[simp]
private theorem weightedDivisor_apply
    {P : Type*} (weight : P → ℕ) (D : Divisor P) (P : P) :
    weightedDivisor weight D P = D P * (weight P : ℤ) :=
  rfl

private theorem weightedDivisor_sum
    {P : Type*} (weight : P → ℕ) (D : Divisor P) :
    (weightedDivisor weight D).sum (fun _ value => value) =
      Divisor.degree weight D := by
  classical
  unfold weightedDivisor Divisor.degree Divisor.degreeHom Finsupp.sum
  erw [Finsupp.support_onFinset]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hzero : D P * (weight P : ℤ) = 0 <;> simp [hzero] <;> rfl

private theorem affineFinsupp_weightedDivisor
    (D : Divisor (GlobalPlace k F)) :
    affineFinsupp (k := k) (F := F)
        (weightedDivisor (residueDegree (k := k) (F := F)) D) =
      weightedDivisor (AffinePlace.residueDegree k F)
        (affineFinsupp (k := k) (F := F) D) := by
  ext C
  simp only [affineFinsupp, Finsupp.comapDomain_apply,
    weightedDivisor_apply]
  rw [residueDegree_eq_affine (AffinePlace.globalPlace k F C) C rfl]

private theorem infinityFibreFinsupp_weightedDivisor
    (D : Divisor (GlobalPlace k F)) :
    infinityFibreFinsupp (k := k) (F := F)
        (weightedDivisor (residueDegree (k := k) (F := F)) D) =
      weightedDivisor
        (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
        (infinityFibreFinsupp (k := k) (F := F) D) := by
  ext C
  simp only [infinityFibreFinsupp, Finsupp.comapDomain_apply,
    weightedDivisor_apply]
  rw [residueDegree_eq_inverseFibre
    (InverseAffinePlace.infinityFibreGlobalPlace
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s)
      (κ := AffinePlace.constantAlgebra k F) C) C rfl]

/-- The weighted degree of an actual all-place divisor is the sum of the
degrees of its genuine direct-chart and finite inverse-fibre restrictions. -/
theorem divisorDegree_eq_affine_add_infinityFibre
    (D : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) D =
      Divisor.degree (AffinePlace.residueDegree k F)
          (affineFinsupp (k := k) (F := F) D) +
        Divisor.degree
          (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
          (infinityFibreFinsupp (k := k) (F := F) D) := by
  let weighted := weightedDivisor (residueDegree (k := k) (F := F)) D
  have hsplit := finsupp_sum_eq_affine_add_infinityFibre
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s)
    (k := k) (F := F) weighted
  rw [affineFinsupp_weightedDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D,
    infinityFibreFinsupp_weightedDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D,
    weightedDivisor_sum, weightedDivisor_sum] at hsplit
  rw [weightedDivisor_sum] at hsplit
  exact hsplit

private theorem affineFinsupp_polarDivisor_chartVariable_eq_zero :
    affineFinsupp (k := k) (F := F)
        (polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F))) = 0 := by
  ext C
  have hx : chartVariable (k := k) (F := F) ≠ 0 :=
    chartVariable_ne_zero (ρ := ρ) k F
  have hcoordinate : chartVariable (k := k) (F := F) =
      algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap (Polynomial k)
          (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) := by
    unfold chartVariable
    calc
      algebraMap (RatFunc k) F RatFunc.X =
          algebraMap (RatFunc k) F
            (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) := by rfl
      _ = algebraMap (Polynomial k) F Polynomial.X := by
        rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) F]
      _ = algebraMap (_root_.FunctionField.ringOfIntegers k F) F
          (algebraMap (Polynomial k)
            (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) := by
        rw [IsScalarTower.algebraMap_apply (Polynomial k)
          (_root_.FunctionField.ringOfIntegers k F) F]
  have hregular : (AffinePlace.globalPlace k F C).valuation
      (chartVariable (k := k) (F := F)) ≤ 1 := by
    rw [hcoordinate]
    exact C.valuation_le_one _
  have horder : 0 ≤ (AffinePlace.globalPlace k F C).order
      (chartVariable (k := k) (F := F)) :=
    (regularAt_iff_order_nonnegative (AffinePlace.globalPlace k F C) hx).mp hregular
  simp only [affineFinsupp, Finsupp.comapDomain_apply, polarDivisor,
    dif_neg hx, Finsupp.sup_apply, Finsupp.zero_apply]
  rw [Finsupp.neg_apply, principalDivisor_apply]
  simp only [Units.val_mk0]
  exact max_eq_right (by omega)

private theorem infinityFibreFinsupp_polarDivisor_chartVariable_eq_neg_principal :
    infinityFibreFinsupp (k := k) (F := F)
        (polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F))) =
      -InverseAffinePlace.infinityFibrePrincipalDivisor
        (k := k) (F := F)
        (Units.mk0 (chartVariable (k := k) (F := F))
          (chartVariable_ne_zero (ρ := ρ) k F)) := by
  ext D
  letI : Algebra (RatFunc k) F :=
    InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
  letI : Algebra (Polynomial k) F :=
    InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F :=
    InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable (RatFunc k) F :=
    InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := s) k F
  let P := InverseAffinePlace.globalPlace
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) (oldSeparable := s) k F D
  have hx : chartVariable (ρ := ρ) (k := k) (F := F) ≠ 0 :=
    chartVariable_ne_zero (ρ := ρ) k F
  have hinverseValuation : P.valuation
      (chartVariable (ρ := ρ) (k := k) (F := F))⁻¹ < 1 := by
    have h := InverseAffinePlace.globalPlace_coordinate_valuation_lt_one
      (oldPolynomialAlgebra := π) (oldRationalAlgebra := ρ)
      (oldScalarTower := τ) (oldFunctionField := φ) (oldSeparable := s) k F D
    rw [← IsScalarTower.algebraMap_apply (Polynomial k)
        (_root_.FunctionField.ringOfIntegers k F) F,
      IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) F] at h
    change P.valuation
      (InverseAffinePlace.transportedRationalMap
        (oldRationalAlgebra := ρ) k F RatFunc.X) < 1 at h
    rw [InverseAffinePlace.transportedRationalMap_X
      (oldPolynomialAlgebra := π) (oldRationalAlgebra := ρ)
      (oldScalarTower := τ) (oldFunctionField := φ) (oldSeparable := s)] at h
    simpa only [InverseChart.inverseCoordinate, InverseChart.coordinate,
      chartVariable] using h
  have hinverseNe : P.valuation
      (chartVariable (ρ := ρ) (k := k) (F := F))⁻¹ ≠ 0 :=
    P.valuation.ne_zero_iff.mpr (inv_ne_zero hx)
  have hlog : WithZero.log
      (P.valuation (chartVariable (ρ := ρ) (k := k) (F := F))⁻¹) < 0 := by
    rw [← WithZero.exp_log hinverseNe, ← WithZero.exp_zero] at hinverseValuation
    exact WithZero.exp_lt_exp.mp hinverseValuation
  have horder : P.order
      (chartVariable (ρ := ρ) (k := k) (F := F)) < 0 := by
    have hinverseOrder : 0 < P.order
        (chartVariable (ρ := ρ) (k := k) (F := F))⁻¹ := by
      unfold order
      omega
    rw [order_inv] at hinverseOrder
    omega
  simp only [infinityFibreFinsupp, Finsupp.comapDomain_apply, polarDivisor,
    dif_neg hx, Finsupp.sup_apply, principalDivisor_apply, Units.val_mk0,
    Finsupp.neg_apply]
  rw [InverseAffinePlace.infinityFibrePrincipalDivisor_apply
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s)]
  change max (-P.order (chartVariable (ρ := ρ) (k := k) (F := F))) 0 =
    -P.order (chartVariable (ρ := ρ) (k := k) (F := F))
  exact max_eq_left (by omega)

private theorem infinityFibrePrincipalDivisor_chartVariable_degree :
    Divisor.degree
        (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
        (InverseAffinePlace.infinityFibrePrincipalDivisor (k := k) (F := F)
          (Units.mk0 (chartVariable (k := k) (F := F))
            (chartVariable_ne_zero (ρ := ρ) k F))) =
      -(Module.finrank (RatFunc k) F : ℤ) := by
  rw [_root_.QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree.inverse_fibre_degree_eq_fieldNorm_rationalInfinity_order]
  change GlobalPlace.order (GlobalPlace.rationalInfinity k)
      (Algebra.norm (RatFunc k)
        (algebraMap (RatFunc k) F RatFunc.X)) = _
  rw [Algebra.norm_algebraMap]
  have hpow : (RatFunc.X : RatFunc k) ^ Module.finrank (RatFunc k) F ≠ 0 :=
    pow_ne_zero _ RatFunc.X_ne_zero
  rw [RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
    k _ hpow]
  have hintDegree :
      ((RatFunc.X : RatFunc k) ^ Module.finrank (RatFunc k) F).intDegree =
        (Module.finrank (RatFunc k) F : ℤ) := by
    induction Module.finrank (RatFunc k) F with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ RatFunc.X_ne_zero)
          RatFunc.X_ne_zero, ih, RatFunc.intDegree_X]
        norm_num
  rw [hintDegree]

/-- The pole divisor of the chosen rational coordinate has degree exactly the
rational-function extension degree. -/
theorem polarDivisor_chartVariable_degree_eq_finrank :
    Divisor.degree (residueDegree (k := k) (F := F))
        (polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F))) =
      (Module.finrank (RatFunc k) F : ℤ) := by
  rw [divisorDegree_eq_affine_add_infinityFibre
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s),
    affineFinsupp_polarDivisor_chartVariable_eq_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s),
    Divisor.degree_zero, zero_add,
    infinityFibreFinsupp_polarDivisor_chartVariable_eq_neg_principal
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s),
    Divisor.degree_neg,
    infinityFibrePrincipalDivisor_chartVariable_degree
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  ring

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
