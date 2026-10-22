/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Codes.Code
import QEC.Coding.AlgebraicGeometry.Residues.Global.FunctionFieldGlobalResidue
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PolarFamily
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Theorem

/-!
# Dimensions and canonical-divisor duality for AG evaluation codes

This module derives the Riemann--Roch dimension formulas for the actual
evaluation-code range and constructs a differential normalized to have traced
residue one at every selected rational place.  Its differential divisor gives
the literal, unscaled dual evaluation code.

The normalization is proved by a finite-dimensional residue-map argument.  It
is not supplied as a hypothesis, and no parameter or duality conclusion is
stored in a code record.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators Polynomial RatFunc WithTop WithZero

noncomputable section

variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance agCodeDualityAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance agCodeDualityScalarTower : IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ)
    (φ := φ) (s := s) k F

local instance agCodeDualityFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G

variable [IsFullConstantField k F]
variable {ι : Type*} [Fintype ι]

/-- The dimension of an injective AG evaluation code satisfies the
Riemann--Roch lower bound. -/
theorem agEvaluation_dimension_lower_bound
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (hdegree :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
        Fintype.card ι) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G + 1 -
        (GlobalPlace.functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) ≤
      (QEC.Coding.Dimension (agEvaluationCode G Q hG) : ℤ) := by
  have hinjective := agEvaluation_injective G Q hQ hG hdegree
  have hrange := LinearMap.finrank_range_of_inj hinjective
  have hrr := GlobalPlace.riemannRoch_lower_bound
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
  change _ ≤ (Module.finrank k (LinearMap.range (agEvaluationLinearMap G Q hG)) : ℤ)
  rw [hrange]
  simpa only [GlobalPlace.riemannRochDimension] using hrr

/-- In the large-degree injective range, an AG evaluation code has the exact
Riemann--Roch dimension. -/
theorem agEvaluation_dimension_eq_of_large_degree
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (hlarge :
      2 * (GlobalPlace.functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G)
    (hsmall :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
        Fintype.card ι) :
    (QEC.Coding.Dimension (agEvaluationCode G Q hG) : ℤ) =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G + 1 -
        (GlobalPlace.functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := by
  have hinjective := agEvaluation_injective G Q hQ hG hsmall
  have hrange := LinearMap.finrank_range_of_inj hinjective
  have hrr := GlobalPlace.riemannRoch_eq_of_large_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G hlarge
  change (Module.finrank k (LinearMap.range (agEvaluationLinearMap G Q hG)) : ℤ) = _
  rw [hrange]
  simpa only [GlobalPlace.riemannRochDimension] using hrr

/-- The evaluation kernel embeds into the Riemann--Roch space obtained by
subtracting the complete evaluation divisor.  This is the direction of the
kernel description needed for the unrestricted duality dimension argument. -/
private noncomputable def agEvaluationKernelRestriction
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (agEvaluationLinearMap G Q hG).ker →ₗ[k]
      GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) where
  toFun f := ⟨(f.1 : F),
    evaluationZero_mem_riemannRochSubmodule_sub G Q hQ hG f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem agEvaluationKernelRestriction_injective
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    Function.Injective
      (agEvaluationKernelRestriction (k := k) (F := F) G Q hQ hG) := by
  intro x y hxy
  have hval : ((x.1 : GlobalPlace.riemannRochSubmodule G) : F) =
      ((y.1 : GlobalPlace.riemannRochSubmodule G) : F) :=
    congrArg
      (fun z : GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) =>
        (z : F)) hxy
  exact Subtype.ext (Subtype.ext hval)

/-- Without any degree-range hypothesis, the evaluation-code dimension is at
least the difference of the two relevant Riemann--Roch dimensions. -/
private theorem agEvaluation_dimension_ge_riemannRoch_difference
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (GlobalPlace.riemannRochDimension G : ℤ) -
        (GlobalPlace.riemannRochDimension (G - evaluationDivisor Q) : ℤ) ≤
      (QEC.Coding.Dimension (agEvaluationCode G Q hG) : ℤ) := by
  have hkerNat : Module.finrank k (agEvaluationLinearMap G Q hG).ker ≤
      Module.finrank k
        (GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q)) :=
    LinearMap.finrank_le_finrank_of_injective
      (agEvaluationKernelRestriction_injective
        (k := k) (F := F) G Q hQ hG)
  have hker : (Module.finrank k (agEvaluationLinearMap G Q hG).ker : ℤ) ≤
      (GlobalPlace.riemannRochDimension (G - evaluationDivisor Q) : ℤ) := by
    exact_mod_cast hkerNat
  have hrankNat := (agEvaluationLinearMap G Q hG).finrank_range_add_finrank_ker
  have hrank := congrArg (fun n : ℕ => (n : ℤ)) hrankNat
  simp only [Nat.cast_add] at hrank
  change (GlobalPlace.riemannRochDimension G : ℤ) -
      (GlobalPlace.riemannRochDimension (G - evaluationDivisor Q) : ℤ) ≤
    (Module.finrank k (agEvaluationLinearMap G Q hG).range : ℤ)
  change (Module.finrank k (agEvaluationLinearMap G Q hG).range : ℤ) +
      (Module.finrank k (agEvaluationLinearMap G Q hG).ker : ℤ) =
    (GlobalPlace.riemannRochDimension G : ℤ) at hrank
  omega

/-! ## A finite-field avoidance function -/

/-- The polynomial `X ^ |k| - X + 1`, whose value is one at every element of
the finite constant field. -/
private noncomputable def evaluationAvoidancePolynomial : Polynomial k :=
  Polynomial.X ^ Fintype.card k - Polynomial.X + 1

private theorem evaluationAvoidancePolynomial_natDegree :
    (evaluationAvoidancePolynomial k).natDegree = Fintype.card k := by
  have hcard : 1 < Fintype.card k := Fintype.one_lt_card
  rw [evaluationAvoidancePolynomial]
  calc
    (Polynomial.X ^ Fintype.card k - Polynomial.X + 1 : Polynomial k).natDegree =
        (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial k).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt (by
        rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hcard]
        simpa using (Nat.zero_lt_of_lt hcard))
    _ = Fintype.card k :=
      FiniteField.X_pow_card_sub_X_natDegree_eq k hcard

private theorem evaluationAvoidancePolynomial_monic :
    (evaluationAvoidancePolynomial k).Monic := by
  have hcard : 1 < Fintype.card k := Fintype.one_lt_card
  rw [evaluationAvoidancePolynomial]
  have hdegree :
      (Polynomial.X - 1 : Polynomial k).degree < Fintype.card k := by
    calc
      (Polynomial.X - 1 : Polynomial k).degree ≤
          max (Polynomial.X : Polynomial k).degree
            (1 : Polynomial k).degree := Polynomial.degree_sub_le _ _
      _ = (1 : WithBot ℕ) := by norm_num
      _ < Fintype.card k := by exact_mod_cast hcard
  have hpoly : (Polynomial.X ^ Fintype.card k - (Polynomial.X - 1) : Polynomial k) =
      Polynomial.X ^ Fintype.card k - Polynomial.X + 1 := by ring
  rw [← hpoly]
  exact Polynomial.monic_X_pow_sub hdegree

/-- The value of the avoidance polynomial at the direct chart coordinate. -/
private noncomputable def evaluationAvoidanceDenominator : F :=
  Polynomial.aeval (GlobalPlace.chartVariable (k := k) (F := F))
    (evaluationAvoidancePolynomial k)

/-- A nonconstant function regular at every rational evaluation place. -/
private noncomputable def evaluationAvoidanceFunction : F :=
  (evaluationAvoidanceDenominator (k := k) (F := F))⁻¹

private theorem evaluationAvoidanceDenominator_transcendental :
    Transcendental k (evaluationAvoidanceDenominator (k := k) (F := F)) := by
  apply (GlobalPlace.chartVariable_transcendental
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F).aeval
  · rw [evaluationAvoidancePolynomial_natDegree]
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt Fintype.one_lt_card)
  · rw [(evaluationAvoidancePolynomial_monic k).leadingCoeff]
    exact mem_nonZeroDivisors_iff_ne_zero.mpr one_ne_zero

private theorem evaluationAvoidanceDenominator_ne_zero :
    evaluationAvoidanceDenominator (k := k) (F := F) ≠ 0 := by
  intro hzero
  apply evaluationAvoidanceDenominator_transcendental
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  rw [hzero]
  exact isAlgebraic_zero

private theorem evaluationAvoidanceFunction_transcendental :
    Transcendental k (evaluationAvoidanceFunction (k := k) (F := F)) := by
  intro halgebraic
  apply evaluationAvoidanceDenominator_transcendental
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  exact IsAlgebraic.inv_iff.mp halgebraic

private theorem evaluationAvoidanceFunction_ne_zero :
    evaluationAvoidanceFunction (k := k) (F := F) ≠ 0 := by
  rw [evaluationAvoidanceFunction]
  exact inv_ne_zero (evaluationAvoidanceDenominator_ne_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)

private theorem evaluationAvoidanceDenominator_eq :
    evaluationAvoidanceDenominator (k := k) (F := F) =
      GlobalPlace.chartVariable (k := k) (F := F) ^ Fintype.card k -
        GlobalPlace.chartVariable (k := k) (F := F) + 1 := by
  simp only [evaluationAvoidanceDenominator, evaluationAvoidancePolynomial,
    map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_one]

private theorem inv_coe_mem_valuationRing_of_evaluate_ne_zero
    (Q : RationalPlace k F) (x : Q.place.valuationRing)
    (hx : Q.evaluate x ≠ 0) : ((x : F)⁻¹) ∈ Q.place.valuationRing := by
  have hunit : IsUnit x := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmaximal
    exact hx ((Q.evaluate_eq_zero_iff x).2 hmaximal)
  rw [← hunit.unit_spec]
  change (Q.place.valuationRing.subtype
    (↑hunit.unit : Q.place.valuationRing))⁻¹ ∈ Q.place.valuationRing
  rw [← map_units_inv Q.place.valuationRing.subtype hunit.unit]
  exact (↑(hunit.unit⁻¹) : Q.place.valuationRing).property

private theorem evaluationAvoidanceFunction_regularAt_of_chartVariable_le_one
    (Q : RationalPlace k F)
    (ht : Q.place.valuation
      (GlobalPlace.chartVariable (k := k) (F := F)) ≤ 1) :
    Q.place.RegularAt (evaluationAvoidanceFunction (k := k) (F := F)) := by
  let tO : Q.place.valuationRing :=
    ⟨GlobalPlace.chartVariable (k := k) (F := F), ht⟩
  let dO : Q.place.valuationRing :=
    tO ^ Fintype.card k - tO + 1
  have hdO : (dO : F) =
      evaluationAvoidanceDenominator (k := k) (F := F) := by
    rw [evaluationAvoidanceDenominator_eq]
    rfl
  have hevaluate : Q.evaluate dO = 1 := by
    dsimp only [dO]
    rw [map_add, map_sub, map_pow, map_one, FiniteField.pow_card]
    ring
  rw [GlobalPlace.regularAt_iff_mem_valuationRing,
    evaluationAvoidanceFunction, ← hdO]
  exact inv_coe_mem_valuationRing_of_evaluate_ne_zero
    (k := k) (F := F) Q dO (by
    rw [hevaluate]
    exact one_ne_zero)

private theorem evaluationAvoidanceFunction_eq_inverse_chart :
    evaluationAvoidanceFunction (k := k) (F := F) =
      (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^ Fintype.card k *
        (1 - (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^
            (Fintype.card k - 1) +
          (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^
            Fintype.card k)⁻¹ := by
  let t := GlobalPlace.chartVariable (k := k) (F := F)
  have ht : t ≠ 0 := GlobalPlace.chartVariable_ne_zero (ρ := ρ) k F
  rw [evaluationAvoidanceFunction, evaluationAvoidanceDenominator_eq]
  change (t ^ Fintype.card k - t + 1)⁻¹ =
    (t⁻¹) ^ Fintype.card k *
      (1 - (t⁻¹) ^ (Fintype.card k - 1) +
        (t⁻¹) ^ Fintype.card k)⁻¹
  have hcard : 0 < Fintype.card k := Fintype.card_pos
  have ht_mul_inv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have hshift :
      t * (t⁻¹) ^ Fintype.card k =
        (t⁻¹) ^ (Fintype.card k - 1) := by
    rw [show Fintype.card k = Fintype.card k - 1 + 1 by omega,
      pow_succ]
    calc
      t * ((t⁻¹) ^ (Fintype.card k - 1) * t⁻¹) =
          (t⁻¹) ^ (Fintype.card k - 1) * (t * t⁻¹) := by ring
      _ = (t⁻¹) ^ (Fintype.card k - 1) := by rw [ht_mul_inv, mul_one]
  have hscale :
      (t⁻¹) ^ Fintype.card k * (t ^ Fintype.card k - t + 1) =
        1 - (t⁻¹) ^ (Fintype.card k - 1) +
          (t⁻¹) ^ Fintype.card k := by
    calc
      (t⁻¹) ^ Fintype.card k * (t ^ Fintype.card k - t + 1) =
          ((t⁻¹) * t) ^ Fintype.card k -
            t * (t⁻¹) ^ Fintype.card k +
              (t⁻¹) ^ Fintype.card k := by rw [mul_pow]; ring
      _ = 1 - (t⁻¹) ^ (Fintype.card k - 1) +
          (t⁻¹) ^ Fintype.card k := by
        rw [inv_mul_cancel₀ ht, one_pow, hshift]
  have hdenominator : t ^ Fintype.card k - t + 1 ≠ 0 := by
    rw [← evaluationAvoidanceDenominator_eq]
    exact evaluationAvoidanceDenominator_ne_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  rw [← hscale]
  field_simp [ht, hdenominator]

private theorem evaluationAvoidanceFunction_regularAt_of_inverse_chart_lt_one
    (Q : RationalPlace k F)
    (hy : Q.place.valuation
      (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ < 1) :
    Q.place.RegularAt (evaluationAvoidanceFunction (k := k) (F := F)) := by
  let yO : Q.place.valuationRing :=
    ⟨(GlobalPlace.chartVariable (k := k) (F := F))⁻¹, le_of_lt hy⟩
  let dO : Q.place.valuationRing :=
    1 - yO ^ (Fintype.card k - 1) + yO ^ Fintype.card k
  have hymaximal : yO ∈
      IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    exact hy
  have hyevaluate : Q.evaluate yO = 0 :=
    (Q.evaluate_eq_zero_iff yO).2 hymaximal
  have hcard : 1 < Fintype.card k := Fintype.one_lt_card
  have hcard_ne : Fintype.card k ≠ 0 := by omega
  have hcard_sub_ne : Fintype.card k - 1 ≠ 0 := by omega
  have hdevaluate : Q.evaluate dO = 1 := by
    dsimp only [dO]
    rw [map_add, map_sub, map_pow, map_pow, map_one, hyevaluate]
    simp [hcard_ne, hcard_sub_ne]
  have hdO : (dO : F) =
      1 - (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^
          (Fintype.card k - 1) +
        (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^
          Fintype.card k := rfl
  have hdOinv : ((dO : F)⁻¹) ∈ Q.place.valuationRing :=
    inv_coe_mem_valuationRing_of_evaluate_ne_zero
      (k := k) (F := F) Q dO (by
        rw [hdevaluate]
        exact one_ne_zero)
  rw [GlobalPlace.regularAt_iff_mem_valuationRing,
    evaluationAvoidanceFunction_eq_inverse_chart, ← hdO]
  exact Q.place.valuationRing.mul_mem _ _
    (Q.place.valuationRing.pow_mem yO.property _) hdOinv

private theorem evaluationAvoidanceFunction_regularAt_rationalPlace
    (Q : RationalPlace k F) :
    Q.place.RegularAt (evaluationAvoidanceFunction (k := k) (F := F)) := by
  rcases Valuation.val_le_one_or_val_inv_lt_one Q.place.valuation
      (GlobalPlace.chartVariable (k := k) (F := F)) with ht | hy
  · exact evaluationAvoidanceFunction_regularAt_of_chartVariable_le_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q ht
  · exact evaluationAvoidanceFunction_regularAt_of_inverse_chart_lt_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hy

/-- The pole divisor of the avoidance function.  Its support misses every
rational evaluation place, while its degree is strictly positive. -/
private noncomputable def evaluationAvoidancePoleDivisor :
    Divisor (GlobalPlace k F) :=
  GlobalPlace.polarDivisor (k := k) (F := F)
    (evaluationAvoidanceFunction (k := k) (F := F))

private theorem evaluationAvoidancePoleDivisor_apply_rationalPlace
    (Q : RationalPlace k F) :
    evaluationAvoidancePoleDivisor (k := k) (F := F) Q.place = 0 := by
  have hfunction := evaluationAvoidanceFunction_ne_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have hregular := evaluationAvoidanceFunction_regularAt_rationalPlace
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q
  have horder : 0 ≤ Q.place.order
      (evaluationAvoidanceFunction (k := k) (F := F)) :=
    (GlobalPlace.regularAt_iff_order_nonnegative Q.place hfunction).mp hregular
  simp only [evaluationAvoidancePoleDivisor, GlobalPlace.polarDivisor,
    dif_neg hfunction, Finsupp.sup_apply, Finsupp.zero_apply]
  rw [Finsupp.neg_apply, GlobalPlace.principalDivisor_apply]
  simp only [Units.val_mk0]
  exact max_eq_right (by omega)

private theorem exists_valuation_gt_one_of_not_isAlgebraic_for_avoidance
    {x : F} (hx : ¬IsAlgebraic k x) :
    ∃ P : GlobalPlace k F, 1 < P.valuation x := by
  by_contra h
  push Not at h
  exact hx (GlobalPlace.isAlgebraic_of_valuation_le_one
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x h)

private theorem residueDegree_pos_for_avoidance (P : GlobalPlace k F) :
    0 < GlobalPlace.residueDegree (k := k) (F := F) P := by
  letI : Algebra k (GlobalPlace.residueField P) :=
    GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  rw [GlobalPlace.residueDegree_eq_finrank P]
  exact Module.finrank_pos

private theorem divisorDegree_mono_for_avoidance
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) D ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegree_nonnegative : 0 ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegree_nonnegative

private theorem evaluationAvoidancePoleDivisor_degree_pos :
    0 < Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
      (evaluationAvoidancePoleDivisor (k := k) (F := F)) := by
  classical
  let x := evaluationAvoidanceFunction (k := k) (F := F)
  have hx0 : x ≠ 0 := evaluationAvoidanceFunction_ne_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have hx : ¬IsAlgebraic k x := evaluationAvoidanceFunction_transcendental
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  obtain ⟨P, hP⟩ :=
    exists_valuation_gt_one_of_not_isAlgebraic_for_avoidance
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hx
  have hcoefficient : 0 <
      evaluationAvoidancePoleDivisor (k := k) (F := F) P := by
    have hlog : WithZero.log 1 < WithZero.log (P.valuation x) :=
      (WithZero.log_lt_log one_ne_zero
        ((P.valuation).ne_zero_iff.mpr hx0)).2 hP
    simp only [WithZero.log_one] at hlog
    change 0 < GlobalPlace.polarDivisor (k := k) (F := F) x P
    simp only [GlobalPlace.polarDivisor, dif_neg hx0,
      Finsupp.sup_apply, Finsupp.zero_apply]
    change 0 < max
      (-(GlobalPlace.principalDivisor (k := k) (F := F)
        (Units.mk0 x hx0) P)) 0
    rw [GlobalPlace.principalDivisor_apply]
    simp only [Units.val_mk0]
    have hnegOrder : 0 < -P.order x := by
      simpa only [GlobalPlace.order, neg_neg] using hlog
    exact hnegOrder.trans_le (le_max_left _ _)
  have hsingle : Finsupp.single P
      (evaluationAvoidancePoleDivisor (k := k) (F := F) P) ≤
      evaluationAvoidancePoleDivisor (k := k) (F := F) := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQP)]
      exact GlobalPlace.polarDivisor_nonnegative
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x Q
  have hle := divisorDegree_mono_for_avoidance
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hsingle
  have hsingleDegree :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
          (Finsupp.single P
            (evaluationAvoidancePoleDivisor (k := k) (F := F) P)) =
        evaluationAvoidancePoleDivisor (k := k) (F := F) P *
          (GlobalPlace.residueDegree (k := k) (F := F) P : ℤ) := by
    simp [Divisor.degree, Divisor.degreeHom]
  rw [hsingleDegree] at hle
  have hresidue : 0 <
      (GlobalPlace.residueDegree (k := k) (F := F) P : ℤ) := by
    exact_mod_cast residueDegree_pos_for_avoidance
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F P
  exact (mul_pos hcoefficient hresidue).trans_le hle

/-! ## Finite-dimensional residue interpolation -/

private noncomputable def residueInterpolationBaseDifferential :
    Differential k F :=
  FunctionFieldDifferential.functionFieldDifferentialGenerator
    (k := k) (F := F)

private theorem residueInterpolationBaseDifferential_ne_zero :
    residueInterpolationBaseDifferential (k := k) (F := F) ≠ 0 :=
  FunctionFieldDifferential.functionFieldDifferentialGenerator_ne_zero
    (k := k) (F := F)

private noncomputable def residueInterpolationCanonicalDivisor :
    Divisor (GlobalPlace k F) :=
  FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F)
    (residueInterpolationBaseDifferential (k := k) (F := F))
    (residueInterpolationBaseDifferential_ne_zero (k := k) (F := F))

private theorem residueInterpolationCanonicalDivisor_isCanonical :
    FunctionFieldDifferential.IsCanonicalDivisor (k := k) (F := F)
      (residueInterpolationCanonicalDivisor (k := k) (F := F)) :=
  FunctionFieldDifferential.differentialDivisor_isCanonical
    (k := k) (F := F)
    (residueInterpolationBaseDifferential (k := k) (F := F))
    (residueInterpolationBaseDifferential_ne_zero (k := k) (F := F))

private noncomputable def residueInterpolationBaseDivisor :
    Divisor (GlobalPlace k F) :=
  residueInterpolationCanonicalDivisor (k := k) (F := F) +
    evaluationAvoidancePoleDivisor (k := k) (F := F)

private noncomputable def residueInterpolationDivisor
    (Q : ι → RationalPlace k F) : Divisor (GlobalPlace k F) :=
  residueInterpolationBaseDivisor (k := k) (F := F) +
    evaluationDivisor Q

private theorem evaluationDivisor_nonnegative_for_interpolation
    (Q : ι → RationalPlace k F) :
    Divisor.Nonnegative (evaluationDivisor Q) := by
  classical
  intro P
  unfold evaluationDivisor zeroCoordinateDivisor
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : (Q i).place = P
  · subst P
    simp
  · rw [Finsupp.single_apply, if_neg hi]

private theorem residueInterpolationBaseDivisor_le
    (Q : ι → RationalPlace k F) :
    residueInterpolationBaseDivisor (k := k) (F := F) ≤
      residueInterpolationDivisor (k := k) (F := F) Q := by
  intro P
  simp only [residueInterpolationDivisor, Finsupp.add_apply]
  exact le_add_of_nonneg_right
    (evaluationDivisor_nonnegative_for_interpolation
      (k := k) (F := F) Q P)

private theorem residueInterpolationCanonicalDivisor_degree :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationCanonicalDivisor (k := k) (F := F)) =
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 2 :=
  CanonicalDivisor.degree_eq_two_mul_genus_sub_two
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (residueInterpolationCanonicalDivisor_isCanonical
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)

private theorem residueInterpolationBaseDivisor_degree :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationBaseDivisor (k := k) (F := F)) =
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 2 +
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
          (evaluationAvoidancePoleDivisor (k := k) (F := F)) := by
  rw [residueInterpolationBaseDivisor, Divisor.degree_add,
    residueInterpolationCanonicalDivisor_degree
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]

private theorem residueInterpolationDivisor_degree
    (Q : ι → RationalPlace k F) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationDivisor (k := k) (F := F) Q) =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
          (residueInterpolationBaseDivisor (k := k) (F := F)) +
        Fintype.card ι := by
  rw [residueInterpolationDivisor, Divisor.degree_add,
    evaluationDivisor_degree_eq_card]

private theorem residueInterpolationBaseDivisor_large :
    2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationBaseDivisor (k := k) (F := F)) := by
  rw [residueInterpolationBaseDivisor_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  have hpositive := evaluationAvoidancePoleDivisor_degree_pos
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  omega

private theorem residueInterpolationDivisor_large
    (Q : ι → RationalPlace k F) :
    2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationDivisor (k := k) (F := F) Q) := by
  rw [residueInterpolationDivisor_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  have hbase := residueInterpolationBaseDivisor_large
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have hcard : 0 ≤ (Fintype.card ι : ℤ) := by positivity
  omega

private theorem residueInterpolation_smul_baseDifferential_mem_simplePole
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (f : GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q)) (i : ι) :
    (f : F) • residueInterpolationBaseDifferential (k := k) (F := F) ∈
      Differential.simplePoleDifferentialLattice (Q i).place := by
  by_cases hf : (f : F) = 0
  · rw [hf, zero_smul]
    exact (Differential.simplePoleDifferentialLattice (Q i).place).zero_mem
  · apply (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      (k := k) (F := F) (Q i).place (f : F) hf
      (residueInterpolationBaseDifferential (k := k) (F := F))
      (residueInterpolationBaseDifferential_ne_zero (k := k) (F := F))).mpr
    have hbound :=
      (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
        (residueInterpolationDivisor (k := k) (F := F) Q) hf).mp
          f.property (Q i).place
    simp only [residueInterpolationDivisor, residueInterpolationBaseDivisor,
      Finsupp.add_apply] at hbound
    rw [evaluationDivisor_apply_at Q hQ i,
      evaluationAvoidancePoleDivisor_apply_rationalPlace
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)] at hbound
    have hcanonical :
        residueInterpolationCanonicalDivisor (k := k) (F := F) (Q i).place =
          FunctionFieldDifferential.differentialOrder
            (k := k) (F := F) (Q i).place
            (residueInterpolationBaseDifferential (k := k) (F := F))
            (residueInterpolationBaseDifferential_ne_zero
              (k := k) (F := F)) := by
      change FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F)
          (residueInterpolationBaseDifferential (k := k) (F := F))
          (residueInterpolationBaseDifferential_ne_zero
            (k := k) (F := F)) (Q i).place = _
      exact FunctionFieldDifferential.differentialDivisor_apply _ _ _
    rw [hcanonical] at hbound
    omega

private noncomputable def residueInterpolationMap
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    GlobalPlace.riemannRochSubmodule
        (residueInterpolationDivisor (k := k) (F := F) Q) →ₗ[k]
      (ι → k) where
  toFun f i :=
    (Q i).constantsEquiv.symm
      (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
        ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
          residueInterpolation_smul_baseDifferential_mem_simplePole
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
            k F Q hQ f i⟩)
  map_add' f g := by
    funext i
    let hfmem :=
      residueInterpolation_smul_baseDifferential_mem_simplePole
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ f i
    let hgmem :=
      residueInterpolation_smul_baseDifferential_mem_simplePole
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ g i
    let hfgmem :=
      residueInterpolation_smul_baseDifferential_mem_simplePole
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ (f + g) i
    change (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨((f : F) + (g : F)) •
              residueInterpolationBaseDifferential (k := k) (F := F),
            hfgmem⟩) =
      (Q i).constantsEquiv.symm
          (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
            ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
              hfmem⟩) +
        (Q i).constantsEquiv.symm
          (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
            ⟨(g : F) • residueInterpolationBaseDifferential (k := k) (F := F),
              hgmem⟩)
    have hadd :
        (⟨((f : F) + (g : F)) •
            residueInterpolationBaseDifferential (k := k) (F := F), hfgmem⟩ :
          Differential.simplePoleDifferentialLattice (Q i).place) =
          ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
            hfmem⟩ +
          ⟨(g : F) • residueInterpolationBaseDifferential (k := k) (F := F),
            hgmem⟩ := by
      apply Subtype.ext
      exact add_smul _ _ _
    rw [hadd, map_add, map_add]
  map_smul' c f := by
    funext i
    let cO : (Q i).place.valuationRing :=
      GlobalPlace.constantsToValuationRing (Q i).place c
    let eta : Differential.simplePoleDifferentialLattice (Q i).place :=
      ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
        residueInterpolation_smul_baseDifferential_mem_simplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F Q hQ f i⟩
    let hcfmem :=
      residueInterpolation_smul_baseDifferential_mem_simplePole
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ (c • f) i
    have hscaled :
        (⟨((c • f : GlobalPlace.riemannRochSubmodule
              (residueInterpolationDivisor (k := k) (F := F) Q)) : F) •
              residueInterpolationBaseDifferential (k := k) (F := F), hcfmem⟩ :
          Differential.simplePoleDifferentialLattice (Q i).place) =
          cO • eta := by
      apply Subtype.ext
      change (algebraMap k F c * (f : F)) •
          residueInterpolationBaseDifferential (k := k) (F := F) =
        (algebraMap k F c) • ((f : F) •
          residueInterpolationBaseDifferential (k := k) (F := F))
      rw [mul_smul]
    change (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨((c • f : GlobalPlace.riemannRochSubmodule
              (residueInterpolationDivisor (k := k) (F := F) Q)) : F) •
              residueInterpolationBaseDifferential (k := k) (F := F), hcfmem⟩) =
      c * (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place eta)
    rw [hscaled,
      Differential.simplePoleResidue_smul (k := k) (F := F), map_mul]
    change (Q i).constantsEquiv.symm
        ((Q i).place.residue cO) *
          (Q i).constantsEquiv.symm
            (Differential.simplePoleResidue (k := k) (F := F) (Q i).place eta) = _
    congr 1
    change (Q i).constantsEquiv.symm
      (GlobalPlace.constantsToResidue (Q i).place c) = c
    rw [← (Q i).constantsEquiv_apply c,
      (Q i).constantsEquiv.symm_apply_apply]

private theorem simplePoleResidue_eq_zero_iff_mem_localDifferentialLattice
    (P : GlobalPlace k F)
    (eta : Differential.simplePoleDifferentialLattice P) :
    Differential.simplePoleResidue (k := k) (F := F) P eta = 0 ↔
      (eta : Differential k F) ∈ Differential.localDifferentialLattice P := by
  constructor
  · intro hzero
    have hmk :
        (Differential.regularDifferentialSubmoduleOfSimplePole P).mkQ eta = 0 := by
      apply (Differential.simplePoleResidueEquiv
        (k := k) (F := F) P).injective
      simpa only [Differential.simplePoleResidue, LinearMap.comp_apply,
        Submodule.mkQ_apply, map_zero, LinearEquiv.coe_coe] using hzero
    exact (Submodule.Quotient.mk_eq_zero
      (p := Differential.regularDifferentialSubmoduleOfSimplePole P)
      (x := eta)).mp hmk
  · intro hregular
    exact Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) P eta hregular

private noncomputable def residueInterpolationBaseSubmodule
    (Q : ι → RationalPlace k F) :
    Submodule k (GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q)) :=
  (GlobalPlace.riemannRochSubmodule
      (residueInterpolationBaseDivisor (k := k) (F := F))).comap
    (GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q)).subtype

private theorem residueInterpolationMap_ker
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    LinearMap.ker (residueInterpolationMap
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) =
      residueInterpolationBaseSubmodule (k := k) (F := F) Q := by
  ext f
  rw [LinearMap.mem_ker]
  change residueInterpolationMap
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ f = 0 ↔
    (f : F) ∈ GlobalPlace.riemannRochSubmodule
      (residueInterpolationBaseDivisor (k := k) (F := F))
  constructor
  · intro hresidues
    by_cases hf : (f : F) = 0
    · simpa only [hf] using
        (GlobalPlace.riemannRochSubmodule
          (residueInterpolationBaseDivisor (k := k) (F := F))).zero_mem
    · apply (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
        (residueInterpolationBaseDivisor (k := k) (F := F)) hf).mpr
      intro P
      by_cases hselected : ∃ i, (Q i).place = P
      · obtain ⟨i, rfl⟩ := hselected
        have hcoordinate := congrFun hresidues i
        change (Q i).constantsEquiv.symm
            (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
              ⟨(f : F) •
                  residueInterpolationBaseDifferential (k := k) (F := F),
                residueInterpolation_smul_baseDifferential_mem_simplePole
                  (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
                  k F Q hQ f i⟩) = 0 at hcoordinate
        have hresidue :
            Differential.simplePoleResidue (k := k) (F := F) (Q i).place
              ⟨(f : F) •
                  residueInterpolationBaseDifferential (k := k) (F := F),
                residueInterpolation_smul_baseDifferential_mem_simplePole
                  (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
                  k F Q hQ f i⟩ = 0 := by
          apply (Q i).constantsEquiv.symm.injective
          simpa only [map_zero] using hcoordinate
        have hregular :=
          (simplePoleResidue_eq_zero_iff_mem_localDifferentialLattice
            (k := k) (F := F) (Q i).place _).mp hresidue
        have horder :=
          (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
            (k := k) (F := F) (Q i).place (f : F) hf
            (residueInterpolationBaseDifferential (k := k) (F := F))
            (residueInterpolationBaseDifferential_ne_zero
              (k := k) (F := F))).mp hregular
        simp only [residueInterpolationBaseDivisor, Finsupp.add_apply]
        rw [evaluationAvoidancePoleDivisor_apply_rationalPlace
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
        have hcanonical :
            residueInterpolationCanonicalDivisor
                (k := k) (F := F) (Q i).place =
              FunctionFieldDifferential.differentialOrder
                (k := k) (F := F) (Q i).place
                (residueInterpolationBaseDifferential (k := k) (F := F))
                (residueInterpolationBaseDifferential_ne_zero
                  (k := k) (F := F)) := by
          change FunctionFieldDifferential.differentialDivisor
              (k := k) (F := F)
              (residueInterpolationBaseDifferential (k := k) (F := F))
              (residueInterpolationBaseDifferential_ne_zero
                (k := k) (F := F)) (Q i).place = _
          exact FunctionFieldDifferential.differentialDivisor_apply _ _ _
        rw [hcanonical, add_zero]
        exact horder
      · have hdivisor : evaluationDivisor Q P = 0 := by
          simpa only [evaluationDivisor] using
            zeroCoordinateDivisor_apply_eq_zero_of_not_mem
              Q Finset.univ P (by
                intro i _ hQi
                exact hselected ⟨i, hQi⟩)
        have hbound :=
          (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
            (residueInterpolationDivisor (k := k) (F := F) Q) hf).mp
              f.property P
        simp only [residueInterpolationDivisor, Finsupp.add_apply,
          hdivisor, add_zero] at hbound
        exact hbound
  · intro hbase
    apply funext
    intro i
    have hregular :
        (f : F) • residueInterpolationBaseDifferential (k := k) (F := F) ∈
          Differential.localDifferentialLattice (Q i).place := by
      by_cases hf : (f : F) = 0
      · rw [hf, zero_smul]
        exact (Differential.localDifferentialLattice (Q i).place).zero_mem
      · apply (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
          (k := k) (F := F) (Q i).place (f : F) hf
          (residueInterpolationBaseDifferential (k := k) (F := F))
          (residueInterpolationBaseDifferential_ne_zero
            (k := k) (F := F))).mpr
        have hbound :=
          (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
            (residueInterpolationBaseDivisor (k := k) (F := F)) hf).mp
              hbase (Q i).place
        simp only [residueInterpolationBaseDivisor, Finsupp.add_apply] at hbound
        rw [evaluationAvoidancePoleDivisor_apply_rationalPlace
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)] at hbound
        have hcanonical :
            residueInterpolationCanonicalDivisor
                (k := k) (F := F) (Q i).place =
              FunctionFieldDifferential.differentialOrder
                (k := k) (F := F) (Q i).place
                (residueInterpolationBaseDifferential (k := k) (F := F))
                (residueInterpolationBaseDifferential_ne_zero
                  (k := k) (F := F)) := by
          change FunctionFieldDifferential.differentialDivisor
              (k := k) (F := F)
              (residueInterpolationBaseDifferential (k := k) (F := F))
              (residueInterpolationBaseDifferential_ne_zero
                (k := k) (F := F)) (Q i).place = _
          exact FunctionFieldDifferential.differentialDivisor_apply _ _ _
        rw [hcanonical, add_zero] at hbound
        exact hbound
    change (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
            residueInterpolation_smul_baseDifferential_mem_simplePole
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
              k F Q hQ f i⟩) = 0
    rw [Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) (Q i).place _ hregular, map_zero]

private noncomputable def residueInterpolationBaseSubmoduleEquiv
    (Q : ι → RationalPlace k F) :
    residueInterpolationBaseSubmodule (k := k) (F := F) Q ≃ₗ[k]
      GlobalPlace.riemannRochSubmodule
        (residueInterpolationBaseDivisor (k := k) (F := F)) where
  toFun x := ⟨(x : F), x.property⟩
  invFun x :=
    ⟨⟨(x : F), GlobalPlace.riemannRochSubmodule_mono
      (residueInterpolationBaseDivisor_le
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q) x.property⟩,
      x.property⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' c x := by rfl

private theorem residueInterpolationMap_surjective
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    Function.Surjective (residueInterpolationMap
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) := by
  let T := residueInterpolationMap
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  have hkerNat : Module.finrank k T.ker =
      Module.finrank k (GlobalPlace.riemannRochSubmodule
        (residueInterpolationBaseDivisor (k := k) (F := F))) := by
    rw [show T.ker = residueInterpolationBaseSubmodule
      (k := k) (F := F) Q from residueInterpolationMap_ker
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ]
    exact (residueInterpolationBaseSubmoduleEquiv
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q).finrank_eq
  have hbase := GlobalPlace.riemannRoch_eq_of_large_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (residueInterpolationBaseDivisor (k := k) (F := F))
    (residueInterpolationBaseDivisor_large
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
  have htotal := GlobalPlace.riemannRoch_eq_of_large_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (residueInterpolationDivisor (k := k) (F := F) Q)
    (residueInterpolationDivisor_large
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q)
  change (Module.finrank k (GlobalPlace.riemannRochSubmodule
      (residueInterpolationBaseDivisor (k := k) (F := F))) : ℤ) = _ at hbase
  change (Module.finrank k (GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q)) : ℤ) = _ at htotal
  have hrank := T.finrank_range_add_finrank_ker
  have hrankInt := congrArg (fun n : ℕ => (n : ℤ)) hrank
  simp only [Nat.cast_add] at hrankInt
  have hkerInt := congrArg (fun n : ℕ => (n : ℤ)) hkerNat
  have hdegree := residueInterpolationDivisor_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q
  have hrangeInt : (Module.finrank k T.range : ℤ) = Fintype.card ι := by
    omega
  have hrangeNat : Module.finrank k T.range = Fintype.card ι := by
    exact_mod_cast hrangeInt
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa using hrangeNat

/-! ## A differential normalized at the evaluation places -/

variable [Nonempty ι]

private noncomputable def normalizedEvaluationMultiplier
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q) :=
  Classical.choose
    (residueInterpolationMap_surjective
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
      (1 : ι → k))

private theorem normalizedEvaluationMultiplier_residueInterpolationMap
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    residueInterpolationMap
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
        (normalizedEvaluationMultiplier
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) =
      (1 : ι → k) :=
  Classical.choose_spec
    (residueInterpolationMap_surjective
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
      (1 : ι → k))

/-- A noncomputably selected differential whose normalized traced residue is
one at every member of the finite evaluation family. -/
noncomputable def normalizedEvaluationDifferential
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) : Differential k F :=
  (normalizedEvaluationMultiplier
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ : F) •
    residueInterpolationBaseDifferential (k := k) (F := F)

private theorem normalizedEvaluationDifferential_mem_simplePole
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ ∈
      Differential.simplePoleDifferentialLattice (Q i).place := by
  simpa only [normalizedEvaluationDifferential] using
    (residueInterpolation_smul_baseDifferential_mem_simplePole
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
      (normalizedEvaluationMultiplier
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) i)

private theorem normalizedEvaluationDifferential_residueCoordinate_eq_one
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨normalizedEvaluationDifferential
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
            normalizedEvaluationDifferential_mem_simplePole
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩) = 1 := by
  have hmap := congrFun
    (normalizedEvaluationMultiplier_residueInterpolationMap
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) i
  change (Q i).constantsEquiv.symm
      (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
        ⟨normalizedEvaluationDifferential
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
          normalizedEvaluationDifferential_mem_simplePole
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩) =
    (1 : ι → k) i at hmap
  simpa only [Pi.one_apply] using hmap

/-- The selected normalized evaluation differential is nonzero. -/
theorem normalizedEvaluationDifferential_ne_zero
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ ≠ 0 := by
  intro hzero
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  have hcoordinate :=
    normalizedEvaluationDifferential_residueCoordinate_eq_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
  have hsubtype :
      (⟨normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
        normalizedEvaluationDifferential_mem_simplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩ :
          Differential.simplePoleDifferentialLattice (Q i).place) = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hsubtype, map_zero, map_zero] at hcoordinate
  exact zero_ne_one hcoordinate

/-- At every selected rational place, the normalized differential has traced
simple-pole residue exactly one. -/
theorem normalizedEvaluationDifferential_traceResidue_eq_one
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    Differential.simplePoleTraceResidue (k := k) (F := F) (Q i).place
        (normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
        (normalizedEvaluationDifferential_mem_simplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i) = 1 := by
  letI : Algebra k (Q i).place.residueField :=
    GlobalPlace.residueAlgebra (Q i).place
  letI : FiniteDimensional k (Q i).place.residueField :=
    GlobalPlace.residueField_finiteDimensional (Q i).place
  have hcoordinate :=
    normalizedEvaluationDifferential_residueCoordinate_eq_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
  have hresidue :
      Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨normalizedEvaluationDifferential
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
            normalizedEvaluationDifferential_mem_simplePole
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩ =
        (Q i).constantsEquiv 1 := by
    apply (Q i).constantsEquiv.symm.injective
    simpa only [map_one] using hcoordinate
  change Algebra.trace k (Q i).place.residueField
      (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
        ⟨normalizedEvaluationDifferential
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
          normalizedEvaluationDifferential_mem_simplePole
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩) = 1
  rw [hresidue, (Q i).constantsEquiv_apply]
  change Algebra.trace k (Q i).place.residueField
      (algebraMap k (Q i).place.residueField 1) = 1
  rw [Algebra.trace_algebraMap]
  have hfinrank : Module.finrank k (Q i).place.residueField = 1 := by
    apply Module.finrank_of_bijective_algebraMap
    simpa only [GlobalPlace.residueAlgebra, RingHom.algebraMap_toAlgebra] using
      (Q i).constantsToResidue_bijective
  rw [hfinrank]
  simp

/-- The normalized differential has order exactly `-1` at every evaluation
place. -/
theorem normalizedEvaluationDifferential_order_at
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    FunctionFieldDifferential.differentialOrder (k := k) (F := F)
        (Q i).place
        (normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
        (normalizedEvaluationDifferential_ne_zero
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) = -1 := by
  let eta := normalizedEvaluationDifferential
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  have heta : eta ≠ 0 := normalizedEvaluationDifferential_ne_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  change FunctionFieldDifferential.differentialOrder
    (k := k) (F := F) (Q i).place eta heta = -1
  have hsimple : eta ∈ Differential.simplePoleDifferentialLattice (Q i).place :=
    normalizedEvaluationDifferential_mem_simplePole
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
  have hlower : -1 ≤ FunctionFieldDifferential.differentialOrder
      (k := k) (F := F) (Q i).place eta heta :=
    (Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := F) (Q i).place eta heta).mp hsimple
  have hnotRegular :
      eta ∉ Differential.localDifferentialLattice (Q i).place := by
    intro hregular
    have hzero :=
      Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) (Q i).place eta hsimple hregular
    have hone := normalizedEvaluationDifferential_traceResidue_eq_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
    exact one_ne_zero (hone.symm.trans hzero)
  have hnotNonnegative :
      ¬ 0 ≤ FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) (Q i).place eta heta := by
    intro hnonnegative
    apply hnotRegular
    exact
      (Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
        (k := k) (F := F) (Q i).place eta heta).mpr hnonnegative
  omega

/-- The canonical divisor cut out by the normalized evaluation differential. -/
noncomputable def normalizedEvaluationCanonicalDivisor
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    Divisor (GlobalPlace k F) :=
  FunctionFieldDifferential.differentialDivisor (k := k) (F := F)
    (normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
    (normalizedEvaluationDifferential_ne_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)

/-- The normalized evaluation divisor is an actual canonical divisor. -/
theorem normalizedEvaluationCanonicalDivisor_isCanonical
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    FunctionFieldDifferential.IsCanonicalDivisor (k := k) (F := F)
      (normalizedEvaluationCanonicalDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) :=
  FunctionFieldDifferential.differentialDivisor_isCanonical
    (k := k) (F := F)
    (normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
    (normalizedEvaluationDifferential_ne_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)

/-- The normalized canonical divisor has coefficient `-1` at every selected
rational place. -/
theorem normalizedEvaluationCanonicalDivisor_apply_at
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    normalizedEvaluationCanonicalDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
        (Q i).place = -1 := by
  rw [normalizedEvaluationCanonicalDivisor,
    FunctionFieldDifferential.differentialDivisor_apply]
  exact normalizedEvaluationDifferential_order_at
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i

/-! ## The complementary evaluation divisor -/

/-- The source complementary divisor `R + D - G`, formed from the actual
normalized canonical divisor. -/
noncomputable def normalizedEvaluationDualDivisor
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) : Divisor (GlobalPlace k F) :=
  normalizedEvaluationCanonicalDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ +
    evaluationDivisor Q - G

/-- Disjointness of `G` from the evaluation family makes its complementary
divisor disjoint from the same family. -/
theorem normalizedEvaluationDualDivisor_apply_at
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) (hG : ∀ i, G (Q i).place = 0)
    (i : ι) :
    normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G
        (Q i).place = 0 := by
  simp only [normalizedEvaluationDualDivisor, Finsupp.sub_apply,
    Finsupp.add_apply]
  rw [normalizedEvaluationCanonicalDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i,
    evaluationDivisor_apply_at Q hQ i, hG i]
  norm_num

private theorem normalizedEvaluationDualDivisor_degree
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (normalizedEvaluationDualDivisor
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) =
      2 * (GlobalPlace.functionFieldGenus
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 2 +
        Fintype.card ι -
          Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G := by
  rw [normalizedEvaluationDualDivisor, Divisor.degree_sub, Divisor.degree_add,
    CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
      (normalizedEvaluationCanonicalDivisor_isCanonical
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ),
    evaluationDivisor_degree_eq_card]

private theorem normalizedEvaluationDualDivisor_large
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F))
    (hsmall :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
        Fintype.card ι) :
    2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (normalizedEvaluationDualDivisor
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) := by
  rw [normalizedEvaluationDualDivisor_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  omega

private theorem normalizedEvaluationDualDivisor_small
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F))
    (hlarge :
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (normalizedEvaluationDualDivisor
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) <
      Fintype.card ι := by
  rw [normalizedEvaluationDualDivisor_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  omega

/-- In the source range, the genuine dual code has the complementary
Riemann--Roch dimension. -/
theorem agEvaluation_dual_dimension_eq
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (hlarge :
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G)
    (hsmall :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
        Fintype.card ι) :
    (QEC.Coding.Dimension (agEvaluationCode G Q hG).dual : ℤ) =
      Fintype.card ι -
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G - 1 +
          (GlobalPlace.functionFieldGenus
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) := by
  have hdimension := agEvaluation_dimension_eq_of_large_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
    k F G Q hQ hG hlarge hsmall
  have hsum := (agEvaluationCode G Q hG).dimension_add_dual_dimension_eq_length
  change QEC.Coding.Dimension (agEvaluationCode G Q hG) +
      QEC.Coding.Dimension (agEvaluationCode G Q hG).dual = Fintype.card ι at hsum
  have hsumInt := congrArg (fun n : ℕ => (n : ℤ)) hsum
  simp only [Nat.cast_add] at hsumInt
  omega

/-! ## The normalized global residue pairing -/

private theorem evaluationDivisor_apply_eq_zero_or_one
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (P : GlobalPlace k F) : evaluationDivisor Q P = 0 ∨
      evaluationDivisor Q P = 1 := by
  by_cases hselected : ∃ i, (Q i).place = P
  · obtain ⟨i, rfl⟩ := hselected
    exact Or.inr (evaluationDivisor_apply_at Q hQ i)
  · left
    simpa only [evaluationDivisor] using
      zeroCoordinateDivisor_apply_eq_zero_of_not_mem Q Finset.univ P (by
        intro i _ hplace
        exact hselected ⟨i, hplace⟩)

private theorem normalizedEvaluationProduct_isGlobalSimplePole
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F))
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)) :
    Differential.IsGlobalSimplePole (k := k) (F := F)
      (((x : F) * (y : F)) • normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) := by
  intro P
  by_cases hx : (x : F) = 0
  · simp only [hx, zero_mul, zero_smul]
    exact (Differential.simplePoleDifferentialLattice P).zero_mem
  by_cases hy : (y : F) = 0
  · simp only [hy, mul_zero, zero_smul]
    exact (Differential.simplePoleDifferentialLattice P).zero_mem
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  apply
    (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      (k := k) (F := F) P ((x : F) * (y : F)) hxy
      (normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
      (normalizedEvaluationDifferential_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)).mpr
  rw [GlobalPlace.order_mul P hx hy]
  have hxP :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp
      x.property P
  have hyP :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) hy).mp
      y.property P
  simp only [normalizedEvaluationDualDivisor, Finsupp.sub_apply,
    Finsupp.add_apply, normalizedEvaluationCanonicalDivisor,
    FunctionFieldDifferential.differentialDivisor_apply] at hyP
  rcases evaluationDivisor_apply_eq_zero_or_one
      (k := k) (F := F) Q hQ P with hD | hD <;> rw [hD] at hyP <;> omega

private theorem normalizedEvaluationProduct_mem_localDifferentialLattice_of_not_selected
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F))
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G))
    (P : GlobalPlace k F) (hP : ¬ ∃ i, (Q i).place = P) :
    ((x : F) * (y : F)) • normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ ∈
      Differential.localDifferentialLattice P := by
  by_cases hx : (x : F) = 0
  · simp only [hx, zero_mul, zero_smul]
    exact (Differential.localDifferentialLattice P).zero_mem
  by_cases hy : (y : F) = 0
  · simp only [hy, mul_zero, zero_smul]
    exact (Differential.localDifferentialLattice P).zero_mem
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  apply (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
    (k := k) (F := F) P ((x : F) * (y : F)) hxy
    (normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
    (normalizedEvaluationDifferential_ne_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)).mpr
  rw [GlobalPlace.order_mul P hx hy]
  have hxP :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp
      x.property P
  have hyP :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) hy).mp
      y.property P
  have hD : evaluationDivisor Q P = 0 := by
    simpa only [evaluationDivisor] using
      zeroCoordinateDivisor_apply_eq_zero_of_not_mem Q Finset.univ P (by
        intro i _ hplace
        exact hP ⟨i, hplace⟩)
  simp only [normalizedEvaluationDualDivisor, Finsupp.sub_apply,
    Finsupp.add_apply, normalizedEvaluationCanonicalDivisor,
    FunctionFieldDifferential.differentialDivisor_apply, hD, add_zero] at hyP
  omega

private theorem simplePoleTraceResidue_rational_eq_coordinate
    (Q : RationalPlace k F) (omega : Differential k F)
    (homega : omega ∈ Differential.simplePoleDifferentialLattice Q.place) :
    Differential.simplePoleTraceResidue (k := k) (F := F) Q.place omega homega =
      Q.constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) Q.place
          ⟨omega, homega⟩) := by
  letI : Algebra k Q.place.residueField := GlobalPlace.residueAlgebra Q.place
  letI : FiniteDimensional k Q.place.residueField :=
    GlobalPlace.residueField_finiteDimensional Q.place
  obtain ⟨c, hc⟩ := Q.constantsEquiv.surjective
    (Differential.simplePoleResidue (k := k) (F := F) Q.place ⟨omega, homega⟩)
  change Algebra.trace k Q.place.residueField
      (Differential.simplePoleResidue (k := k) (F := F) Q.place
        ⟨omega, homega⟩) = _
  rw [← hc, Q.constantsEquiv_apply]
  have hconstants : Q.place.constantsToResidue c =
      algebraMap k Q.place.residueField c := by
    rfl
  rw [hconstants]
  rw [Algebra.trace_algebraMap]
  have hcoordinate :
      Q.constantsEquiv.symm (algebraMap k Q.place.residueField c) = c := by
    rw [← hconstants, ← Q.constantsEquiv_apply,
      Q.constantsEquiv.symm_apply_apply]
  have hfinrank : Module.finrank k Q.place.residueField = 1 := by
    apply Module.finrank_of_bijective_algebraMap
    simpa only [GlobalPlace.residueAlgebra, RingHom.algebraMap_toAlgebra] using
      Q.constantsToResidue_bijective
  rw [hfinrank, hcoordinate]
  simp

private theorem normalizedEvaluationProduct_traceResidue_at
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) (hG : ∀ i, G (Q i).place = 0)
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G))
    (i : ι) :
    Differential.simplePoleTraceResidue (k := k) (F := F) (Q i).place
        (((x : F) * (y : F)) • normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
        (normalizedEvaluationProduct_isGlobalSimplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G x y
          (Q i).place) =
      agEvaluationLinearMap G Q hG x i *
        agEvaluationLinearMap
          (normalizedEvaluationDualDivisor
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
          Q (normalizedEvaluationDualDivisor_apply_at
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G hG) y i := by
  let eta := normalizedEvaluationDifferential
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  have hetaSimple : eta ∈
      Differential.simplePoleDifferentialLattice (Q i).place :=
    normalizedEvaluationDifferential_mem_simplePole
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
  have hxRegular : GlobalPlace.RegularAt (Q i).place (x : F) := by
    have hxBound := (GlobalPlace.mem_riemannRochSubmodule_iff G (x : F)).mp
      x.property (Q i).place
    rw [hG i] at hxBound
    simpa only [GlobalPlace.RegularAt, WithZero.exp_zero] using hxBound
  have hyRegular : GlobalPlace.RegularAt (Q i).place (y : F) := by
    have hyBound := (GlobalPlace.mem_riemannRochSubmodule_iff
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) (y : F)).mp
      y.property (Q i).place
    rw [normalizedEvaluationDualDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G hG i] at hyBound
    simpa only [GlobalPlace.RegularAt, WithZero.exp_zero] using hyBound
  let xO : (Q i).place.valuationRing :=
    ⟨(x : F), (GlobalPlace.mem_valuationRing_iff (Q i).place _).mpr hxRegular⟩
  let yO : (Q i).place.valuationRing :=
    ⟨(y : F), (GlobalPlace.mem_valuationRing_iff (Q i).place _).mpr hyRegular⟩
  let xyO : (Q i).place.valuationRing := xO * yO
  rw [simplePoleTraceResidue_rational_eq_coordinate
    (k := k) (F := F) (Q i)]
  have hsubtype :
      (⟨((x : F) * (y : F)) • eta,
          normalizedEvaluationProduct_isGlobalSimplePole
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
            k F Q hQ G x y (Q i).place⟩ :
        Differential.simplePoleDifferentialLattice (Q i).place) =
      xyO • (⟨eta, hetaSimple⟩ :
        Differential.simplePoleDifferentialLattice (Q i).place) := by
    rfl
  rw [hsubtype, Differential.simplePoleResidue_smul, map_mul,
    normalizedEvaluationDifferential_residueCoordinate_eq_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i,
    mul_one]
  change (Q i).evaluate xyO = _
  rw [show xyO = xO * yO by rfl, map_mul]
  rfl

private theorem normalizedEvaluationProduct_wordPairing_eq_zero
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) (hG : ∀ i, G (Q i).place = 0)
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)) :
    QEC.Coding.wordPairing
        (agEvaluationLinearMap
          (normalizedEvaluationDualDivisor
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
          Q (normalizedEvaluationDualDivisor_apply_at
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G hG) y)
        (agEvaluationLinearMap G Q hG x) = 0 := by
  classical
  let omega : Differential k F :=
    ((x : F) * (y : F)) • normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  let homega : Differential.IsGlobalSimplePole (k := k) (F := F) omega :=
    normalizedEvaluationProduct_isGlobalSimplePole
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G x y
  let residues : GlobalPlace k F →₀ k :=
    Differential.globalSimplePoleResidue (k := k) (F := F) omega homega
  have hsupport : residues.support ⊆
      Finset.univ.image (fun i => (Q i).place) := by
    intro P hP
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_contra hnotSelected
    have hregular : omega ∈ Differential.localDifferentialLattice P :=
      normalizedEvaluationProduct_mem_localDifferentialLattice_of_not_selected
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ G x y P hnotSelected
    have hzero :=
      Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) P omega (homega P) hregular
    have hcoefficient : residues P = 0 := by
      change Differential.simplePoleTraceResidue
        (k := k) (F := F) P omega (homega P) = 0
      exact hzero
    exact (Finsupp.mem_support_iff.mp hP) hcoefficient
  have hsumSupport :
      residues.sum (fun _ coefficient => coefficient) =
        ∑ P ∈ Finset.univ.image (fun i => (Q i).place), residues P :=
    Finsupp.sum_of_support_subset residues hsupport
      (fun _ coefficient => coefficient) (fun _ _ => rfl)
  have hsumImage :
      (∑ P ∈ Finset.univ.image (fun i => (Q i).place), residues P) =
        ∑ i : ι, residues (Q i).place := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact hQ hij
  have hcoefficient (i : ι) :
      residues (Q i).place =
        agEvaluationLinearMap G Q hG x i *
          agEvaluationLinearMap
            (normalizedEvaluationDualDivisor
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
            Q (normalizedEvaluationDualDivisor_apply_at
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
              k F Q hQ G hG) y i := by
    change Differential.simplePoleTraceResidue (k := k) (F := F) (Q i).place
        (((x : F) * (y : F)) • normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
        (normalizedEvaluationProduct_isGlobalSimplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F Q hQ G x y (Q i).place) = _
    exact normalizedEvaluationProduct_traceResidue_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG x y i
  have hsumZero := Differential.globalSimplePoleResidueSum_eq_zero
    (k := k) (F := F) omega homega
  change residues.sum (fun _ coefficient => coefficient) = 0 at hsumZero
  change (∑ i : ι,
      agEvaluationLinearMap
          (normalizedEvaluationDualDivisor
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
          Q (normalizedEvaluationDualDivisor_apply_at
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
            k F Q hQ G hG) y i *
        agEvaluationLinearMap G Q hG x i) = 0
  calc
    _ = ∑ i : ι, agEvaluationLinearMap G Q hG x i *
        agEvaluationLinearMap
          (normalizedEvaluationDualDivisor
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
          Q (normalizedEvaluationDualDivisor_apply_at
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
            k F Q hQ G hG) y i := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = ∑ i : ι, residues (Q i).place := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hcoefficient i).symm
    _ = residues.sum (fun _ coefficient => coefficient) :=
      hsumImage.symm.trans hsumSupport.symm
    _ = 0 := hsumZero

private theorem normalizedEvaluationDualCode_le_dual
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) (hG : ∀ i, G (Q i).place = 0) :
    (agEvaluationCode
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
      Q (normalizedEvaluationDualDivisor_apply_at
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ G hG)).carrier ≤
      (agEvaluationCode G Q hG).dual.carrier := by
  intro dualWord hdualWord
  apply ((agEvaluationCode G Q hG).mem_dual dualWord).mpr
  intro word hword
  change dualWord ∈ (agEvaluationLinearMap
    (normalizedEvaluationDualDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
    Q (normalizedEvaluationDualDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG)).range at hdualWord
  change word ∈ (agEvaluationLinearMap G Q hG).range at hword
  obtain ⟨y, rfl⟩ := hdualWord
  obtain ⟨x, rfl⟩ := hword
  exact normalizedEvaluationProduct_wordPairing_eq_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
    k F Q hQ G hG x y

/-- The genuine Euclidean dual of `C_L(D,G)` is literally the evaluation code
for `R + D - G`, with `R` the constructed normalized canonical divisor. -/
theorem agEvaluation_dual_carrier_eq
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (agEvaluationCode G Q hG).dual.carrier =
      (agEvaluationCode
        (normalizedEvaluationDualDivisor
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
        Q (normalizedEvaluationDualDivisor_apply_at
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F Q hQ G hG)).carrier := by
  let D := evaluationDivisor Q
  let K := normalizedEvaluationCanonicalDivisor
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  let H := normalizedEvaluationDualDivisor
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G
  let hH : ∀ i, H (Q i).place = 0 :=
    normalizedEvaluationDualDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG
  change (agEvaluationCode G Q hG).dual.carrier =
    (agEvaluationCode H Q hH).carrier
  have hinclusion : (agEvaluationCode H Q hH).carrier ≤
      (agEvaluationCode G Q hG).dual.carrier :=
    normalizedEvaluationDualCode_le_dual
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG
  symm
  apply Submodule.eq_of_le_of_finrank_eq hinclusion
  apply Nat.le_antisymm
  · exact Submodule.finrank_mono hinclusion
  · change QEC.Coding.Dimension (agEvaluationCode G Q hG).dual ≤
      QEC.Coding.Dimension (agEvaluationCode H Q hH)
    have hHLower := agEvaluation_dimension_ge_riemannRoch_difference
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F H Q hQ hH
    have hGLower := agEvaluation_dimension_ge_riemannRoch_difference
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F G Q hQ hG
    change (GlobalPlace.riemannRochDimension H : ℤ) -
        (GlobalPlace.riemannRochDimension (H - D) : ℤ) ≤
      (QEC.Coding.Dimension (agEvaluationCode H Q hH) : ℤ) at hHLower
    change (GlobalPlace.riemannRochDimension G : ℤ) -
        (GlobalPlace.riemannRochDimension (G - D) : ℤ) ≤
      (QEC.Coding.Dimension (agEvaluationCode G Q hG) : ℤ) at hGLower
    have hH_eq : H = K + D - G := by rfl
    have hH_sub_D : H - D = K - G := by
      rw [hH_eq]
      abel
    have hK_sub_G_sub_D : K - (G - D) = H := by
      rw [hH_eq]
      abel
    rw [hH_sub_D] at hHLower
    have hcorrectionG := GlobalPlace.riemannRoch_correction_term
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
      (normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
      (normalizedEvaluationDifferential_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) G
    have hcorrectionGD := GlobalPlace.riemannRoch_correction_term
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
      (normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
      (normalizedEvaluationDifferential_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
      (G - D)
    change (GlobalPlace.riemannRochDimension G : ℤ) -
        (GlobalPlace.riemannRochDimension (K - G) : ℤ) =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G + 1 -
        (GlobalPlace.functionFieldGenus
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ)
      at hcorrectionG
    change (GlobalPlace.riemannRochDimension (G - D) : ℤ) -
        (GlobalPlace.riemannRochDimension (K - (G - D)) : ℤ) =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) (G - D) + 1 -
        (GlobalPlace.functionFieldGenus
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ)
      at hcorrectionGD
    rw [hK_sub_G_sub_D] at hcorrectionGD
    have hdegreeD :
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) D =
          Fintype.card ι := by
      exact evaluationDivisor_degree_eq_card Q
    have hdegreeGD :
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) (G - D) =
          Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G -
            Fintype.card ι := by
      rw [Divisor.degree_sub, hdegreeD]
    rw [hdegreeGD] at hcorrectionGD
    have hsumNat :=
      (agEvaluationCode G Q hG).dimension_add_dual_dimension_eq_length
    change QEC.Coding.Dimension (agEvaluationCode G Q hG) +
        QEC.Coding.Dimension (agEvaluationCode G Q hG).dual =
      Fintype.card ι at hsumNat
    have hsum := congrArg (fun n : ℕ => (n : ℤ)) hsumNat
    simp only [Nat.cast_add] at hsum
    have hdualLe :
        (QEC.Coding.Dimension (agEvaluationCode G Q hG).dual : ℤ) ≤
          (QEC.Coding.Dimension (agEvaluationCode H Q hH) : ℤ) := by
      omega
    exact_mod_cast hdualLe

/-- The actual dual code satisfies the source complementary designed-distance
bound `deg G + 2 - 2g`. -/
theorem agEvaluation_dual_distance_lower_bound
    [DecidableEq k] [DecidableEq ι]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (hlarge :
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G)
    (hsmall :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
        Fintype.card ι) :
    (Int.toNat
      (Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G + 2 -
        2 * (GlobalPlace.functionFieldGenus
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ)) : WithTop ℕ) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
        (agEvaluationCode G Q hG).dual := by
  let H := normalizedEvaluationDualDivisor
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G
  let hH : ∀ i, H (Q i).place = 0 :=
    normalizedEvaluationDualDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG
  have hcarrier := agEvaluation_dual_carrier_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
    k F G Q hQ hG
  have hcode : (agEvaluationCode G Q hG).dual = agEvaluationCode H Q hH := by
    exact congrArg
      (fun carrier : Submodule k (QEC.Coding.Word k ι) =>
        ({ carrier := carrier } : QEC.Coding.LinearCode k ι)) hcarrier
  rw [hcode]
  have hdistance := agEvaluation_distance_lower_bound H Q hQ hH
  have hdegree :
      (Fintype.card ι : ℤ) -
          Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) H =
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G + 2 -
          2 * (GlobalPlace.functionFieldGenus
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) := by
    dsimp only [H]
    rw [normalizedEvaluationDualDivisor_degree
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
    ring
  simpa only [hdegree] using hdistance

end

end QEC.Coding.AlgebraicGeometry
