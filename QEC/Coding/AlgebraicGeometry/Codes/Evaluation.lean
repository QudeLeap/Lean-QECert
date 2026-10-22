/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.Core.Definitions
import QEC.Coding.AlgebraicGeometry.RiemannRoch.NegativeDegreeVanishing
import QEC.Coding.AlgebraicGeometry.Places.RationalPlaceDegree

/-!
# Algebraic-geometry evaluation maps

This file gives the source-level evaluation construction for a finite family
of pairwise distinct rational global places.  Its domain is the actual
all-place valuation-bound Riemann--Roch submodule, so every coordinate is
evaluated only after regularity has been proved from the zero coefficient of
the support divisor.

The elementary kernel argument is also recorded here.  Vanishing on a finite
set of coordinates forces membership in the Riemann--Roch submodule for the
divisor obtained by subtracting the corresponding reduced place divisor.
For all coordinates, negative-degree vanishing then gives injectivity.  No
Riemann--Roch dimension formula, canonical duality, or evaluation-code
distance theorem is used in this file.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators Polynomial RatFunc WithZero

variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]

/-- The reduced divisor supported on a selected finite set of evaluation
coordinates.  The declaration intentionally counts coordinates before the
pairwise-distinctness hypothesis is used; that hypothesis is supplied exactly
when a coefficient or degree is identified with a cardinality. -/
noncomputable def zeroCoordinateDivisor (Q : ι → RationalPlace k F)
    (S : Finset ι) : Divisor (GlobalPlace k F) := by
  classical
  exact ∑ i ∈ S, Finsupp.single (Q i).place (1 : ℤ)

/-- The divisor of the complete finite evaluation family. -/
noncomputable def evaluationDivisor (Q : ι → RationalPlace k F) :
    Divisor (GlobalPlace k F) :=
  zeroCoordinateDivisor Q Finset.univ

/-- At a selected coordinate, pairwise distinctness makes the reduced divisor
coefficient exactly one. -/
theorem zeroCoordinateDivisor_apply_at (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (S : Finset ι)
    {i : ι} (hi : i ∈ S) :
    zeroCoordinateDivisor Q S (Q i).place = 1 := by
  classical
  unfold zeroCoordinateDivisor
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hplace : (Q j).place ≠ (Q i).place := by
      intro h
      exact hji (hQ h)
    simp [Finsupp.single_apply, hplace]
  · simp [hi]

/-- Away from the selected coordinates, the selected-coordinate divisor has
zero coefficient. -/
theorem zeroCoordinateDivisor_apply_eq_zero_of_not_mem (Q : ι → RationalPlace k F)
    (S : Finset ι) (P : GlobalPlace k F)
    (hP : ∀ i ∈ S, (Q i).place ≠ P) :
    zeroCoordinateDivisor Q S P = 0 := by
  classical
  unfold zeroCoordinateDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  simp [Finsupp.single_apply, hP i hi]

/-- The full evaluation divisor has coefficient one at every coordinate. -/
theorem evaluationDivisor_apply_at (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    evaluationDivisor Q (Q i).place = 1 := by
  simpa only [evaluationDivisor] using
    zeroCoordinateDivisor_apply_at Q hQ Finset.univ (Finset.mem_univ i)

private theorem divisor_degree_single (degreeOf : GlobalPlace k F → ℕ)
    (P : GlobalPlace k F) (coefficient : ℤ) :
    Divisor.degree degreeOf (Finsupp.single P coefficient) =
      coefficient * (degreeOf P : ℤ) := by
  simp [Divisor.degree, Divisor.degreeHom]

/-- The selected-coordinate divisor has degree the cardinality of its finite
index set: every selected rational global place has the genuine all-place
residue degree one, supplied by `RationalPlace.globalResidueDegree_eq_one`. -/
theorem zeroCoordinateDivisor_degree_eq_card
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (Q : ι → RationalPlace k F) (S : Finset ι) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (zeroCoordinateDivisor Q S) = S.card := by
  classical
  unfold zeroCoordinateDivisor
  change Divisor.degreeHom (GlobalPlace.residueDegree (k := k) (F := F))
      (∑ i ∈ S, Finsupp.single (Q i).place (1 : ℤ)) = S.card
  rw [map_sum]
  calc
    (∑ i ∈ S, Divisor.degreeHom (GlobalPlace.residueDegree (k := k) (F := F))
        (Finsupp.single (Q i).place (1 : ℤ))) =
        ∑ i ∈ S, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      change Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
          (Finsupp.single (Q i).place (1 : ℤ)) = (1 : ℤ)
      rw [divisor_degree_single,
        RationalPlace.globalResidueDegree_eq_one]
      simp
    _ = S.card := by simp

/-- The full evaluation divisor has degree the number of coordinates. -/
theorem evaluationDivisor_degree_eq_card
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (Q : ι → RationalPlace k F) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (evaluationDivisor Q) = Fintype.card ι := by
  simpa only [evaluationDivisor, Finset.card_univ] using
    zeroCoordinateDivisor_degree_eq_card Q Finset.univ

private theorem evaluationRegularity (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G) (i : ι) :
    GlobalPlace.RegularAt (Q i).place (f : F) := by
  have hbound : (Q i).place.valuation (f : F) ≤ WithZero.exp (G (Q i).place) :=
    (GlobalPlace.mem_riemannRochSubmodule_iff G (f : F)).mp f.property (Q i).place
  rw [hG i] at hbound
  rw [WithZero.exp_zero] at hbound
  exact hbound

private theorem rational_evaluateRegular_add (Q : RationalPlace k F)
    (f g : F) (hf : GlobalPlace.RegularAt Q.place f)
    (hg : GlobalPlace.RegularAt Q.place g)
    (hfg : GlobalPlace.RegularAt Q.place (f + g)) :
    Q.evaluateRegular (f + g) hfg =
      Q.evaluateRegular f hf + Q.evaluateRegular g hg := by
  let xf : GlobalPlace.valuationRing Q.place :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let xg : GlobalPlace.valuationRing Q.place :=
    ⟨g, (GlobalPlace.mem_valuationRing_iff Q.place g).mpr hg⟩
  let xfg : GlobalPlace.valuationRing Q.place :=
    ⟨f + g, (GlobalPlace.mem_valuationRing_iff Q.place (f + g)).mpr hfg⟩
  change Q.evaluate xfg = Q.evaluate xf + Q.evaluate xg
  have hsum : xfg = xf + xg := by
    rfl
  rw [hsum]
  exact Q.evaluate.map_add xf xg

private theorem rational_evaluateRegular_smul (Q : RationalPlace k F)
    (a : k) (f : F) (hf : GlobalPlace.RegularAt Q.place f)
    (hsf : GlobalPlace.RegularAt Q.place (a • f)) :
    Q.evaluateRegular (a • f) hsf = a • Q.evaluateRegular f hf := by
  let xf : GlobalPlace.valuationRing Q.place :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let xaf : GlobalPlace.valuationRing Q.place :=
    ⟨a • f, (GlobalPlace.mem_valuationRing_iff Q.place (a • f)).mpr hsf⟩
  let xa : GlobalPlace.valuationRing Q.place :=
    GlobalPlace.constantsToValuationRing Q.place a
  change Q.evaluate xaf = a • Q.evaluate xf
  have haf : xaf = xa * xf := by
    apply Subtype.ext
    change a • f = algebraMap k F a * f
    exact Algebra.smul_def _ _
  calc
    Q.evaluate xaf = Q.evaluate (xa * xf) := congrArg Q.evaluate haf
    _ = Q.evaluate xa * Q.evaluate xf := Q.evaluate.map_mul xa xf
    _ = a * Q.evaluate xf := by
      change Q.evaluate (GlobalPlace.constantsToValuationRing Q.place a) * Q.evaluate xf =
        a * Q.evaluate xf
      rw [Q.evaluate_constants]
    _ = a • Q.evaluate xf := (smul_eq_mul _ _).symm

/-- The linear evaluation map on the actual Riemann--Roch submodule.  The
support-disjointness equality is exactly what proves every coordinate regular;
it is not packaged as a separate evaluation assumption. -/
noncomputable def agEvaluationLinearMap (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0) :
    GlobalPlace.riemannRochSubmodule G →ₗ[k] Word k ι where
  toFun f := fun i => (Q i).evaluateRegular (f : F) (evaluationRegularity G Q hG f i)
  map_add' f g := by
    funext i
    exact rational_evaluateRegular_add (Q i) (f : F) (g : F)
      (evaluationRegularity G Q hG f i)
      (evaluationRegularity G Q hG g i)
      (evaluationRegularity G Q hG (f + g) i)
  map_smul' a f := by
    funext i
    exact rational_evaluateRegular_smul (Q i) a (f : F)
      (evaluationRegularity G Q hG f i)
      (evaluationRegularity G Q hG (a • f) i)

/-- Coordinate formula for the evaluation linear map. -/
@[simp]
theorem agEvaluationLinearMap_apply (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G) (i : ι) :
    agEvaluationLinearMap G Q hG f i =
      (Q i).evaluateRegular (f : F) (evaluationRegularity G Q hG f i) :=
  rfl

/-- The algebraic-geometry evaluation code is the actual range of its linear
evaluation map, rather than a separately stored parameter package. -/
noncomputable def agEvaluationCode [Fintype k]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hG : ∀ i, G (Q i).place = 0) : LinearCode k ι where
  carrier := (agEvaluationLinearMap G Q hG).range

/-- If an evaluated function vanishes on a selected set of coordinates, its
valuation bounds improve by one at precisely those rational places. -/
theorem evaluationZeroOn_mem_riemannRochSubmodule_sub
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) (S : Finset ι)
    (f : GlobalPlace.riemannRochSubmodule G)
    (hzero : ∀ i, i ∈ S → agEvaluationLinearMap G Q hG f i = 0) :
    (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S) := by
  rw [GlobalPlace.mem_riemannRochSubmodule_iff]
  intro P
  classical
  by_cases hP : ∃ i, i ∈ S ∧ (Q i).place = P
  · obtain ⟨i, hi, rfl⟩ := hP
    have hcoordinate :
        (Q i).evaluateRegular (f : F) (evaluationRegularity G Q hG f i) = 0 := by
      simpa only [agEvaluationLinearMap_apply] using hzero i hi
    have hmaximal :
        (⟨(f : F), (GlobalPlace.mem_valuationRing_iff (Q i).place (f : F)).mpr
          (evaluationRegularity G Q hG f i)⟩ : GlobalPlace.valuationRing (Q i).place) ∈
          IsLocalRing.maximalIdeal (GlobalPlace.valuationRing (Q i).place) :=
      (Q i).evaluateRegular_eq_zero_iff (f : F)
        (evaluationRegularity G Q hG f i) |>.mp hcoordinate
    rw [Valuation.mem_maximalIdeal_iff] at hmaximal
    change (Q i).place.valuation (f : F) < 1 at hmaximal
    rw [Finsupp.sub_apply, hG i, zeroCoordinateDivisor_apply_at Q hQ S hi]
    by_cases hf : (f : F) = 0
    · simp [hf]
    · have hvaluation_ne_zero : (Q i).place.valuation (f : F) ≠ 0 :=
        ((Q i).place.valuation.ne_zero_iff).mpr hf
      have hlog_lt : WithZero.log ((Q i).place.valuation (f : F)) < 0 := by
        rw [← WithZero.exp_log hvaluation_ne_zero, ← WithZero.exp_zero] at hmaximal
        exact WithZero.exp_lt_exp.mp hmaximal
      have hlog_le : WithZero.log ((Q i).place.valuation (f : F)) ≤ (-1 : ℤ) := by
        omega
      exact (WithZero.log_le_iff_le_exp hvaluation_ne_zero).mp hlog_le
  · have hdivisor_zero : zeroCoordinateDivisor Q S P = 0 :=
      zeroCoordinateDivisor_apply_eq_zero_of_not_mem Q S P (by
        intro i hi hplace
        exact hP ⟨i, hi, hplace⟩)
    rw [Finsupp.sub_apply, hdivisor_zero, sub_zero]
    exact (GlobalPlace.mem_riemannRochSubmodule_iff G (f : F)).mp f.property P

/-- The full-zero special case used by the evaluation-map kernel argument. -/
theorem evaluationZero_mem_riemannRochSubmodule_sub
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G)
    (hzero : agEvaluationLinearMap G Q hG f = 0) :
    (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) := by
  simpa only [evaluationDivisor] using
    evaluationZeroOn_mem_riemannRochSubmodule_sub G Q hQ hG Finset.univ f (by
      intro i hi
      exact congrFun hzero i)

/-- If the divisor degree is smaller than the number of distinct rational
evaluation coordinates, the evaluation map is injective.  The proof uses only
the zero-coordinate divisor, its degree-one rational places, and the existing
negative-degree vanishing theorem. -/
theorem agEvaluation_injective
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (hdegree : Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
      Fintype.card ι) :
    Function.Injective (agEvaluationLinearMap G Q hG) := by
  intro f g hfg
  apply Subtype.ext
  have hzero : agEvaluationLinearMap G Q hG (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hmem : ((f - g : GlobalPlace.riemannRochSubmodule G) : F) ∈
      GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) :=
    evaluationZero_mem_riemannRochSubmodule_sub G Q hQ hG (f - g) hzero
  have hnegative :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (G - evaluationDivisor Q) < 0 := by
    rw [Divisor.degree_sub, evaluationDivisor_degree_eq_card]
    omega
  have hbot := GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
    k F (G - evaluationDivisor Q) hnegative
  have hsub : ((f - g : GlobalPlace.riemannRochSubmodule G) : F) = 0 := by
    have hmem_bot : ((f - g : GlobalPlace.riemannRochSubmodule G) : F) ∈
        (⊥ : Submodule k F) := by
      rw [← hbot]
      exact hmem
    exact (Submodule.mem_bot k).mp hmem_bot
  exact sub_eq_zero.mp hsub

end QEC.Coding.AlgebraicGeometry
