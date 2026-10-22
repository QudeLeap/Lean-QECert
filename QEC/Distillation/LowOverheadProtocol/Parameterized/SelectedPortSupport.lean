import QEC.Distillation.Triorthogonal.NoisyInjection
import QEC.Semantics.Channels.TraceNorm
import QEC.Semantics.ErrorCorrection.QuditSubsystem
/-!
# One-qubit A-basis support for parameterized HH18 ports

This source-neutral layer records the exact finite A-basis measurement facts
used by the parameterized selected-port handoff.  It depends only on the
ordinary one-qubit resource semantics, not on any HH18 carrier or protocol.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace OneQubitABasisSupport

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit

private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

private theorem pauliZ_positive_projector_eq_rankOne :
    (1 / 2 : Complex) • (1 + pauliZ) =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex 0)
        (EuclideanSpace.basisFun (Fin 2) Complex 0)).toLinearMap := by
  ext psi bit
  fin_cases bit <;>
    simp [LinearMap.smul_apply, LinearMap.add_apply, pauliZ_apply, zPhase,
      InnerProductSpace.rankOne_apply, PiLp.inner_apply]
  all_goals ring

private theorem pauliZ_negative_projector_eq_rankOne :
    (1 / 2 : Complex) • (1 - pauliZ) =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex 1)
        (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap := by
  ext psi bit
  fin_cases bit <;>
    simp [LinearMap.smul_apply, LinearMap.sub_apply, pauliZ_apply, zPhase,
      InnerProductSpace.rankOne_apply, PiLp.inner_apply]
  all_goals ring

private theorem aBasisTransport_conj_positive_projector :
    aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 + pauliZ)) =
      aBasisProjector .positive := by
  unfold aBasisProjector
  rw [show StabilizerOutcome.sign StabilizerOutcome.positive = (1 : Complex) by rfl]
  ext psi
  simp [aBasisObservable, UnitaryTransport.conjOperator, map_add, map_smul]

private theorem aBasisTransport_conj_negative_projector :
    aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 - pauliZ)) =
      aBasisProjector .negative := by
  unfold aBasisProjector
  rw [show StabilizerOutcome.sign StabilizerOutcome.negative = (-1 : Complex) by rfl]
  ext psi
  simp [aBasisObservable, UnitaryTransport.conjOperator, map_sub, map_smul]
  ring

private theorem aBasisProjector_positive_eq_aZeroDensity :
    aBasisProjector .positive = aZeroDensity.toOperator := by
  calc
    aBasisProjector .positive =
        aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 + pauliZ)) :=
      aBasisTransport_conj_positive_projector.symm
    _ = aBasisTransport.conjOperator
        ((InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Fin 2) Complex 0)
          (EuclideanSpace.basisFun (Fin 2) Complex 0)).toLinearMap) := by
      rw [pauliZ_positive_projector_eq_rankOne]
    _ = (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap := by
      rw [QuditSubsystem.conjOperator_rankOne, aBasisTransport_basis_zero]
    _ = aZeroDensity.toOperator := aZeroDensity_rankOne.symm

private theorem aBasisProjector_negative_eq_aOneDensity :
    aBasisProjector .negative = aOneDensity.toOperator := by
  calc
    aBasisProjector .negative =
        aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 - pauliZ)) :=
      aBasisTransport_conj_negative_projector.symm
    _ = aBasisTransport.conjOperator
        ((InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Fin 2) Complex 1)
          (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap) := by
      rw [pauliZ_negative_projector_eq_rankOne]
    _ = (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by
      rw [QuditSubsystem.conjOperator_rankOne, aBasisTransport_basis_one]
    _ = aOneDensity.toOperator := aOneDensity_rankOne.symm

private noncomputable def aBasisProjectorProbability
    (outcome : StabilizerOutcome) (rho : DensityOperator QubitSpace) : ℝ :=
  (LinearMap.trace Complex QubitSpace
    (aBasisProjector outcome * rho.toOperator)).re

private theorem aBasisInstrument_bornWeight_eq_projectorProbability
    (outcome : StabilizerOutcome) (rho : DensityOperator QubitSpace) :
    aBasisInstrument.bornWeight outcome rho =
      aBasisProjectorProbability outcome rho := by
  classical
  unfold FiniteInstrument.bornWeight aBasisProjectorProbability
  rw [FiniteInstrument.branchOperator_apply]
  rw [Fintype.sum_eq_single outcome]
  · simp only [aBasisInstrument, aBasisDephasingKrausFamily, id_eq, ↓reduceIte]
    change Complex.re (LinearMap.trace Complex QubitSpace
      (aBasisProjector outcome *
        (rho.toOperator * LinearMap.adjoint (aBasisProjector outcome)))) = _
    rw [aBasisProjector_adjoint]
    calc
      Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome *
            (rho.toOperator * aBasisProjector outcome))) =
          Complex.re (LinearMap.trace Complex QubitSpace
            ((aBasisProjector outcome * rho.toOperator) *
              aBasisProjector outcome)) := by
            congr 2
      _ = Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome *
            (aBasisProjector outcome * rho.toOperator))) := by
            rw [LinearMap.trace_mul_comm]
      _ = Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome * rho.toOperator)) := by
            rw [← mul_assoc, aBasisProjector_idempotent]
  · intro other hother
    simp [aBasisInstrument, aBasisDephasingKrausFamily, hother]

private theorem negative_aBasisProjector_isStarProjection :
    IsStarProjection (aBasisProjector .negative) := by
  rw [LinearMap.isStarProjection_iff_isSymmetricProjection]
  constructor
  · exact aBasisProjector_idempotent .negative
  · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    exact aBasisProjector_adjoint .negative

private theorem negative_aBasisProjector_aZero_trace_zero :
    (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative * aZeroDensity.toOperator)).re = 0 := by
  change aBasisProjectorProbability .negative aZeroDensity = 0
  rw [← aBasisInstrument_bornWeight_eq_projectorProbability]
  rw [FiniteInstrument.bornWeight, aBasisInstrument_branch_aZero]
  have hne : (StabilizerOutcome.negative : StabilizerOutcome) ≠ .positive := by decide
  rw [if_neg hne]
  norm_num

/-- The literal negative-A Born probability of a physical qubit density is
bounded by its trace norm distance from the ideal `A₀` density. -/
theorem negativeABornWeight_le_traceDistance_to_aZero
    (rho : DensityOperator QubitSpace) :
    aBasisInstrument.bornWeight .negative rho ≤
      traceNorm (rho.toOperator - aZeroDensity.toOperator) := by
  let P : Operator QubitSpace := aBasisProjector .negative
  have hprojector : IsStarProjection P := negative_aBasisProjector_isStarProjection
  have hideal :
      (LinearMap.trace Complex QubitSpace (P * aZeroDensity.toOperator)).re = 0 :=
    negative_aBasisProjector_aZero_trace_zero
  have hraw :
      aBasisInstrument.bornWeight .negative rho =
        (LinearMap.trace Complex QubitSpace (P * rho.toOperator)).re :=
    aBasisInstrument_bornWeight_eq_projectorProbability .negative rho
  have hcenter :
      (LinearMap.trace Complex QubitSpace (P * rho.toOperator)).re =
        (LinearMap.trace Complex QubitSpace
          (P * (rho.toOperator - aZeroDensity.toOperator))).re := by
    rw [mul_sub, map_sub, Complex.sub_re, hideal, sub_zero]
  calc
    aBasisInstrument.bornWeight .negative rho =
        (LinearMap.trace Complex QubitSpace
          (P * (rho.toOperator - aZeroDensity.toOperator))).re := hraw.trans hcenter
    _ ≤ |(LinearMap.trace Complex QubitSpace
          (P * (rho.toOperator - aZeroDensity.toOperator))).re| := le_abs_self _
    _ ≤ ‖LinearMap.trace Complex QubitSpace
          (P * (rho.toOperator - aZeroDensity.toOperator))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ traceNorm (P * (rho.toOperator - aZeroDensity.toOperator)) :=
      norm_trace_le_traceNorm _
    _ ≤ operatorNorm P * traceNorm (rho.toOperator - aZeroDensity.toOperator) :=
      traceNorm_mul_left_le _ _
    _ ≤ 1 * traceNorm (rho.toOperator - aZeroDensity.toOperator) := by
      exact mul_le_mul_of_nonneg_right
        (operatorNorm_projection_le P hprojector) (traceNorm_nonneg _)
    _ = traceNorm (rho.toOperator - aZeroDensity.toOperator) := by ring

private theorem rankOne_sandwich
    (u : QubitSpace) (_hu : inner Complex u u = 1) (A : Operator QubitSpace) :
    (InnerProductSpace.rankOne Complex u u).toLinearMap *
        (A * (InnerProductSpace.rankOne Complex u u).toLinearMap) =
      (inner Complex u (A u)) •
        (InnerProductSpace.rankOne Complex u u).toLinearMap := by
  ext vector
  simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply]
  ring

private theorem trace_rankOne_mul
    (u : QubitSpace) (A : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
      ((InnerProductSpace.rankOne Complex u u).toLinearMap * A) =
        inner Complex u (A u) := by
  rw [LinearMap.trace_mul_comm]
  have hcomp : A * (InnerProductSpace.rankOne Complex u u).toLinearMap =
      (InnerProductSpace.rankOne Complex (A u) u).toLinearMap := by
    ext vector
    simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
      InnerProductSpace.rankOne_apply]
  rw [hcomp]
  exact InnerProductSpace.trace_rankOne (A u) u

private theorem inner_apply_real_of_positive
    (rho : DensityOperator QubitSpace) (u : QubitSpace) :
    ((inner Complex u (rho.toOperator u)).re : Complex) =
      inner Complex u (rho.toOperator u) := by
  have hpositive := (LinearMap.isPositive_iff_complex rho.toOperator).mp rho.positive u
  simpa [rho.positive.isSymmetric u u] using hpositive.1

private theorem aBasisDephasing_mapDensity_toOperator_components
    (rho : DensityOperator QubitSpace) :
    (aBasisDephasing.mapDensity rho).toOperator =
      (aBasisInstrument.bornWeight .positive rho : Complex) • aZeroDensity.toOperator +
        (aBasisInstrument.bornWeight .negative rho : Complex) • aOneDensity.toOperator := by
  have hzeroInner : inner Complex aZeroState aZeroState = 1 := by
    rw [inner_self_eq_norm_sq_to_K, aZeroState_norm]
    norm_num
  have honeInner : inner Complex aOneState aOneState = 1 := by
    rw [inner_self_eq_norm_sq_to_K, aOneState_norm]
    norm_num
  have hplusWeight :
      (aBasisInstrument.bornWeight .positive rho : Complex) =
        inner Complex aZeroState (rho.toOperator aZeroState) := by
    rw [aBasisInstrument_bornWeight_eq_projectorProbability]
    unfold aBasisProjectorProbability
    rw [aBasisProjector_positive_eq_aZeroDensity, aZeroDensity_rankOne,
      trace_rankOne_mul]
    exact inner_apply_real_of_positive rho aZeroState
  have hnegativeWeight :
      (aBasisInstrument.bornWeight .negative rho : Complex) =
        inner Complex aOneState (rho.toOperator aOneState) := by
    rw [aBasisInstrument_bornWeight_eq_projectorProbability]
    unfold aBasisProjectorProbability
    rw [aBasisProjector_negative_eq_aOneDensity, aOneDensity_rankOne,
      trace_rankOne_mul]
    exact inner_apply_real_of_positive rho aOneState
  rw [QuantumChannel.mapDensity_toOperator, aBasisDephasing,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  change (∑ outcome : StabilizerOutcome,
      aBasisProjector outcome *
        (rho.toOperator * LinearMap.adjoint (aBasisProjector outcome))) = _
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {StabilizerOutcome.positive, StabilizerOutcome.negative} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [aBasisProjector_adjoint .positive, aBasisProjector_adjoint .negative,
    aBasisProjector_positive_eq_aZeroDensity, aBasisProjector_negative_eq_aOneDensity,
    aZeroDensity_rankOne, aOneDensity_rankOne,
    rankOne_sandwich aZeroState hzeroInner rho.toOperator,
    rankOne_sandwich aOneState honeInner rho.toOperator,
    ← hplusWeight, ← hnegativeWeight,
    ← aZeroDensity_rankOne, ← aOneDensity_rankOne]

/-- A-basis dephasing is exactly the diagonal A resource at its measured
negative-A Born rate. -/
theorem aBasisDephasing_mapDensity_eq_diagonalAResource_at_measuredRate
    (rho : DensityOperator QubitSpace) (p : ErrorParameter)
    (hrate : p.rate = aBasisInstrument.bornWeight .negative rho) :
    aBasisDephasing.mapDensity rho = diagonalAResource p := by
  have hsum := aBasisInstrument_weight_sum rho
  have hclean : p.cleanWeight = aBasisInstrument.bornWeight .positive rho := by
    unfold ErrorParameter.cleanWeight
    rw [hrate]
    linarith
  apply densityOperator_ext
  rw [aBasisDephasing_mapDensity_toOperator_components,
    diagonalAResource_toOperator, hclean]
  rw [hrate]
  simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
  rfl

end OneQubitABasisSupport
end Distillation
end QEC
