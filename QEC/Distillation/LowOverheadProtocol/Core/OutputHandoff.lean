import QEC.Distillation.LowOverheadProtocol.Core.DecodedErrorBridge

/-!
# HH18 physical output handoff

This facet identifies the one-site decoded HH18 logical carrier with the
ordinary qubit, extracts the literal negative-A Born weight of its accepted
output, and dephases that output into the exact diagonal A-basis resource.
It deliberately stops before the phase-resource, small-domain, and recurrence
layers.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic

attribute [local instance 100] Fintype.ofFinite

local instance instOutputHandoffClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev OutputLogicalSite := HH18PuncturedReedMuller.LogicalSite 4 0

private def hh18OutputLogicalSiteZero : OutputLogicalSite :=
  ⟨0, by simp [Coding.ReedMuller.pointWeight]⟩

private theorem hh18OutputLogicalSite_eq_zero (site : OutputLogicalSite) :
    site = hh18OutputLogicalSiteZero := by
  apply Subtype.ext
  have hsite := site.2
  change HammingWeight site.1 ≤ 0 at hsite
  have hweight : HammingWeight site.1 = 0 := Nat.eq_zero_of_le_zero hsite
  simpa [hh18OutputLogicalSiteZero] using (HammingWeight_eq_zero_iff _).mp hweight

private def hh18OutputLogicalSiteEquivUnit : OutputLogicalSite ≃ Unit where
  toFun _ := ()
  invFun _ := hh18OutputLogicalSiteZero
  left_inv := fun site => (hh18OutputLogicalSite_eq_zero site).symm
  right_inv := by
    intro unit
    cases unit
    rfl

private theorem hh18OutputLogicalSite_card : Fintype.card OutputLogicalSite = 1 := by
  calc
    Fintype.card OutputLogicalSite = Fintype.card Unit :=
      Fintype.card_congr hh18OutputLogicalSiteEquivUnit
    _ = 1 := by simp

private def hh18OutputLogicalBitEquiv : Bitstring OutputLogicalSite ≃ Fin 2 where
  toFun bits := bits hh18OutputLogicalSiteZero
  invFun bit := fun _ => bit
  left_inv := by
    intro bits
    funext site
    rw [hh18OutputLogicalSite_eq_zero site]
  right_inv := by
    intro bit
    rfl

private theorem hh18OutputLogicalUniformScalar :
    Triorthogonal.BinaryRowFamily.logicalUniformScalar OutputLogicalSite =
      (Real.sqrt 2 : Complex)⁻¹ := by
  rw [Triorthogonal.BinaryRowFamily.logicalUniformScalar, Nat.card_eq_fintype_card]
  have hbits : Fintype.card (Bitstring OutputLogicalSite) = 2 := by
    simpa using Fintype.card_congr hh18OutputLogicalBitEquiv
  rw [hbits]
  norm_num

private theorem hh18OutputHammingWeight_constant_zero :
    HammingWeight (bitstringWordEquiv OutputLogicalSite (fun _ => (0 : Fin 2))) = 0 := by
  apply (HammingWeight_eq_zero_iff _).2
  funext site
  rfl

private theorem hh18OutputHammingWeight_constant_one :
    HammingWeight (bitstringWordEquiv OutputLogicalSite (fun _ => (1 : Fin 2))) = 1 := by
  rw [HammingWeight_eq_card_hammingSupport]
  have hsupp : hammingSupport
      (bitstringWordEquiv OutputLogicalSite (fun _ => (1 : Fin 2))) =
        Finset.univ := by
    ext site
    simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [bitstringWordEquiv_apply]
    exact iff_true_intro one_ne_zero
  rw [hsupp, Finset.card_univ]
  exact hh18OutputLogicalSite_card

/-- Basis-preserving identification of the unique decoded HH18 logical site
with the ordinary one-qubit Hilbert space. -/
noncomputable def hh18LogicalOutputTransport :
    UnitaryTransport LogicalRegister QubitSpace := by
  let sourceBasis := EuclideanSpace.basisFun (Bitstring OutputLogicalSite) Complex
  let targetBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let U := sourceBasis.equiv targetBasis hh18OutputLogicalBitEquiv
  exact { toLinearEquiv := U.toLinearEquiv, map_inner := U.inner_map_map }

@[simp] private theorem hh18LogicalOutputTransport_apply
    (psi : LogicalRegister) (bit : Fin 2) :
    hh18LogicalOutputTransport psi bit = psi (fun _ => bit) := by
  rfl

/-- The registered HH18 ideal logical output is literally the source `A₀`
state under the basis-preserving one-qubit identification. -/
theorem hh18LogicalOutputTransport_idealOutputState :
    hh18LogicalOutputTransport idealLogicalTOutputState = aZeroState := by
  have hinverse :
      HH18PuncturedReedMuller.logicalTInv 0 4 idealLogicalTOutputState =
        HH18NoisyInput.hh18LogicalPlusInput := by
    change (HH18PuncturedReedMuller.logicalTInv 0 4).toLinearEquiv
      ((HH18PuncturedReedMuller.logicalTInv 0 4).toLinearEquiv.symm
        HH18NoisyInput.hh18LogicalPlusInput) = _
    exact (HH18PuncturedReedMuller.logicalTInv 0 4).toLinearEquiv.apply_symm_apply _
  ext bit
  rw [hh18LogicalOutputTransport_apply]
  fin_cases bit
  · have hcoordinate := congrArg
      (fun state : LogicalRegister =>
        state (fun _ : OutputLogicalSite => (0 : Fin 2))) hinverse
    rw [HH18PuncturedReedMuller.logicalTInv_eq_allSitePhase_neg_pi_div_four] at hcoordinate
    change (Triorthogonal.allSitePhase (Index := OutputLogicalSite) (-Real.pi / 4)
      idealLogicalTOutputState) (fun _ : OutputLogicalSite => (0 : Fin 2)) =
        HH18NoisyInput.hh18LogicalPlusInput
          (fun _ : OutputLogicalSite => (0 : Fin 2)) at hcoordinate
    rw [Triorthogonal.allSitePhase_apply,
      hh18OutputHammingWeight_constant_zero] at hcoordinate
    simpa [HH18NoisyInput.hh18LogicalPlusInput,
      Triorthogonal.BinaryRowFamily.logicalPlusState,
      hh18OutputLogicalUniformScalar, aZeroState,
      OneQubitMagic.phaseState_apply_zero] using hcoordinate
  · have hcoordinate := congrArg
      (fun state : LogicalRegister =>
        state (fun _ : OutputLogicalSite => (1 : Fin 2))) hinverse
    rw [HH18PuncturedReedMuller.logicalTInv_eq_allSitePhase_neg_pi_div_four] at hcoordinate
    change (Triorthogonal.allSitePhase (Index := OutputLogicalSite) (-Real.pi / 4)
      idealLogicalTOutputState) (fun _ : OutputLogicalSite => (1 : Fin 2)) =
        HH18NoisyInput.hh18LogicalPlusInput
          (fun _ : OutputLogicalSite => (1 : Fin 2)) at hcoordinate
    rw [Triorthogonal.allSitePhase_apply,
      hh18OutputHammingWeight_constant_one] at hcoordinate
    have hcoord :
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
            idealLogicalTOutputState
              (fun _ : OutputLogicalSite => (1 : Fin 2)) =
          (Real.sqrt 2 : Complex)⁻¹ := by
      convert hcoordinate using 1 <;> simp [HH18NoisyInput.hh18LogicalPlusInput,
        Triorthogonal.BinaryRowFamily.logicalPlusState,
        hh18OutputLogicalUniformScalar] <;> ring
    have hphase :
        OneQubitMagic.phaseAmplitude (Real.pi / 4) *
            OneQubitMagic.phaseAmplitude (-Real.pi / 4) = 1 := by
      rw [← OneQubitMagic.phaseAmplitude_add]
      convert OneQubitMagic.phaseAmplitude_zero using 1 <;> ring
    calc
      idealLogicalTOutputState (fun _ : OutputLogicalSite => (1 : Fin 2)) =
          (OneQubitMagic.phaseAmplitude (Real.pi / 4) *
            OneQubitMagic.phaseAmplitude (-Real.pi / 4)) *
              idealLogicalTOutputState (fun _ : OutputLogicalSite => (1 : Fin 2)) := by
            rw [hphase]
            ring
      _ = OneQubitMagic.phaseAmplitude (Real.pi / 4) *
            (OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
              idealLogicalTOutputState (fun _ : OutputLogicalSite => (1 : Fin 2))) := by
            ring
      _ = aZeroState 1 := by
            rw [hcoord]
            simp [aZeroState, OneQubitMagic.phaseState_apply_one] <;> ring

/-- The decoded HH18 ideal density becomes the literal source `A₀` density. -/
theorem hh18LogicalOutputTransport_idealOutput :
    hh18LogicalOutputTransport.conjDensity idealLogicalTOutput = aZeroDensity := by
  apply DensityOperator.ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator, idealLogicalTOutput,
    DensityOperator.pureDensity_toOperator, QuditSubsystem.conjOperator_rankOne,
    hh18LogicalOutputTransport_idealOutputState, aZeroDensity,
    OneQubitMagic.phaseStateDensity_toOperator]
  rfl

/-- The accepted decoded physical HH18 output transported onto the ordinary
one-qubit Hilbert space. -/
noncomputable def hh18TransportedAcceptedOutput
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : DensityOperator QubitSpace :=
  hh18LogicalOutputTransport.conjDensity
    (resourceDecodedRun (noisyResources epsilon)).acceptedOutput

/-- Literal negative-A Born probability of the transported accepted output. -/
noncomputable def hh18NextInputRawError
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  aBasisInstrument.bornWeight .negative (hh18TransportedAcceptedOutput epsilon)

theorem hh18NextInputRawError_nonneg
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 ≤ hh18NextInputRawError epsilon := by
  unfold hh18NextInputRawError
  exact aBasisInstrument_weight_nonneg .negative _

theorem hh18NextInputRawError_le_one
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputRawError epsilon ≤ 1 := by
  unfold hh18NextInputRawError
  have hsum := aBasisInstrument_weight_sum (hh18TransportedAcceptedOutput epsilon)
  have hpositive := aBasisInstrument_weight_nonneg .positive
    (hh18TransportedAcceptedOutput epsilon)
  linarith

/-- The exact closed unit-interval parameter obtained from the physical
accepted HH18 output's negative-A Born probability. -/
noncomputable def hh18NextInputRawParameter
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ErrorParameter where
  rate := hh18NextInputRawError epsilon
  rate_nonneg := hh18NextInputRawError_nonneg epsilon
  rate_le_one := hh18NextInputRawError_le_one epsilon

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
      InnerProductSpace.rankOne_apply, PiLp.inner_apply] <;>
    ring

private theorem pauliZ_negative_projector_eq_rankOne :
    (1 / 2 : Complex) • (1 - pauliZ) =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex 1)
        (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap := by
  ext psi bit
  fin_cases bit <;>
    simp [LinearMap.smul_apply, LinearMap.sub_apply, pauliZ_apply, zPhase,
      InnerProductSpace.rankOne_apply, PiLp.inner_apply] <;>
    ring

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
  · simp only [aBasisInstrument, aBasisDephasingKrausFamily, id_eq,
      ↓reduceIte]
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

private theorem aBasisProjectorProbability_transport
    (rho : DensityOperator LogicalRegister) :
    aBasisProjectorProbability .negative
        (hh18LogicalOutputTransport.conjDensity rho) =
      (LinearMap.trace Complex LogicalRegister
        (hh18LogicalOutputTransport.symm.conjOperator
          (aBasisProjector .negative) * rho.toOperator)).re := by
  unfold aBasisProjectorProbability
  rw [UnitaryTransport.conjDensity_toOperator]
  have hproduct :
      aBasisProjector .negative *
          hh18LogicalOutputTransport.conjOperator rho.toOperator =
        hh18LogicalOutputTransport.conjOperator
          (hh18LogicalOutputTransport.symm.conjOperator
            (aBasisProjector .negative) * rho.toOperator) := by
    rw [UnitaryTransport.conjOperator_mul,
      hh18LogicalOutputTransport.conjOperator_symm_conjOperator]
  rw [hproduct, hh18LogicalOutputTransport.trace_conjOperator]

private theorem negative_aBasisProjector_pullback_isStarProjection :
    IsStarProjection
      (hh18LogicalOutputTransport.symm.conjOperator
        (aBasisProjector .negative)) := by
  rw [LinearMap.isStarProjection_iff_isSymmetricProjection]
  constructor
  · change
      hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative) *
          hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative) =
        hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative)
    rw [← UnitaryTransport.conjOperator_mul, aBasisProjector_idempotent]
  · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    change
      LinearMap.adjoint
          (hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative)) =
        hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative)
    rw [UnitaryTransport.conjOperator_adjoint, aBasisProjector_adjoint]

private theorem transported_ideal_negative_aBasis_weight_zero :
    aBasisInstrument.bornWeight .negative
      (hh18LogicalOutputTransport.conjDensity idealLogicalTOutput) = 0 := by
  rw [hh18LogicalOutputTransport_idealOutput]
  rw [FiniteInstrument.bornWeight, aBasisInstrument_branch_aZero]
  have hne : (StabilizerOutcome.negative : StabilizerOutcome) ≠ .positive := by decide
  rw [if_neg hne]
  norm_num

private theorem pulled_negative_projector_ideal_trace_zero :
    (LinearMap.trace Complex LogicalRegister
      (hh18LogicalOutputTransport.symm.conjOperator
        (aBasisProjector .negative) * idealLogicalTOutput.toOperator)).re = 0 := by
  calc
    (LinearMap.trace Complex LogicalRegister
      (hh18LogicalOutputTransport.symm.conjOperator
        (aBasisProjector .negative) * idealLogicalTOutput.toOperator)).re =
        aBasisProjectorProbability .negative
          (hh18LogicalOutputTransport.conjDensity idealLogicalTOutput) := by
          symm
          exact aBasisProjectorProbability_transport idealLogicalTOutput
    _ = aBasisInstrument.bornWeight .negative
          (hh18LogicalOutputTransport.conjDensity idealLogicalTOutput) := by
          symm
          exact aBasisInstrument_bornWeight_eq_projectorProbability .negative _
    _ = 0 := transported_ideal_negative_aBasis_weight_zero

/-- The literal physical negative-A Born error is bounded by the actual
decoded accepted-output trace error on the logical carrier. -/
theorem hh18NextInputRawError_le_outputTrace
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputRawError epsilon ≤
      hh18OutputTraceError
        (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
        idealLogicalTOutput := by
  let P : Operator LogicalRegister :=
    hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative)
  let rho : DensityOperator LogicalRegister :=
    (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
  have hprojector : IsStarProjection P :=
    negative_aBasisProjector_pullback_isStarProjection
  have hideal :
      (LinearMap.trace Complex LogicalRegister (P * idealLogicalTOutput.toOperator)).re =
        0 :=
    pulled_negative_projector_ideal_trace_zero
  have hraw :
      hh18NextInputRawError epsilon =
        (LinearMap.trace Complex LogicalRegister (P * rho.toOperator)).re := by
    unfold hh18NextInputRawError hh18TransportedAcceptedOutput
    rw [aBasisInstrument_bornWeight_eq_projectorProbability]
    exact aBasisProjectorProbability_transport rho
  have hcenter :
      (LinearMap.trace Complex LogicalRegister (P * rho.toOperator)).re =
        (LinearMap.trace Complex LogicalRegister
          (P * (rho.toOperator - idealLogicalTOutput.toOperator))).re := by
    rw [mul_sub, map_sub, Complex.sub_re, hideal, sub_zero]
  calc
    hh18NextInputRawError epsilon =
        (LinearMap.trace Complex LogicalRegister
          (P * (rho.toOperator - idealLogicalTOutput.toOperator))).re := hraw.trans hcenter
    _ ≤ |(LinearMap.trace Complex LogicalRegister
          (P * (rho.toOperator - idealLogicalTOutput.toOperator))).re| := le_abs_self _
    _ ≤ ‖LinearMap.trace Complex LogicalRegister
          (P * (rho.toOperator - idealLogicalTOutput.toOperator))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ traceNorm (P * (rho.toOperator - idealLogicalTOutput.toOperator)) :=
      norm_trace_le_traceNorm _
    _ ≤ operatorNorm P *
          traceNorm (rho.toOperator - idealLogicalTOutput.toOperator) :=
      traceNorm_mul_left_le _ _
    _ ≤ 1 * traceNorm (rho.toOperator - idealLogicalTOutput.toOperator) := by
      exact mul_le_mul_of_nonneg_right
        (operatorNorm_projection_le P hprojector) (traceNorm_nonneg _)
    _ = hh18OutputTraceError rho idealLogicalTOutput := by
      simp [hh18OutputTraceError]

/-- The raw physical Born error inherits the cubic bound from the actual
decoded trace bridge and the registered accepted-residual endpoint bound. -/
theorem hh18NextInputRawError_le_cubic
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputRawError epsilon ≤
      (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by
  calc
    hh18NextInputRawError epsilon ≤
        hh18OutputTraceError
          (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
          idealLogicalTOutput := hh18NextInputRawError_le_outputTrace epsilon
    _ ≤ 2 * acceptedResidualError epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual epsilon
    _ ≤ 2 * (residualCubicCoefficient * epsilon.1 ^ 3) := by
      exact mul_le_mul_of_nonneg_left (acceptedResidualError_le_cubic epsilon) (by norm_num)
    _ = (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by ring

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

private theorem aBasisDephasing_mapDensity_eq_measuredRate
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

/-- The literal A-basis dephasing of the transported accepted HH18 output is
exactly the diagonal resource with its measured negative-A Born rate. -/
noncomputable def hh18NextInputDephasedOutput
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : DensityOperator QubitSpace :=
  aBasisDephasing.mapDensity (hh18TransportedAcceptedOutput epsilon)

theorem hh18NextInputDephasedOutput_eq_diagonalAResource
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputDephasedOutput epsilon =
      diagonalAResource (hh18NextInputRawParameter epsilon) := by
  unfold hh18NextInputDephasedOutput
  apply aBasisDephasing_mapDensity_eq_measuredRate
  rfl

end HH18Protocol
end Distillation
end QEC
