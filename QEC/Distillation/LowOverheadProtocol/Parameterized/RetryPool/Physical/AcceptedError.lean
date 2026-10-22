import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.OutputCoordinate
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Paths.GlobalBridge
import QEC.Semantics.Instruments.Branches.FilteredBranchMeasurement
/-!
# Accepted-output error of the physical HH18 retry protocol

This layer measures one literal terminal qubit on the unnormalized global
success branch.  Global success is a subevent of success along the nominated
routed path, so positivity bounds that mass by the already-evaluated path
branch.  Only after this comparison do we divide by the actual global success
mass to obtain an error bound for the genuine `DistillationRun` output.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- The unnormalized negative-A mass of one terminal coordinate inside the
actual global successful-routing event. -/
noncomputable def decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) : Real :=
  Complex.re (LinearMap.trace Complex QubitSpace
    (aBasisInstrument.branchOperator .negative
      ((decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
        m w z q hz coordinate)
        ((decodedRetryPoolPhysicalProtocolBinaryInstrument
          h hdegree z q hz).branchOperator .accepted rho.toOperator))))

/-- The named accepted-coordinate mass unfolds to the physical instrument's
literal global-event filtered branch. -/
theorem decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz rho coordinate =
      Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          ((decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
            m w z q hz coordinate)
            (filteredBranchOperatorSum
              (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
              (fun outcome =>
                decodedRetryPoolPhysicalProtocolSuccessfulRouting
                  m w z q hz outcome = true)
              rho.toOperator)))) := by
  unfold decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
    decodedRetryPoolPhysicalProtocolBinaryInstrument
  rw [binaryCoarsen_branchOperator_accepted]
  rw [filteredBranchOperatorSum_eq_sum_filter]

/-- On one terminal routed path, the filtered branch operator is the existing
whole-history path-success marginal. -/
private theorem decodedRetryPoolPhysicalProtocolPathFilteredCoordinate_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    (decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
      m w z q hz coordinate)
        (filteredBranchOperatorSum
          (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
          (fun outcome =>
            decodedRetryPoolProtocolPathSuccessfulRoutingAux
              m w z q (z - 1) (by omega) coordinate.1 outcome = true)
          rho.toOperator) =
      (decodedRetryPoolAcceptedProductCoordinateChannel m w
        (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz))
        coordinate.2.1 coordinate.2.2)
        (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
          h hdegree z q hz (z - 1) (by omega) coordinate.1 rho) := by
  rfl

/-- Global success is contained in success along the nominated actual path,
so its measured terminal error mass is no larger. -/
theorem decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_path
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz rho coordinate <=
      Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          ((decodedRetryPoolAcceptedProductCoordinateChannel m w
            (decodedRetryPoolBackwardSchedule m w z q
              (decodedRetryPoolProtocolTerminalStage z hz))
            coordinate.2.1 coordinate.2.2)
            (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
              h hdegree z q hz (z - 1) (by omega) coordinate.1 rho)))) := by
  rw [decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_eq]
  rw [← decodedRetryPoolPhysicalProtocolPathFilteredCoordinate_eq
    h hdegree z q hz rho coordinate]
  apply filteredBranchMeasuredTrace_mono
  intro outcome hglobal
  exact decodedRetryPoolProtocolSuccessfulRoutingAux_implies_path
    m w z q (z - 1) (by omega) outcome hglobal coordinate.1

/-- The measured error on a successful terminal path is its actual path Born
mass times the genuine selected-port raw error at the reached physical rate. -/
theorem decodedRetryPoolPhysicalProtocolPathCoordinateErrorMass_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          ((decodedRetryPoolAcceptedProductCoordinateChannel m w
            (decodedRetryPoolBackwardSchedule m w z q
              (decodedRetryPoolProtocolTerminalStage z hz))
            coordinate.2.1 coordinate.2.2)
            (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
              h hdegree z q hz (z - 1) (by omega) coordinate.1
              (decodedRetryPoolPhysicalProtocolNoisyRootInput
                m w z q hz epsilon rhoUnit))))) =
      decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit (z - 1) (by omega)
            coordinate.1 *
        selectedLogicalPortRawError h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall (z - 1)
            coordinate.1) coordinate.2.2 := by
  rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_mass_smul_acceptedProduct
    h hdegree epsilon hsmall z q hz rhoUnit (z - 1) (by omega) coordinate.1]
  rw [map_smul, branchOperator_smul, map_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  change _ * aBasisInstrument.bornWeight .negative
      ((decodedRetryPoolAcceptedProductCoordinateChannel m w
        (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz))
        coordinate.2.1 coordinate.2.2).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall (z - 1)
            coordinate.1) rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            (decodedRetryPoolProtocolTerminalStage z hz)))) = _
  rw [decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel_mapDensity_acceptedProduct]
  rfl

/-- Weighting the genuine run's normalized coordinate error by its actual
success probability recovers the unnormalized global accepted-event mass. -/
theorem decodedRetryPoolPhysicalProtocolRun_success_mul_coordinateError_eq_mass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    (decodedRetryPoolPhysicalProtocolRun
        h hdegree epsilon z q hz rhoUnit).successProbability *
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w z q hz coordinate
        (decodedRetryPoolPhysicalProtocolRun
          h hdegree epsilon z q hz rhoUnit).acceptedOutput =
      decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) coordinate := by
  rw [decodedRetryPoolPhysicalProtocolRun_successProbability,
    decodedRetryPoolPhysicalProtocolRun_acceptedOutput]
  unfold decodedRetryPoolPhysicalProtocolCoordinateRawError
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
    decodedRetryPoolPhysicalProtocolSuccessMass
    decodedRetryPoolPhysicalProtocolBinaryInstrument
  rw [← binaryCoarsen_bornWeight_smul_completion_toOperator
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
    (decodedRetryPoolPhysicalProtocolNoisyRootInput
      m w z q hz epsilon rhoUnit)
    (decodedRetryPoolPhysicalProtocolFallback m w z q hz) .accepted]
  rw [map_smul, branchOperator_smul, map_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  let coordinateDensity :=
    (decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
      m w z q hz coordinate).mapDensity
      (binaryCoarsenCompletion
        (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
        (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit)
        (decodedRetryPoolPhysicalProtocolFallback m w z q hz) .accepted)
  have htrace := aBasisInstrument.trace_branchOperator_eq_bornWeight
    .negative coordinateDensity
  have hre :
      Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          coordinateDensity.toOperator)) =
        aBasisInstrument.bornWeight .negative coordinateDensity := by
    rw [htrace]
    norm_num
  change _ * aBasisInstrument.bornWeight .negative coordinateDensity =
    _ * Complex.re (LinearMap.trace Complex QubitSpace
      (aBasisInstrument.branchOperator .negative coordinateDensity.toOperator))
  rw [hre]

/-- Before normalization, the actual accepted-event error at every terminal
coordinate is bounded by the depth-`z` physical recurrence envelope. -/
theorem decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_envelope
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) coordinate <=
      routedDepthErrorEnvelope w r m epsilon z := by
  have hinclusion :=
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_path
      h hdegree z q hz
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) coordinate
  rw [decodedRetryPoolPhysicalProtocolPathCoordinateErrorMass_eq
    h hdegree epsilon hsmall z q hz rhoUnit coordinate] at hinclusion
  have hpathMassLe :
      decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit (z - 1) (by omega)
          coordinate.1 <= 1 :=
    decodedRetryPoolProtocolPathEnoughMassAux_le_one
      h hdegree epsilon hsmall z q rhoUnit (z - 1) (by omega) coordinate.1
  have hrawNonneg :
      0 <= selectedLogicalPortRawError h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall (z - 1)
          coordinate.1) coordinate.2.2 :=
    selectedLogicalPortRawError_nonneg h hdegree _ coordinate.2.2
  have hpathProductLeRaw :
      decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit (z - 1) (by omega)
            coordinate.1 *
        selectedLogicalPortRawError h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall (z - 1)
            coordinate.1) coordinate.2.2 <=
      selectedLogicalPortRawError h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall (z - 1)
          coordinate.1) coordinate.2.2 := by
    calc
      _ <= 1 * selectedLogicalPortRawError h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall (z - 1)
            coordinate.1) coordinate.2.2 :=
        mul_le_mul_of_nonneg_right hpathMassLe hrawNonneg
      _ = _ := one_mul _
  have hrawLe :
      selectedLogicalPortRawError h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall (z - 1)
            coordinate.1) coordinate.2.2 <=
        routedDepthErrorEnvelope w r m epsilon z := by
    have hrate := routedDepthPathRate_le_errorEnvelope
      h hdegree epsilon hsmall ((z - 1) + 1)
        (routedDepthOutputPathAppend m w (z - 1) coordinate.1 coordinate.2.2)
    rw [routedDepthPathRate_append_eq_rawError] at hrate
    have hzSucc : z - 1 + 1 = z := by omega
    simpa only [hzSucc] using hrate
  exact hinclusion.trans (hpathProductLeRaw.trans hrawLe)

/-- Every actual terminal coordinate of the normalized physical run has
negative-A error at most `4/3` times the depth-`z` distance-power envelope.
The factor is solely the reciprocal of the proved global success lower bound. -/
theorem decodedRetryPoolPhysicalProtocolRun_coordinateError_le_four_thirds_envelope
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolCoordinateRawError m w z q hz coordinate
        (decodedRetryPoolPhysicalProtocolRun
          h hdegree epsilon z q hz rhoUnit).acceptedOutput <=
      (4 / 3 : Real) * routedDepthErrorEnvelope w r m epsilon z := by
  let run := decodedRetryPoolPhysicalProtocolRun
    h hdegree epsilon z q hz rhoUnit
  let error := decodedRetryPoolPhysicalProtocolCoordinateRawError
    m w z q hz coordinate run.acceptedOutput
  have hsuccess : (3 / 4 : Real) <= run.successProbability :=
    decodedRetryPoolPhysicalProtocolRun_success_three_quarters_le
      h hdegree epsilon hpool z q hz rhoUnit
  have herrorNonneg : 0 <= error :=
    decodedRetryPoolPhysicalProtocolCoordinateRawError_nonneg
      m w z q hz coordinate run.acceptedOutput
  have hweighted :
      run.successProbability * error <=
        routedDepthErrorEnvelope w r m epsilon z := by
    rw [decodedRetryPoolPhysicalProtocolRun_success_mul_coordinateError_eq_mass
      h hdegree epsilon z q hz rhoUnit coordinate]
    exact decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_envelope
      h hdegree epsilon
        (decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
          epsilon hpool)
        z q hz rhoUnit coordinate
  have hscale : (3 / 4 : Real) * error <= run.successProbability * error :=
    mul_le_mul_of_nonneg_right hsuccess herrorNonneg
  dsimp only [error, run] at hscale hweighted ⊢
  nlinarith

end HH18Parameterized
end Distillation
end QEC
