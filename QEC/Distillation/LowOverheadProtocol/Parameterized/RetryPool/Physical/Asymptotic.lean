import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.Cost

/-!
# Physical asymptotic adapter for parameterized HH18

This module exposes the dependent finite-depth adapter needed by downstream
overhead theorems.  At every index it uses one actual exact-batch physical run,
its literal raw-input and terminal-coordinate types, its Born success mass,
and the finite maximum of measurements on its normalized accepted output.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument

attribute [local instance 100] Fintype.ofFinite

/-- The exact-batch terminal-coordinate type is inhabited at every index. -/
theorem decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
    (m w depth : Nat) :
    Nonempty (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) := by
  apply Fintype.card_pos_iff.mp
  rw [decodedRetryPoolPhysicalExactBatchOutputSlots_card]
  exact mul_pos
    (decodedRetryPoolExactBatchTerminalRequest_pos (depth + 1))
    (pow_pos (routedDepthLogicalOutputCount_pos m w) _)

/-- The reached output error is the finite maximum of the genuine negative-A
measurements on the actual run's normalized accepted output. -/
noncomputable def decodedRetryPoolPhysicalExactBatchActualOutputError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) : Real := by
  classical
  exact Finset.univ.sup'
    ⟨(decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
      m w depth).some, Finset.mem_univ _⟩
    fun coordinate =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput

/-- Every literal terminal coordinate participates in the reached maximum. -/
theorem decodedRetryPoolPhysicalExactBatchCoordinateError_le_actualOutputError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) :
    decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput <=
      decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit := by
  classical
  unfold decodedRetryPoolPhysicalExactBatchActualOutputError
  exact Finset.le_sup'
    (fun other : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) other
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput)
    (Finset.mem_univ coordinate)

/-- The actual finite maximum is attained at one physical terminal coordinate. -/
theorem decodedRetryPoolPhysicalExactBatchActualOutputError_exists_coordinate
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∃ coordinate : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth,
      decodedRetryPoolPhysicalExactBatchActualOutputError
          h hdegree epsilon depth rhoUnit =
        decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
          (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
          (Nat.succ_pos depth) coordinate
          (decodedRetryPoolPhysicalExactBatchRun
            h hdegree epsilon depth rhoUnit).acceptedOutput := by
  classical
  unfold decodedRetryPoolPhysicalExactBatchActualOutputError
  obtain ⟨coordinate, _, hcoordinate⟩ := Finset.exists_mem_eq_sup'
    ⟨(decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
      m w depth).some, Finset.mem_univ _⟩
    (fun coordinate =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput)
  exact ⟨coordinate, hcoordinate⟩

/-- The actual reached maximum is nonnegative. -/
theorem decodedRetryPoolPhysicalExactBatchActualOutputError_nonneg
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    0 <= decodedRetryPoolPhysicalExactBatchActualOutputError
      h hdegree epsilon depth rhoUnit := by
  obtain ⟨coordinate, hcoordinate⟩ :=
    decodedRetryPoolPhysicalExactBatchActualOutputError_exists_coordinate
      h hdegree epsilon depth rhoUnit
  rw [hcoordinate]
  exact decodedRetryPoolPhysicalProtocolCoordinateRawError_nonneg
    m w (depth + 1)
      (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
      (Nat.succ_pos depth) coordinate _

/-- Admissibility forces the iteration scale to dominate `4/3`, so the
normalized physical envelope fits the existing distance-power target. -/
theorem four_thirds_mul_routedDepthErrorEnvelope_le_scheduleTargetError
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    (4 / 3 : Real) * routedDepthErrorEnvelope w r m epsilon depth <=
      routedDepthScheduleTargetError w r m epsilon depth := by
  rw [routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope h epsilon depth]
  have hn : 0 < physicalInputCount m w := routedDepthPhysicalInputCount_pos h
  have hscale : (4 / 3 : Real) <= routedDepthIterationScale w r m := by
    have htwo := two_mul_routedDepthPhysicalInputCount_le_iterationScale w r m
    have hcount : (1 : Real) <= physicalInputCount m w := by exact_mod_cast hn
    nlinarith
  exact mul_le_mul_of_nonneg_right hscale
    (routedDepthScheduleErrorEnvelope_nonneg w r m epsilon depth)

/-- The maximum error of the normalized actual run obeys the source-backed
distance-power target at its physical depth. -/
theorem decodedRetryPoolPhysicalExactBatchActualOutputError_le_targetError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit <=
      routedDepthScheduleTargetError w r m epsilon (depth + 1) := by
  classical
  unfold decodedRetryPoolPhysicalExactBatchActualOutputError
  apply Finset.sup'_le
  intro coordinate _
  exact (decodedRetryPoolPhysicalProtocolRun_coordinateError_le_four_thirds_envelope
    h hdegree epsilon hpool (depth + 1)
      (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
      (Nat.succ_pos depth) rhoUnit coordinate).trans
    (four_thirds_mul_routedDepthErrorEnvelope_le_scheduleTargetError
      h epsilon (depth + 1))

/-- The exact physical run yield is uniformly positive. -/
theorem decodedRetryPoolPhysicalExactBatchYield_pos
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    0 < (decodedRetryPoolPhysicalExactBatchYield
      h hdegree epsilon depth rhoUnit : Real) :=
  decodedRetryPoolPhysicalProtocolRun_success_pos
    h hdegree epsilon hpool (depth + 1)
      (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
      (Nat.succ_pos depth) rhoUnit

/-- The successful-output coefficient induced by exact physical retry counts
and the genuine run success lower bound. -/
noncomputable def decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient
    {w r m : Nat} (_h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Real :=
  (16 / 9 : Real) /
    Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
      (routedDepthScheduleGamma w r m)

theorem decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    0 < decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon := by
  unfold decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (routedDepthScheduleLogGrowthBase_pos epsilon hepsilon
        (decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
          epsilon hpool)) _)

/-- The exact physical run's successful-output cost has the required
polylogarithmic comparison at every dependent finite-depth index. -/
theorem decodedRetryPoolPhysicalExactBatchSuccessfulOutputCost_le_polylog
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
        h hdegree epsilon depth rhoUnit <=
      decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon *
        Real.rpow
          (Real.log (1 / routedDepthScheduleTargetError
            w r m epsilon (depth + 1)))
          (routedDepthScheduleGamma w r m) := by
  let base := routedDepthScheduleLogGrowthBase w r m epsilon
  let gamma := routedDepthScheduleGamma w r m
  have hsmall :=
    decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
      epsilon hpool
  have hbase : 0 < base :=
    routedDepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall
  have hbaseRpow : 0 < Real.rpow base gamma :=
    Real.rpow_pos_of_pos hbase _
  have hlog := routedDepthSchedule_distancePow_mul_logGrowthBase_eq_log
    (w := w) (r := r) (m := m) epsilon hepsilon (depth + 1)
  have hfactorization :
      Real.rpow ((codeDistance r w : Real) ^ (depth + 1) * base) gamma =
        Real.rpow ((codeDistance r w : Real) ^ (depth + 1)) gamma *
          Real.rpow base gamma :=
    Real.mul_rpow (by positivity) hbase.le
  calc
    decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
        h hdegree epsilon depth rhoUnit <=
      (16 / 9 : Real) *
        ((physicalInputCount m w : Real) / logicalOutputCount m w) ^
          (depth + 1) :=
      decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_le_sixteen_ninths
        h hdegree epsilon hpool depth rhoUnit
    _ = (16 / 9 : Real) *
        Real.rpow ((codeDistance r w : Real) ^ (depth + 1)) gamma := by
      rw [routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow h]
    _ = ((16 / 9 : Real) *
          Real.rpow ((codeDistance r w : Real) ^ (depth + 1)) gamma *
          Real.rpow base gamma) / Real.rpow base gamma := by
      field_simp [ne_of_gt hbaseRpow]
    _ = decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon *
        Real.rpow ((codeDistance r w : Real) ^ (depth + 1) * base) gamma := by
      rw [hfactorization]
      unfold decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient
      dsimp only [base, gamma]
      field_simp [ne_of_gt hbaseRpow]
    _ = decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon *
        Real.rpow
          (Real.log (1 / routedDepthScheduleTargetError
            w r m epsilon (depth + 1))) gamma := by
      rw [hlog]

/-- Final dependent adapter: slots, reached errors, and yields all come from
the same actual exact-batch physical run at each index. -/
theorem decodedRetryPoolPhysicalExactBatch_physicalPolylogarithmicExpectedYieldOverhead
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (decodedRetryPoolPhysicalExactBatchInputSlots m w)
      (decodedRetryPoolPhysicalExactBatchOutputSlots m w)
      (fun depth =>
        routedDepthScheduleTargetError w r m epsilon (depth + 1))
      (fun depth => decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit)
      (fun depth => decodedRetryPoolPhysicalExactBatchYield
        h hdegree epsilon depth rhoUnit)
      (routedDepthScheduleGamma w r m)
      (decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon) := by
  refine
    ⟨(decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
      h epsilon hepsilon hpool).le, ?_⟩
  intro depth _ _
  exact
    ⟨decodedRetryPoolPhysicalExactBatchActualOutputError_le_targetError
      h hdegree epsilon hpool depth rhoUnit,
    decodedRetryPoolPhysicalExactBatchYield_pos
      h hdegree epsilon hpool depth rhoUnit,
    decodedRetryPoolPhysicalExactBatchSuccessfulOutputCost_le_polylog
      h hdegree epsilon hepsilon hpool depth rhoUnit⟩

/-! ## Pointwise bridge to the #458 family interface -/

/-- The actual root Hilbert space of the exact physical batch at one depth. -/
abbrev decodedRetryPoolPhysicalExactBatchInputCarrier
    (m w depth : Nat) :=
  decodedRetryPoolProtocolRootInputCarrier m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)

/-- The actual nested terminal Hilbert space of the same physical batch. -/
abbrev decodedRetryPoolPhysicalExactBatchOutputCarrier
    (m w depth : Nat) :=
  decodedRetryPoolPhysicalProtocolOutputCarrier m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)

/-- The base register repeated inside the exact batch's nested output. -/
abbrev decodedRetryPoolPhysicalExactBatchBaseOutputSlots
    (m w depth : Nat) :=
  Fin (decodedRetryPoolBackwardSchedule m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (decodedRetryPoolProtocolTerminalStage (depth + 1)
      (Nat.succ_pos depth))) × LogicalSite m w

/-- Repeatedly tensor one density through the literal nested carrier. -/
noncomputable def decodedRetryPoolNestedProductDensity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (rho : DensityOperator H) (branches : Nat) :
    (depth : Nat) → DensityOperator (nestedTensorCarrier H branches depth)
  | 0 => rho
  | depth + 1 =>
      decodedRetryPoolNestedProductDensity
        (tensorPowerProductInput rho decodedRetryPoolTensorUnitDensity branches)
        branches depth

/-- The source-oriented all-`A` density on the terminal base register. -/
noncomputable def decodedRetryPoolPhysicalExactBatchBaseIdealOutput
    (m w depth : Nat) :
    DensityOperator
      (QubitRegister
        (decodedRetryPoolPhysicalExactBatchBaseOutputSlots m w depth)) :=
  DensityOperator.pureDensity
    (Triorthogonal.BinaryRowFamily.logicalMagicState
      (decodedRetryPoolPhysicalExactBatchBaseOutputSlots m w depth)) (by
        have hinner :=
          Triorthogonal.BinaryRowFamily.logicalMagicState_inner_self
            (decodedRetryPoolPhysicalExactBatchBaseOutputSlots m w depth)
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner]
        norm_num)

/-- The genuine all-`A` ideal on every terminal coordinate of the nested
physical batch.  Its carrier is the same literal carrier returned by the run. -/
noncomputable def decodedRetryPoolPhysicalExactBatchIdealOutput
    (m w depth : Nat) :
    DensityOperator (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth) :=
  decodedRetryPoolNestedProductDensity
    (decodedRetryPoolPhysicalExactBatchBaseIdealOutput m w depth)
    (logicalOutputCount m w) depth

/-- The protocol error functional is the worst negative-`A` measurement over
the literal terminal coordinates of the supplied output density. -/
noncomputable def decodedRetryPoolPhysicalExactBatchOutputError
    (m w depth : Nat)
    (rho _sigma : DensityOperator
      (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth)) : Real := by
  classical
  exact Finset.univ.sup'
    ⟨(decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
      m w depth).some, Finset.mem_univ _⟩
    fun coordinate =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate rho

/-- The coordinate-measurement output functional is nonnegative. -/
theorem decodedRetryPoolPhysicalExactBatchOutputError_nonneg
    (m w depth : Nat)
    (rho sigma : DensityOperator
      (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth)) :
    0 ≤ decodedRetryPoolPhysicalExactBatchOutputError m w depth rho sigma := by
  classical
  unfold decodedRetryPoolPhysicalExactBatchOutputError
  obtain ⟨coordinate, _, hcoordinate⟩ := Finset.exists_mem_eq_sup'
    ⟨(decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
      m w depth).some, Finset.mem_univ _⟩
    (fun coordinate : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate rho)
  rw [hcoordinate]
  exact decodedRetryPoolPhysicalProtocolCoordinateRawError_nonneg
    m w (depth + 1)
      (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
      (Nat.succ_pos depth) coordinate rho

/-- The actual independent resource model at one depth.  Its rates and input
family are exactly those consumed by the physical run. -/
def decodedRetryPoolPhysicalExactBatchIndependentInputModel
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    IndependentInputErrorModel
      (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).resourceCount QubitSpace where
  rate := fun _ => epsilon.1
  rate_nonneg := fun _ => epsilon.property.1
  rate_le_one := fun _ => by linarith [epsilon.property.2]
  admissible := fun rates inputs =>
    (∀ slot, rates slot = epsilon.1) ∧
      inputs = (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).noisyInput

/-- Package one depth of the dependent physical construction as a genuine
`MagicStateDistillationProtocol`.  The run, input, branches, ideal, and error
functional are all the concrete objects constructed above. -/
noncomputable def decodedRetryPoolPhysicalExactBatchMagicStateProtocol
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    MagicStateDistillationProtocol QubitSpace
      (decodedRetryPoolPhysicalExactBatchInputCarrier m w depth)
      (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth) where
  run := decodedRetryPoolPhysicalExactBatchRun
    h hdegree epsilon depth rhoUnit
  inputErrorModel := .independent
    (decodedRetryPoolPhysicalExactBatchIndependentInputModel
      h hdegree epsilon depth rhoUnit)
  inputPermitted := by
    exact ⟨fun _ => rfl, rfl⟩
  behavior := .postselected
  idealOutput := decodedRetryPoolPhysicalExactBatchIdealOutput m w depth
  outputError := decodedRetryPoolPhysicalExactBatchOutputError m w depth
  outputError_nonneg := decodedRetryPoolPhysicalExactBatchOutputError_nonneg
    m w depth

/-- The packaged protocol's error is definitionally the reached maximum of
the accepted output of the same physical run. -/
theorem decodedRetryPoolPhysicalExactBatchMagicStateProtocol_successfulOutputError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalExactBatchMagicStateProtocol
      h hdegree epsilon depth rhoUnit).successfulOutputError =
      decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit := by
  rfl

/-- At each depth, expose the dependent physical protocol as an ordinary
one-index #458 family on its actual depth-dependent input/output carriers. -/
noncomputable def decodedRetryPoolPhysicalExactBatchProtocolFamily
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DistillationProtocolFamily QubitSpace
      (decodedRetryPoolPhysicalExactBatchInputCarrier m w depth)
      (decodedRetryPoolPhysicalExactBatchOutputCarrier m w depth) PUnit where
  targetError := fun _ =>
    routedDepthScheduleTargetError w r m epsilon (depth + 1)
  protocol := fun _ =>
    decodedRetryPoolPhysicalExactBatchMagicStateProtocol
      h hdegree epsilon depth rhoUnit
  outputResourceCount := fun _ =>
    Fintype.card (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth)
  outputResourceCount_pos := by
    intro _
    exact Fintype.card_pos_iff.mpr
      (decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty m w depth)
  successfulOutputError_le_targetError := by
    intro _
    rw [decodedRetryPoolPhysicalExactBatchMagicStateProtocol_successfulOutputError]
    exact decodedRetryPoolPhysicalExactBatchActualOutputError_le_targetError
      h hdegree epsilon hpool depth rhoUnit

/-- The typed exact-batch cost is exactly the #458 successful-output cost of
the genuine pointwise family. -/
theorem decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_eq_protocolFamily
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
        h hdegree epsilon depth rhoUnit =
      (decodedRetryPoolPhysicalExactBatchProtocolFamily
        h hdegree epsilon hpool depth rhoUnit).successfulOutputCost PUnit.unit := by
  unfold decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
  refine
    DependentBatch.typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
      (decodedRetryPoolPhysicalExactBatchProtocolFamily
        h hdegree epsilon hpool depth rhoUnit) PUnit.unit
      (decodedRetryPoolPhysicalExactBatchInputSlots m w depth)
      (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth)
      (decodedRetryPoolPhysicalExactBatchYield
        h hdegree epsilon depth rhoUnit) ?_ ?_ ?_
  · simpa [DistillationProtocolFamily.inputResourceCount,
      decodedRetryPoolPhysicalExactBatchProtocolFamily,
      decodedRetryPoolPhysicalExactBatchMagicStateProtocol] using
      (decodedRetryPoolPhysicalExactBatchInputSlots_card_eq_run_resourceCount
        h hdegree epsilon depth rhoUnit)
  · rfl
  · exact decodedRetryPoolPhysicalExactBatchYield_eq_runSuccess
      h hdegree epsilon depth rhoUnit

/-- Literal #458 bridge: every actual depth family satisfies the existing
`PolylogarithmicOverhead` predicate with the uniform physical coefficient. -/
theorem decodedRetryPoolPhysicalExactBatchProtocolFamily_polylogarithmicOverhead
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    PolylogarithmicOverhead
      (decodedRetryPoolPhysicalExactBatchProtocolFamily
        h hdegree epsilon hpool depth rhoUnit)
      (routedDepthScheduleGamma w r m)
      (decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon) := by
  refine ⟨(decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
    h epsilon hepsilon hpool).le, ?_⟩
  intro index _ _
  cases index
  constructor
  · change 0 < (decodedRetryPoolPhysicalExactBatchRun
      h hdegree epsilon depth rhoUnit).successProbability
    simpa only [decodedRetryPoolPhysicalExactBatchYield_eq_runSuccess] using
      (decodedRetryPoolPhysicalExactBatchYield_pos
        h hdegree epsilon hpool depth rhoUnit)
  · rw [← decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_eq_protocolFamily
      h hdegree epsilon hpool depth rhoUnit]
    simpa [decodedRetryPoolPhysicalExactBatchProtocolFamily] using
      (decodedRetryPoolPhysicalExactBatchSuccessfulOutputCost_le_polylog
        h hdegree epsilon hepsilon hpool depth rhoUnit)

end HH18Parameterized
end Distillation
end QEC
