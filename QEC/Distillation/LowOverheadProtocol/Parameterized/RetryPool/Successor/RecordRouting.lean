import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Records.AcceptedPortRecordProduct
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Records.MeasuredRecordProduct
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Routing

/-!
# Parameterized HH18 successor record routing

For one fixed logical branch, the accepted parent records have exactly the
cardinality needed by the next stage's trial/physical grid.  This module
reindexes their genuine tensor product through the compiled successor-slot
equivalence and identifies every routed trial block with the measured physical
input consumed by that next HH18 attempt.
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
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- The fixed-port selected-block index is exactly the immediate successor's
trial/physical coordinate. -/
noncomputable def decodedRetryPoolSuccessorPortRecordSlotEquiv
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Fin (decodedRetryPoolBackwardSchedule m w z q stage) ≃
      Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
        PhysicalSite m w :=
  decodedRetryPoolSuccessorAttemptSlotsEquiv m w z q stage hstage

/-- Reindex a fixed-port register bitstring into its successor trial/physical
coordinates without changing any recorded bit. -/
noncomputable def decodedRetryPoolSuccessorPortRecordBitstringEquiv
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Bitstring (Fin (decodedRetryPoolBackwardSchedule m w z q stage)) ≃
      Bitstring
        (Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
          PhysicalSite m w) where
  toFun := fun bits target =>
    bits ((decodedRetryPoolSuccessorPortRecordSlotEquiv
      m w z q stage hstage).symm target)
  invFun := fun bits source =>
    bits (decodedRetryPoolSuccessorPortRecordSlotEquiv
      m w z q stage hstage source)
  left_inv := by
    intro bits
    funext source
    simp
  right_inv := by
    intro bits
    funext target
    simp

/-- The basis-preserving physical transport from the fixed-port accepted
record register to the next-stage trial/physical register. -/
noncomputable def decodedRetryPoolSuccessorPortRecordTransport
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    UnitaryTransport
      (QubitRegister (Fin (decodedRetryPoolBackwardSchedule m w z q stage)))
      (QubitRegister
        (Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
          PhysicalSite m w)) := by
  let sourceBasis := EuclideanSpace.basisFun
    (Bitstring (Fin (decodedRetryPoolBackwardSchedule m w z q stage))) Complex
  let targetBasis := EuclideanSpace.basisFun
    (Bitstring
      (Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
        PhysicalSite m w)) Complex
  let transport := sourceBasis.equiv targetBasis
    (decodedRetryPoolSuccessorPortRecordBitstringEquiv m w z q stage hstage)
  exact
    { toLinearEquiv := transport.toLinearEquiv
      map_inner := transport.inner_map_map }

/-- The fixed-port successor transport maps every computational basis vector
to the basis vector at its exact next-stage coordinate. -/
@[simp] theorem decodedRetryPoolSuccessorPortRecordTransport_apply_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Bitstring (Fin (decodedRetryPoolBackwardSchedule m w z q stage))) :
    decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
        (EuclideanSpace.basisFun
          (Bitstring (Fin (decodedRetryPoolBackwardSchedule m w z q stage)))
          Complex bits) =
      EuclideanSpace.basisFun
        (Bitstring
          (Fin (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) Complex
        (decodedRetryPoolSuccessorPortRecordBitstringEquiv
          m w z q stage hstage bits) := by
  dsimp [decodedRetryPoolSuccessorPortRecordTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- Identify a recursive one-qubit tensor history of exact natural depth with
the bitstring register on `Fin required`. -/
def decodedRetryPoolQubitTensorPowerFinBitstringEquiv (required : Nat) :
    tensorPowerHistory (Fin 2) required ≃ Bitstring (Fin required) :=
  tensorPowerHistoryEquiv (Fin 2) required

/-- The exact-depth basis transport from a recursive one-qubit tensor carrier
to its ordinary `Fin required` register. -/
noncomputable def decodedRetryPoolQubitTensorPowerFinRegisterTransport
    (required : Nat) :
    UnitaryTransport (tensorPowerCarrier QubitSpace required)
      (QubitRegister (Fin required)) := by
  let sourceBasis := tensorPowerBasis
    (EuclideanSpace.basisFun (Fin 2) Complex) required
  let targetBasis := EuclideanSpace.basisFun
    (Bitstring (Fin required)) Complex
  let transport := sourceBasis.equiv targetBasis
    (decodedRetryPoolQubitTensorPowerFinBitstringEquiv required)
  exact
    { toLinearEquiv := transport.toLinearEquiv
      map_inner := transport.inner_map_map }

/-- The exact-depth transport preserves every recursive computational basis
label. -/
@[simp] theorem decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis
    (required : Nat) (history : tensorPowerHistory (Fin 2) required) :
    decodedRetryPoolQubitTensorPowerFinRegisterTransport required
        (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
          required history) =
      EuclideanSpace.basisFun (Bitstring (Fin required)) Complex
        (decodedRetryPoolQubitTensorPowerFinBitstringEquiv required history) := by
  dsimp [decodedRetryPoolQubitTensorPowerFinRegisterTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- The homogeneous fixed-port record product, represented on the ordinary
selected-block register before successor routing. -/
noncomputable def decodedRetryPoolAcceptedPortRecordRegisterProductDensity
    (m w : Nat) (parameter : ErrorParameter)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (required : Nat) :
    DensityOperator (QubitRegister (Fin required)) :=
  (decodedRetryPoolQubitTensorPowerFinRegisterTransport required).conjDensity
    (tensorPowerProductInput
      (decodedRetryPoolOneQubitRecordDensity parameter) rhoUnit required)

/-- The complete physical fixed-port record channel followed by the canonical
flattening from its recursive one-qubit tensor carrier to the selected-block
record register. -/
noncomputable def decodedRetryPoolAcceptedPortRecordRegisterChannel
    (m w : Nat) (port : LogicalSite m w) (required : Nat) :
    QuantumChannel
      (QubitRegister (Fin required × LogicalSite m w))
      (QubitRegister (Fin required)) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (decodedRetryPoolQubitTensorPowerFinRegisterTransport required))
    (decodedRetryPoolAcceptedPortRecordProductChannel m w port required)

/-- On the genuine product of distinct accepted parent blocks, the flattened
fixed-port channel produces the corresponding homogeneous record product. -/
theorem decodedRetryPoolAcceptedPortRecordRegisterChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (port : LogicalSite m w) (required : Nat) :
    (decodedRetryPoolAcceptedPortRecordRegisterChannel
      m w port required).mapDensity
        (decodedRetryPoolAcceptedProductDensity
          h hdegree epsilon rhoUnit required) =
      decodedRetryPoolAcceptedPortRecordRegisterProductDensity
        m w (selectedLogicalPortRawParameter h hdegree epsilon port)
        rhoUnit required := by
  rw [decodedRetryPoolAcceptedPortRecordRegisterChannel,
    QuantumChannel.comp_mapDensity,
    decodedRetryPoolAcceptedPortRecordProductChannel_mapDensity
      h hdegree epsilon rhoUnit port required]
  rfl

/-- Route the fixed-port accepted-record product to the actual immediate
successor trial/physical grid. -/
noncomputable def decodedRetryPoolSuccessorPortRecordProductDensity
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (parameter : ErrorParameter)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator
      (QubitRegister
        (Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
          PhysicalSite m w)) :=
  (decodedRetryPoolSuccessorPortRecordTransport
    m w z q stage hstage).conjDensity
      (decodedRetryPoolAcceptedPortRecordRegisterProductDensity
        m w parameter rhoUnit
        (decodedRetryPoolBackwardSchedule m w z q stage))

/-- The complete CPTP route from the actual accepted-parent product to the
fixed logical branch's immediate successor trial/physical record register. -/
noncomputable def decodedRetryPoolAcceptedPortSuccessorRecordChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    QuantumChannel
      (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q stage) ×
          LogicalSite m w))
      (QubitRegister
        (Fin (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (decodedRetryPoolSuccessorPortRecordTransport
        m w z q stage hstage))
    (decodedRetryPoolAcceptedPortRecordRegisterChannel m w port
      (decodedRetryPoolBackwardSchedule m w z q stage))

/-- The complete successor-port channel maps the genuine accepted-parent
product to the already-identified routed record product. -/
theorem decodedRetryPoolAcceptedPortSuccessorRecordChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    (decodedRetryPoolAcceptedPortSuccessorRecordChannel
      m w z q stage hstage port).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      decodedRetryPoolSuccessorPortRecordProductDensity
        m w z q stage hstage
        (selectedLogicalPortRawParameter h hdegree epsilon port) rhoUnit := by
  rw [decodedRetryPoolAcceptedPortSuccessorRecordChannel,
    QuantumChannel.comp_mapDensity,
    decodedRetryPoolAcceptedPortRecordRegisterChannel_mapDensity
      h hdegree epsilon rhoUnit port
        (decodedRetryPoolBackwardSchedule m w z q stage)]
  rfl

/-- Computational entries of the routed fixed-port product factor over its
actual next-stage trial/physical coordinates. -/
theorem decodedRetryPoolSuccessorPortRecordProductDensity_matrixEntry
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (parameter : ErrorParameter)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (left right : Bitstring
      (Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
        PhysicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun
          (Bitstring
            (Fin (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) Complex left)
        ((decodedRetryPoolSuccessorPortRecordProductDensity
          m w z q stage hstage parameter rhoUnit).toOperator
          (EuclideanSpace.basisFun
            (Bitstring
              (Fin (decodedRetryPoolBackwardAttempts m w z q
                  ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) Complex right)) =
      ∏ coordinate :
          Fin (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w,
        inner Complex
          (EuclideanSpace.basisFun (Fin 2) Complex (left coordinate))
          ((decodedRetryPoolOneQubitRecordDensity parameter).toOperator
            (EuclideanSpace.basisFun (Fin 2) Complex (right coordinate))) := by
  let required := decodedRetryPoolBackwardSchedule m w z q stage
  let leftSource :=
    (decodedRetryPoolSuccessorPortRecordBitstringEquiv
      m w z q stage hstage).symm left
  let rightSource :=
    (decodedRetryPoolSuccessorPortRecordBitstringEquiv
      m w z q stage hstage).symm right
  let leftHistory :=
    (decodedRetryPoolQubitTensorPowerFinBitstringEquiv required).symm leftSource
  let rightHistory :=
    (decodedRetryPoolQubitTensorPowerFinBitstringEquiv required).symm rightSource
  have hleftAt (source : Fin required) :
      tensorPowerHistoryAt (Fin 2) required leftHistory source =
        left (decodedRetryPoolSuccessorPortRecordSlotEquiv
          m w z q stage hstage source) := by
    have hsource :
        tensorPowerHistoryAt (Fin 2) required leftHistory source =
          leftSource source := by
      exact congrFun
        ((decodedRetryPoolQubitTensorPowerFinBitstringEquiv
          required).apply_symm_apply leftSource) source
    have hroute :
        leftSource source =
          left (decodedRetryPoolSuccessorPortRecordSlotEquiv
            m w z q stage hstage source) := by
      rfl
    calc
      tensorPowerHistoryAt (Fin 2) required leftHistory source =
          leftSource source := hsource
      _ = left (decodedRetryPoolSuccessorPortRecordSlotEquiv
          m w z q stage hstage source) := hroute
  have hrightAt (source : Fin required) :
      tensorPowerHistoryAt (Fin 2) required rightHistory source =
        right (decodedRetryPoolSuccessorPortRecordSlotEquiv
          m w z q stage hstage source) := by
    have hsource :
        tensorPowerHistoryAt (Fin 2) required rightHistory source =
          rightSource source := by
      exact congrFun
        ((decodedRetryPoolQubitTensorPowerFinBitstringEquiv
          required).apply_symm_apply rightSource) source
    have hroute :
        rightSource source =
          right (decodedRetryPoolSuccessorPortRecordSlotEquiv
            m w z q stage hstage source) := by
      rfl
    calc
      tensorPowerHistoryAt (Fin 2) required rightHistory source =
          rightSource source := hsource
      _ = right (decodedRetryPoolSuccessorPortRecordSlotEquiv
          m w z q stage hstage source) := hroute
  have hleftBasis :
      decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
          (decodedRetryPoolQubitTensorPowerFinRegisterTransport required
            (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
              required leftHistory)) =
        EuclideanSpace.basisFun
          (Bitstring
            (Fin (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) Complex left := by
    rw [decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis,
      decodedRetryPoolSuccessorPortRecordTransport_apply_basis]
    simp [leftHistory, leftSource]
  have hrightBasis :
      decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
          (decodedRetryPoolQubitTensorPowerFinRegisterTransport required
            (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
              required rightHistory)) =
        EuclideanSpace.basisFun
          (Bitstring
            (Fin (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩) × PhysicalSite m w)) Complex right := by
    rw [decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis,
      decodedRetryPoolSuccessorPortRecordTransport_apply_basis]
    simp [rightHistory, rightSource]
  calc
    _ = inner Complex
        (decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
          (decodedRetryPoolQubitTensorPowerFinRegisterTransport required
            (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
              required leftHistory)))
        ((decodedRetryPoolSuccessorPortRecordTransport
          m w z q stage hstage).conjOperator
          ((decodedRetryPoolQubitTensorPowerFinRegisterTransport
            required).conjOperator
            (tensorPowerProductInput
              (decodedRetryPoolOneQubitRecordDensity parameter) rhoUnit
              required).toOperator)
          (decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
            (decodedRetryPoolQubitTensorPowerFinRegisterTransport required
              (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
                required rightHistory)))) := by
      rw [hleftBasis, hrightBasis]
      simp only [decodedRetryPoolSuccessorPortRecordProductDensity,
        decodedRetryPoolAcceptedPortRecordRegisterProductDensity,
        UnitaryTransport.conjDensity_toOperator]
      rfl
    _ = inner Complex
        (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
          required leftHistory)
        ((tensorPowerProductInput
          (decodedRetryPoolOneQubitRecordDensity parameter) rhoUnit
          required).toOperator
          (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
            required rightHistory)) := by
      rw [UnitaryTransport.conjOperator_apply]
      simp only [LinearEquiv.symm_apply_apply]
      rw [(decodedRetryPoolSuccessorPortRecordTransport
        m w z q stage hstage).map_inner]
      rw [UnitaryTransport.conjOperator_apply]
      simp only [LinearEquiv.symm_apply_apply]
      exact (decodedRetryPoolQubitTensorPowerFinRegisterTransport
        required).map_inner _ _
    _ = ∏ source : Fin required,
        inner Complex
          (EuclideanSpace.basisFun (Fin 2) Complex
            (tensorPowerHistoryAt (Fin 2) required leftHistory source))
          ((decodedRetryPoolOneQubitRecordDensity parameter).toOperator
            (EuclideanSpace.basisFun (Fin 2) Complex
              (tensorPowerHistoryAt (Fin 2) required rightHistory source))) := by
      exact tensorPowerProductInput_matrixEntry_eq_prod
        (EuclideanSpace.basisFun (Fin 2) Complex)
        (decodedRetryPoolOneQubitRecordDensity parameter) rhoUnit
        required leftHistory rightHistory
    _ = _ := by
      exact Fintype.prod_equiv
        (decodedRetryPoolSuccessorPortRecordSlotEquiv
          m w z q stage hstage)
        _ _ (fun source => by rw [hleftAt source, hrightAt source])

/-- After routing, every next-stage trial block is the exact measured-resource
input density at the fixed selected-port error parameter. -/
theorem decodedRetryPoolSuccessorPortRecordProductDensity_eq_trialProductInput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorPortRecordProductDensity
        m w z q stage hstage
        (selectedLogicalPortRawParameter h hdegree epsilon port) rhoUnit =
      tensorPowerRegisterProductDensity (PhysicalSite m w)
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun
    (Bitstring
      (Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
        PhysicalSite m w)) Complex
  apply basis.toBasis.ext
  intro right
  apply InnerProductSpace.ext_inner_left_basis basis.toBasis
  intro left
  dsimp [basis]
  rw [decodedRetryPoolSuccessorPortRecordProductDensity_matrixEntry]
  rw [tensorPowerRegisterProductDensity_matrixEntry]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro trial _
  have hrecord :
      decodedRetryPoolDiagonalErrorRate
          (selectedLogicalPortRawParameter h hdegree epsilon port) hhalf =
        selectedLogicalPortNextInputRate h hdegree epsilon port hhalf := by
    rfl
  have hprepare :
      prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)) =
        decodedRetryPoolPhysicalRecordProductDensity m w
          (selectedLogicalPortRawParameter h hdegree epsilon port) rhoUnit := by
    rw [← hrecord]
    exact (decodedRetryPoolPhysicalRecordProductDensity_eq_prepareMeasuredResources
      m w (selectedLogicalPortRawParameter h hdegree epsilon port) hhalf rhoUnit).symm
  rw [hprepare]
  rw [decodedRetryPoolPhysicalRecordProductDensity_matrixEntry]
  simp_rw [decodedRetryPoolOneQubitRecordDensity_matrixEntry
    (selectedLogicalPortRawParameter h hdegree epsilon port) hhalf]
  let leftBlock : Bitstring (PhysicalSite m w) :=
    fun physical => left (trial, physical)
  let rightBlock : Bitstring (PhysicalSite m w) :=
    fun physical => right (trial, physical)
  change (∏ physical : PhysicalSite m w,
      if leftBlock physical = rightBlock physical then
        (HH18NoisyInput.bitErrorWeight
          (decodedRetryPoolDiagonalErrorRate
            (selectedLogicalPortRawParameter h hdegree epsilon port) hhalf)
          (leftBlock physical : ZMod 2) : Complex)
      else 0) =
    if leftBlock = rightBlock then
      (HH18NoisyInput.errorWordWeight
        (decodedRetryPoolDiagonalErrorRate
          (selectedLogicalPortRawParameter h hdegree epsilon port) hhalf)
        (Coding.PauliSymplectic.bitstringWordEquiv
          (PhysicalSite m w) leftBlock) : Complex)
    else 0
  by_cases heq : leftBlock = rightBlock
  · simp only [heq, ite_true, HH18NoisyInput.errorWordWeight,
      Coding.PauliSymplectic.bitstringWordEquiv_apply]
    norm_cast
  · have hsite : ∃ physical, leftBlock physical ≠ rightBlock physical := by
      simpa only [Function.ne_iff] using heq
    rw [if_neg heq]
    rcases hsite with ⟨physical, hphysical⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ physical)]
    simp [hphysical]

/-- The complete physical fixed-port channel supplies exactly the measured
resource product consumed by every immediate-successor retry attempt. -/
theorem
    decodedRetryPoolAcceptedPortSuccessorRecordChannel_mapDensity_eq_trialProductInput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolAcceptedPortSuccessorRecordChannel
      m w z q stage hstage port).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      tensorPowerRegisterProductDensity (PhysicalSite m w)
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  rw [decodedRetryPoolAcceptedPortSuccessorRecordChannel_mapDensity
    h hdegree epsilon rhoUnit z q stage hstage port]
  exact decodedRetryPoolSuccessorPortRecordProductDensity_eq_trialProductInput
    h hdegree epsilon z q stage hstage port hhalf rhoUnit

/-- The actual next decoded retry pool reads the fixed successor port through
the inverse of the same basis-preserving flattening used to expose its
trial/physical input register. -/
noncomputable def decodedRetryPoolAcceptedPortSuccessorInputChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    QuantumChannel
      (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q stage) ×
          LogicalSite m w))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (tensorPowerQubitRegisterTransport (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm)
    (decodedRetryPoolAcceptedPortSuccessorRecordChannel
      m w z q stage hstage port)

/-- The next-pool input channel maps the genuine accepted-parent product to
the literal recursive product input of the immediate-successor retry pool. -/
theorem decodedRetryPoolAcceptedPortSuccessorInputChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolAcceptedPortSuccessorInputChannel
      m w z q stage hstage port).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  apply DensityOperator.ext_toOperator
  simp only [decodedRetryPoolAcceptedPortSuccessorInputChannel,
    QuantumChannel.mapDensity_toOperator, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  have hroute := congrArg DensityOperator.toOperator
    (decodedRetryPoolAcceptedPortSuccessorRecordChannel_mapDensity_eq_trialProductInput
      h hdegree epsilon z q stage hstage port hhalf rhoUnit)
  simp only [QuantumChannel.mapDensity_toOperator] at hroute
  change
    (tensorPowerQubitRegisterTransport (PhysicalSite m w)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)).symm.conjOperator
      ((decodedRetryPoolAcceptedPortSuccessorRecordChannel
        m w z q stage hstage port).toLinearMap
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)).toOperator) = _
  rw [hroute]
  exact (tensorPowerQubitRegisterTransport (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)).symm_conjOperator_conjOperator _

/-- The observed Born mass of one immediate-successor history on the actual
routed fixed-port input. -/
noncomputable def decodedRetryPoolAcceptedPortSuccessorBornWeight
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (_hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)) : Real :=
  (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩)).bornWeight
    ⟨history, PUnit.unit⟩
    ((decodedRetryPoolAcceptedPortSuccessorInputChannel
      m w z q stage hstage port).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)))

/-- The actual routed successor history has precisely the Born product at the
selected port's derived next-input rate. -/
theorem
    decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)) :
    decodedRetryPoolAcceptedPortSuccessorBornWeight
        h hdegree epsilon z q stage hstage port hhalf rhoUnit history =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) history := by
  rw [decodedRetryPoolAcceptedPortSuccessorBornWeight,
    decodedRetryPoolAcceptedPortSuccessorInputChannel_mapDensity
      h hdegree epsilon z q stage hstage port hhalf rhoUnit]
  exact decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput
    h hdegree
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)
    (decodedRetryPoolBackwardSchedule m w z q
      ⟨stage.1 + 1, hstage⟩)
    (noisyResources m w
      (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf))
    rhoUnit history

/-- A positive enough immediate-successor history normalizes to the genuine
product of selected accepted outputs at the derived next-input rate. -/
theorem
    decodedRetryPoolAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩))
    (henough :
      decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩ ≤
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩) history).card)
    (hpositive : 0 <
      decodedRetryPoolAcceptedPortSuccessorBornWeight
        h hdegree epsilon z q stage hstage port hhalf rhoUnit history) :
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩)).conditionalDensity
        ⟨history, PUnit.unit⟩
        ((decodedRetryPoolAcceptedPortSuccessorInputChannel
          m w z q stage hstage port).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage)))
        hpositive =
      decodedRetryPoolAcceptedProductDensity h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)
        rhoUnit
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  let attempts :=
    decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩
  let required :=
    decodedRetryPoolBackwardSchedule m w z q
      ⟨stage.1 + 1, hstage⟩
  let nextRate :=
    selectedLogicalPortNextInputRate h hdegree epsilon port hhalf
  have hinput :=
    decodedRetryPoolAcceptedPortSuccessorInputChannel_mapDensity
      h hdegree epsilon z q stage hstage port hhalf rhoUnit
  have hbranch :=
    decodedRetryPool_enoughBranch_eq_bornProduct_smul_acceptedProduct
      h hdegree nextRate rhoUnit attempts required history henough
  have hweight :=
    decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
      h hdegree epsilon z q stage hstage port hhalf rhoUnit history
  apply DensityOperator.ext_toOperator
  erw [FiniteInstrument.conditionalDensity_toOperator]
  change
    ((decodedRetryPoolAcceptedPortSuccessorBornWeight
      h hdegree epsilon z q stage hstage port hhalf rhoUnit history : Complex)⁻¹) •
      (decodedRetryPoolInstrument h hdegree attempts required).branchOperator
        ⟨history, PUnit.unit⟩
        ((decodedRetryPoolAcceptedPortSuccessorInputChannel
          m w z q stage hstage port).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage))).toOperator = _
  rw [hinput]
  rw [hbranch]
  rw [hweight]
  rw [← mul_smul]
  rw [inv_mul_cancel₀]
  · change (1 : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree nextRate rhoUnit
          required).toOperator = _
    rw [one_smul]
  · exact_mod_cast (hweight ▸ ne_of_gt hpositive)

end HH18Parameterized
end Distillation
end QEC
