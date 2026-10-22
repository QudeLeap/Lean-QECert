import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Regrouping
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.RecordRouting
import QEC.Semantics.Instruments.TensorPower.ChannelProductFunctorial
/-!
# Parameterized HH18 fixed-port successor branch products

The global successor route retains one logical branch from every accepted
parent block.  This module constructs the same fixed-port operation directly:
undo the parent-product register flattening, apply the genuine coordinate
marginal independently to every parent block, route the resulting one-qubit
register through the compiled successor-slot equivalence, and restore the
literal recursive physical input carrier of the next retry pool.

The channel is defined on arbitrary source operators.  Product structure is
used only by its explicit evaluation theorem.
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

local instance instSuccessorBranchClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Undo the accepted-parent register flattening and apply the true nominated
coordinate marginal independently to every parent block. -/
noncomputable def decodedRetryPoolSuccessorCoordinateTensorChannel
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w) :
    QuantumChannel
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (tensorPowerCarrier QubitSpace
        (decodedRetryPoolBackwardSchedule m w z q stage)) :=
  QuantumChannel.comp
    (quantumChannelTensorPower
      (decodedRetryPoolQubitRegisterCoordinateChannel (LogicalSite m w) port)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (QuantumChannel.unitaryConj
      (tensorPowerQubitRegisterTransport (LogicalSite m w)
        (decodedRetryPoolBackwardSchedule m w z q stage)).symm)

/-- The exact composite unitary that flattens the retained qubit tensor,
reindexes it through the successor trial/physical slots, and restores the
literal recursive physical-register carrier. -/
noncomputable def decodedRetryPoolSuccessorCoordinateBranchRouteTransport
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    UnitaryTransport
      (tensorPowerCarrier QubitSpace
        (decodedRetryPoolBackwardSchedule m w z q stage))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) := by
  let flatten := decodedRetryPoolQubitTensorPowerFinRegisterTransport
    (decodedRetryPoolBackwardSchedule m w z q stage)
  let route := decodedRetryPoolSuccessorPortRecordTransport
    m w z q stage hstage
  let restore := (tensorPowerQubitRegisterTransport (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)).symm
  exact
    { toLinearEquiv :=
        (flatten.toLinearEquiv.trans route.toLinearEquiv).trans
          restore.toLinearEquiv
      map_inner := by
        intro x y
        exact (restore.map_inner (route (flatten x)) (route (flatten y))).trans
          ((route.map_inner (flatten x) (flatten y)).trans
            (flatten.map_inner x y)) }

@[simp] theorem decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (x : tensorPowerCarrier QubitSpace
      (decodedRetryPoolBackwardSchedule m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchRouteTransport
        m w z q stage hstage x =
      (tensorPowerQubitRegisterTransport (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm
        (decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
          (decodedRetryPoolQubitTensorPowerFinRegisterTransport
            (decodedRetryPoolBackwardSchedule m w z q stage) x)) := by
  rfl

/-- Route the recursively tensorized fixed-port qubits through the compiled
successor-slot equivalence and into the literal next-pool physical carrier. -/
noncomputable def decodedRetryPoolSuccessorCoordinateBranchRouteChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    QuantumChannel
      (tensorPowerCarrier QubitSpace
        (decodedRetryPoolBackwardSchedule m w z q stage))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) :=
  QuantumChannel.unitaryConj
    (decodedRetryPoolSuccessorCoordinateBranchRouteTransport
      m w z q stage hstage)

/-- Select one actual logical coordinate from every parent block, then route
those physical qubits into the literal recursive input of the next retry
pool.  Every step is a complete channel; no product or independence premise
is built into the operation. -/
noncomputable def decodedRetryPoolSuccessorCoordinateBranchChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    QuantumChannel
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) :=
  QuantumChannel.comp
    (decodedRetryPoolSuccessorCoordinateBranchRouteChannel
      m w z q stage hstage)
    (decodedRetryPoolSuccessorCoordinateTensorChannel
      m w z q stage port)

/-- The coordinate-tensor stage maps a genuine product of parent blocks to
the recursive product of their actual coordinate marginals. -/
theorem decodedRetryPoolSuccessorCoordinateTensorChannel_mapDensity_product
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (rho : DensityOperator (LogicalRegister m w))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorCoordinateTensorChannel
      m w z q stage port).mapDensity
        (tensorPowerRegisterProductDensity (LogicalSite m w) rho rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      tensorPowerProductInput
        ((decodedRetryPoolQubitRegisterCoordinateChannel
          (LogicalSite m w) port).mapDensity rho)
        rhoUnit (decodedRetryPoolBackwardSchedule m w z q stage) := by
  rw [decodedRetryPoolSuccessorCoordinateTensorChannel]
  simp only [QuantumChannel.comp_mapDensity,
    tensorPowerRegisterProductDensity]
  have hundone :
      (QuantumChannel.unitaryConj
        (tensorPowerQubitRegisterTransport (LogicalSite m w)
          (decodedRetryPoolBackwardSchedule m w z q stage)).symm).mapDensity
          ((tensorPowerQubitRegisterTransport (LogicalSite m w)
            (decodedRetryPoolBackwardSchedule m w z q stage)).conjDensity
            (tensorPowerProductInput rho rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage))) =
        tensorPowerProductInput rho rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage) := by
    apply DensityOperator.ext_toOperator
    simp only [QuantumChannel.mapDensity_toOperator,
      QuantumChannel.unitaryConj_apply,
      UnitaryTransport.conjDensity_toOperator]
    exact (tensorPowerQubitRegisterTransport (LogicalSite m w)
      (decodedRetryPoolBackwardSchedule m w z q stage)).symm_conjOperator_conjOperator _
  rw [hundone]
  exact quantumChannelTensorPower_mapDensity_product
    (decodedRetryPoolQubitRegisterCoordinateChannel (LogicalSite m w) port)
    rho rhoUnit rhoUnit rfl
    (decodedRetryPoolBackwardSchedule m w z q stage)

/-- On a genuine product of parent-block densities, the physical fixed-port
channel produces the tensor product of their true coordinate marginals and
then applies only the exact successor-slot and recursive-register transports.
-/
theorem decodedRetryPoolSuccessorCoordinateBranchChannel_mapDensity_product
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) (rho : DensityOperator (LogicalRegister m w))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorCoordinateBranchChannel
      m w z q stage hstage port).mapDensity
        (tensorPowerRegisterProductDensity (LogicalSite m w) rho rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      (tensorPowerQubitRegisterTransport (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm.conjDensity
        ((decodedRetryPoolSuccessorPortRecordTransport
          m w z q stage hstage).conjDensity
          ((decodedRetryPoolQubitTensorPowerFinRegisterTransport
            (decodedRetryPoolBackwardSchedule m w z q stage)).conjDensity
            (tensorPowerProductInput
              ((decodedRetryPoolQubitRegisterCoordinateChannel
                (LogicalSite m w) port).mapDensity rho)
              rhoUnit (decodedRetryPoolBackwardSchedule m w z q stage)))) := by
  rw [decodedRetryPoolSuccessorCoordinateBranchChannel,
    QuantumChannel.comp_mapDensity,
    decodedRetryPoolSuccessorCoordinateTensorChannel_mapDensity_product]
  apply DensityOperator.ext_toOperator
  rfl

/-- Bit label retained by the fixed-port route, expressed directly on the
recursive next-pool physical carrier. -/
noncomputable def decodedRetryPoolSuccessorCoordinateBranchHistory
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (bits : Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    tensorPowerHistory (Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩) :=
  (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)).symm
    (fun target => bits
      ((decodedRetryPoolSuccessorAttemptSlotsEquiv
        m w z q stage hstage).symm target, port))

/-- Coefficient obtained by tensorizing the true one-block coordinate
marginal across all accepted parent blocks. -/
noncomputable def decodedRetryPoolSuccessorCoordinateBranchCoefficient
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) : Complex :=
  ∏ trial : Fin (decodedRetryPoolBackwardSchedule m w z q stage),
    ∏ coordinate : Fin (Fintype.card (LogicalSite m w)),
      if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
      else inner Complex
        (EuclideanSpace.basisFun (Fin 2) Complex
          (right (trial,
            (Fintype.equivFin (LogicalSite m w)).symm coordinate)))
        (EuclideanSpace.basisFun (Fin 2) Complex
          (left (trial,
            (Fintype.equivFin (LogicalSite m w)).symm coordinate)))

/-- Source computational matrix unit for the flat parent-block register. -/
noncomputable def decodedRetryPoolSuccessorSourceMatrixUnit
    (m w z q : Nat) (stage : Fin z)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    Operator (QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :=
  (InnerProductSpace.rankOne Complex
    (EuclideanSpace.basisFun
      (Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      Complex left)
    (EuclideanSpace.basisFun
      (Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      Complex right)).toLinearMap

/-- Matrix unit obtained after retaining the nominated coordinate from every
parent block, before applying the successor-slot transports. -/
noncomputable def decodedRetryPoolSuccessorCoordinateTensorBasisVector
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (bits : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    tensorPowerCarrier QubitSpace
      (decodedRetryPoolBackwardSchedule m w z q stage) :=
  tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
    (decodedRetryPoolBackwardSchedule m w z q stage)
    (tensorPowerHistoryMap (fun localBits => localBits port)
      (decodedRetryPoolBackwardSchedule m w z q stage)
      ((tensorPowerQubitBitstringEquiv (LogicalSite m w)
        (decodedRetryPoolBackwardSchedule m w z q stage)).symm bits))

/-- Matrix unit obtained after retaining the nominated coordinate from every
parent block, before applying the successor-slot transports. -/
noncomputable def decodedRetryPoolSuccessorCoordinateTensorMatrixUnit
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    Operator (tensorPowerCarrier QubitSpace
      (decodedRetryPoolBackwardSchedule m w z q stage)) :=
  (InnerProductSpace.rankOne Complex
    (decodedRetryPoolSuccessorCoordinateTensorBasisVector
      m w z q stage port left)
    (decodedRetryPoolSuccessorCoordinateTensorBasisVector
      m w z q stage port right)).toLinearMap

/-- Routed basis vector on the literal recursive next-pool carrier. -/
noncomputable def decodedRetryPoolSuccessorCoordinateBranchBasisVector
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (bits : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩) :=
  tensorPowerBasis
    (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex)
    (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
    (decodedRetryPoolSuccessorCoordinateBranchHistory
      m w z q stage hstage port bits)

/-- Routed matrix unit on the literal recursive next-pool carrier. -/
noncomputable def decodedRetryPoolSuccessorCoordinateBranchMatrixUnit
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    Operator (tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)) :=
  (InnerProductSpace.rankOne Complex
    (decodedRetryPoolSuccessorCoordinateBranchBasisVector
      m w z q stage hstage port left)
    (decodedRetryPoolSuccessorCoordinateBranchBasisVector
      m w z q stage hstage port right)).toLinearMap

/-- The coordinate-tensor stage acts on flat source matrix units by the
product of the true one-block coordinate-contraction coefficients. -/
theorem decodedRetryPoolSuccessorCoordinateTensorChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateTensorChannel m w z q stage port
        (decodedRetryPoolSuccessorSourceMatrixUnit
          m w z q stage left right) =
      decodedRetryPoolSuccessorCoordinateBranchCoefficient
          m w z q stage port left right •
        decodedRetryPoolSuccessorCoordinateTensorMatrixUnit
          m w z q stage port left right := by
  let required := decodedRetryPoolBackwardSchedule m w z q stage
  let leftHistory :=
    (tensorPowerQubitBitstringEquiv (LogicalSite m w) required).symm left
  let rightHistory :=
    (tensorPowerQubitBitstringEquiv (LogicalSite m w) required).symm right
  let coordinateCoefficient :
      Bitstring (LogicalSite m w) → Bitstring (LogicalSite m w) → Complex :=
    fun localLeft localRight =>
      ∏ coordinate : Fin (Fintype.card (LogicalSite m w)),
        if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
        else inner Complex
          (EuclideanSpace.basisFun (Fin 2) Complex
            (localRight ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))
          (EuclideanSpace.basisFun (Fin 2) Complex
            (localLeft ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))
  have hleftAt (trial : Fin required) :
      tensorPowerHistoryAt (Bitstring (LogicalSite m w)) required
          leftHistory trial = fun site => left (trial, site) := by
    funext site
    exact tensorPowerQubitBitstringEquiv_symm_at
      (LogicalSite m w) required left trial site
  have hrightAt (trial : Fin required) :
      tensorPowerHistoryAt (Bitstring (LogicalSite m w)) required
          rightHistory trial = fun site => right (trial, site) := by
    funext site
    exact tensorPowerQubitBitstringEquiv_symm_at
      (LogicalSite m w) required right trial site
  have htensor := quantumChannelTensorPower_rankOne_basis
    (decodedRetryPoolQubitRegisterCoordinateChannel (LogicalSite m w) port)
    (EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex)
    (EuclideanSpace.basisFun (Fin 2) Complex)
    (fun localBits => localBits port) coordinateCoefficient
    (by
      intro localLeft localRight
      exact decodedRetryPoolQubitRegisterCoordinateChannel_rankOne_basis
        (LogicalSite m w) port localLeft localRight)
    required leftHistory rightHistory
  simp only [decodedRetryPoolSuccessorCoordinateTensorChannel,
    decodedRetryPoolSuccessorSourceMatrixUnit,
    decodedRetryPoolSuccessorCoordinateTensorMatrixUnit,
    decodedRetryPoolSuccessorCoordinateTensorBasisVector,
    QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne,
    tensorPowerQubitRegisterTransport_symm_apply_basis,
    tensorPowerQubitRegisterTransport_symm_apply_basis]
  change _ = _ at htensor
  rw [htensor]
  congr 1
  apply Finset.prod_congr rfl
  intro trial _
  simp only [coordinateCoefficient, hleftAt trial, hrightAt trial]

/-- The exact composite successor transport sends a retained-coordinate basis
vector to its literal recursive physical-register label. -/
theorem decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (bits : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchRouteTransport
        m w z q stage hstage
        (decodedRetryPoolSuccessorCoordinateTensorBasisVector
          m w z q stage port bits) =
      decodedRetryPoolSuccessorCoordinateBranchBasisVector
        m w z q stage hstage port bits := by
  let required := decodedRetryPoolBackwardSchedule m w z q stage
  let attempts := decodedRetryPoolBackwardAttempts m w z q
    ⟨stage.1 + 1, hstage⟩
  simp only [decodedRetryPoolSuccessorCoordinateTensorBasisVector,
    decodedRetryPoolSuccessorCoordinateBranchBasisVector]
  rw [decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply,
    decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis,
    decodedRetryPoolSuccessorPortRecordTransport_apply_basis,
    tensorPowerQubitRegisterTransport_symm_apply_basis]
  let selectedHistory :=
    tensorPowerHistoryMap (fun localBits => localBits port) required
      ((tensorPowerQubitBitstringEquiv (LogicalSite m w) required).symm bits)
  let routedBits : Bitstring (Fin attempts × PhysicalSite m w) :=
    decodedRetryPoolSuccessorPortRecordBitstringEquiv m w z q stage hstage
      (decodedRetryPoolQubitTensorPowerFinBitstringEquiv required selectedHistory)
  let expectedBits : Bitstring (Fin attempts × PhysicalSite m w) :=
    fun target => bits
      ((decodedRetryPoolSuccessorAttemptSlotsEquiv
        m w z q stage hstage).symm target, port)
  have hrouted (target : Fin attempts × PhysicalSite m w) :
      routedBits target = expectedBits target := by
    change tensorPowerHistoryAt (Fin 2) required selectedHistory
        ((decodedRetryPoolSuccessorAttemptSlotsEquiv
          m w z q stage hstage).symm target) =
      bits ((decodedRetryPoolSuccessorAttemptSlotsEquiv
        m w z q stage hstage).symm target, port)
    simp only [selectedHistory, tensorPowerHistoryAt_map,
      tensorPowerQubitBitstringEquiv_symm_at]
  have hroutedEq : routedBits = expectedBits := by
    funext target
    exact hrouted target
  congr 1
  change (tensorPowerQubitBitstringEquiv (PhysicalSite m w) attempts).symm
      routedBits =
    (tensorPowerQubitBitstringEquiv (PhysicalSite m w) attempts).symm
      expectedBits
  exact congrArg
    (tensorPowerQubitBitstringEquiv (PhysicalSite m w) attempts).symm
    hroutedEq

/-- The exact successor-slot route maps the tensorized fixed-port matrix unit
to the corresponding literal recursive next-pool matrix unit. -/
theorem decodedRetryPoolSuccessorCoordinateBranchRouteChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchRouteChannel m w z q stage hstage
        (decodedRetryPoolSuccessorCoordinateTensorMatrixUnit
          m w z q stage port left right) =
      decodedRetryPoolSuccessorCoordinateBranchMatrixUnit
        m w z q stage hstage port left right := by
  simp only [decodedRetryPoolSuccessorCoordinateBranchRouteChannel,
    decodedRetryPoolSuccessorCoordinateTensorMatrixUnit,
    decodedRetryPoolSuccessorCoordinateBranchMatrixUnit,
    QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne,
    decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply_basis,
    decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply_basis]

/-- On a computational matrix unit, the direct fixed-port channel contracts
precisely the sibling logical coordinates and retains the nominated port at
every parent-block index. -/
theorem decodedRetryPoolSuccessorCoordinateBranchChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchChannel m w z q stage hstage port
        (decodedRetryPoolSuccessorSourceMatrixUnit
          m w z q stage left right) =
      decodedRetryPoolSuccessorCoordinateBranchCoefficient
          m w z q stage port left right •
        decodedRetryPoolSuccessorCoordinateBranchMatrixUnit
          m w z q stage hstage port left right := by
  rw [decodedRetryPoolSuccessorCoordinateBranchChannel,
    QuantumChannel.comp_apply,
    decodedRetryPoolSuccessorCoordinateTensorChannel_rankOne_basis]
  rw [map_smul]
  exact congrArg
    (fun A => decodedRetryPoolSuccessorCoordinateBranchCoefficient
      m w z q stage port left right • A)
    (decodedRetryPoolSuccessorCoordinateBranchRouteChannel_rankOne_basis
      m w z q stage hstage port left right)

/-- The exact condition under which a source matrix unit survives discarding
all logical coordinates other than the nominated successor port. -/
def decodedRetryPoolSuccessorSiblingAgreement
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) : Prop :=
  ∀ trial : Fin (decodedRetryPoolBackwardSchedule m w z q stage),
    ∀ site : LogicalSite m w, site ≠ port →
      right (trial, site) = left (trial, site)

/-- The direct coordinate-tensor coefficient is the indicator of exact
agreement on all discarded sibling coordinates. -/
theorem decodedRetryPoolSuccessorCoordinateBranchCoefficient_eq_ite
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchCoefficient
        m w z q stage port left right =
      if decodedRetryPoolSuccessorSiblingAgreement
          m w z q stage port left right then 1 else 0 := by
  by_cases hagreement : decodedRetryPoolSuccessorSiblingAgreement
      m w z q stage port left right
  · rw [if_pos hagreement]
    apply Fintype.prod_eq_one
    intro trial
    apply Fintype.prod_eq_one
    intro coordinate
    by_cases hcoordinate :
        coordinate = Fintype.equivFin (LogicalSite m w) port
    · simp [hcoordinate]
    · have hsite :
          (Fintype.equivFin (LogicalSite m w)).symm coordinate ≠ port := by
        intro heq
        apply hcoordinate
        rw [← heq, Equiv.apply_symm_apply]
      have hbit := hagreement trial
        ((Fintype.equivFin (LogicalSite m w)).symm coordinate) hsite
      simp only [hcoordinate, if_false,
        (EuclideanSpace.basisFun (Fin 2) Complex).inner_eq_ite]
      simp [hbit]
  · rw [if_neg hagreement]
    have hexists : ∃ trial : Fin
        (decodedRetryPoolBackwardSchedule m w z q stage),
        ∃ site : LogicalSite m w,
          site ≠ port ∧ right (trial, site) ≠ left (trial, site) := by
      simp only [decodedRetryPoolSuccessorSiblingAgreement] at hagreement
      push Not at hagreement
      exact hagreement
    obtain ⟨trial, site, hsite, hbit⟩ := hexists
    let coordinate : Fin (Fintype.card (LogicalSite m w)) :=
      Fintype.equivFin (LogicalSite m w) site
    have hcoordinate :
        coordinate ≠ Fintype.equivFin (LogicalSite m w) port := by
      intro heq
      apply hsite
      exact (Fintype.equivFin (LogicalSite m w)).injective heq
    rw [decodedRetryPoolSuccessorCoordinateBranchCoefficient]
    apply Finset.prod_eq_zero (Finset.mem_univ trial)
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    rw [if_neg hcoordinate]
    simp only [coordinate, Equiv.symm_apply_apply]
    rw [(EuclideanSpace.basisFun (Fin 2) Complex).inner_eq_ite]
    exact if_neg hbit

/-- Coefficient in the already-compiled global reindex/regroup branch
selector, named so it can be compared symbolically with the direct route. -/
noncomputable def decodedRetryPoolSuccessorRoutedBranchCoefficient
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (branch : Fin (logicalOutputCount m w))
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) : Complex :=
  ∏ coordinate : Fin (logicalOutputCount m w),
    if coordinate = branch then 1
    else inner Complex
      (tensorPowerBasis
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)
        ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩)).symm
          (fun target => right
            ((decodedRetryPoolSuccessorAttemptSlotsEquiv
              m w z q stage hstage).symm target,
              (decodedRetryPoolLogicalSiteFinEquiv m w).symm coordinate))))
      (tensorPowerBasis
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)
        ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩)).symm
          (fun target => left
            ((decodedRetryPoolSuccessorAttemptSlotsEquiv
              m w z q stage hstage).symm target,
              (decodedRetryPoolLogicalSiteFinEquiv m w).symm coordinate))))

/-- The global branch coefficient is the same sibling-agreement indicator as
the direct coordinate-tensor coefficient. -/
theorem decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_ite
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorRoutedBranchCoefficient m w z q stage hstage
        (decodedRetryPoolLogicalSiteFinEquiv m w port) left right =
      if decodedRetryPoolSuccessorSiblingAgreement
          m w z q stage port left right then 1 else 0 := by
  let attempts := decodedRetryPoolBackwardAttempts m w z q
    ⟨stage.1 + 1, hstage⟩
  let branchEquiv := decodedRetryPoolLogicalSiteFinEquiv m w
  let attemptEquiv := decodedRetryPoolSuccessorAttemptSlotsEquiv
    m w z q stage hstage
  let historyEquiv := tensorPowerQubitBitstringEquiv (PhysicalSite m w) attempts
  let physicalBasis :=
    EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex
  by_cases hagreement : decodedRetryPoolSuccessorSiblingAgreement
      m w z q stage port left right
  · rw [if_pos hagreement]
    rw [decodedRetryPoolSuccessorRoutedBranchCoefficient]
    apply Fintype.prod_eq_one
    intro coordinate
    by_cases hcoordinate : coordinate = branchEquiv port
    · simp [branchEquiv, hcoordinate]
    · have hsite : branchEquiv.symm coordinate ≠ port := by
        intro heq
        apply hcoordinate
        calc
          coordinate = branchEquiv (branchEquiv.symm coordinate) :=
            (branchEquiv.apply_symm_apply coordinate).symm
          _ = branchEquiv port := congrArg branchEquiv heq
      have hhistory :
          historyEquiv.symm (fun target =>
              right (attemptEquiv.symm target, branchEquiv.symm coordinate)) =
            historyEquiv.symm (fun target =>
              left (attemptEquiv.symm target, branchEquiv.symm coordinate)) := by
        apply historyEquiv.injective
        funext target
        simp only [Equiv.apply_symm_apply]
        exact hagreement (attemptEquiv.symm target)
          (branchEquiv.symm coordinate) hsite
      rw [if_neg hcoordinate,
        (tensorPowerBasis physicalBasis attempts).inner_eq_ite,
        if_pos hhistory]
  · rw [if_neg hagreement]
    have hexists : ∃ trial : Fin
        (decodedRetryPoolBackwardSchedule m w z q stage),
        ∃ site : LogicalSite m w,
          site ≠ port ∧ right (trial, site) ≠ left (trial, site) := by
      simp only [decodedRetryPoolSuccessorSiblingAgreement] at hagreement
      push Not at hagreement
      exact hagreement
    obtain ⟨trial, site, hsite, hbit⟩ := hexists
    let coordinate : Fin (logicalOutputCount m w) := branchEquiv site
    have hcoordinate : coordinate ≠ branchEquiv port := by
      intro heq
      apply hsite
      exact branchEquiv.injective heq
    have hsiteCoordinate : branchEquiv.symm coordinate = site := by
      simp [coordinate]
    have hhistory :
        historyEquiv.symm (fun target =>
            right (attemptEquiv.symm target, branchEquiv.symm coordinate)) ≠
          historyEquiv.symm (fun target =>
            left (attemptEquiv.symm target, branchEquiv.symm coordinate)) := by
      intro heq
      have hflat := congrArg historyEquiv heq
      have htarget := congrFun hflat (attemptEquiv trial)
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at htarget
      rw [hsiteCoordinate] at htarget
      exact hbit htarget
    rw [decodedRetryPoolSuccessorRoutedBranchCoefficient]
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    rw [if_neg hcoordinate,
      (tensorPowerBasis physicalBasis attempts).inner_eq_ite,
      if_neg hhistory]

/-- The global and direct physical fixed-port selectors have identical
coefficients on every source computational matrix unit. -/
theorem decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_coordinate
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorRoutedBranchCoefficient m w z q stage hstage
        (decodedRetryPoolLogicalSiteFinEquiv m w port) left right =
      decodedRetryPoolSuccessorCoordinateBranchCoefficient
        m w z q stage port left right := by
  rw [decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_ite,
    decodedRetryPoolSuccessorCoordinateBranchCoefficient_eq_ite]

/-- The globally reindexed branch selector is exactly the direct physical
fixed-port successor channel, as channels on arbitrary source operators. -/
theorem decodedRetryPoolSuccessorRoutedBranchChannel_eq_coordinateBranch
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    decodedRetryPoolSuccessorRoutedBranchChannel m w z q stage hstage
        (decodedRetryPoolLogicalSiteFinEquiv m w port) =
      decodedRetryPoolSuccessorCoordinateBranchChannel
        m w z q stage hstage port := by
  have hmaps :
      (decodedRetryPoolSuccessorRoutedBranchChannel m w z q stage hstage
        (decodedRetryPoolLogicalSiteFinEquiv m w port)).toLinearMap =
      (decodedRetryPoolSuccessorCoordinateBranchChannel
        m w z q stage hstage port).toLinearMap := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis
      (EuclideanSpace.basisFun
        (Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage)) Complex)
    intro left right
    rw [decodedRetryPoolSuccessorRoutedBranchChannel_rankOne_basis]
    change _ = decodedRetryPoolSuccessorCoordinateBranchChannel
      m w z q stage hstage port
        (decodedRetryPoolSuccessorSourceMatrixUnit
          m w z q stage left right)
    rw [decodedRetryPoolSuccessorCoordinateBranchChannel_rankOne_basis]
    change decodedRetryPoolSuccessorRoutedBranchCoefficient
          m w z q stage hstage
            (decodedRetryPoolLogicalSiteFinEquiv m w port) left right • _ =
        decodedRetryPoolSuccessorCoordinateBranchCoefficient
          m w z q stage port left right • _
    rw [decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_coordinate]
    congr 1
    simp only [decodedRetryPoolSuccessorCoordinateBranchMatrixUnit,
      decodedRetryPoolSuccessorCoordinateBranchBasisVector,
      decodedRetryPoolSuccessorCoordinateBranchHistory,
      Equiv.symm_apply_apply]
  generalize hleft :
      decodedRetryPoolSuccessorRoutedBranchChannel m w z q stage hstage
        (decodedRetryPoolLogicalSiteFinEquiv m w port) = Phi at hmaps ⊢
  generalize hright :
      decodedRetryPoolSuccessorCoordinateBranchChannel
        m w z q stage hstage port = Psi at hmaps ⊢
  cases Phi
  cases Psi
  cases hmaps
  rfl

/-- The true marginal of the actual globally regrouped successor input is
the corresponding physical routed-branch channel applied after the genuine
sitewise record preparation.  This is a no-signalling statement about one
coordinate of the joint successor state; it does not assert that distinct
logical branches are independent. -/
theorem decodedRetryPoolSuccessorNestedInputChannel_inputMarginal
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator (QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)))
    (branch : Fin (logicalOutputCount m w)) :
    tensorPowerInputMarginal (logicalOutputCount m w)
        ((decodedRetryPoolSuccessorNestedInputChannel
          m w z q stage hstage).mapDensity rho) branch =
      (decodedRetryPoolSuccessorRoutedBranchChannel
        m w z q stage hstage branch).mapDensity
          ((decodedRetryPoolSuccessorRecordPreparationChannel
            m w z q stage).mapDensity rho) := by
  rw [← tensorPowerCoordinateOperator_mapDensity]
  simp only [decodedRetryPoolSuccessorNestedInputChannel,
    decodedRetryPoolSuccessorRoutedBranchChannel,
    decodedRetryPoolSuccessorRegroupBranchChannel,
    QuantumChannel.comp_mapDensity]

/-- On the genuine accepted-parent product, the actual global physical route
(sitewise record preparation, full successor reindexing/regrouping, then one
outer-branch marginal) supplies exactly the literal product input consumed by
the corresponding immediate-successor retry pool.  No independence between
distinct logical ports of one accepted parent block is assumed. -/
theorem
    decodedRetryPoolSuccessorRoutedBranchChannel_mapDensity_recordPreparation_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorRoutedBranchChannel m w z q stage hstage
      (decodedRetryPoolLogicalSiteFinEquiv m w port)).mapDensity
        ((decodedRetryPoolSuccessorRecordPreparationChannel
          m w z q stage).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage))) =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  rw [decodedRetryPoolSuccessorRoutedBranchChannel_eq_coordinateBranch]
  rw [decodedRetryPoolAcceptedProductDensity]
  rw [decodedRetryPoolSuccessorRecordPreparationChannel_mapDensity_product]
  rw [decodedRetryPoolSuccessorCoordinateBranchChannel_mapDensity_product]
  have hcoordinate :
      (decodedRetryPoolQubitRegisterCoordinateChannel
          (LogicalSite m w) port).mapDensity
          ((decodedRetryPoolQubitRegisterSitewiseChannel
            decodedRetryPoolSuccessorOneQubitRecordChannel
            (LogicalSite m w)).mapDensity
              (resourceDecodedRun h hdegree
                (noisyResources m w epsilon)).acceptedOutput) =
        decodedRetryPoolOneQubitRecordDensity
          (selectedLogicalPortRawParameter h hdegree epsilon port) := by
    rw [decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_sitewise]
    rw [decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort]
    exact decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput
      h hdegree epsilon port
  rw [hcoordinate]
  change
    (tensorPowerQubitRegisterTransport (PhysicalSite m w)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)).symm.conjDensity
      (decodedRetryPoolSuccessorPortRecordProductDensity
        m w z q stage hstage
        (selectedLogicalPortRawParameter h hdegree epsilon port) rhoUnit) = _
  rw [decodedRetryPoolSuccessorPortRecordProductDensity_eq_trialProductInput
    h hdegree epsilon z q stage hstage port hhalf rhoUnit]
  apply DensityOperator.ext_toOperator
  simp only [tensorPowerRegisterProductDensity,
    UnitaryTransport.conjDensity_toOperator]
  exact (tensorPowerQubitRegisterTransport (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)).symm_conjOperator_conjOperator _

/-- Every true branch marginal of the actual joint successor input produced
from a genuine accepted-parent product is the literal noisy-resource product
for that port's next routed error rate.  The theorem deliberately remains a
marginal statement: the joint successor input may be correlated across
distinct logical ports. -/
theorem
    decodedRetryPoolSuccessorNestedInputChannel_inputMarginal_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    tensorPowerInputMarginal (logicalOutputCount m w)
        ((decodedRetryPoolSuccessorNestedInputChannel
          m w z q stage hstage).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage)))
        (decodedRetryPoolLogicalSiteFinEquiv m w port) =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  rw [decodedRetryPoolSuccessorNestedInputChannel_inputMarginal]
  exact
    decodedRetryPoolSuccessorRoutedBranchChannel_mapDensity_recordPreparation_acceptedProduct
      h hdegree epsilon z q stage hstage port hhalf rhoUnit

end HH18Parameterized
end Distillation
end QEC
