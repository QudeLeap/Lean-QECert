import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Routing
import QEC.Distillation.LowOverheadProtocol.Parameterized.DepthTwoRouting
import QEC.Semantics.Instruments.TensorPower.Basis
import QEC.Semantics.Instruments.Registers.Marginal
import QEC.Semantics.Channels.Instrument
/-!
# Parameterized HH18 decoded retry-pool successor preparation

The selected logical outputs consumed by the next HH18 layer are not merely
coordinates to be permuted.  Each retained qubit must first undergo the same
physical A-basis dephasing and inverse phase transport used by the established
fresh-parent route.  This module constructs that transformation as a genuine
sitewise CPTP channel on the entire selected-output register.  Tensoring the
one-qubit channel is valid on arbitrary correlated inputs and introduces no
product-state premise.
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

/-- The homogeneous tensor power of a genuine one-qubit channel, obtained
from its finite Choi--Kraus instrument and the existing physical tensor-power
construction. -/
noncomputable def decodedRetryPoolQubitChannelTensorPower
    (channel : QuantumChannel QubitSpace QubitSpace) (sites : Nat) :
    QuantumChannel (tensorPowerCarrier QubitSpace sites)
      (tensorPowerCarrier QubitSpace sites) :=
  ((channel.toFiniteInstrument).tensorPower sites).kraus.toQuantumChannel
    ((channel.toFiniteInstrument).tensorPower_complete
      channel.toFiniteInstrument_complete sites)

/-- Identify the recursive one-qubit tensor history with the bitstrings of
an arbitrary finite register, using only the canonical finite enumeration of
its site type. -/
noncomputable def decodedRetryPoolQubitTensorPowerBitstringEquiv
    (ι : Type) [Fintype ι] :
    tensorPowerHistory (Fin 2) (Fintype.card ι) ≃ Bitstring ι :=
  (tensorPowerHistoryEquiv (Fin 2) (Fintype.card ι)).trans
    { toFun := fun bits site => bits (Fintype.equivFin ι site)
      invFun := fun bits coordinate => bits ((Fintype.equivFin ι).symm coordinate)
      left_inv := by
        intro bits
        funext coordinate
        simp
      right_inv := by
        intro bits
        funext site
        simp }

/-- The basis-preserving unitary between the literal recursive tensor power
of one-qubit carriers and the corresponding finite qubit register. -/
noncomputable def decodedRetryPoolQubitTensorPowerRegisterTransport
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    UnitaryTransport (tensorPowerCarrier QubitSpace (Fintype.card ι))
      (QubitRegister ι) := by
  let sourceBasis := tensorPowerBasis
    (EuclideanSpace.basisFun (Fin 2) Complex) (Fintype.card ι)
  let targetBasis := EuclideanSpace.basisFun (Bitstring ι) Complex
  let U := sourceBasis.equiv targetBasis
    (decodedRetryPoolQubitTensorPowerBitstringEquiv ι)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- Apply one physical one-qubit channel independently at every site of an
arbitrary finite register.  The channel itself acts on the full density
operator and therefore remains meaningful for correlated inputs. -/
noncomputable def decodedRetryPoolQubitRegisterSitewiseChannel
    (channel : QuantumChannel QubitSpace QubitSpace)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    QuantumChannel (QubitRegister ι) (QubitRegister ι) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (decodedRetryPoolQubitTensorPowerRegisterTransport ι))
    (QuantumChannel.comp
      (decodedRetryPoolQubitChannelTensorPower channel (Fintype.card ι))
      (QuantumChannel.unitaryConj
        (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm))

/-- Physically retain one nominated qubit from an arbitrary finite register,
using the same canonical finite enumeration as the sitewise tensor channel. -/
noncomputable def decodedRetryPoolQubitRegisterCoordinateChannel
    (ι : Type) [Fintype ι] [DecidableEq ι] (site : ι) :
    QuantumChannel (QubitRegister ι) QubitSpace :=
  QuantumChannel.comp
    (tensorPowerCoordinateOperator (Fintype.card ι) (Fintype.equivFin ι site))
    (QuantumChannel.unitaryConj
      (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm)

/-- Undoing the canonical finite-register transport sends a computational
basis vector to the recursive tensor basis with its exact inverse label. -/
@[simp] theorem decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis
    (ι : Type) [Fintype ι] [DecidableEq ι] (bits : Bitstring ι) :
    (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm
        (EuclideanSpace.basisFun (Bitstring ι) Complex bits) =
      tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
        (Fintype.card ι)
        ((decodedRetryPoolQubitTensorPowerBitstringEquiv ι).symm bits) := by
  apply (decodedRetryPoolQubitTensorPowerRegisterTransport ι).toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [(decodedRetryPoolQubitTensorPowerRegisterTransport ι).toLinearEquiv.apply_symm_apply]
  dsimp [decodedRetryPoolQubitTensorPowerRegisterTransport]
  rw [OrthonormalBasis.equiv_apply_basis]
  simp

/-- An inverse transported history stores exactly the original register bit
at the corresponding canonically enumerated site. -/
@[simp] theorem decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at
    (ι : Type) [Fintype ι] (bits : Bitstring ι)
    (coordinate : Fin (Fintype.card ι)) :
    tensorPowerHistoryAt (Fin 2) (Fintype.card ι)
        ((decodedRetryPoolQubitTensorPowerBitstringEquiv ι).symm bits) coordinate =
      bits ((Fintype.equivFin ι).symm coordinate) := by
  change tensorPowerHistoryAt (Fin 2) (Fintype.card ι)
      (tensorPowerHistoryOf (Fin 2) (Fintype.card ι)
        (fun trial => bits ((Fintype.equivFin ι).symm trial))) coordinate = _
  exact congrFun
    (tensorPowerHistoryAt_of (Fin 2) (Fintype.card ι)
      (fun trial => bits ((Fintype.equivFin ι).symm trial))) coordinate

/-- The canonical coordinate channel contracts every discarded
computational coordinate and retains the nominated one. -/
theorem decodedRetryPoolQubitRegisterCoordinateChannel_rankOne_basis
    (ι : Type) [Fintype ι] [DecidableEq ι] (site : ι)
    (left right : Bitstring ι) :
    decodedRetryPoolQubitRegisterCoordinateChannel ι site
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Bitstring ι) Complex left)
          (EuclideanSpace.basisFun (Bitstring ι) Complex right)).toLinearMap =
      (∏ coordinate : Fin (Fintype.card ι),
          if coordinate = Fintype.equivFin ι site then 1
          else inner Complex
            (EuclideanSpace.basisFun (Fin 2) Complex
              (right ((Fintype.equivFin ι).symm coordinate)))
            (EuclideanSpace.basisFun (Fin 2) Complex
              (left ((Fintype.equivFin ι).symm coordinate)))) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Fin 2) Complex (left site))
          (EuclideanSpace.basisFun (Fin 2) Complex (right site))).toLinearMap := by
  simp only [decodedRetryPoolQubitRegisterCoordinateChannel,
    QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne,
    decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis,
    decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis,
    tensorPowerCoordinateOperator_rankOne_basis]
  simp only [decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at,
    Equiv.symm_apply_apply]

/-- The canonical tensor-coordinate operation is exactly the genuine
singleton finite-subsystem partial trace and basis transport used for one
logical output port.  The equality holds for every input density, including
joint outputs with correlations between sibling logical ports. -/
theorem decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort
    (m w : Nat) (port : LogicalSite m w)
    (rho : DensityOperator (LogicalRegister m w)) :
    (decodedRetryPoolQubitRegisterCoordinateChannel
        (LogicalSite m w) port).mapDensity rho =
      (selectedLogicalPortTransport m w port).conjDensity
        ((selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister.mapDensity
          rho) := by
  apply DensityOperator.ext_toOperator
  simp only [QuantumChannel.mapDensity_toOperator,
    UnitaryTransport.conjDensity_toOperator]
  let sourceBasis := EuclideanSpace.basisFun
    (Bitstring (LogicalSite m w)) Complex
  let selectedChannel : QuantumChannel (LogicalRegister m w) QubitSpace :=
    QuantumChannel.comp
      (QuantumChannel.unitaryConj (selectedLogicalPortTransport m w port))
      (selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister
  have hselectedRankOne (left right : Bitstring (LogicalSite m w)) :
      selectedChannel
          (InnerProductSpace.rankOne Complex (sourceBasis left)
            (sourceBasis right)).toLinearMap =
        inner Complex
            (EuclideanSpace.basisFun
              (Bitstring
                (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
              Complex
              ((selectedLogicalPortSubsystem m w port).splitBitstring right).2)
            (EuclideanSpace.basisFun
              (Bitstring
                (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
              Complex
              ((selectedLogicalPortSubsystem m w port).splitBitstring left).2) •
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Fin 2) Complex (left port))
            (EuclideanSpace.basisFun (Fin 2) Complex (right port))).toLinearMap := by
    simp only [selectedChannel, FiniteSubsystem.selectedPartialTraceFromRegister,
      QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
    rw [QuditSubsystem.conjOperator_rankOne,
      FiniteSubsystem.registerFactorization_apply_basis,
      FiniteSubsystem.registerFactorization_apply_basis]
    rw [FiniteSubsystem.selectedPartialTrace_toLinearMap,
      QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
    rw [(selectedLogicalPortTransport m w port).conjOperatorLinearMap.map_smul]
    simp only [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [QuditSubsystem.conjOperator_rankOne]
    rw [selectedLogicalPortTransport_apply_basis,
      selectedLogicalPortTransport_apply_basis]
    rfl
  have hmaps :
      (decodedRetryPoolQubitRegisterCoordinateChannel
        (LogicalSite m w) port).toLinearMap = selectedChannel.toLinearMap := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis sourceBasis
    intro left right
    rw [decodedRetryPoolQubitRegisterCoordinateChannel_rankOne_basis]
    rw [hselectedRankOne]
    refine congrArg (fun scalar : Complex => scalar •
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex (left port))
        (EuclideanSpace.basisFun (Fin 2) Complex (right port))).toLinearMap) ?_
    by_cases hcomplement :
        ((selectedLogicalPortSubsystem m w port).splitBitstring right).2 =
          ((selectedLogicalPortSubsystem m w port).splitBitstring left).2
    · have hfactor (coordinate : Fin (Fintype.card (LogicalSite m w))) :
          (if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
            else inner Complex
              (EuclideanSpace.basisFun (Fin 2) Complex
                (right ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))
              (EuclideanSpace.basisFun (Fin 2) Complex
                (left ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))) = 1 := by
        by_cases hcoordinate : coordinate = Fintype.equivFin (LogicalSite m w) port
        · simp [hcoordinate]
        · have hsite :
              (Fintype.equivFin (LogicalSite m w)).symm coordinate ≠ port := by
            intro heq
            apply hcoordinate
            rw [← heq, Equiv.apply_symm_apply]
          let complement :
              (selectedLogicalPortSubsystem m w port).ComplementCoordinates :=
            ⟨(Fintype.equivFin (LogicalSite m w)).symm coordinate, by
              simpa [selectedLogicalPortSubsystem] using hsite⟩
          have hbit := congrFun hcomplement complement
          simp only [FiniteSubsystem.splitBitstring] at hbit
          have hbit' :
              right ((Fintype.equivFin (LogicalSite m w)).symm coordinate) =
                left ((Fintype.equivFin (LogicalSite m w)).symm coordinate) := by
            exact hbit
          rw [if_neg hcoordinate, hbit']
          rw [(EuclideanSpace.basisFun (Fin 2) Complex).inner_eq_ite]
          simp
      rw [Fintype.prod_eq_one _ hfactor]
      rw [(EuclideanSpace.basisFun
        (Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
        Complex).inner_eq_ite]
      rw [if_pos hcomplement]
    · have hexists : ∃ complement :
          (selectedLogicalPortSubsystem m w port).ComplementCoordinates,
          ((selectedLogicalPortSubsystem m w port).splitBitstring right).2 complement ≠
            ((selectedLogicalPortSubsystem m w port).splitBitstring left).2 complement := by
        by_contra hnone
        simp only [not_exists, not_not] at hnone
        apply hcomplement
        funext complement
        exact hnone complement
      obtain ⟨complement, hbit⟩ := hexists
      let coordinate : Fin (Fintype.card (LogicalSite m w)) :=
        Fintype.equivFin (LogicalSite m w) complement.1
      have hcoordinate :
          coordinate ≠ Fintype.equivFin (LogicalSite m w) port := by
        intro heq
        have hsite : (complement : LogicalSite m w) = port :=
          (Fintype.equivFin (LogicalSite m w)).injective heq
        exact complement.2 (by simp [selectedLogicalPortSubsystem, hsite])
      have hzero :
          (if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
            else inner Complex
              (EuclideanSpace.basisFun (Fin 2) Complex
                (right ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))
              (EuclideanSpace.basisFun (Fin 2) Complex
                (left ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))) = 0 := by
        simp only [hcoordinate, if_false, coordinate, Equiv.symm_apply_apply,
          (EuclideanSpace.basisFun (Fin 2) Complex).inner_eq_ite]
        simp only [FiniteSubsystem.splitBitstring] at hbit
        simp [hbit]
      have hproduct :
          (∏ coordinate : Fin (Fintype.card (LogicalSite m w)),
            if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
            else inner Complex
              (EuclideanSpace.basisFun (Fin 2) Complex
                (right ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))
              (EuclideanSpace.basisFun (Fin 2) Complex
                (left ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ coordinate) hzero
      rw [hproduct]
      rw [(EuclideanSpace.basisFun
        (Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
        Complex).inner_eq_ite]
      rw [if_neg hcomplement]
  change (decodedRetryPoolQubitRegisterCoordinateChannel
      (LogicalSite m w) port).toLinearMap rho.toOperator =
    selectedChannel.toLinearMap rho.toOperator
  exact LinearMap.congr_fun hmaps rho.toOperator

/-- A homogeneous sitewise channel cannot signal into a nominated coordinate:
the retained output is exactly the one-qubit channel applied to the true
retained input, even for a correlated register density. -/
theorem decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_sitewise
    (channel : QuantumChannel QubitSpace QubitSpace)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (site : ι) (rho : DensityOperator (QubitRegister ι)) :
    (decodedRetryPoolQubitRegisterCoordinateChannel ι site).mapDensity
        ((decodedRetryPoolQubitRegisterSitewiseChannel channel ι).mapDensity rho) =
      channel.mapDensity
        ((decodedRetryPoolQubitRegisterCoordinateChannel ι site).mapDensity rho) := by
  rw [decodedRetryPoolQubitRegisterSitewiseChannel,
    decodedRetryPoolQubitRegisterCoordinateChannel]
  simp only [QuantumChannel.comp_mapDensity]
  have hundoneInput :
      (QuantumChannel.unitaryConj
        (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm).mapDensity
          ((QuantumChannel.unitaryConj
            (decodedRetryPoolQubitTensorPowerRegisterTransport ι)).mapDensity
              ((decodedRetryPoolQubitChannelTensorPower channel
                (Fintype.card ι)).mapDensity
                ((QuantumChannel.unitaryConj
                  (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm).mapDensity
                    rho))) =
        (decodedRetryPoolQubitChannelTensorPower channel
          (Fintype.card ι)).mapDensity
          ((QuantumChannel.unitaryConj
            (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm).mapDensity rho) := by
    apply DensityOperator.ext_toOperator
    simp only [QuantumChannel.mapDensity_toOperator,
      QuantumChannel.unitaryConj_apply]
    exact (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm_conjOperator_conjOperator _
  rw [hundoneInput]
  rw [tensorPowerCoordinateOperator_mapDensity,
    tensorPowerCoordinateOperator_mapDensity]
  have hmarginal := tensorPower_channel_mapDensity_coordinate_marginal
    channel.toFiniteInstrument channel.toFiniteInstrument_complete
    (Fintype.card ι)
    ((QuantumChannel.unitaryConj
      (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm).mapDensity rho)
    (Fintype.equivFin ι site)
  have hchannel :
      (channel.toFiniteInstrument.kraus.toQuantumChannel
        channel.toFiniteInstrument_complete).mapDensity
          (tensorPowerInputMarginal (Fintype.card ι)
            ((QuantumChannel.unitaryConj
              (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm).mapDensity rho)
            (Fintype.equivFin ι site)) =
        channel.mapDensity
          (tensorPowerInputMarginal (Fintype.card ι)
            ((QuantumChannel.unitaryConj
              (decodedRetryPoolQubitTensorPowerRegisterTransport ι).symm).mapDensity rho)
            (Fintype.equivFin ι site)) := by
    apply DensityOperator.ext_toOperator
    exact LinearMap.congr_fun channel.toFiniteInstrument_inducedMap_eq _
  exact hmarginal.trans hchannel

/-- The one-qubit HH18 successor preparation: forget the A-basis measurement
result, then apply the inverse physical phase transport required by the next
inverse-T resource input. -/
noncomputable def decodedRetryPoolSuccessorOneQubitPreparation :
    QuantumChannel QubitSpace QubitSpace :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm)
    aBasisDephasing

/-- Pointwise action of the physical one-qubit successor preparation. -/
theorem decodedRetryPoolSuccessorOneQubitPreparation_mapDensity
    (rho : DensityOperator QubitSpace) :
    decodedRetryPoolSuccessorOneQubitPreparation.mapDensity rho =
      (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm.conjDensity
        (aBasisDephasing.mapDensity rho) := by
  apply DensityOperator.ext_toOperator
  rfl

/-- On an actual accepted logical output port, the physical channel is
exactly the established dephased inverse-phase next-input construction. -/
theorem decodedRetryPoolSuccessorOneQubitPreparation_selectedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    decodedRetryPoolSuccessorOneQubitPreparation.mapDensity
        (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port) =
      selectedLogicalPortDephasedNextInput h hdegree epsilon port := by
  apply DensityOperator.ext_toOperator
  rfl

/-- The complete sitewise physical preparation on the actual selected-output
register of one retry-pool stage. -/
noncomputable def decodedRetryPoolSuccessorPreparationChannel
    (m w z q : Nat) (stage : Fin z) :
    QuantumChannel
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :=
  decodedRetryPoolQubitRegisterSitewiseChannel
    decodedRetryPoolSuccessorOneQubitPreparation
    (decodedRetryPoolSuccessorSourceSlots m w z q stage)

end HH18Parameterized
end Distillation
end QEC
