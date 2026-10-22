import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Measurement

/-!
# Parameterized HH18 decoded retry-pool successor regrouping

This internal physical layer first applies the complete A-basis measurement-
record preparation at every retained selected-output site, then converts the
complete flat successor register into the literal nested tensor carrier
consumed by the next retry-pool layer.  The later routing and regrouping are
basis-preserving unitaries: no coordinate is discarded, no state is replaced,
and no independence or probability claim is introduced.
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

/-- The actual logical-site carrier, identified with the finite outer tensor
factor used by the literal nested successor input. -/
noncomputable def decodedRetryPoolLogicalSiteFinEquiv (m w : Nat) :
    LogicalSite m w ≃ Fin (logicalOutputCount m w) := by
  simpa only [logicalOutputCount] using Fintype.equivFin (LogicalSite m w)

/-- The complete next-stage input carrier: one literal retry-pool input for
each logical output branch of the preceding stage. -/
abbrev decodedRetryPoolSuccessorNestedInputCarrier
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  tensorPowerCarrier
    (tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w)

/-- Regroup the flat branch/trial/physical bit labels into the exact nested
outer-branch and inner-trial tensor histories. -/
noncomputable def decodedRetryPoolSuccessorRegroupBitstringEquiv
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Qubit.Bitstring (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage) ≃
      tensorPowerHistory
        (tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
        (logicalOutputCount m w) := by
  let branchEquiv := decodedRetryPoolLogicalSiteFinEquiv m w
  let innerEquiv := tensorPowerQubitBitstringEquiv (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
  let outerEquiv := tensorPowerHistoryEquiv
    (tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w)
  refine
    { toFun := fun bits =>
        outerEquiv.symm (fun branch =>
          innerEquiv.symm (fun coordinate =>
            bits (branchEquiv.symm branch, coordinate)))
      invFun := fun history coordinate =>
        innerEquiv (outerEquiv history (branchEquiv coordinate.1)) coordinate.2
      left_inv := ?_
      right_inv := ?_ }
  · intro bits
    funext coordinate
    rcases coordinate with ⟨branch, coordinate⟩
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  · intro history
    apply outerEquiv.injective
    funext branch
    apply innerEquiv.injective
    funext coordinate
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Coordinate-level meaning of the regrouping: outer tensor factor, inner
trial, and physical-site evaluation reads exactly the original flat bit. -/
@[simp] theorem decodedRetryPoolSuccessorRegroupBitstringEquiv_apply_at
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
    (branch : Fin (logicalOutputCount m w))
    (trial : Fin
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
    (physical : PhysicalSite m w) :
    tensorPowerHistoryAt (Qubit.Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (tensorPowerHistoryAt
        (tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
        (logicalOutputCount m w)
        (decodedRetryPoolSuccessorRegroupBitstringEquiv m w z q stage hstage bits)
        branch)
      trial physical =
    bits ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch,
      (trial, physical)) := by
  let innerEquiv := tensorPowerQubitBitstringEquiv (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
  let branchEquiv := decodedRetryPoolLogicalSiteFinEquiv m w
  let outerEquiv := tensorPowerHistoryEquiv
    (tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w)
  have houter :
      tensorPowerHistoryAt
        (tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
        (logicalOutputCount m w)
        (decodedRetryPoolSuccessorRegroupBitstringEquiv m w z q stage hstage bits)
        branch =
      innerEquiv.symm (fun coordinate =>
        bits (branchEquiv.symm branch, coordinate)) := by
    have hdefinition :
        decodedRetryPoolSuccessorRegroupBitstringEquiv m w z q stage hstage bits =
          outerEquiv.symm (fun branch =>
            innerEquiv.symm (fun coordinate =>
              bits (branchEquiv.symm branch, coordinate))) := rfl
    change outerEquiv
      (decodedRetryPoolSuccessorRegroupBitstringEquiv m w z q stage hstage bits)
      branch = _
    rw [hdefinition]
    exact congrFun (outerEquiv.apply_symm_apply _) branch
  rw [houter]
  calc
    tensorPowerHistoryAt (Qubit.Bitstring (PhysicalSite m w))
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (innerEquiv.symm (fun coordinate =>
          bits ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch, coordinate)))
        trial physical =
      innerEquiv
        (innerEquiv.symm (fun coordinate =>
          bits ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch, coordinate)))
        (trial, physical) := by
          symm
          exact tensorPowerQubitBitstringEquiv_apply (PhysicalSite m w)
            (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
            (innerEquiv.symm (fun coordinate =>
              bits ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch, coordinate)))
            trial physical
    _ = _ := by simp only [Equiv.apply_symm_apply]

/-- The complete inner-trial history carried by one successor branch, read
directly from its flat branch/trial/physical record. -/
noncomputable def decodedRetryPoolSuccessorPortTrialHistory
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
    (branch : Fin (logicalOutputCount m w)) :
    tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) :=
  (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)).symm
      (fun coordinate =>
        bits ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch, coordinate))

/-- Selecting an outer history after regrouping retains exactly the complete
flat trial/physical record of the corresponding logical port. -/
theorem decodedRetryPoolSuccessorRegroupBitstringEquiv_historyAt
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
    (branch : Fin (logicalOutputCount m w)) :
    tensorPowerHistoryAt
        (tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
        (logicalOutputCount m w)
        (decodedRetryPoolSuccessorRegroupBitstringEquiv
          m w z q stage hstage bits) branch =
      decodedRetryPoolSuccessorPortTrialHistory
        m w z q stage hstage bits branch := by
  apply (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)).injective
  funext coordinate
  rcases coordinate with ⟨trial, physical⟩
  rw [tensorPowerQubitBitstringEquiv_apply,
    decodedRetryPoolSuccessorRegroupBitstringEquiv_apply_at]
  simp only [decodedRetryPoolSuccessorPortTrialHistory,
    Equiv.apply_symm_apply]

/-- The basis-preserving unitary that physically regroups the flat successor
register into the literal nested next-stage retry-pool input carrier. -/
noncomputable def decodedRetryPoolSuccessorRegroupTransport
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    UnitaryTransport
      (Qubit.QubitRegister
        (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
      (decodedRetryPoolSuccessorNestedInputCarrier m w z q stage hstage) := by
  let flatBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) Complex
  let nestedBasis := tensorPowerBasis
    (tensorPowerBasis
      (EuclideanSpace.basisFun (Qubit.Bitstring (PhysicalSite m w)) Complex)
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w)
  let U := flatBasis.equiv nestedBasis
    (decodedRetryPoolSuccessorRegroupBitstringEquiv m w z q stage hstage)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The regrouping transport maps every flat computational basis vector to
the corresponding literal nested tensor basis vector. -/
@[simp] theorem decodedRetryPoolSuccessorRegroupTransport_apply_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) :
    decodedRetryPoolSuccessorRegroupTransport m w z q stage hstage
      (EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
        Complex bits) =
      tensorPowerBasis
        (tensorPowerBasis
          (EuclideanSpace.basisFun (Qubit.Bitstring (PhysicalSite m w)) Complex)
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
        (logicalOutputCount m w)
        (decodedRetryPoolSuccessorRegroupBitstringEquiv m w z q stage hstage bits) := by
  dsimp [decodedRetryPoolSuccessorRegroupTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- The unitary channel realizing complete successor-register regrouping. -/
noncomputable def decodedRetryPoolSuccessorRegroupChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    QuantumChannel
      (Qubit.QubitRegister
        (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
      (decodedRetryPoolSuccessorNestedInputCarrier m w z q stage hstage) :=
  QuantumChannel.unitaryConj
    (decodedRetryPoolSuccessorRegroupTransport m w z q stage hstage)

/-- The regrouping channel acts by conjugation with its basis-preserving
unitary. -/
@[simp] theorem decodedRetryPoolSuccessorRegroupChannel_apply
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (Qubit.QubitRegister
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))) :
    decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage A =
      (decodedRetryPoolSuccessorRegroupTransport m w z q stage hstage).conjOperator A :=
  rfl

/-- Regrouping sends a flat computational matrix unit to the corresponding
nested computational matrix unit. -/
theorem decodedRetryPoolSuccessorRegroupChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (left right : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) :
    decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
            Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
            Complex right)).toLinearMap =
      (InnerProductSpace.rankOne Complex
        (tensorPowerBasis
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩))
          (logicalOutputCount m w)
          (decodedRetryPoolSuccessorRegroupBitstringEquiv
            m w z q stage hstage left))
        (tensorPowerBasis
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩))
          (logicalOutputCount m w)
          (decodedRetryPoolSuccessorRegroupBitstringEquiv
            m w z q stage hstage right))).toLinearMap := by
  let flatBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) Complex
  let nestedBasis := tensorPowerBasis
    (tensorPowerBasis
      (EuclideanSpace.basisFun
        (Qubit.Bitstring (PhysicalSite m w)) Complex)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w)
  let transport := decodedRetryPoolSuccessorRegroupTransport
    m w z q stage hstage
  have hleft :
      transport (flatBasis left) =
        nestedBasis (decodedRetryPoolSuccessorRegroupBitstringEquiv
          m w z q stage hstage left) := by
    exact decodedRetryPoolSuccessorRegroupTransport_apply_basis
      m w z q stage hstage left
  have hright :
      transport (flatBasis right) =
        nestedBasis (decodedRetryPoolSuccessorRegroupBitstringEquiv
          m w z q stage hstage right) := by
    exact decodedRetryPoolSuccessorRegroupTransport_apply_basis
      m w z q stage hstage right
  change transport.conjOperator
      (InnerProductSpace.rankOne Complex
        (flatBasis left) (flatBasis right)).toLinearMap = _
  calc
    _ = (InnerProductSpace.rankOne Complex
          (transport (flatBasis left))
          (transport (flatBasis right))).toLinearMap :=
      QuditSubsystem.conjOperator_rankOne transport
        (flatBasis left) (flatBasis right)
    _ = (InnerProductSpace.rankOne Complex
          (nestedBasis
            (decodedRetryPoolSuccessorRegroupBitstringEquiv
              m w z q stage hstage left))
          (nestedBasis
            (decodedRetryPoolSuccessorRegroupBitstringEquiv
              m w z q stage hstage right))).toLinearMap := by
      exact congrArg₂
        (fun x y =>
          (InnerProductSpace.rankOne Complex x y).toLinearMap)
        hleft hright

/-- Retain one complete logical branch from the physically regrouped successor
register.  All other branches are genuinely discarded by partial trace. -/
noncomputable def decodedRetryPoolSuccessorRegroupBranchChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (branch : Fin (logicalOutputCount m w)) :
    QuantumChannel
      (Qubit.QubitRegister
        (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) :=
  QuantumChannel.comp
    (tensorPowerCoordinateOperator (logicalOutputCount m w) branch)
    (decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage)

/-- On a flat computational matrix unit, the physical outer-branch selector
retains the exact trial/physical record at that logical port and contracts
every discarded logical branch by its full computational-basis inner product. -/
theorem decodedRetryPoolSuccessorRegroupBranchChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (branch : Fin (logicalOutputCount m w))
    (left right : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) :
    decodedRetryPoolSuccessorRegroupBranchChannel
        m w z q stage hstage branch
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
            Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
            Complex right)).toLinearMap =
      (∏ coordinate : Fin (logicalOutputCount m w),
          if coordinate = branch then 1
          else inner Complex
            (tensorPowerBasis
              (EuclideanSpace.basisFun
                (Qubit.Bitstring (PhysicalSite m w)) Complex)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)
              (decodedRetryPoolSuccessorPortTrialHistory
                m w z q stage hstage right coordinate))
            (tensorPowerBasis
              (EuclideanSpace.basisFun
                (Qubit.Bitstring (PhysicalSite m w)) Complex)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)
              (decodedRetryPoolSuccessorPortTrialHistory
                m w z q stage hstage left coordinate))) •
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)
            (decodedRetryPoolSuccessorPortTrialHistory
              m w z q stage hstage left branch))
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)
            (decodedRetryPoolSuccessorPortTrialHistory
              m w z q stage hstage right branch))).toLinearMap := by
  simp only [decodedRetryPoolSuccessorRegroupBranchChannel,
    QuantumChannel.comp_apply]
  rw [decodedRetryPoolSuccessorRegroupChannel_rankOne_basis,
    tensorPowerCoordinateOperator_rankOne_basis]
  simp_rw [decodedRetryPoolSuccessorRegroupBitstringEquiv_historyAt]

/-- The recursive successor-trial history selected from a routed source label
is exactly the fixed logical port's selected-block record, reindexed through
the compiled attempt/physical-slot equivalence. -/
theorem decodedRetryPoolSuccessorPortTrialHistory_reindex
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage))
    (branch : Fin (logicalOutputCount m w)) :
    decodedRetryPoolSuccessorPortTrialHistory m w z q stage hstage
        (decodedRetryPoolSuccessorBitstringEquiv
          m w z q stage hstage bits) branch =
      (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm
        (fun coordinate =>
          bits
            ((decodedRetryPoolSuccessorAttemptSlotsEquiv
              m w z q stage hstage).symm coordinate,
              (decodedRetryPoolLogicalSiteFinEquiv m w).symm branch)) := by
  apply (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩)).injective
  funext coordinate
  simp only [decodedRetryPoolSuccessorPortTrialHistory,
    Equiv.apply_symm_apply]
  rfl

/-- Retain one complete logical successor branch after the exact global
selected-block reindex and physical regrouping. -/
noncomputable def decodedRetryPoolSuccessorRoutedBranchChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (branch : Fin (logicalOutputCount m w)) :
    QuantumChannel
      (Qubit.QubitRegister
        (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)) :=
  QuantumChannel.comp
    (decodedRetryPoolSuccessorRegroupBranchChannel
      m w z q stage hstage branch)
    (decodedRetryPoolSuccessorReindexChannel m w z q stage hstage)

/-- On a source computational matrix unit, the routed successor selector
retains precisely the fixed logical port across all selected parent blocks;
all other logical ports contribute only their exact discarded-basis inner
products. -/
theorem decodedRetryPoolSuccessorRoutedBranchChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (branch : Fin (logicalOutputCount m w))
    (left right : Qubit.Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorRoutedBranchChannel
        m w z q stage hstage branch
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorSourceSlots m w z q stage))
            Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorSourceSlots m w z q stage))
            Complex right)).toLinearMap =
      (∏ coordinate : Fin (logicalOutputCount m w),
          if coordinate = branch then 1
          else inner Complex
            (tensorPowerBasis
              (EuclideanSpace.basisFun
                (Qubit.Bitstring (PhysicalSite m w)) Complex)
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
              (EuclideanSpace.basisFun
                (Qubit.Bitstring (PhysicalSite m w)) Complex)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)
              ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
                (decodedRetryPoolBackwardAttempts m w z q
                  ⟨stage.1 + 1, hstage⟩)).symm
                (fun target => left
                  ((decodedRetryPoolSuccessorAttemptSlotsEquiv
                    m w z q stage hstage).symm target,
                    (decodedRetryPoolLogicalSiteFinEquiv m w).symm coordinate))))) •
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)
            ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)).symm
              (fun target => left
                ((decodedRetryPoolSuccessorAttemptSlotsEquiv
                  m w z q stage hstage).symm target,
                  (decodedRetryPoolLogicalSiteFinEquiv m w).symm branch))))
          (tensorPowerBasis
            (EuclideanSpace.basisFun
              (Qubit.Bitstring (PhysicalSite m w)) Complex)
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)
            ((tensorPowerQubitBitstringEquiv (PhysicalSite m w)
              (decodedRetryPoolBackwardAttempts m w z q
                ⟨stage.1 + 1, hstage⟩)).symm
              (fun target => right
                ((decodedRetryPoolSuccessorAttemptSlotsEquiv
                  m w z q stage hstage).symm target,
                  (decodedRetryPoolLogicalSiteFinEquiv m w).symm branch))))).toLinearMap := by
  simp only [decodedRetryPoolSuccessorRoutedBranchChannel,
    QuantumChannel.comp_apply]
  rw [decodedRetryPoolSuccessorReindexChannel_rankOne_basis,
    decodedRetryPoolSuccessorRegroupBranchChannel_rankOne_basis]
  simp_rw [decodedRetryPoolSuccessorPortTrialHistory_reindex]

/-- The complete physical handoff channel: measure and record every selected
output site in the established A basis, route each record to its successor
slot, then regroup all branches into the literal nested input consumed by the
next retry-pool layer. -/
noncomputable def decodedRetryPoolSuccessorNestedInputChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    QuantumChannel
      (Qubit.QubitRegister
        (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (decodedRetryPoolSuccessorNestedInputCarrier m w z q stage hstage) :=
  QuantumChannel.comp
    (decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage)
    (QuantumChannel.comp
      (decodedRetryPoolSuccessorReindexChannel m w z q stage hstage)
      (decodedRetryPoolSuccessorRecordPreparationChannel m w z q stage))

/-- The physical handoff is exactly sitewise preparation, reindexing, then
regrouping. -/
@[simp] theorem decodedRetryPoolSuccessorNestedInputChannel_apply
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (Qubit.QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage))) :
    decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage A =
      decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage
        (decodedRetryPoolSuccessorReindexChannel m w z q stage hstage
          (decodedRetryPoolSuccessorRecordPreparationChannel m w z q stage A)) :=
  rfl

end HH18Parameterized
end Distillation
end QEC
