import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Schedule.BackwardSchedule

/-!
# Parameterized HH18 decoded retry-pool successor routing

This internal layer routes every selected output coordinate of one
nonterminal retry-pool stage into the full next-stage input coordinate grid.
The route is a lossless finite reindexing derived from the compiled backward
schedule equation.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit

attribute [local instance 100] Fintype.ofFinite

/-- The selected output coordinates available at one forward retry-pool stage. -/
abbrev decodedRetryPoolSuccessorSourceSlots (m w z q : Nat) (stage : Fin z) :=
  Fin (decodedRetryPoolBackwardSchedule m w z q stage) × LogicalSite m w

/-- The branch-grouped physical input coordinates of the immediate successor
stage. -/
abbrev decodedRetryPoolSuccessorTargetSlots
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  LogicalSite m w ×
    (Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
      PhysicalSite m w)

/-- The selected-block index at one nonterminal stage is equivalently an
actual next retry-attempt index paired with one physical input coordinate. -/
noncomputable def decodedRetryPoolSuccessorAttemptSlotsEquiv
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Fin (decodedRetryPoolBackwardSchedule m w z q stage) ≃
      Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
        PhysicalSite m w := by
  have hcount : decodedRetryPoolBackwardSchedule m w z q stage =
      decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩ *
        physicalInputCount m w := by
    calc
      decodedRetryPoolBackwardSchedule m w z q stage =
          physicalInputCount m w *
            decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩ :=
        decodedRetryPoolBackwardSchedule_required_eq_physicalInputCount_mul_attempt_succ
          m w z q stage hstage
      _ = decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩ *
          physicalInputCount m w := Nat.mul_comm _ _
  let physicalEquiv : Fin (physicalInputCount m w) ≃ PhysicalSite m w := by
    simpa [physicalInputCount] using (Fintype.equivFin (PhysicalSite m w)).symm
  exact (finCongr hcount).trans
    (finProdFinEquiv.symm.trans
      (Equiv.prodCongr (Equiv.refl _) physicalEquiv))

/-- The full selected-output route preserves the selected logical branch and
reindexes its selected block coordinate into one next retry attempt and one
physical input. -/
noncomputable def decodedRetryPoolSuccessorSlotEquiv
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    decodedRetryPoolSuccessorSourceSlots m w z q stage ≃
      decodedRetryPoolSuccessorTargetSlots m w z q stage hstage :=
  (Equiv.prodCongr
    (decodedRetryPoolSuccessorAttemptSlotsEquiv m w z q stage hstage)
    (Equiv.refl _)).trans (Equiv.prodComm _ _)

/-- The selected logical branch is retained by the full coordinate route. -/
@[simp] theorem decodedRetryPoolSuccessorSlotEquiv_fst
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (selected : Fin (decodedRetryPoolBackwardSchedule m w z q stage))
    (port : LogicalSite m w) :
    (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage (selected, port)).1 = port :=
  rfl

/-- Routing a selected coordinate forward and back is exact. -/
@[simp] theorem decodedRetryPoolSuccessorSlotEquiv_roundtrip
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (source : decodedRetryPoolSuccessorSourceSlots m w z q stage) :
    (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage).symm
      (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage source) = source :=
  (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage).symm_apply_apply source

/-- Routing a successor coordinate back and forward is exact. -/
@[simp] theorem decodedRetryPoolSuccessorSlotEquiv_roundtrip_symm
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (target : decodedRetryPoolSuccessorTargetSlots m w z q stage hstage) :
    decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage
      ((decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage).symm target) = target :=
  (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage).apply_symm_apply target

/-- The selected-output coordinate carrier has its literal selected-block and
logical-port cardinality. -/
theorem decodedRetryPoolSuccessorSourceSlots_card
    (m w z q : Nat) (stage : Fin z) :
    Fintype.card (decodedRetryPoolSuccessorSourceSlots m w z q stage) =
      decodedRetryPoolBackwardSchedule m w z q stage * logicalOutputCount m w := by
  simp [logicalOutputCount]

/-- The successor coordinate carrier has one logical branch for each next
retry attempt and each physical input coordinate. -/
theorem decodedRetryPoolSuccessorTargetSlots_card
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Fintype.card (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage) =
      logicalOutputCount m w *
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩ *
          physicalInputCount m w) := by
  simp [logicalOutputCount, physicalInputCount]

/-- The derived lossless route proves equality of the source and successor
coordinate cardinalities. -/
theorem decodedRetryPoolSuccessorSlots_card_eq
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Fintype.card (decodedRetryPoolSuccessorSourceSlots m w z q stage) =
      Fintype.card (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage) :=
  Fintype.card_congr (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage)

/-- The next retry-attempt and physical-input coordinate selected by one
output block at a fixed logical branch. -/
noncomputable def decodedRetryPoolSuccessorNextTrialInput
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (selected : Fin (decodedRetryPoolBackwardSchedule m w z q stage)) :
    Fin (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) ×
      PhysicalSite m w :=
  (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage (selected, port)).2

/-- Distinct selected blocks at a fixed logical branch route to distinct
next-stage trial coordinates. -/
theorem decodedRetryPoolSuccessorNextTrialInput_injective
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    Function.Injective
      (decodedRetryPoolSuccessorNextTrialInput m w z q stage hstage port) := by
  intro left right hroute
  have hwhole :
      decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage (left, port) =
        decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage (right, port) := by
    apply Prod.ext
    · simp
    · exact hroute
  have hpairs : (left, port) = (right, port) :=
    (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage).injective hwhole
  exact congrArg Prod.fst hpairs

/-- Unequal selected blocks at a fixed logical branch retain distinct
next-stage trial coordinates. -/
theorem decodedRetryPoolSuccessorNextTrialInput_ne_of_ne
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    {left right : Fin (decodedRetryPoolBackwardSchedule m w z q stage)}
    (hne : left ≠ right) :
    decodedRetryPoolSuccessorNextTrialInput m w z q stage hstage port left ≠
      decodedRetryPoolSuccessorNextTrialInput m w z q stage hstage port right := by
  intro hroute
  exact hne (decodedRetryPoolSuccessorNextTrialInput_injective
    m w z q stage hstage port hroute)

/-- The computational-basis labels of the selected-output register and the
successor register are reindexed by the derived coordinate route. -/
noncomputable def decodedRetryPoolSuccessorBitstringEquiv
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Qubit.Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage) ≃
      Qubit.Bitstring (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage) where
  toFun := fun bits target =>
    bits ((decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage).symm target)
  invFun := fun bits source =>
    bits (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage source)
  left_inv := by
    intro bits
    funext source
    simp
  right_inv := by
    intro bits
    funext target
    simp

/-- The basis-preserving unitary transport of the complete selected-output
register into the complete branch-grouped successor register. -/
noncomputable def decodedRetryPoolSuccessorRegisterTransport
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    UnitaryTransport
      (Qubit.QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (Qubit.QubitRegister (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) := by
  let sourceBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage)) Complex
  let targetBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) Complex
  let U := sourceBasis.equiv targetBasis
    (decodedRetryPoolSuccessorBitstringEquiv m w z q stage hstage)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The register transport maps every selected-output computational basis
vector to the computational basis vector of its exact successor coordinates. -/
@[simp] theorem decodedRetryPoolSuccessorRegisterTransport_apply_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorRegisterTransport m w z q stage hstage
      (EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage)) Complex bits) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) Complex
        (decodedRetryPoolSuccessorBitstringEquiv m w z q stage hstage bits) := by
  dsimp [decodedRetryPoolSuccessorRegisterTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- The unitary channel realizing the complete successor-register reindexing. -/
noncomputable def decodedRetryPoolSuccessorReindexChannel
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    QuantumChannel
      (Qubit.QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (Qubit.QubitRegister (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) :=
  QuantumChannel.unitaryConj
    (decodedRetryPoolSuccessorRegisterTransport m w z q stage hstage)

/-- The reindex channel acts by conjugation with the derived basis-preserving
unitary transport. -/
@[simp] theorem decodedRetryPoolSuccessorReindexChannel_apply
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (Qubit.QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage))) :
    decodedRetryPoolSuccessorReindexChannel m w z q stage hstage A =
      (decodedRetryPoolSuccessorRegisterTransport m w z q stage hstage).conjOperator A :=
  rfl

/-- The complete successor reindexing sends every source computational matrix
unit to the corresponding target computational matrix unit. -/
theorem decodedRetryPoolSuccessorReindexChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (left right : Qubit.Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorReindexChannel m w z q stage hstage
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorSourceSlots m w z q stage))
            Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (decodedRetryPoolSuccessorSourceSlots m w z q stage))
            Complex right)).toLinearMap =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun
          (Qubit.Bitstring
            (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
          Complex
          (decodedRetryPoolSuccessorBitstringEquiv
            m w z q stage hstage left))
        (EuclideanSpace.basisFun
          (Qubit.Bitstring
            (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
          Complex
          (decodedRetryPoolSuccessorBitstringEquiv
            m w z q stage hstage right))).toLinearMap := by
  let sourceBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) Complex
  let targetBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) Complex
  let transport := decodedRetryPoolSuccessorRegisterTransport
    m w z q stage hstage
  have hleft :
      transport (sourceBasis left) =
        targetBasis (decodedRetryPoolSuccessorBitstringEquiv
          m w z q stage hstage left) := by
    exact decodedRetryPoolSuccessorRegisterTransport_apply_basis
      m w z q stage hstage left
  have hright :
      transport (sourceBasis right) =
        targetBasis (decodedRetryPoolSuccessorBitstringEquiv
          m w z q stage hstage right) := by
    exact decodedRetryPoolSuccessorRegisterTransport_apply_basis
      m w z q stage hstage right
  change transport.conjOperator
      (InnerProductSpace.rankOne Complex
        (sourceBasis left) (sourceBasis right)).toLinearMap = _
  calc
    _ = (InnerProductSpace.rankOne Complex
          (transport (sourceBasis left))
          (transport (sourceBasis right))).toLinearMap :=
      QuditSubsystem.conjOperator_rankOne transport
        (sourceBasis left) (sourceBasis right)
    _ = _ := congrArg₂
      (fun x y => (InnerProductSpace.rankOne Complex x y).toLinearMap)
      hleft hright

end HH18Parameterized
end Distillation
end QEC
