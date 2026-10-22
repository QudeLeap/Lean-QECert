import QEC.Distillation.Core.DependentBatch
import QEC.Distillation.LowOverheadProtocol.Parameterized.ResourceMeasurement
import QEC.Distillation.LowOverheadProtocol.Parameterized.SelectedPort

/-!
# Parameterized HH18 depth-two fresh-parent routing

This module routes actual selected, A-dephased outputs of indexed fresh
parameterized HH18 parent runs into one second-level child run per logical
port.  The finite transpose ensures that the physical inputs of any one child
come from distinct parent indices.  The indices record provenance only: this
module makes no independence assertion between parent executions or distinct
child ports.

The selected A-basis error rate is first required explicitly to lie in HH18's
native `0 ≤ ε ≤ 1/2` input domain.  The inverse physical `S` transport then
returns the dephased A resource to the inverse-T frame consumed by the child.
This module stops at depth two; it has no recursive schedule, yield, terminal
overhead, or terminal accounting conclusion.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit

attribute [local instance 100] Fintype.ofFinite

/-- One actual selected logical port of each indexed fresh parent run. -/
abbrev depthTwoParentOutputSlots (m w : Nat) :=
  Fin (physicalInputCount m w) × LogicalSite m w

/-- The resource-input slots of one child, indexed by its selected parent
logical port and the distinct fresh parent supplying that input. -/
abbrev depthTwoChildInputSlots (m w : Nat) :=
  LogicalSite m w × Fin (physicalInputCount m w)

/-- The actual parent-output to child-input route is the literal finite
transpose.  It does not imply any relation between different child ports. -/
def depthTwoRouting (m w : Nat) :
    depthTwoParentOutputSlots m w ≃ depthTwoChildInputSlots m w :=
  DependentBatch.parentPortTranspose
    (Fin (physicalInputCount m w)) (LogicalSite m w)

@[simp] theorem depthTwoRouting_apply (m w : Nat)
    (parent : Fin (physicalInputCount m w)) (port : LogicalSite m w) :
    depthTwoRouting m w (parent, port) = (port, parent) :=
  rfl

/-- The exact number of actual parent-output slots in the depth-two grid. -/
theorem depthTwoParentOutputSlots_card (m w : Nat) :
    Fintype.card (depthTwoParentOutputSlots m w) =
      physicalInputCount m w * logicalOutputCount m w := by
  simp [depthTwoParentOutputSlots, logicalOutputCount]

/-- The exact number of actual child-input slots in the transposed grid. -/
theorem depthTwoChildInputSlots_card (m w : Nat) :
    Fintype.card (depthTwoChildInputSlots m w) =
      logicalOutputCount m w * physicalInputCount m w := by
  simp [depthTwoChildInputSlots, logicalOutputCount]

/-- The source slot supplying one physical input of a fixed child. -/
def depthTwoChildInputSlot (m w : Nat) (child : LogicalSite m w)
    (parent : Fin (physicalInputCount m w)) : depthTwoChildInputSlots m w :=
  depthTwoRouting m w (DependentBatch.childInputSlot child parent)

@[simp] theorem depthTwoChildInputSlot_apply (m w : Nat)
    (child : LogicalSite m w) (parent : Fin (physicalInputCount m w)) :
    depthTwoChildInputSlot m w child parent = (child, parent) :=
  rfl

/-- A fixed child receives its physical inputs from pairwise distinct parent
indices. -/
theorem depthTwoChildInputSlot_injective (m w : Nat)
    (child : LogicalSite m w) :
    Function.Injective (depthTwoChildInputSlot m w child) := by
  intro left right hroute
  apply DependentBatch.childInputSlot_injective child
  apply (depthTwoRouting m w).injective
  exact hroute

/-- The selected A-basis Born rate, certified by an explicit upper-bound
witness to be admissible as a new HH18 diagonal inverse-T input rate. -/
noncomputable def selectedLogicalPortNextInputRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2) :
    HH18NoisyInput.DiagonalErrorRate :=
  ⟨selectedLogicalPortRawError h hdegree epsilon port,
    selectedLogicalPortRawError_nonneg h hdegree epsilon port, hhalf⟩

/-- The A-basis parameter of the domain-certified child input is exactly the
literal measured selected-port parameter. -/
theorem aBasisErrorParameter_selectedLogicalPortNextInputRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2) :
    aBasisErrorParameter
      (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf) =
      selectedLogicalPortRawParameter h hdegree epsilon port := by
  rfl

/-- The inverse physical `S` transport returns a dephased selected output to
the inverse-T resource frame consumed by a child block. -/
noncomputable def selectedLogicalPortDephasedNextInput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    DensityOperator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm.conjDensity
    (selectedLogicalPortDephasedOutput h hdegree epsilon port)

/-- The actual inverse-transported, dephased selected output is exactly the
noisy inverse-T resource at its explicitly domain-certified measured rate. -/
theorem selectedLogicalPortDephasedNextInput_eq_noisyTInvResource {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2) :
    selectedLogicalPortDephasedNextInput h hdegree epsilon port =
      HH18NoisyInput.noisyTInvResource
        (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf) := by
  rw [selectedLogicalPortDephasedNextInput,
    selectedLogicalPortDephasedOutput_eq_diagonalAResource,
    ← aBasisErrorParameter_selectedLogicalPortNextInputRate h hdegree epsilon port hhalf,
    ← rotateTInvResource_noisy]
  apply DensityOperator.ext_toOperator
  simp only [rotateTInvResource, UnitaryTransport.conjDensity_toOperator,
    UnitaryTransport.symm_conjOperator_conjOperator]

/-- An indexed copy of the actual one-level parent execution.  The index
records resource provenance and makes no independence assertion. -/
noncomputable def depthTwoFreshParentRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (_parent : Fin (physicalInputCount m w)) :=
  resourceDecodedRun h hdegree (noisyResources m w epsilon)

/-- The actual transported and A-dephased selected output of one indexed
fresh parent execution. -/
noncomputable def depthTwoFreshParentDephasedOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w) : DensityOperator QubitSpace :=
  aBasisDephasing.mapDensity
    ((selectedLogicalPortTransport m w source.2).conjDensity
      ((selectedLogicalPortSubsystem m w source.2).selectedPartialTraceFromRegister.mapDensity
        (depthTwoFreshParentRun h hdegree epsilon source.1).acceptedOutput))

/-- The dephased output of an indexed parent is the literal selected-port
dephasing of the actual one-level parameterized parent run. -/
theorem depthTwoFreshParentDephasedOutput_eq_selectedLogicalPortDephasedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w) :
    depthTwoFreshParentDephasedOutput h hdegree epsilon source =
      selectedLogicalPortDephasedOutput h hdegree epsilon source.2 := by
  rfl

/-- The actual inverse-T resource supplied by one indexed fresh parent
output after selected-port dephasing. -/
noncomputable def depthTwoFreshParentNextInput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w) : DensityOperator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm.conjDensity
    (depthTwoFreshParentDephasedOutput h hdegree epsilon source)

/-- A routed fresh parent source supplies exactly the homogeneous noisy
inverse-T resource at the measured rate of its selected logical port. -/
theorem depthTwoFreshParentNextInput_eq_noisyTInvResource {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon source.2 ≤ 1 / 2) :
    depthTwoFreshParentNextInput h hdegree epsilon source =
      HH18NoisyInput.noisyTInvResource
        (selectedLogicalPortNextInputRate h hdegree epsilon source.2 hhalf) := by
  rw [depthTwoFreshParentNextInput,
    depthTwoFreshParentDephasedOutput_eq_selectedLogicalPortDephasedOutput]
  exact selectedLogicalPortDephasedNextInput_eq_noisyTInvResource
    h hdegree epsilon source.2 hhalf

/-- The `n` actual physical resources supplied to a fixed second-level child:
one inverse-transported, dephased selected output from each distinct fresh
parent run, all at that child's fixed selected logical port. -/
noncomputable def depthTwoChildResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (_hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    ResourceInput (physicalInputCount m w) QubitSpace :=
  fun parent => depthTwoFreshParentNextInput h hdegree epsilon
    ((depthTwoRouting m w).symm (depthTwoChildInputSlot m w child parent))

/-- Each input of a fixed child records its exact fresh-parent provenance:
the same child port and the nominated distinct parent index. -/
@[simp] theorem depthTwoChildResources_apply {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (parent : Fin (physicalInputCount m w)) :
    depthTwoChildResources h hdegree epsilon child hhalf parent =
      depthTwoFreshParentNextInput h hdegree epsilon (parent, child) :=
  rfl

/-- The actual distinct-parent child resource family is exactly the ordinary
parameterized HH18 noisy-resource family at the child's measured rate. -/
theorem depthTwoChildResources_eq_noisyResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    depthTwoChildResources h hdegree epsilon child hhalf =
      noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) := by
  funext parent
  change depthTwoFreshParentNextInput h hdegree epsilon (parent, child) =
    HH18NoisyInput.noisyTInvResource
      (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf)
  exact depthTwoFreshParentNextInput_eq_noisyTInvResource h hdegree epsilon
    (parent, child) hhalf

/-- The actual second-level decoded child run built from routed fresh parent
outputs. -/
noncomputable def depthTwoChildRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :=
  resourceDecodedRun h hdegree (depthTwoChildResources h hdegree epsilon child hhalf)

/-- The routed actual child run is exactly the ordinary one-level
parameterized run at its derived physical input rate. -/
theorem depthTwoChildRun_eq_resourceDecodedRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    depthTwoChildRun h hdegree epsilon child hhalf =
      resourceDecodedRun h hdegree (noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf)) := by
  unfold depthTwoChildRun
  rw [depthTwoChildResources_eq_noisyResources]

/-- The actual accepted Born mass of the routed child is positive. -/
theorem depthTwoChildRun_success_pos {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    0 < (depthTwoChildRun h hdegree epsilon child hhalf).successProbability := by
  rw [depthTwoChildRun_eq_resourceDecodedRun]
  exact endpointWeight_accepted_pos h hdegree
    (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf)

/-- The physical selected output of a second-level routed child run. -/
noncomputable def depthTwoChildSelectedPortOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) : DensityOperator QubitSpace :=
  (selectedLogicalPortTransport m w port).conjDensity
    ((selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister.mapDensity
      (depthTwoChildRun h hdegree epsilon child hhalf).acceptedOutput)

/-- The actual selected child output is the established one-level selected
output at the derived physical input rate. -/
theorem depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    depthTwoChildSelectedPortOutput h hdegree epsilon child hhalf port =
      selectedLogicalPortTransportedAcceptedOutput h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port := by
  unfold depthTwoChildSelectedPortOutput
  rw [depthTwoChildRun_eq_resourceDecodedRun]
  rfl

/-- The literal negative-A Born error of an actual selected depth-two child
output. -/
noncomputable def depthTwoChildSelectedPortRawError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) : ℝ :=
  aBasisInstrument.bornWeight .negative
    (depthTwoChildSelectedPortOutput h hdegree epsilon child hhalf port)

/-- The selected child Born error is exactly the one-level selected-port
Born error at the child's derived physical input rate. -/
theorem depthTwoChildSelectedPortRawError_eq_selectedLogicalPortRawError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    depthTwoChildSelectedPortRawError h hdegree epsilon child hhalf port =
      selectedLogicalPortRawError h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port := by
  unfold depthTwoChildSelectedPortRawError
  rw [depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput]
  rfl

/-- The second application of the compiled selected-port error bridge, at the
actual derived child input rate. -/
theorem depthTwoChildSelectedPortRawError_le_two_mul_acceptedResidual
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    depthTwoChildSelectedPortRawError h hdegree epsilon child hhalf port ≤
      2 * acceptedResidualError h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) := by
  rw [depthTwoChildSelectedPortRawError_eq_selectedLogicalPortRawError]
  exact selectedLogicalPortRawError_le_two_mul_acceptedResidual h hdegree
    (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port

/-- The two depth-two selected-port inequalities are precisely two separate
applications of the compiled one-step bridge: first to the parent port, then
to a selected child port at the derived input rate. -/
theorem depthTwoSelectedPortRawError_twoStepBounds {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree epsilon child ≤
        2 * acceptedResidualError h hdegree epsilon ∧
      depthTwoChildSelectedPortRawError h hdegree epsilon child hhalf port ≤
        2 * acceptedResidualError h hdegree
          (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) :=
  ⟨selectedLogicalPortRawError_le_two_mul_acceptedResidual h hdegree epsilon child,
    depthTwoChildSelectedPortRawError_le_two_mul_acceptedResidual h hdegree epsilon
      child hhalf port⟩

end HH18Parameterized
end Distillation
end QEC
