import QEC.Distillation.LowOverheadProtocol.Parameterized.DepthTwoRouting

/-!
# Parameterized HH18 recursively indexed fresh routing

This internal layer records finite selected-port paths and the exact sequence
of domain-certified physical rates reached along such a path.  At each
successor step it forms a finite pool of indexed copies of the actual
one-level run, routes one selected/dephased output from each parent through
the depth-two transpose, and obtains the actual child run at the next rate.

The parent index records provenance only.  Neither a probability space nor an
independence claim between distinct pool elements or output paths is added
here.  This module stops before target-error limits, overhead, yields, or any
terminal family packaging.
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

/-- A finite address of one physical resource slot at each routed depth. -/
abbrev routedDepthInputSlots (m w depth : Nat) :=
  Fin depth → Fin (physicalInputCount m w)

/-- A finite address of one selected logical output port at each routed depth. -/
abbrev routedDepthOutputSlots (m w depth : Nat) :=
  Fin depth → LogicalSite m w

/-- The exact cardinality of the finite routed physical-input address carrier. -/
theorem routedDepthInputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthInputSlots m w depth) =
      physicalInputCount m w ^ depth := by
  simp [routedDepthInputSlots]

/-- The exact cardinality of the finite routed logical-output address carrier. -/
theorem routedDepthOutputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthOutputSlots m w depth) =
      logicalOutputCount m w ^ depth := by
  simp [routedDepthOutputSlots, logicalOutputCount]

/-- Adding one physical resource coordinate multiplies the actual routed
input-address count by the actual block input count. -/
theorem routedDepthInputSlots_card_succ (m w depth : Nat) :
    Fintype.card (routedDepthInputSlots m w (depth + 1)) =
      Fintype.card (routedDepthInputSlots m w depth) * physicalInputCount m w := by
  rw [routedDepthInputSlots_card, routedDepthInputSlots_card]
  exact pow_succ _ _

/-- Adding one selected-port coordinate multiplies the actual routed
output-address count by the actual block logical-output count. -/
theorem routedDepthOutputSlots_card_succ (m w depth : Nat) :
    Fintype.card (routedDepthOutputSlots m w (depth + 1)) =
      Fintype.card (routedDepthOutputSlots m w depth) * logicalOutputCount m w := by
  rw [routedDepthOutputSlots_card, routedDepthOutputSlots_card]
  exact pow_succ _ _

/-- The unique empty selected-port path. -/
def routedDepthOutputPathEmpty (m w : Nat) : routedDepthOutputSlots m w 0 :=
  fun index => Fin.elim0 index

/-- Append one selected logical port to a finite routed output address. -/
def routedDepthOutputPathAppend (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (port : LogicalSite m w) :
    routedDepthOutputSlots m w (depth + 1) :=
  Fin.lastCases port path

/-- A prefix-indexed physical transpose acts locally on the actual parent
output and child-input grids. -/
def routedDepthSuccessorRouting (m w depth : Nat) :
    routedDepthOutputSlots m w depth × depthTwoParentOutputSlots m w ≃
      routedDepthOutputSlots m w depth × depthTwoChildInputSlots m w :=
  Equiv.prodCongr (Equiv.refl _) (depthTwoRouting m w)

@[simp] theorem routedDepthSuccessorRouting_apply (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth)
    (parent : Fin (physicalInputCount m w)) (port : LogicalSite m w) :
    routedDepthSuccessorRouting m w depth (pathPrefix, (parent, port)) =
      (pathPrefix, (port, parent)) :=
  rfl

/-- The source slot supplying a named physical input of one prefix-indexed
child. -/
def routedDepthChildInputSlot (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth) (child : LogicalSite m w)
    (parent : Fin (physicalInputCount m w)) :
    routedDepthOutputSlots m w depth × depthTwoChildInputSlots m w :=
  routedDepthSuccessorRouting m w depth
    (pathPrefix, DependentBatch.childInputSlot child parent)

@[simp] theorem routedDepthChildInputSlot_apply (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth) (child : LogicalSite m w)
    (parent : Fin (physicalInputCount m w)) :
    routedDepthChildInputSlot m w depth pathPrefix child parent =
      (pathPrefix, (child, parent)) :=
  rfl

/-- Inputs of a fixed prefix-indexed child come from distinct parent indices. -/
theorem routedDepthChildInputSlot_injective (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth) (child : LogicalSite m w) :
    Function.Injective (routedDepthChildInputSlot m w depth pathPrefix child) := by
  intro left right hroute
  apply depthTwoChildInputSlot_injective m w child
  exact congrArg Prod.snd hroute

/-- A recursively indexed actual-rate path.  Each successor constructor
carries the exact `[0, 1/2]` witness required to feed its selected dephased
parent output back into the inverse-T HH18 input frame. -/
inductive RoutedDepthState {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (depth : Nat) → routedDepthOutputSlots m w depth →
      HH18NoisyInput.DiagonalErrorRate → Type
  | root : RoutedDepthState h hdegree epsilon 0
      (routedDepthOutputPathEmpty m w) epsilon
  | succ {depth : Nat} {path : routedDepthOutputSlots m w depth}
      {rate : HH18NoisyInput.DiagonalErrorRate}
      (previous : RoutedDepthState h hdegree epsilon depth path rate)
      (port : LogicalSite m w)
      (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
      RoutedDepthState h hdegree epsilon (depth + 1)
        (routedDepthOutputPathAppend m w depth path port)
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf)

/-- The actual one-level decoded run at the rate indexed by a finite routed
state.  The state constrains the rate/path provenance; the run itself remains
the actual resource-consuming one-level construction. -/
noncomputable def routedDepthActualRun {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (_state : RoutedDepthState h hdegree epsilon depth path rate) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  resourceDecodedRun h hdegree (noisyResources m w rate)

/-- The root of the recursively indexed construction is exactly the actual
one-level run at the original physical input rate. -/
theorem routedDepthActualRun_root {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    routedDepthActualRun h hdegree (RoutedDepthState.root (h := h)
      (hdegree := hdegree) (epsilon := epsilon)) =
      resourceDecodedRun h hdegree (noisyResources m w epsilon) :=
  rfl

/-- A finite pool of indexed copies of one actual parent run.  Indices record
which parent supplies a child input; this definition makes no independence
assertion about the indexed copies. -/
noncomputable def routedDepthFreshParentPool {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate) :
    Fin (physicalInputCount m w) →
      DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  fun _parent => routedDepthActualRun h hdegree state

/-- Each indexed fresh-parent pool entry is the actual current routed-depth
run, with the index retained solely as provenance. -/
theorem routedDepthFreshParentPool_apply {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (parent : Fin (physicalInputCount m w)) :
    routedDepthFreshParentPool h hdegree state parent =
      routedDepthActualRun h hdegree state :=
  rfl

/-- The actual A-dephased selected output of an indexed parent in a routed
finite-depth pool. -/
noncomputable def routedDepthFreshParentDephasedOutput {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (source : depthTwoParentOutputSlots m w) : DensityOperator QubitSpace :=
  aBasisDephasing.mapDensity
    ((selectedLogicalPortTransport m w source.2).conjDensity
      ((selectedLogicalPortSubsystem m w source.2).selectedPartialTraceFromRegister.mapDensity
        (routedDepthFreshParentPool h hdegree state source.1).acceptedOutput))

/-- The indexed-pool dephased output is exactly the existing actual
depth-two parent-output dephasing at the routed state rate. -/
theorem routedDepthFreshParentDephasedOutput_eq_depthTwoFreshParentDephasedOutput
    {w r m depth : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (source : depthTwoParentOutputSlots m w) :
    routedDepthFreshParentDephasedOutput h hdegree state source =
      depthTwoFreshParentDephasedOutput h hdegree rate source :=
  rfl

/-- The inverse-S transported physical input supplied by one indexed fresh
parent output at a routed finite depth. -/
noncomputable def routedDepthFreshParentNextInput {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (source : depthTwoParentOutputSlots m w) : DensityOperator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).symm.conjDensity
    (routedDepthFreshParentDephasedOutput h hdegree state source)

/-- The actual inverse-S routed input has precisely the noisy inverse-T
resource density at the selected port's explicit next rate. -/
theorem routedDepthFreshParentNextInput_eq_noisyTInvResource
    {w r m depth : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (parent : Fin (physicalInputCount m w)) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthFreshParentNextInput h hdegree state (parent, port) =
      HH18NoisyInput.noisyTInvResource
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf) := by
  change depthTwoFreshParentNextInput h hdegree rate (parent, port) = _
  exact depthTwoFreshParentNextInput_eq_noisyTInvResource h hdegree rate
    (parent, port) hhalf

/-- The actual child resources obtained from the routed finite-depth parent
pool.  Each child input uses the same selected port and a distinct parent
index through the literal depth-two transpose. -/
noncomputable def routedDepthChildResources {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (_hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    ResourceInput (physicalInputCount m w) QubitSpace :=
  fun parent => routedDepthFreshParentNextInput h hdegree state
    ((depthTwoRouting m w).symm (depthTwoChildInputSlot m w port parent))

/-- Every physical input of a fixed routed child has its explicit parent-port
provenance: the child port is fixed and only the fresh parent index varies. -/
@[simp] theorem routedDepthChildResources_apply {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2)
    (parent : Fin (physicalInputCount m w)) :
    routedDepthChildResources h hdegree state port hhalf parent =
      routedDepthFreshParentNextInput h hdegree state (parent, port) :=
  rfl

/-- The routed finite-depth child resources agree definitionally with the
already-proved actual depth-two construction at the state rate. -/
theorem routedDepthChildResources_eq_depthTwoChildResources {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthChildResources h hdegree state port hhalf =
      depthTwoChildResources h hdegree rate port hhalf := by
  rfl

/-- The finite-depth child resources are exactly the ordinary HH18 noisy
resource family at the explicitly witnessed next physical rate. -/
theorem routedDepthChildResources_eq_noisyResources {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthChildResources h hdegree state port hhalf =
      noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf) := by
  rw [routedDepthChildResources_eq_depthTwoChildResources]
  exact depthTwoChildResources_eq_noisyResources h hdegree rate port hhalf

/-- The actual decoded child run formed from an indexed fresh parent pool. -/
noncomputable def routedDepthChildRun {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  resourceDecodedRun h hdegree (routedDepthChildResources h hdegree state port hhalf)

/-- The child run of a routed state is the ordinary actual one-level run at
the selected port's exact next physical rate. -/
theorem routedDepthChildRun_eq_resourceDecodedRun {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthChildRun h hdegree state port hhalf =
      resourceDecodedRun h hdegree (noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf)) := by
  unfold routedDepthChildRun
  rw [routedDepthChildResources_eq_noisyResources]

/-- The accepted Born mass of every explicitly constructed routed child run
is positive at its domain-certified successor rate. -/
theorem routedDepthChildRun_success_pos {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    0 < (routedDepthChildRun h hdegree state port hhalf).successProbability := by
  rw [routedDepthChildRun_eq_resourceDecodedRun]
  exact endpointWeight_accepted_pos h hdegree
    (selectedLogicalPortNextInputRate h hdegree rate port hhalf)

/-- The recursive child run is exactly the actual run indexed by the
successor state, not a surrogate rate-only execution. -/
theorem routedDepthChildRun_eq_successor {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthChildRun h hdegree state port hhalf =
      routedDepthActualRun h hdegree (RoutedDepthState.succ state port hhalf) := by
  rw [routedDepthChildRun_eq_resourceDecodedRun]
  rfl

/-- The successor state's HH18 physical input rate is exactly the literal
negative-A Born error of its selected parent port. -/
theorem routedDepthSuccessorRate_eq_rawError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    (selectedLogicalPortNextInputRate h hdegree rate port hhalf).1 =
      selectedLogicalPortRawError h hdegree rate port := by
  rfl

/-- The recurrence's next physical rate inherits the compiled selected-port
residual bridge directly, with no target-error or asymptotic conclusion. -/
theorem routedDepthSuccessorRate_le_two_mul_acceptedResidual {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    (selectedLogicalPortNextInputRate h hdegree rate port hhalf).1 ≤
      2 * acceptedResidualError h hdegree rate := by
  change selectedLogicalPortRawError h hdegree rate port ≤ _
  exact selectedLogicalPortRawError_le_two_mul_acceptedResidual h hdegree rate port

end HH18Parameterized
end Distillation
end QEC
