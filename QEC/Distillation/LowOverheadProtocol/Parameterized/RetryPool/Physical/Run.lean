import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.SuccessLowerBound
import QEC.Distillation.Core.FiniteInstrumentBinaryRun
import QEC.Semantics.Instruments.NestedTensor.PowerBasis
/-!
# Genuine arbitrary-depth physical HH18 retry-pool run

This layer packages the already-constructed complete physical retry instrument
as a `DistillationRun`.  Its resource family consists of actual independently
noisy one-block HH18 inputs; preparation forms their literal tensor product.
The success probability and accepted conditional output are therefore derived
from the same binary coarsening of the physical instrument, rather than being
stored as protocol metadata.
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

/-- The canonical normalized density on the one-dimensional tensor unit. -/
noncomputable def decodedRetryPoolTensorUnitDensity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : DensityOperator (tensorPowerCarrier H 0) :=
  DensityOperator.pureDensity
    (tensorPowerBasis (stdOrthonormalBasis Complex H) 0 PUnit.unit) (by
      rw [show ‖tensorPowerBasis (stdOrthonormalBasis Complex H) 0 PUnit.unit‖ = 1 from
        (tensorPowerBasis (stdOrthonormalBasis Complex H) 0).norm_eq_one PUnit.unit]
      norm_num)

/-- The homogeneous family of actual noisy one-qubit inverse-`T` resources
consumed at the root of a positive-depth retry schedule. -/
noncomputable def decodedRetryPoolPhysicalProtocolNoisyResources
    (m w z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    Fin (physicalInputCount m w *
      decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) →
      DensityOperator QubitSpace :=
  fun _ => HH18NoisyInput.noisyTInvResource epsilon

/-- Prepare an arbitrary family of physical HH18 blocks by a literal finite
tensor product.  The recursion uses every supplied resource coordinate. -/
noncomputable def decodedRetryPoolPhysicalProtocolPrepareBlocks
    {m w : Nat}
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (attempts : Nat) →
    (Fin attempts → DensityOperator (PhysicalRegister m w)) →
      DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)
  | 0, _ => rhoUnit
  | attempts + 1, inputs =>
      DensityOperator.tensorDensity (inputs 0)
        (decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit attempts
          (fun trial => inputs trial.succ))

/-- On a homogeneous resource family the recursive preparation is exactly the
named product density used throughout the physical success proof. -/
theorem decodedRetryPoolPhysicalProtocolPrepareBlocks_constant
    {m w attempts : Nat}
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (rho : DensityOperator (PhysicalRegister m w)) :
    decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit attempts
        (fun _ : Fin attempts => rho) =
      tensorPowerProductInput rho rhoUnit attempts := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      change DensityOperator.tensorDensity rho
          (decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit attempts
            (fun _ : Fin attempts => rho)) =
        DensityOperator.tensorDensity rho
          (tensorPowerProductInput rho rhoUnit attempts)
      rw [ih]

/-- Group a flat family of raw one-qubit resources into the actual measured
HH18 blocks and then form their literal root tensor product. -/
noncomputable def decodedRetryPoolPhysicalProtocolPrepareResources
    (m w attempts : Nat)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (inputs : Fin (physicalInputCount m w * attempts) → DensityOperator QubitSpace) :
    DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts) :=
  decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit attempts fun trial =>
    prepareMeasuredResources m w fun site =>
      inputs (finProdFinEquiv (site, trial))

/-- The actual flat noisy resource family prepares precisely the genuine root
input used by the complete retry-protocol Born-mass theorems. -/
theorem decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources
    (m w z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalProtocolPrepareResources m w
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) rhoUnit
        (decodedRetryPoolPhysicalProtocolNoisyResources m w z q hz epsilon) =
      decodedRetryPoolPhysicalProtocolNoisyRootInput m w z q hz epsilon
        rhoUnit := by
  change decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit _
      (fun _ => prepareMeasuredResources m w (noisyResources m w epsilon)) = _
  exact decodedRetryPoolPhysicalProtocolPrepareBlocks_constant rhoUnit
    (prepareMeasuredResources m w (noisyResources m w epsilon))

/-- A concrete terminal density used only to totalize zero-mass conditional
branches at the `DistillationRun` interface. -/
private def decodedRetryPoolNestedConstantHistory
    {alpha : Type*} (value : alpha) (branches : Nat) :
    (depth : Nat) → nestedTensorHistory alpha branches depth
  | 0 => value
  | depth + 1 =>
      decodedRetryPoolNestedConstantHistory
        (tensorPowerHistoryOf alpha branches (fun _ => value)) branches depth

private def decodedRetryPoolPhysicalProtocolFallbackLabel
    (m w z q : Nat) (hz : 0 < z) :
    nestedTensorHistory
      (Bitstring
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
      (logicalOutputCount m w) (z - 1) := by
  let zeroWord :
      Bitstring
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w) :=
    fun _ => 0
  exact decodedRetryPoolNestedConstantHistory zeroWord
    (logicalOutputCount m w) (z - 1)

noncomputable def decodedRetryPoolPhysicalProtocolFallback
    (m w z q : Nat) (hz : 0 < z) :
    DensityOperator (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz) :=
  DensityOperator.pureDensity
    (nestedTensorBasis
      (EuclideanSpace.basisFun
        (Bitstring
          (Fin (decodedRetryPoolBackwardSchedule m w z q
            (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
        Complex)
      (logicalOutputCount m w) (z - 1)
      (decodedRetryPoolPhysicalProtocolFallbackLabel m w z q hz)) (by
        rw [OrthonormalBasis.norm_eq_one]
        norm_num)

/-- The genuine positive-depth physical HH18 retry-pool run.  It is obtained
by binary coarsening the complete physical finite instrument on its literal
global routing-success event. -/
noncomputable def decodedRetryPoolPhysicalProtocolRun
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DistillationRun QubitSpace
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz)
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz) :=
  binaryDistillationRun
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
    (decodedRetryPoolPhysicalProtocolInstrument_complete h hdegree z q hz)
    (physicalInputCount m w *
      decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
    (decodedRetryPoolPhysicalProtocolNoisyResources m w z q hz epsilon)
    (decodedRetryPoolPhysicalProtocolPrepareResources m w
      (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) rhoUnit)
    (decodedRetryPoolPhysicalProtocolFallback m w z q hz)

@[simp] theorem decodedRetryPoolPhysicalProtocolRun_resourceCount
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalProtocolRun
      h hdegree epsilon z q hz rhoUnit).resourceCount =
      physicalInputCount m w *
        decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ :=
  rfl

@[simp] theorem decodedRetryPoolPhysicalProtocolRun_successProbability
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalProtocolRun
        h hdegree epsilon z q hz rhoUnit).successProbability =
      decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz
        (decodedRetryPoolPhysicalProtocolNoisyRootInput m w z q hz epsilon
          rhoUnit) := by
  change decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz
      (decodedRetryPoolPhysicalProtocolPrepareResources m w
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) rhoUnit
        (decodedRetryPoolPhysicalProtocolNoisyResources m w z q hz epsilon)) = _
  rw [decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources]

/-- The run's accepted conditional density is exactly the normalized accepted
branch of the same binary-coarsened physical instrument. -/
theorem decodedRetryPoolPhysicalProtocolRun_acceptedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalProtocolRun
      h hdegree epsilon z q hz rhoUnit).acceptedOutput =
      binaryCoarsenCompletion
        (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
        (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput m w z q hz epsilon
          rhoUnit)
        (decodedRetryPoolPhysicalProtocolFallback m w z q hz) .accepted := by
  change binaryCoarsenCompletion _ _
      (decodedRetryPoolPhysicalProtocolPrepareResources m w
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) rhoUnit
        (decodedRetryPoolPhysicalProtocolNoisyResources m w z q hz epsilon)) _ _ = _
  rw [decodedRetryPoolPhysicalProtocolPrepareResources_noisyResources]

/-- The derived physical success bound applies directly to the genuine run. -/
theorem decodedRetryPoolPhysicalProtocolRun_success_three_quarters_le
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (3 / 4 : Real) <=
      (decodedRetryPoolPhysicalProtocolRun
        h hdegree epsilon z q hz rhoUnit).successProbability := by
  rw [decodedRetryPoolPhysicalProtocolRun_successProbability]
  exact decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_three_quarters_le
    h hdegree epsilon hpool z q hz rhoUnit

/-- In particular the genuine physical run has strictly positive success. -/
theorem decodedRetryPoolPhysicalProtocolRun_success_pos
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    0 < (decodedRetryPoolPhysicalProtocolRun
      h hdegree epsilon z q hz rhoUnit).successProbability := by
  have hthree := decodedRetryPoolPhysicalProtocolRun_success_three_quarters_le
    h hdegree epsilon hpool z q hz rhoUnit
  norm_num at hthree ⊢
  linarith

end HH18Parameterized
end Distillation
end QEC
