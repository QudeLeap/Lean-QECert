import QEC.Distillation.LowOverheadProtocol.Parameterized.Preparation
import QEC.Distillation.Triorthogonal.NoisyInjection
import QEC.Distillation.LowOverheadProtocol.Core.PhaseInjection
import QEC.Semantics.Entropy.Purification
/-!
# Parameterized HH18 physical resource measurement

This layer physically consumes the supplied one-qubit resources only through
the sitewise `S` rotation and established A-basis instrument. It records the
complete finite physical-error word on one named symbolic support, proves its
product probabilities and Bernoulli specialization, and prepares the
normalized word record. It stops before any Kraus consumer channel.
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

attribute [local instance 100] Fintype.ofFinite

/-- A `T†` phase-basis error outcome, read through the existing A-basis
instrument after the physical rotation. -/
def resourceOutcome (error : ZMod 2) : StabilizerOutcome :=
  if error = 0 then .positive else .negative

/-- The physical `S` rotation that maps the `T†` resource basis to the
established A-basis measurement. -/
noncomputable def rotateTInvResource (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).conjDensity rho

/-- The physical rotation sends a clean inverse-T resource to the positive
A-basis eigenstate. -/
theorem rotateTInvResource_clean :
    rotateTInvResource (HH18NoisyInput.tInvResourceErrorDensity 0) =
      Triorthogonal.BH12NoisyInjection.OneQubit.aZeroDensity := by
  apply DensityOperator.ext_toOperator
  rw [rotateTInvResource, UnitaryTransport.conjDensity_toOperator,
    HH18NoisyInput.tInvResourceErrorDensity_zero_eq_phaseStateDensity,
    OneQubitMagic.phaseStateDensity_toOperator,
    QuditSubsystem.conjOperator_rankOne,
    OneQubitMagic.phaseShiftTransport_apply,
    OneQubitMagic.phaseShiftOperator_phaseState,
    Triorthogonal.BH12NoisyInjection.OneQubit.aZeroDensity,
    OneQubitMagic.phaseStateDensity_toOperator]
  congr 1; ring_nf

/-- The same physical rotation sends a diagonal-Z-error inverse-T resource to
the negative A-basis eigenstate. -/
theorem rotateTInvResource_error :
    rotateTInvResource (HH18NoisyInput.tInvResourceErrorDensity 1) =
      Triorthogonal.BH12NoisyInjection.OneQubit.aOneDensity := by
  apply DensityOperator.ext_toOperator
  rw [rotateTInvResource, UnitaryTransport.conjDensity_toOperator,
    HH18PhaseInjection.tInvErrorResourceDensity_eq_phaseStateDensity,
    OneQubitMagic.phaseStateDensity_toOperator,
    QuditSubsystem.conjOperator_rankOne,
    OneQubitMagic.phaseShiftTransport_apply,
    OneQubitMagic.phaseShiftOperator_phaseState,
    Triorthogonal.BH12NoisyInjection.OneQubit.aOneDensity_rankOne,
    Triorthogonal.BH12NoisyInjection.OneQubit.aOneState_eq_pauliZ,
    Triorthogonal.BH12NoisyInjection.OneQubit.aZeroState,
    HH18PhaseInjection.pauliZ_phaseState_eq_phaseState_add_pi]
  congr 1
  all_goals
    simp [HH18PhaseInjection.tInvErrorAngle, HH18PhaseInjection.tInvIdealAngle]
    ring_nf

/-- The A-basis error parameter inherited exactly from one diagonal inverse-T
resource-error rate. -/
def aBasisErrorParameter (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    Triorthogonal.BH12NoisyInjection.ErrorParameter where
  rate := epsilon.1
  rate_nonneg := epsilon.property.1
  rate_le_one := by linarith [epsilon.property.2]

/-- Rotating the actual noisy inverse-T resource yields the existing A-basis
diagonal mixture with the same physical error rate. -/
theorem rotateTInvResource_noisy
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rotateTInvResource (HH18NoisyInput.noisyTInvResource epsilon) =
      Triorthogonal.BH12NoisyInjection.OneQubit.diagonalAResource
        (aBasisErrorParameter epsilon) := by
  apply DensityOperator.ext_toOperator
  rw [rotateTInvResource, UnitaryTransport.conjDensity_toOperator,
    HH18NoisyInput.noisyTInvResource]
  simp only [DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
  rw [map_sum]
  simp_rw [map_smul, UnitaryTransport.conjOperatorLinearMap_apply]
  have hclean := congrArg DensityOperator.toOperator rotateTInvResource_clean
  have herror := congrArg DensityOperator.toOperator rotateTInvResource_error
  simp only [rotateTInvResource, UnitaryTransport.conjDensity_toOperator] at hclean herror
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
  rw [Finset.sum_insert, Finset.sum_singleton]
  · rw [hclean, herror,
      Triorthogonal.BH12NoisyInjection.OneQubit.diagonalAResource_toOperator]
    simp [aBasisErrorParameter,
      Triorthogonal.BH12NoisyInjection.ErrorParameter.cleanWeight,
      HH18NoisyInput.bitErrorWeight]
    norm_cast
  · simp

/-- The product probability of observing one complete physical-error word
from a supplied parameterized resource family. -/
noncomputable def measuredErrorWordProbability (m w : Nat)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (error : PhysicalErrorWord m w) : ℝ :=
  ∏ site, Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument.bornWeight
    (resourceOutcome (error site))
    (rotateTInvResource (inputs (resourceSiteEquiv m w site)))

theorem measuredErrorWordProbability_nonneg (m w : Nat)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (error : PhysicalErrorWord m w) :
    0 ≤ measuredErrorWordProbability m w inputs error := by
  unfold measuredErrorWordProbability
  apply Finset.prod_nonneg
  intro site _hsite
  exact Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_weight_nonneg _ _

/-- The unique named finite support shared by every parameterized
physical-error-word sum. -/
noncomputable def physicalErrorWords (m w : Nat) : Finset (PhysicalErrorWord m w) :=
  Finset.univ

@[simp] theorem mem_physicalErrorWords (m w : Nat) (error : PhysicalErrorWord m w) :
    error ∈ physicalErrorWords m w :=
  Finset.mem_univ error

theorem physicalErrorWords_card (m w : Nat) :
    (physicalErrorWords m w).card = Fintype.card (PhysicalErrorWord m w) :=
  rfl

/-- The measured word probabilities are normalized over the one named
symbolic physical-error support. -/
theorem sum_measuredErrorWordProbability (m w : Nat)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    (physicalErrorWords m w).sum
      (fun error => measuredErrorWordProbability m w inputs error) = 1 := by
  classical
  have h := Finset.sum_prod_piFinset
    (R := ℝ) (ι := PhysicalSite m w) (κ := ZMod 2) (s := Finset.univ)
    (g := fun site bit =>
      Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument.bornWeight
        (resourceOutcome bit)
        (rotateTInvResource (inputs (resourceSiteEquiv m w site))))
  have hsite (site : PhysicalSite m w) :
      ∑ bit : ZMod 2,
        Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument.bornWeight
          (resourceOutcome bit)
          (rotateTInvResource (inputs (resourceSiteEquiv m w site))) = 1 := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    simpa [resourceOutcome] using
      Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_weight_sum
        (rotateTInvResource (inputs (resourceSiteEquiv m w site)))
  simp_rw [hsite] at h
  simpa [physicalErrorWords, measuredErrorWordProbability] using h

/-- Measuring the literal independent parameterized inverse-T resource family
recovers its exact product Bernoulli error-word law. -/
theorem measuredErrorWordProbability_noisyResources (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord m w) :
    measuredErrorWordProbability m w (noisyResources m w epsilon) error =
      HH18NoisyInput.errorWordWeight epsilon error := by
  unfold measuredErrorWordProbability HH18NoisyInput.errorWordWeight
  apply Finset.prod_congr rfl
  intro site _hsite
  by_cases herror : error site = 0
  · simp [noisyResources, HH18NoisyInput.noisyTInvResources,
      resourceOutcome, herror, rotateTInvResource_noisy,
      Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_diagonalAResource_weight,
      aBasisErrorParameter,
      Triorthogonal.BH12NoisyInjection.ErrorParameter.cleanWeight,
      HH18NoisyInput.bitErrorWeight]
  · simp [noisyResources, HH18NoisyInput.noisyTInvResources,
      resourceOutcome, herror, rotateTInvResource_noisy,
      Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_diagonalAResource_weight,
      aBasisErrorParameter,
      HH18NoisyInput.bitErrorWeight]

/-- The computational record of one observed parameterized physical-error
word. -/
def errorWordBasisState (m w : Nat) (error : PhysicalErrorWord m w) :
    PhysicalRegister m w :=
  EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex
    ((PauliSymplectic.bitstringWordEquiv (PhysicalSite m w)).symm error)

theorem errorWordBasisState_normSq (m w : Nat) (error : PhysicalErrorWord m w) :
    ‖errorWordBasisState m w error‖ ^ 2 = 1 := by
  simp [errorWordBasisState]

/-- The normalized classical physical-register record of one observed error
word. -/
noncomputable def errorWordBasisDensity (m w : Nat) (error : PhysicalErrorWord m w) :
    DensityOperator (PhysicalRegister m w) :=
  DensityOperator.pureDensity (errorWordBasisState m w error)
    (errorWordBasisState_normSq m w error)

/-- The actual normalized density which records a complete sitewise resource
measurement of the supplied family. -/
noncomputable def prepareMeasuredResources (m w : Nat)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    DensityOperator (PhysicalRegister m w) :=
  DensityOperator.convexCombination (physicalErrorWords m w)
    (measuredErrorWordProbability m w inputs) (errorWordBasisDensity m w)
    (fun error _ => measuredErrorWordProbability_nonneg m w inputs error)
    (sum_measuredErrorWordProbability m w inputs)

@[simp] theorem prepareMeasuredResources_toOperator (m w : Nat)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    (prepareMeasuredResources m w inputs).toOperator =
      (physicalErrorWords m w).sum (fun error =>
        (measuredErrorWordProbability m w inputs error : Complex) •
          (errorWordBasisDensity m w error).toOperator) := by
  simp [prepareMeasuredResources, DensityOperator.convexCombinationOperator]

/-- The actual corrected physical state selected by a measured resource-error
word, applied to the inverse physical-`T` target. -/
noncomputable def errorBranchState {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w) :
    PhysicalRegister m w :=
  HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree)

private theorem physicalTInvBranch_norm {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) : ‖physicalTInvBranch h hdegree‖ = 1 := by
  change ‖(HH18PuncturedReedMuller.physicalTInv w m).toLinearIsometryEquiv
    (encodedLogicalPlus h)‖ = 1
  rw [(HH18PuncturedReedMuller.physicalTInv w m).toLinearIsometryEquiv.norm_map]
  change ‖(HH18PuncturedReedMuller.encodedCode h).encoding (logicalPlus m w)‖ = 1
  rw [(HH18PuncturedReedMuller.encodedCode h).encoding.norm_map]
  exact logicalPlus_norm m w

/-- Every selected physical-error branch is normalized. -/
theorem errorBranchState_normSq {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w) :
    ‖errorBranchState h hdegree error‖ ^ 2 = 1 := by
  have hinner : inner Complex (errorBranchState h hdegree error)
      (errorBranchState h hdegree error) = 1 := by
    simp only [errorBranchState, HH18NoisyInput.zErrorOperator]
    rw [← LinearMap.adjoint_inner_left]
    have hunit := PauliSymplectic.toQubitOperator_adjoint_comp_self
      (PauliSymplectic.cssZCheck error)
    have happ :
        LinearMap.adjoint (PauliSymplectic.toQubitOperator
          (PauliSymplectic.cssZCheck error))
          (PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck error)
            (physicalTInvBranch h hdegree)) = physicalTInvBranch h hdegree := by
      have happly := LinearMap.congr_fun hunit (physicalTInvBranch h hdegree)
      simpa [LinearMap.comp_apply] using happly
    rw [happ]
    rw [inner_self_eq_norm_sq_to_K, physicalTInvBranch_norm h hdegree]
    norm_num
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner]
  norm_num

end HH18Parameterized
end Distillation
end QEC
