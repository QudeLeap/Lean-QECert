import QEC.Distillation.LowOverheadProtocol.Core.PhysicalTypes
import QEC.Distillation.LowOverheadProtocol.Core.Postselection
import QEC.Distillation.Triorthogonal.NoisyInjection

/-!
# HH18 physical resource preparation

This layer measures every supplied resource, records its actual finite word,
and prepares only the corresponding corrected physical branch.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- The finite syndrome predicate is used as a branch selector throughout the
physical error-word expansion. -/
local instance instClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def resourceCount : Nat := Fintype.card PhysicalSite

/-- The fixed physical route has exactly the fifteen sites of the registered
`[[15,1,3]]` HH18 block. -/
theorem resourceCount_eq_fifteen : resourceCount = 15 := by
  simpa [resourceCount, Length] using
    (HH18NoisyInput.hh18_15_1_0_parameters).1

/-- The literal physical-site to resource-slot routing. -/
noncomputable def resourceSiteEquiv : PhysicalSite ≃ Fin resourceCount :=
  Fintype.equivFin PhysicalSite

/-- The literal homogeneous family of independently diagonal-noisy `T†`
resources consumed by the fifteen physical sites. -/
noncomputable def noisyResources (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ResourceInput resourceCount QubitSpace :=
  HH18NoisyInput.noisyTInvResources resourceCount epsilon

/-- The route's independent-input regime records the concrete per-site rate
and admits exactly the literal independently prepared `T†` family. -/
def independentInputModel (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    IndependentInputErrorModel resourceCount QubitSpace where
  rate := fun _ => epsilon.1
  rate_nonneg := fun _ => epsilon.property.1
  rate_le_one := fun _ => by linarith [epsilon.property.2]
  admissible := fun rate inputs =>
    (∀ slot, rate slot = epsilon.1) ∧ inputs = noisyResources epsilon

theorem noisyResources_permitted
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    InputErrorModel.Permits (.independent (independentInputModel epsilon))
      (noisyResources epsilon) := by
  constructor
  · intro slot
    rfl
  · rfl

/-- A `T†` phase-basis outcome is read through the established A-basis
instrument after an actual physical `S` rotation. -/
def resourceOutcome (error : ZMod 2) : StabilizerOutcome :=
  if error = 0 then .positive else .negative

/-- The physical `S` rotation that maps the HH18 `T†` resource basis to the
existing A-basis measurement. -/
noncomputable def rotateTInvResource (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport (Real.pi / 2)).conjDensity rho

/-- The physical `S` rotation sends the clean `T†` resource to the positive
eigenstate of the measured A basis. -/
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
  congr 1 <;> ring

/-- The physical `S` rotation sends the selected diagonal `Z` error to the
negative A-basis eigenstate. -/
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
  congr 1 <;>
    simp [HH18PhaseInjection.tInvErrorAngle, HH18PhaseInjection.tInvIdealAngle] <;>
    ring

/-- The shared A-basis error parameter induced by the HH18 diagonal resource
rate.  Its upper bound follows from the HH18 source domain. -/
def aBasisErrorParameter (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    Triorthogonal.BH12NoisyInjection.ErrorParameter where
  rate := epsilon.1
  rate_nonneg := epsilon.property.1
  rate_le_one := by linarith [epsilon.property.2]

/-- After the physical `S` rotation, the actual HH18 diagonal `T†` resource
is exactly the A-basis diagonal mixture with the same error rate. -/
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
  have hclean := congrArg DensityOperator.toOperator
    (rotateTInvResource_clean)
  have herror := congrArg DensityOperator.toOperator
    (rotateTInvResource_error)
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

/-- The actual product probability of observing a complete error word from
the supplied resource family. -/
noncomputable def measuredErrorWordProbability
    (inputs : ResourceInput resourceCount QubitSpace)
    (error : PhysicalErrorWord) : ℝ :=
  ∏ site, Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument.bornWeight
    (resourceOutcome (error site))
    (rotateTInvResource (inputs (resourceSiteEquiv site)))

theorem measuredErrorWordProbability_nonneg
    (inputs : ResourceInput resourceCount QubitSpace)
    (error : PhysicalErrorWord) :
    0 ≤ measuredErrorWordProbability inputs error := by
  unfold measuredErrorWordProbability
  apply Finset.prod_nonneg
  intro site _hsite
  exact Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_weight_nonneg _ _

/-- The one finite support shared by every measured physical-error word sum. -/
noncomputable def physicalErrorWords : Finset PhysicalErrorWord := Finset.univ

@[simp] theorem mem_physicalErrorWords (error : PhysicalErrorWord) :
    error ∈ physicalErrorWords := by
  exact Finset.mem_univ error

theorem physicalErrorWords_card :
    physicalErrorWords.card = Fintype.card PhysicalErrorWord := by
  rfl

theorem sum_measuredErrorWordProbability
    (inputs : ResourceInput resourceCount QubitSpace) :
    physicalErrorWords.sum (fun error =>
      measuredErrorWordProbability inputs error) = 1 := by
  classical
  have h := Finset.sum_prod_piFinset
    (R := ℝ) (ι := PhysicalSite) (κ := ZMod 2) (s := Finset.univ)
    (g := fun site bit => Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument.bornWeight
      (resourceOutcome bit) (rotateTInvResource (inputs (resourceSiteEquiv site))))
  have hsite (site : PhysicalSite) :
      ∑ bit : ZMod 2, Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument.bornWeight
        (resourceOutcome bit)
          (rotateTInvResource (inputs (resourceSiteEquiv site))) = 1 := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    simpa [resourceOutcome] using Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_weight_sum
      (rotateTInvResource (inputs (resourceSiteEquiv site)))
  simp_rw [hsite] at h
  simpa [physicalErrorWords, measuredErrorWordProbability] using h

/-- Measuring the literal independent HH18 resource family gives precisely
the product Bernoulli law of its physical diagonal-error word. -/
theorem measuredErrorWordProbability_noisyResources
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord) :
    measuredErrorWordProbability (noisyResources epsilon) error =
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
      Triorthogonal.BH12NoisyInjection.ErrorParameter.cleanWeight,
      HH18NoisyInput.bitErrorWeight]

/-- The computational record of a measured resource-error word. -/
def errorWordBasisState (error : PhysicalErrorWord) : PhysicalRegister :=
  EuclideanSpace.basisFun (Bitstring PhysicalSite) Complex
    ((PauliSymplectic.bitstringWordEquiv PhysicalSite).symm error)

theorem errorWordBasisState_normSq (error : PhysicalErrorWord) :
    ‖errorWordBasisState error‖ ^ 2 = 1 := by
  simp [errorWordBasisState]

/-- The normalized classical register state recording one observed word. -/
noncomputable def errorWordBasisDensity (error : PhysicalErrorWord) :
    DensityOperator PhysicalRegister :=
  DensityOperator.pureDensity (errorWordBasisState error)
    (errorWordBasisState_normSq error)

/-- A finite classical record of all independently measured supplied
resources. -/
noncomputable def prepareMeasuredResources
    (inputs : ResourceInput resourceCount QubitSpace) :
    DensityOperator PhysicalRegister :=
  DensityOperator.convexCombination physicalErrorWords
    (measuredErrorWordProbability inputs) errorWordBasisDensity
    (fun error _ => measuredErrorWordProbability_nonneg inputs error)
    (sum_measuredErrorWordProbability inputs)

@[simp] theorem prepareMeasuredResources_toOperator
    (inputs : ResourceInput resourceCount QubitSpace) :
    (prepareMeasuredResources inputs).toOperator =
      physicalErrorWords.sum (fun error =>
        (measuredErrorWordProbability inputs error : Complex) •
          (errorWordBasisDensity error).toOperator) := by
  simp [prepareMeasuredResources, DensityOperator.convexCombinationOperator]

/-- The actual corrected physical state selected by a measured resource word. -/
noncomputable def errorBranchState (error : PhysicalErrorWord) : PhysicalRegister :=
  HH18NoisyInput.hh18PhysicalTInvErrorBranch error

private theorem physicalTInvBranch_norm : ‖HH18NoisyInput.hh18PhysicalTInvBranch‖ = 1 := by
  change ‖(HH18PuncturedReedMuller.physicalTInv 0 4).toLinearIsometryEquiv
    HH18NoisyInput.hh18EncodedLogicalPlusInput‖ = 1
  rw [(HH18PuncturedReedMuller.physicalTInv 0 4).toLinearIsometryEquiv.norm_map]
  change ‖HH18NoisyInput.hh18_15_1_0_encodedCode.encoding
      HH18NoisyInput.hh18LogicalPlusInput‖ = 1
  rw [HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.norm_map]
  exact hh18LogicalPlusInput_norm

theorem errorBranchState_normSq (error : PhysicalErrorWord) :
    ‖errorBranchState error‖ ^ 2 = 1 := by
  have hinner : inner Complex (errorBranchState error) (errorBranchState error) = 1 := by
    simp only [errorBranchState, HH18NoisyInput.hh18PhysicalTInvErrorBranch,
      HH18NoisyInput.zErrorOperator]
    rw [← LinearMap.adjoint_inner_left]
    have hunit := PauliSymplectic.toQubitOperator_adjoint_comp_self
      (PauliSymplectic.cssZCheck error)
    have happ :
        LinearMap.adjoint (PauliSymplectic.toQubitOperator
          (PauliSymplectic.cssZCheck error))
          (PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck error)
            HH18NoisyInput.hh18PhysicalTInvBranch) =
          HH18NoisyInput.hh18PhysicalTInvBranch := by
      have := LinearMap.congr_fun hunit HH18NoisyInput.hh18PhysicalTInvBranch
      simpa [LinearMap.comp_apply] using this
    rw [happ]
    rw [inner_self_eq_norm_sq_to_K, physicalTInvBranch_norm]
    norm_num
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner]
  norm_num

end HH18Protocol
end Distillation
end QEC
