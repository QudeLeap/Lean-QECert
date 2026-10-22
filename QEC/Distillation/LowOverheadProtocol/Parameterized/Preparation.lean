import QEC.Distillation.LowOverheadProtocol.Parameterized.Types

/-!
# Parameterized HH18 noisy-resource preparation

This layer keeps the physical input of every admissible HH18 block concrete.
Each finite physical site is routed to one noisy `T†` resource, and the
register density is the actual independent convex mixture over the resulting
binary Pauli-`Z` error words.  No protocol outcome, decoder, or error estimate
is supplied here.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- The literal finite routing from physical HH18 sites to resource slots. -/
noncomputable def resourceSiteEquiv (m w : Nat) :
    PhysicalSite m w ≃ Fin (physicalInputCount m w) :=
  Fintype.equivFin (PhysicalSite m w)

/-- The homogeneous noisy `T†` resource family consumed by the physical sites
of one parameterized block. -/
noncomputable def noisyResources (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ResourceInput (physicalInputCount m w) QubitSpace :=
  HH18NoisyInput.noisyTInvResources (physicalInputCount m w) epsilon

/-- Each routed physical site is supplied with the actual one-qubit diagonal
`T†` resource at the selected error rate. -/
theorem noisyResources_at_site (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (site : PhysicalSite m w) :
    noisyResources m w epsilon (resourceSiteEquiv m w site) =
      HH18NoisyInput.noisyTInvResource epsilon :=
  rfl

/-- The independent input regime records the actual uniform per-site rate and
admits exactly the resource family constructed above. -/
def independentInputModel (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    IndependentInputErrorModel (physicalInputCount m w) QubitSpace where
  rate := fun _ => epsilon.1
  rate_nonneg := fun _ => epsilon.property.1
  rate_le_one := fun _ => by linarith [epsilon.property.2]
  admissible := fun rate inputs =>
    (∀ slot, rate slot = epsilon.1) ∧ inputs = noisyResources m w epsilon

/-- The constructed physical resource family is permitted by its independent
error model. -/
theorem noisyResources_permitted (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    InputErrorModel.Permits (.independent (independentInputModel m w epsilon))
      (noisyResources m w epsilon) := by
  constructor
  · intro slot
    rfl
  · rfl

/-- The actual noisy physical-register density prepared from the independent
diagonal error law. -/
noncomputable def noisyInput (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (m w : Nat) : DensityOperator (PhysicalRegister m w) :=
  HH18NoisyInput.hh18NoisyInput epsilon m w

/-- The parameterized physical input is the generic independent finite
register construction on its actual physical-site type. -/
theorem noisyInput_eq_independentNoisyTRegister
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (m w : Nat) :
    noisyInput epsilon m w =
      HH18NoisyInput.independentNoisyTRegister
        (ι := PhysicalSite m w) epsilon :=
  rfl

/-- The physical error-word law is normalized over the actual finite site
type, without specializing or enumerating a concrete block. -/
theorem errorWordWeight_sum (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ∑ error : PhysicalErrorWord m w,
      HH18NoisyInput.errorWordWeight epsilon error = 1 := by
  simpa only [PhysicalErrorWord] using
    (HH18NoisyInput.errorWordWeight_sum (ι := PhysicalSite m w) epsilon)

/-- The actual parameterized noisy input has the literal normalized product
mixture over physical Pauli-`Z` error branches. -/
theorem noisyInput_toOperator (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (m w : Nat) :
    (noisyInput epsilon m w).toOperator =
      ∑ error : PhysicalErrorWord m w,
        (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          (HH18NoisyInput.errorWordDensity error).toOperator := by
  exact
    (HH18NoisyInput.independentNoisyTRegister_toOperator
      (ι := PhysicalSite m w) epsilon)

end HH18Parameterized
end Distillation
end QEC
