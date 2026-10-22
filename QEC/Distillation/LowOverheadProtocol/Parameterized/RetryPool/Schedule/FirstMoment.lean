import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Core
import QEC.Semantics.Instruments.TensorPower.FirstMoment
/-!
# Parameterized HH18 decoded retry-pool shortage first moment

This thin adapter specializes the generic finite tensor-power shortage bound to
the actual decoded HH18 instrument.  It rewrites only the two physical
postselection outcomes and keeps the generic counting argument separate.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instDecodedRetryPoolFirstMomentClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The pool's shortage mass is the generic decoded-instrument shortage mass
because its terminal selection stage preserves each actual observed history
weight. -/
private theorem decodedRetryPoolShortageMass_eq_tensorPowerShortageMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    decodedRetryPoolShortageMass h hdegree attempts required rho =
      (decodedInstrument h hdegree).tensorPowerShortageMass decodedRetryPoolAccepts
        attempts required rho := by
  unfold decodedRetryPoolShortageMass tensorPowerShortageMass
  simp_rw [decodedRetryPoolInstrument_bornWeight_eq_tensorPower]

/-- The finite decoded rejected-outcome sum is the complementary physical
endpoint mass on the actual noisy measured-resource input. -/
private theorem decodedInstrument_rejectedBornWeightSum_noisyResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ decodedRetryPoolAccepts outcome),
      (decodedInstrument h hdegree).bornWeight outcome
        (prepareMeasuredResources m w (noisyResources m w epsilon)) =
      1 - acceptedBernoulliMass w r m epsilon := by
  have hfilter :
      (Finset.univ.filter (fun outcome : DistillationOutcome =>
        ¬ decodedRetryPoolAccepts outcome)) = {.rejected} := by
    ext outcome
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    cases outcome <;> simp [decodedRetryPoolAccepts]
  rw [hfilter]
  simp only [Finset.sum_singleton]
  rw [decodedInstrument_bornWeight_prepareMeasuredResources]
  have haccepted :
      endpointWeight h hdegree (noisyResources m w epsilon) .accepted =
        acceptedBernoulliMass w r m epsilon := by
    calc
      _ = (decodedInstrument h hdegree).bornWeight .accepted
          (prepareMeasuredResources m w (noisyResources m w epsilon)) := by
        symm
        exact decodedInstrument_bornWeight_prepareMeasuredResources h hdegree
          (noisyResources m w epsilon) .accepted
      _ = _ := decodedInstrument_bornWeight_noisyResources_accepted_eq_acceptedBernoulliMass
        h hdegree epsilon
  linarith [endpointWeights_sum h hdegree (noisyResources m w epsilon)]

/-- The actual finite decoded HH18 retry-pool shortage mass on recursively
tensorized noisy physical inputs is bounded by its rejected one-block mass. -/
theorem decodedRetryPoolShortageMass_markov_le_noisyResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (attempts required : Nat) (hrequired : required ≤ attempts) :
    ((attempts - required + 1 : Nat) : ℝ) *
        decodedRetryPoolShortageMass h hdegree attempts required
          (tensorPowerProductInput
            (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit attempts) ≤
      (attempts : ℝ) * (1 - acceptedBernoulliMass w r m epsilon) := by
  rw [decodedRetryPoolShortageMass_eq_tensorPowerShortageMass]
  calc
    _ ≤ (attempts : ℝ) *
        ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ decodedRetryPoolAccepts outcome),
          (decodedInstrument h hdegree).bornWeight outcome
            (prepareMeasuredResources m w (noisyResources m w epsilon)) :=
      tensorPowerShortageMass_markov_le_rejectedBornWeight
        (decodedInstrument h hdegree) decodedRetryPoolAccepts
        (decodedInstrument_complete h hdegree)
        (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
        attempts required hrequired
    _ = _ := by
      rw [decodedInstrument_rejectedBornWeightSum_noisyResources]

end HH18Parameterized
end Distillation
end QEC
