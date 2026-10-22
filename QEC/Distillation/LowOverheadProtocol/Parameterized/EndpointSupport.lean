import QEC.Semantics.Entropy.Purification
/-!
# Parameterized HH18 endpoint support

This module keeps the finite-support linearity and trace bridges used by the
physical endpoint independent of HH18 carriers or protocol data.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Semantics
open scoped BigOperators

universe u

/-- A linear operator map transports an explicitly supported finite mixture
to the corresponding pointwise mixture. -/
theorem linearMap_apply_input_of_explicit_support
    {ι H K : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (linearMap : Operator H →ₗ[Complex] Operator K) (input : Operator H)
    (weight : ι → Complex) (inputSummand : ι → Operator H)
    (outputSummand : ι → Operator K)
    (hinput : input = support.sum (fun i => weight i • inputSummand i))
    (hpointwise : ∀ i, linearMap (inputSummand i) = outputSummand i) :
    linearMap input = support.sum (fun i => weight i • outputSummand i) := by
  rw [hinput, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, hpointwise i]

/-- The real trace of an explicitly supported finite sum is the finite sum of
its specified real trace summands. -/
theorem realTrace_input_of_explicit_support
    {ι H : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (input : Operator H) (inputSummand : ι → Operator H) (realSummand : ι → ℝ)
    (hinput : input = support.sum inputSummand)
    (hpointwise : ∀ i, Complex.re (LinearMap.trace Complex H (inputSummand i)) =
      realSummand i) :
    Complex.re (LinearMap.trace Complex H input) = support.sum realSummand := by
  rw [hinput, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact hpointwise i

end HH18Parameterized
end Distillation
end QEC
