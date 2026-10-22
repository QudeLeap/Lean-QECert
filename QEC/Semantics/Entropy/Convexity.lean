import QEC.Semantics.Core.Definitions
/-!
# Convexity of density operators

Finite convex combinations of density operators are density operators.
-/

universe u v

namespace QEC
namespace Semantics
namespace DensityOperator

open scoped BigOperators ComplexOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

/--
The operator obtained from a finite real-weighted combination of density
operators on the same finite-dimensional system.
-/
noncomputable def convexCombinationOperator {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) : Operator H :=
  ∑ i ∈ s, (w i : Complex) • (ρ i).toOperator

/-- Positivity is closed under finite nonnegative combinations of densities. -/
theorem convexCombination_positive {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) :
    LinearMap.IsPositive (convexCombinationOperator s w ρ) := by
  classical
  unfold convexCombinationOperator
  exact LinearMap.isPositive_sum s fun i hi =>
    (ρ i).positive.smul_of_nonneg (by exact_mod_cast hw_nonneg i hi)

/-- The trace of a finite convex combination of densities is one. -/
theorem convexCombination_trace_one {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_sum : ∑ i ∈ s, w i = 1) :
    LinearMap.trace Complex H (convexCombinationOperator s w ρ) = 1 := by
  unfold convexCombinationOperator
  calc
    LinearMap.trace Complex H (∑ i ∈ s, (w i : Complex) • (ρ i).toOperator)
        = ∑ i ∈ s, LinearMap.trace Complex H ((w i : Complex) • (ρ i).toOperator) := by
          rw [map_sum]
    _ = ∑ i ∈ s, (w i : Complex) := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp [DensityOperator.trace_toOperator]
    _ = ((∑ i ∈ s, w i : ℝ) : Complex) := by
          exact (Complex.ofReal_sum s w).symm
    _ = 1 := by
          rw [hw_sum]
          exact Complex.ofReal_one

/--
The finite real-weighted combination is positive and trace-one under the
convex-weight hypotheses.
-/
theorem convexCombination_isDensity {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    LinearMap.IsPositive (convexCombinationOperator s w ρ) ∧
      LinearMap.trace Complex H (convexCombinationOperator s w ρ) = 1 :=
  ⟨convexCombination_positive s w ρ hw_nonneg,
    convexCombination_trace_one s w ρ hw_sum⟩

/-- A finite convex combination of density operators is a density operator. -/
noncomputable def convexCombination {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) : DensityOperator H where
  toOperator := convexCombinationOperator s w ρ
  positive := (convexCombination_isDensity s w ρ hw_nonneg hw_sum).1
  trace_one := (convexCombination_isDensity s w ρ hw_nonneg hw_sum).2

@[simp]
theorem convexCombination_toOperator {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    (convexCombination s w ρ hw_nonneg hw_sum).toOperator =
      convexCombinationOperator s w ρ :=
  rfl

end DensityOperator
end Semantics
end QEC
