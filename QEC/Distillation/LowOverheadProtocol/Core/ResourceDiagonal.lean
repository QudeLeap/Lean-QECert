import QEC.Distillation.LowOverheadProtocol.Core.ResourceKraus

/-!
# HH18 physical resource diagonal layer

This layer proves the finite diagonal action of the resource Kraus channel and
exports only the exact per-basis bridge needed by the weighted mixture layer.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

universe u

attribute [local instance 100] Fintype.ofFinite

local instance instDiagonalClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private noncomputable def resourceConsumerBranchMap (error : PhysicalErrorWord) :
    Operator PhysicalRegister →ₗ[Complex] Operator PhysicalRegister where
  toFun := fun operator =>
    (resourceConsumerKrausFamily.operator error).comp
      (operator.comp (LinearMap.adjoint (resourceConsumerKrausFamily.operator error)))
  map_add' := by
    intro left right
    ext psi
    simp [LinearMap.comp_apply, map_add]
  map_smul' := by
    intro scalar operator
    ext psi
    simp [LinearMap.comp_apply, map_smul]

private theorem resourceConsumerBranchMap_errorWordBasisDensity
    (error observed : PhysicalErrorWord) :
    resourceConsumerBranchMap error (errorWordBasisDensity observed).toOperator =
      if error = observed then
        (DensityOperator.pureDensity (errorBranchState error)
          (errorBranchState_normSq error)).toOperator
      else 0 := by
  change (resourceConsumerKrausFamily.operator error).comp
      ((errorWordBasisDensity observed).toOperator.comp
        (LinearMap.adjoint (resourceConsumerKrausFamily.operator error))) = _
  rw [errorWordBasisDensity, DensityOperator.pureDensity_toOperator]
  have hsandwich : (resourceConsumerKrausFamily.operator error).comp
      ((InnerProductSpace.rankOne Complex (errorWordBasisState observed)
        (errorWordBasisState observed)).toLinearMap.comp
        (LinearMap.adjoint (resourceConsumerKrausFamily.operator error))) =
      (InnerProductSpace.rankOne Complex
        (resourceConsumerKrausFamily.operator error (errorWordBasisState observed))
        (resourceConsumerKrausFamily.operator error (errorWordBasisState observed))).toLinearMap := by
    ext x
    simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
      LinearMap.adjoint_inner_right]
  rw [hsandwich, resourceConsumerBranch_basis]
  by_cases h : error = observed
  · subst observed
    simp [DensityOperator.pureDensity_toOperator]
  · rw [if_neg h, if_neg h]
    exact congrArg ContinuousLinearMap.toLinearMap
      (InnerProductSpace.rankOne_eq_zero.mpr (Or.inl rfl))

private theorem finiteKrausChannel_apply_diagonal
    {ι H K : Type u} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (kraus : FiniteKrausFamily ι H K) (complete : kraus.Complete)
    (basis : ι → Operator H) (output : ι → Operator K)
    (hbranch : ∀ error observed,
      (kraus.operator error).comp
        ((basis observed).comp (LinearMap.adjoint (kraus.operator error))) =
          if error = observed then output error else 0)
    (observed : ι) :
    kraus.toQuantumChannel complete (basis observed) = output observed := by
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum,
    Fintype.sum_eq_single observed]
  · rw [hbranch]
    simp
  · intro error hne
    rw [hbranch]
    simp [hne]

/-- The narrow public inter-module bridge for the exact per-basis channel action. -/
theorem resourceConsumerChannel_errorWordBasisDensity
    (observed : PhysicalErrorWord) :
    resourceConsumerChannel (errorWordBasisDensity observed).toOperator =
      (DensityOperator.pureDensity (errorBranchState observed)
        (errorBranchState_normSq observed)).toOperator := by
  unfold resourceConsumerChannel
  exact finiteKrausChannel_apply_diagonal resourceConsumerKrausFamily
    resourceConsumerKrausFamily_complete
    (fun word => (errorWordBasisDensity word).toOperator)
    (fun word => (DensityOperator.pureDensity (errorBranchState word)
      (errorBranchState_normSq word)).toOperator)
    (fun error recorded => by
      have hbranch := resourceConsumerBranchMap_errorWordBasisDensity error recorded
      by_cases hmatch : error = recorded
      · rw [if_pos hmatch] at hbranch ⊢
        exact hbranch
      · rw [if_neg hmatch] at hbranch ⊢
        exact hbranch)
    observed

end HH18Protocol
end Distillation
end QEC
