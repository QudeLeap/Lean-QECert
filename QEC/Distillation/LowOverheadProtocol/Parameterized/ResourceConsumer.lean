import QEC.Distillation.LowOverheadProtocol.Parameterized.ResourceMeasurement
import QEC.Distillation.LowOverheadProtocol.Parameterized.ResourceConsumerSupport

/-!
# Parameterized HH18 physical resource consumer

This layer consumes the normalized measured physical-error-word record with a
complete finite Kraus channel.  Each basis word is mapped to its corresponding
actual physical error branch, and the measured record is transported linearly
over its one named symbolic support.  It stops before syndrome composition or
protocol endpoints.
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

universe u

attribute [local instance 100] Fintype.ofFinite

local instance instConsumerClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private noncomputable def errorWordBasis (m w : Nat) :
    OrthonormalBasis (PhysicalErrorWord m w) Complex (PhysicalRegister m w) :=
  (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex).reindex
    (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w))

@[simp] theorem errorWordBasis_apply (m w : Nat) (error : PhysicalErrorWord m w) :
    errorWordBasis m w error = errorWordBasisState m w error := by
  simp [errorWordBasis, errorWordBasisState]

/-- The finite CPTP word consumer maps each measured physical-error word to
its corresponding actual error branch. -/
def resourceConsumerKrausFamily {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) :
    FiniteKrausFamily (PhysicalErrorWord m w)
      (PhysicalRegister m w) (PhysicalRegister m w) where
  operator error :=
    (InnerProductSpace.rankOne Complex (errorBranchState h hdegree error)
      (errorWordBasisState m w error)).toLinearMap

theorem resourceConsumerKrausFamily_adjoint_comp {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) (error : PhysicalErrorWord m w) :
    (LinearMap.adjoint ((resourceConsumerKrausFamily h hdegree).operator error)).comp
        ((resourceConsumerKrausFamily h hdegree).operator error) =
      (InnerProductSpace.rankOne Complex (errorWordBasisState m w error)
        (errorWordBasisState m w error)).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex (errorBranchState h hdegree error)
        (errorWordBasisState m w error)).toLinearMap) =
      (InnerProductSpace.rankOne Complex (errorWordBasisState m w error)
        (errorBranchState h hdegree error)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex (errorBranchState h hdegree error)
      (errorWordBasisState m w error)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  ext psi
  simp only [resourceConsumerKrausFamily]
  rw [hadjoint]
  have hnormSq : (↑‖errorBranchState h hdegree error‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact errorBranchState_normSq h hdegree error
  simp [LinearMap.comp_apply, hnormSq]

theorem resourceConsumerKrausFamily_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (resourceConsumerKrausFamily h hdegree).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp_rw [resourceConsumerKrausFamily_adjoint_comp]
  have hcomplete := congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id (errorWordBasis m w))
  simp only [errorWordBasis_apply, ContinuousLinearMap.toLinearMap_sum] at hcomplete
  exact hcomplete

/-- The actual CPTP consumption of a parameterized independently measured
physical resource word. -/
noncomputable def resourceConsumerChannel {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) :
    QuantumChannel (PhysicalRegister m w) (PhysicalRegister m w) :=
  (resourceConsumerKrausFamily h hdegree).toQuantumChannel
    (resourceConsumerKrausFamily_complete h hdegree)

theorem resourceConsumerBranch_basis {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error observed : PhysicalErrorWord m w) :
    (resourceConsumerKrausFamily h hdegree).operator error
      (errorWordBasisState m w observed) =
      if error = observed then errorBranchState h hdegree error else 0 := by
  classical
  simp only [resourceConsumerKrausFamily]
  change inner Complex (errorWordBasisState m w error)
      (errorWordBasisState m w observed) • errorBranchState h hdegree error = _
  rw [← errorWordBasis_apply m w error, ← errorWordBasis_apply m w observed]
  rw [(errorWordBasis m w).inner_eq_ite]
  simp

private noncomputable def resourceConsumerBranchMap {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) (error : PhysicalErrorWord m w) :
    Operator (PhysicalRegister m w) →ₗ[Complex] Operator (PhysicalRegister m w) where
  toFun := fun operator =>
    ((resourceConsumerKrausFamily h hdegree).operator error).comp
      (operator.comp (LinearMap.adjoint
        ((resourceConsumerKrausFamily h hdegree).operator error)))
  map_add' := by
    intro left right
    ext psi
    simp [LinearMap.comp_apply, map_add]
  map_smul' := by
    intro scalar operator
    ext psi
    simp [LinearMap.comp_apply, map_smul]

private theorem resourceConsumerBranchMap_errorWordBasisDensity {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error observed : PhysicalErrorWord m w) :
    resourceConsumerBranchMap h hdegree error
      (errorWordBasisDensity m w observed).toOperator =
      if error = observed then
        (DensityOperator.pureDensity (errorBranchState h hdegree error)
          (errorBranchState_normSq h hdegree error)).toOperator
      else 0 := by
  change ((resourceConsumerKrausFamily h hdegree).operator error).comp
      ((errorWordBasisDensity m w observed).toOperator.comp
        (LinearMap.adjoint ((resourceConsumerKrausFamily h hdegree).operator error))) = _
  rw [errorWordBasisDensity, DensityOperator.pureDensity_toOperator]
  have hsandwich : ((resourceConsumerKrausFamily h hdegree).operator error).comp
      ((InnerProductSpace.rankOne Complex (errorWordBasisState m w observed)
        (errorWordBasisState m w observed)).toLinearMap.comp
        (LinearMap.adjoint ((resourceConsumerKrausFamily h hdegree).operator error))) =
      (InnerProductSpace.rankOne Complex
        ((resourceConsumerKrausFamily h hdegree).operator error
          (errorWordBasisState m w observed))
        ((resourceConsumerKrausFamily h hdegree).operator error
          (errorWordBasisState m w observed))).toLinearMap := by
    ext x
    simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
      LinearMap.adjoint_inner_right]
  rw [hsandwich, resourceConsumerBranch_basis]
  by_cases hmatch : error = observed
  · subst observed
    simp [DensityOperator.pureDensity_toOperator]
  · rw [if_neg hmatch, if_neg hmatch]
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

/-- The word consumer maps each basis-word density to the corresponding
normalized actual error branch. -/
theorem resourceConsumerChannel_errorWordBasisDensity {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (observed : PhysicalErrorWord m w) :
    resourceConsumerChannel h hdegree
      (errorWordBasisDensity m w observed).toOperator =
      (DensityOperator.pureDensity (errorBranchState h hdegree observed)
        (errorBranchState_normSq h hdegree observed)).toOperator := by
  unfold resourceConsumerChannel
  exact finiteKrausChannel_apply_diagonal (resourceConsumerKrausFamily h hdegree)
    (resourceConsumerKrausFamily_complete h hdegree)
    (fun word => (errorWordBasisDensity m w word).toOperator)
    (fun word => (DensityOperator.pureDensity (errorBranchState h hdegree word)
      (errorBranchState_normSq h hdegree word)).toOperator)
    (fun error recorded => by
      have hbranch := resourceConsumerBranchMap_errorWordBasisDensity h hdegree error recorded
      by_cases hmatch : error = recorded
      · rw [if_pos hmatch] at hbranch ⊢
        exact hbranch
      · rw [if_neg hmatch] at hbranch ⊢
        exact hbranch)
    observed

/-- The actual measured resource record is mapped linearly to the matching
mixture of actual physical error branches over the same named support. -/
theorem resourceConsumerChannel_prepareMeasuredResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    resourceConsumerChannel h hdegree
      (prepareMeasuredResources m w inputs).toOperator =
      (physicalErrorWords m w).sum (fun error =>
        (measuredErrorWordProbability m w inputs error : Complex) •
          (DensityOperator.pureDensity (errorBranchState h hdegree error)
            (errorBranchState_normSq h hdegree error)).toOperator) := by
  apply quantumChannel_apply_input_of_explicit_support
    (physicalErrorWords m w) (resourceConsumerChannel h hdegree)
    (prepareMeasuredResources m w inputs)
    (fun error => (measuredErrorWordProbability m w inputs error : Complex))
    (errorWordBasisDensity m w)
    (fun error => DensityOperator.pureDensity (errorBranchState h hdegree error)
      (errorBranchState_normSq h hdegree error))
  · exact prepareMeasuredResources_toOperator m w inputs
  · intro error
    exact resourceConsumerChannel_errorWordBasisDensity h hdegree error

end HH18Parameterized
end Distillation
end QEC
