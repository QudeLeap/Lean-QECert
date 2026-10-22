import QEC.Distillation.LowOverheadProtocol.Core.ResourcePreparation

/-!
# HH18 physical resource Kraus layer

This layer owns the measured-word orthonormal basis and the complete finite
Kraus channel from that record to its physical corrected branch.
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

local instance instKrausClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private noncomputable def errorWordBasis :
    OrthonormalBasis PhysicalErrorWord Complex PhysicalRegister :=
  (EuclideanSpace.basisFun (Bitstring PhysicalSite) Complex).reindex
    (PauliSymplectic.bitstringWordEquiv PhysicalSite)

@[simp] theorem errorWordBasis_apply (error : PhysicalErrorWord) :
    errorWordBasis error = errorWordBasisState error := by
  simp [errorWordBasis, errorWordBasisState]

/-- The finite CPTP word consumer: a measured word prepares exactly its
sitewise-injection/error branch, never a caller-provided output. -/
def resourceConsumerKrausFamily :
    FiniteKrausFamily PhysicalErrorWord PhysicalRegister PhysicalRegister where
  operator error :=
    (InnerProductSpace.rankOne Complex (errorBranchState error)
      (errorWordBasisState error)).toLinearMap

theorem resourceConsumerKrausFamily_adjoint_comp (error : PhysicalErrorWord) :
    (LinearMap.adjoint (resourceConsumerKrausFamily.operator error)).comp
        (resourceConsumerKrausFamily.operator error) =
      (InnerProductSpace.rankOne Complex (errorWordBasisState error)
        (errorWordBasisState error)).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex (errorBranchState error)
        (errorWordBasisState error)).toLinearMap) =
      (InnerProductSpace.rankOne Complex (errorWordBasisState error)
        (errorBranchState error)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex (errorBranchState error)
      (errorWordBasisState error)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  ext psi
  simp only [resourceConsumerKrausFamily]
  rw [hadjoint]
  have hnormSq : (↑‖errorBranchState error‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact errorBranchState_normSq error
  simp [LinearMap.comp_apply, hnormSq]

theorem resourceConsumerKrausFamily_complete :
    resourceConsumerKrausFamily.Complete := by
  rw [FiniteKrausFamily.Complete]
  simp_rw [resourceConsumerKrausFamily_adjoint_comp]
  have hcomplete := congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id errorWordBasis)
  simp only [errorWordBasis_apply, ContinuousLinearMap.toLinearMap_sum] at hcomplete
  exact hcomplete

/-- The actual CPTP consumption of the independently measured resource word. -/
noncomputable def resourceConsumerChannel : QuantumChannel PhysicalRegister PhysicalRegister :=
  resourceConsumerKrausFamily.toQuantumChannel resourceConsumerKrausFamily_complete

theorem resourceConsumerBranch_basis
    (error observed : PhysicalErrorWord) :
    resourceConsumerKrausFamily.operator error (errorWordBasisState observed) =
      if error = observed then errorBranchState error else 0 := by
  classical
  simp only [resourceConsumerKrausFamily]
  change inner Complex (errorWordBasisState error) (errorWordBasisState observed) •
      errorBranchState error = _
  rw [← errorWordBasis_apply error, ← errorWordBasis_apply observed]
  rw [errorWordBasis.inner_eq_ite]
  simp

end HH18Protocol
end Distillation
end QEC
