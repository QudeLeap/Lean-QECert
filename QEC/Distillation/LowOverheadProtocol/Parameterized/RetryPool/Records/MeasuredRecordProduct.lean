import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Measurement
import QEC.Distillation.LowOverheadProtocol.Parameterized.ResourceMeasurement
import QEC.Semantics.Instruments.Registers.ProductDensity
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Parameterized HH18 measured-record products

The one-qubit successor record is a literal computational Bernoulli density.
This module tensors that density over the actual physical-site type and
identifies it with the measured-resource register consumed by one
parameterized HH18 block.  The proof is symbolic in the finite site type and
does not enumerate a concrete `PhysicalErrorWord` universe.
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
open Triorthogonal.BH12NoisyInjection

attribute [local instance 100] Fintype.ofFinite

/-- Convert the successor's actual measured record parameter to the HH18
diagonal-error domain used by the next physical block. -/
def decodedRetryPoolDiagonalErrorRate
    (parameter : ErrorParameter) (hhalf : parameter.rate ≤ 1 / 2) :
    HH18NoisyInput.DiagonalErrorRate :=
  ⟨parameter.rate,
    parameter.rate_nonneg,
    hhalf⟩

/-- A one-qubit successor record has the corresponding literal diagonal
computational matrix entry. -/
theorem decodedRetryPoolOneQubitRecordDensity_matrixEntry
    (parameter : ErrorParameter) (hhalf : parameter.rate ≤ 1 / 2)
    (left right : Fin 2) :
    inner Complex (EuclideanSpace.basisFun (Fin 2) Complex left)
        ((decodedRetryPoolOneQubitRecordDensity parameter).toOperator
          (EuclideanSpace.basisFun (Fin 2) Complex right)) =
      if left = right then
        (HH18NoisyInput.bitErrorWeight
          (decodedRetryPoolDiagonalErrorRate parameter hhalf)
          (left : ZMod 2) : Complex)
      else 0 := by
  rw [decodedRetryPoolOneQubitRecordDensity_toOperator]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_right, inner_smul_right]
  change (parameter.cleanWeight : Complex) *
        inner Complex (EuclideanSpace.basisFun (Fin 2) Complex left)
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Fin 2) Complex 0)
            (EuclideanSpace.basisFun (Fin 2) Complex 0)
            (EuclideanSpace.basisFun (Fin 2) Complex right)) +
      (parameter.rate : Complex) *
        inner Complex (EuclideanSpace.basisFun (Fin 2) Complex left)
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Fin 2) Complex 1)
            (EuclideanSpace.basisFun (Fin 2) Complex 1)
            (EuclideanSpace.basisFun (Fin 2) Complex right)) = _
  simp only [InnerProductSpace.inner_right_rankOne_apply]
  simp only [(EuclideanSpace.basisFun (Fin 2) Complex).inner_eq_ite]
  fin_cases left
  · fin_cases right
    · simp [decodedRetryPoolDiagonalErrorRate, HH18NoisyInput.bitErrorWeight,
        ErrorParameter.cleanWeight]
      norm_cast
    · simp
  · fin_cases right
    · simp
    · change (parameter.cleanWeight : Complex) * (0 * 0) +
          (parameter.rate : Complex) * (1 * 1) =
        (HH18NoisyInput.bitErrorWeight
          (decodedRetryPoolDiagonalErrorRate parameter hhalf)
          ((1 : Fin 2) : ZMod 2) : Complex)
      have hcast : ((1 : Fin 2) : ZMod 2) = (1 : ZMod 2) := by decide
      rw [hcast]
      simp [HH18NoisyInput.bitErrorWeight,
        decodedRetryPoolDiagonalErrorRate]

/-- The register transport used for one physical block preserves the named
recursive computational basis without exposing its finite enumeration. -/
@[simp] theorem decodedRetryPoolQubitTensorPowerRegisterTransport_apply_basis
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (history : tensorPowerHistory (Fin 2) (Fintype.card ι)) :
    decodedRetryPoolQubitTensorPowerRegisterTransport ι
        (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
          (Fintype.card ι) history) =
      EuclideanSpace.basisFun (Bitstring ι) Complex
        (decodedRetryPoolQubitTensorPowerBitstringEquiv ι history) := by
  dsimp [decodedRetryPoolQubitTensorPowerRegisterTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- The flattened product of one actual successor record over the physical
sites of a single next-stage HH18 block. -/
noncomputable def decodedRetryPoolPhysicalRecordProductDensity
    (m w : Nat) (parameter : ErrorParameter)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator (PhysicalRegister m w) :=
  (decodedRetryPoolQubitTensorPowerRegisterTransport (PhysicalSite m w)).conjDensity
    (tensorPowerProductInput
      (decodedRetryPoolOneQubitRecordDensity parameter)
      rhoUnit (Fintype.card (PhysicalSite m w)))

/-- Computational entries of the actual physical record product are diagonal
with the exact Bernoulli word weight. -/
theorem decodedRetryPoolPhysicalRecordProductDensity_matrixEntry
    (m w : Nat) (parameter : ErrorParameter)
    (hhalf : parameter.rate ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (left right : Bitstring (PhysicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex left)
        ((decodedRetryPoolPhysicalRecordProductDensity m w parameter rhoUnit).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (PhysicalSite m w)) Complex right)) =
      if left = right then
        (HH18NoisyInput.errorWordWeight
          (decodedRetryPoolDiagonalErrorRate parameter hhalf)
          (bitstringWordEquiv (PhysicalSite m w) left) : Complex)
      else 0 := by
  let leftHistory :=
    (decodedRetryPoolQubitTensorPowerBitstringEquiv (PhysicalSite m w)).symm left
  let rightHistory :=
    (decodedRetryPoolQubitTensorPowerBitstringEquiv (PhysicalSite m w)).symm right
  have hleftHistoryAt (site : PhysicalSite m w) :
      tensorPowerHistoryAt (Fin 2) (Fintype.card (PhysicalSite m w))
          leftHistory (Fintype.equivFin (PhysicalSite m w) site) = left site := by
    exact congrFun
      ((decodedRetryPoolQubitTensorPowerBitstringEquiv
        (PhysicalSite m w)).apply_symm_apply left) site
  have hrightHistoryAt (site : PhysicalSite m w) :
      tensorPowerHistoryAt (Fin 2) (Fintype.card (PhysicalSite m w))
          rightHistory (Fintype.equivFin (PhysicalSite m w) site) = right site := by
    exact congrFun
      ((decodedRetryPoolQubitTensorPowerBitstringEquiv
        (PhysicalSite m w)).apply_symm_apply right) site
  calc
    _ = inner Complex
        (decodedRetryPoolQubitTensorPowerRegisterTransport (PhysicalSite m w)
          (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
            (Fintype.card (PhysicalSite m w)) leftHistory))
        ((decodedRetryPoolQubitTensorPowerRegisterTransport
          (PhysicalSite m w)).conjOperator
          (tensorPowerProductInput
            (decodedRetryPoolOneQubitRecordDensity parameter) rhoUnit
            (Fintype.card (PhysicalSite m w))).toOperator
          (decodedRetryPoolQubitTensorPowerRegisterTransport (PhysicalSite m w)
            (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
              (Fintype.card (PhysicalSite m w)) rightHistory))) := by
      simp only [decodedRetryPoolPhysicalRecordProductDensity,
        UnitaryTransport.conjDensity_toOperator,
        decodedRetryPoolQubitTensorPowerRegisterTransport_apply_basis]
      simp [leftHistory, rightHistory]
    _ = inner Complex
        (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
          (Fintype.card (PhysicalSite m w)) leftHistory)
        ((tensorPowerProductInput
          (decodedRetryPoolOneQubitRecordDensity parameter) rhoUnit
          (Fintype.card (PhysicalSite m w))).toOperator
          (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
            (Fintype.card (PhysicalSite m w)) rightHistory)) := by
      rw [UnitaryTransport.conjOperator_apply]
      simp only [LinearEquiv.symm_apply_apply]
      exact (decodedRetryPoolQubitTensorPowerRegisterTransport
        (PhysicalSite m w)).map_inner _ _
    _ = ∏ coordinate : Fin (Fintype.card (PhysicalSite m w)),
        inner Complex
          (EuclideanSpace.basisFun (Fin 2) Complex
            (tensorPowerHistoryAt (Fin 2) (Fintype.card (PhysicalSite m w))
              leftHistory coordinate))
          ((decodedRetryPoolOneQubitRecordDensity parameter).toOperator
            (EuclideanSpace.basisFun (Fin 2) Complex
              (tensorPowerHistoryAt (Fin 2) (Fintype.card (PhysicalSite m w))
                rightHistory coordinate))) := by
      exact tensorPowerProductInput_matrixEntry_eq_prod
        (EuclideanSpace.basisFun (Fin 2) Complex)
        (decodedRetryPoolOneQubitRecordDensity parameter) rhoUnit
        (Fintype.card (PhysicalSite m w)) leftHistory rightHistory
    _ = ∏ site : PhysicalSite m w,
        inner Complex
          (EuclideanSpace.basisFun (Fin 2) Complex (left site))
          ((decodedRetryPoolOneQubitRecordDensity parameter).toOperator
            (EuclideanSpace.basisFun (Fin 2) Complex (right site))) := by
      exact (Fintype.prod_equiv (Fintype.equivFin (PhysicalSite m w))
        _ _ (fun site => by rw [hleftHistoryAt site, hrightHistoryAt site])).symm
    _ = _ := by
      simp_rw [decodedRetryPoolOneQubitRecordDensity_matrixEntry parameter hhalf]
      by_cases heq : left = right
      · subst right
        simp only [ite_true, HH18NoisyInput.errorWordWeight,
          bitstringWordEquiv_apply]
        norm_cast
      · have hsite : ∃ site, left site ≠ right site := by
          simpa only [Function.ne_iff] using heq
        rw [if_neg heq]
        rcases hsite with ⟨site, hsite⟩
        rw [Finset.prod_eq_zero (Finset.mem_univ site)]
        simp [hsite]

/-- A recorded physical error word is the corresponding computational-basis
rank-one projector, expressed only through Kronecker deltas. -/
theorem errorWordBasisDensity_matrixEntry
    (m w : Nat) (error : PhysicalErrorWord m w)
    (left right : Bitstring (PhysicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex left)
        ((errorWordBasisDensity m w error).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (PhysicalSite m w)) Complex right)) =
      (if (bitstringWordEquiv (PhysicalSite m w)).symm error = right
        then 1 else 0) *
      (if left = (bitstringWordEquiv (PhysicalSite m w)).symm error
        then 1 else 0) := by
  rw [errorWordBasisDensity, DensityOperator.pureDensity_toOperator]
  change inner Complex
      (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex left)
      (InnerProductSpace.rankOne Complex
        (errorWordBasisState m w error) (errorWordBasisState m w error)
        (EuclideanSpace.basisFun
          (Bitstring (PhysicalSite m w)) Complex right)) = _
  rw [InnerProductSpace.inner_right_rankOne_apply]
  simp only [errorWordBasisState,
    (EuclideanSpace.basisFun
      (Bitstring (PhysicalSite m w)) Complex).inner_eq_ite]
  ac_rfl

/-- The measured-register mixture itself has the same diagonal Bernoulli
matrix entries, without unfolding a concrete error-word enumeration. -/
theorem prepareMeasuredResources_noisyResources_matrixEntry
    (m w : Nat) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (left right : Bitstring (PhysicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex left)
        ((prepareMeasuredResources m w (noisyResources m w epsilon)).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (PhysicalSite m w)) Complex right)) =
      if left = right then
        (HH18NoisyInput.errorWordWeight epsilon
          (bitstringWordEquiv (PhysicalSite m w) left) : Complex)
      else 0 := by
  rw [prepareMeasuredResources_toOperator]
  simp_rw [measuredErrorWordProbability_noisyResources]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, inner_smul_right]
  simp_rw [errorWordBasisDensity_matrixEntry]
  by_cases heq : left = right
  · subst right
    rw [if_pos rfl]
    rw [Finset.sum_eq_single
      (bitstringWordEquiv (PhysicalSite m w) left)]
    · simp
    · intro error _ herror
      have hbits :
          (bitstringWordEquiv (PhysicalSite m w)).symm error ≠ left := by
        intro hsame
        apply herror
        rw [← (bitstringWordEquiv (PhysicalSite m w)).apply_symm_apply error,
          hsame]
      simp [hbits]
    · simp [mem_physicalErrorWords]
  · rw [if_neg heq]
    apply Finset.sum_eq_zero
    intro error _
    by_cases hleft :
        left = (bitstringWordEquiv (PhysicalSite m w)).symm error
    · have hright :
          (bitstringWordEquiv (PhysicalSite m w)).symm error ≠ right := by
        intro hmatch
        exact heq (hleft.trans hmatch)
      simp [hleft, hright]
    · simp [hleft]

/-- A genuine product of successor records is exactly the measured physical
input density consumed by the next HH18 block. -/
theorem decodedRetryPoolPhysicalRecordProductDensity_eq_prepareMeasuredResources
    (m w : Nat) (parameter : ErrorParameter)
    (hhalf : parameter.rate ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalRecordProductDensity m w parameter rhoUnit =
      prepareMeasuredResources m w
        (noisyResources m w
          (decodedRetryPoolDiagonalErrorRate parameter hhalf)) := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex
  apply basis.toBasis.ext
  intro right
  apply InnerProductSpace.ext_inner_left_basis basis.toBasis
  intro left
  exact decodedRetryPoolPhysicalRecordProductDensity_matrixEntry
    m w parameter hhalf rhoUnit left right |>.trans
      (prepareMeasuredResources_noisyResources_matrixEntry
        m w (decodedRetryPoolDiagonalErrorRate parameter hhalf) left right).symm

end HH18Parameterized
end Distillation
end QEC
