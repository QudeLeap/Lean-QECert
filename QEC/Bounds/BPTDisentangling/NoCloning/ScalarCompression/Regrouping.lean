import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.Aggregate

/-!
# BPT scalar-compression regrouping

Cacheable transport of the two exact active-sector scalar-compression families
across the tensor associator used by the no-cloning argument.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- Exact two-sided scalar-compression families after reassociating `N tensor (C tensor D)`. -/
def RegroupedTwoFactorScalarCompressions
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C D))) : Prop :=
  (∀ X : Semantics.Operator N, ∃ scalar : Complex,
    (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
        TensorProduct.map (TensorProduct.map X (1 : Semantics.Operator C))
          (1 : Semantics.Operator D) *
        (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) ∧
  (∀ Y : Semantics.Operator C, ∃ scalar : Complex,
    (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
        TensorProduct.map (TensorProduct.map (1 : Semantics.Operator N) Y)
          (1 : Semantics.Operator D) *
        (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright)

set_option maxHeartbeats 4000000 in
/-- Reassociate both exact active-sector scalar-compression families. -/
theorem regroup_actual_active_sector_scalar_compressions
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hrawInternal :
      M.ActualInternalResidualScalarCompression region ccomponent WC UC Qsecond)
    (hrawExternal :
      M.ActualExternalResidualScalarCompression region ccomponent WC UC Qsecond) :
    RegroupedTwoFactorScalarCompressions
      (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) := by
  let N := isotypicLiftedMultiplicity.{0} nB
  let NC := isotypicLiftedMultiplicity.{0} nC
  let C' := WC.restrictScalars Complex
  let D' := Semantics.CompositeSystem NC (M.fourFactorD region)
  let Qprime : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C' D')) :=
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
  change RegroupedTwoFactorScalarCompressions Qprime
  constructor
  · intro X
    rcases hrawInternal X with ⟨scalar, hscalar⟩
    refine ⟨scalar, ?_⟩
    change Qprime * TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator C')
          (TensorProduct.map (1 : Semantics.Operator NC)
            (1 : Semantics.Operator (M.fourFactorD region)))) *
        Qprime = scalar • Qprime at hscalar
    have hscalar' : Qprime * TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator C') (1 : Semantics.Operator D')) *
        Qprime = scalar • Qprime := by
      simpa only [D', TensorProduct.map_one] using hscalar
    have htransport := unitaryTransport_conj_scalar_compression
      (tensorAssociatorUnitary N C' D').symm Qprime
      (TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator C') (1 : Semantics.Operator D')))
      scalar hscalar'
    rw [tensorAssociatorUnitary_symm_conj_tensorMap] at htransport
    exact htransport
  · intro Y
    rcases hrawExternal Y with ⟨scalar, hscalar⟩
    refine ⟨scalar, ?_⟩
    change Qprime * TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator NC)
            (1 : Semantics.Operator (M.fourFactorD region)))) *
        Qprime = scalar • Qprime at hscalar
    have hscalar' : Qprime * TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map Y (1 : Semantics.Operator D')) * Qprime = scalar • Qprime := by
      simpa only [D', TensorProduct.map_one] using hscalar
    have htransport := unitaryTransport_conj_scalar_compression
      (tensorAssociatorUnitary N C' D').symm Qprime
      (TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map Y (1 : Semantics.Operator D'))) scalar hscalar'
    rw [tensorAssociatorUnitary_symm_conj_tensorMap] at htransport
    exact htransport

end BPTCommutingProjectorModel

end Bounds
end QEC
