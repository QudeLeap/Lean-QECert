import QEC.Bounds.BPTDisentangling.NoCloning.ActiveProjection

/-!
# BPT scalar-compression contracts

Transparent names for the exact scalar-compression propositions proved by the
no-cloning transport layers.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- Exact physical internal-residual scalar-compression equation for one probe. -/
def PhysicalInternalResidualProbeCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB : Nat} [NeZero nB]
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
    (scalar : Complex) : Prop :=
  Qsecond *
      TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
          (1 : Semantics.Operator (M.fourFactorD region))) *
      Qsecond = scalar • Qsecond

/-- Exact internal-residual scalar-compression equation for one probe and scalar. -/
def ActualInternalResidualProbeCompression
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
    (X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
    (scalar : Complex) : Prop :=
  M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
      TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
            (1 : Semantics.Operator (M.fourFactorD region)))) *
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
    scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond

/-- Exact internal-residual scalar-compression family on the active joint block. -/
def ActualInternalResidualScalarCompression
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  ∀ X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB),
    ∃ scalar : Complex,
      M.ActualInternalResidualProbeCompression region ccomponent WC UC Qsecond X scalar

/-- Exact external-residual scalar-compression equation for one probe and scalar. -/
def ActualExternalResidualProbeCompression
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
    (Y : Semantics.Operator (WC.restrictScalars Complex)) (scalar : Complex) : Prop :=
  M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
            (1 : Semantics.Operator (M.fourFactorD region)))) *
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
    scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond

/-- Exact external-residual scalar-compression family on the active joint block. -/
def ActualExternalResidualScalarCompression
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  ∀ Y : Semantics.Operator (WC.restrictScalars Complex),
    ∃ scalar : Complex,
      M.ActualExternalResidualProbeCompression region ccomponent WC UC Qsecond Y scalar

/-- Projection, nonzeroness, and both exact scalar-compression families. -/
def ActualActiveSectorScalarCompressions
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
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) : Prop :=
  (LinearMap.IsSymmetricProjection
      (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) ∧
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond ≠ 0) ∧
  M.ActualInternalResidualScalarCompression region ccomponent WC UC Qsecond ∧
  M.ActualExternalResidualScalarCompression region ccomponent WC UC Qsecond

end BPTCommutingProjectorModel

end Bounds
end QEC
