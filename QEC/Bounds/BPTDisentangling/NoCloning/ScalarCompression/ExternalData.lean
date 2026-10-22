import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.Core

/-!
# BPT external-residual transport contracts

Named inputs for the physical zero-extension and scalar-compression facts used
by the external-probe transport.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- A `C'` probe, its pullback to the active subtype, and its physical zero-extension. -/
def ExternalResidualProbePullback
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Y : Semantics.Operator (WC.restrictScalars Complex))
    (E : Semantics.Operator (ccomponent.1.restrictScalars Complex))
    (Ephysical : Semantics.Operator (M.fourFactorC region)) : Prop :=
  E = UC.symm.conjOperator
      (TensorProduct.map Y
        (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))) ∧
  Ephysical = (ccomponent.1.restrictScalars Complex).subtype.comp
    (E.comp (LinearMap.adjoint (ccomponent.1.restrictScalars Complex).subtype))

/-- Exact physical external-residual scalar-compression equation for one probe. -/
def PhysicalExternalResidualProbeCompression
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB : Nat} [NeZero nB]
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (Ephysical : Semantics.Operator (M.fourFactorC region))
    (scalar : Complex) : Prop :=
  Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Ephysical (1 : Semantics.Operator (M.fourFactorD region))) *
      Qsecond = scalar • Qsecond

end BPTCommutingProjectorModel

end Bounds
end QEC
