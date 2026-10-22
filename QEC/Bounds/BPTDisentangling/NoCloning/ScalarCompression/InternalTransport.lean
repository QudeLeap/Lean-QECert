import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.Core

/-!
# BPT internal-probe scalar-compression transport

Pure transport from a physical internal-residual compression equation to the
actual active first-cut coordinates.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 1600000

/-- Transport one fixed internal-residual probe through the active `C` sector. -/
theorem internalResidual_scalar_compression_on_actual_active_sector
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
    (X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB)) (scalar : Complex)
    (hQ : Qsecond.IsSymmetricProjection)
    (hsupport :
      Qsecond.comp
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
            (TensorProduct.map
              (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
              (1 : Semantics.Operator (M.fourFactorD region)))) = Qsecond)
    (hscalar : M.PhysicalInternalResidualProbeCompression
      region Qsecond X scalar) :
    M.ActualInternalResidualProbeCompression
      region ccomponent WC UC Qsecond X scalar := by
  change M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
      TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
            (1 : Semantics.Operator (M.fourFactorD region)))) *
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
    scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
  change Qsecond *
      TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
          (1 : Semantics.Operator (M.fourFactorD region))) *
      Qsecond = scalar • Qsecond at hscalar
  let H := ccomponent.1.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} nB
  let NC := isotypicLiftedMultiplicity.{0} nC
  let C := M.fourFactorC region
  let D := M.fourFactorD region
  let K : (Semantics.CompositeSystem N (Semantics.CompositeSystem H D)) →ₗ[Complex]
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map H.subtype (1 : Semantics.Operator D))
  let Kadj := LinearMap.adjoint K
  let V := composeUnitaryTransport (unitaryRTensor UC D)
    (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D)
  let T := unitaryLTensor N V
  let Z : Semantics.Operator C :=
    leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent
  let S : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map Z (1 : Semantics.Operator D))
  have hsupport' : Qsecond.comp S = Qsecond := by
    simpa [S, Z, N, C, D] using hsupport
  have hKadj_eq : LinearMap.adjoint K = Kadj := rfl
  have hKKadj : K.comp Kadj = S := by
    dsimp [Kadj, K, S, Z]
    rw [TensorProduct.adjoint_map, LinearMap.adjoint_one,
      TensorProduct.adjoint_map, LinearMap.adjoint_one]
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
    rw [submoduleSubtype_comp_adjoint_eq_starProjection H]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id)
      (TensorProduct.map H.starProjection.toLinearMap (LinearMap.id.comp LinearMap.id)) =
        TensorProduct.map LinearMap.id
          (TensorProduct.map
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
            LinearMap.id)
    rw [LinearMap.id_comp, LinearMap.id_comp]
    rfl
  have hright : Qsecond.comp (K.comp Kadj) = Qsecond := by
    rw [hKKadj]
    exact hsupport'
  let R : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)) :=
    TensorProduct.map X
      (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D))
  let Rsub : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem H D)) :=
    TensorProduct.map X
      (TensorProduct.map (1 : Semantics.Operator H) (1 : Semantics.Operator D))
  have hscalar' : Qsecond * R * Qsecond = scalar • Qsecond := by
    simpa [R, N, C, D] using hscalar
  have hintertwines : K.comp Rsub = R.comp K := by
    dsimp [K, R, Rsub]
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp,
      ← TensorProduct.map_comp, ← TensorProduct.map_comp]
    rfl
  have htransfer := activeIsometric_unitaryTransport_scalar_compression_of_intertwining
    K Kadj Qsecond R Rsub T scalar hKadj_eq hQ hright hscalar' hintertwines
  have hTprobe : T.conjOperator Rsub =
      TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
          (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) := by
    have hsourceIdentity :
        TensorProduct.map (1 : Semantics.Operator H) (1 : Semantics.Operator D) =
          (1 : Semantics.Operator (Semantics.CompositeSystem H D)) :=
      TensorProduct.map_one
    have htargetInnerIdentity :
        TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D) =
          (1 : Semantics.Operator (Semantics.CompositeSystem NC D)) :=
      TensorProduct.map_one
    have htargetIdentity :
        TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
            (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D)) =
          (1 : Semantics.Operator (Semantics.CompositeSystem
            (WC.restrictScalars Complex) (Semantics.CompositeSystem NC D))) := by
      calc
        TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
            (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D)) =
          TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
            (1 : Semantics.Operator (Semantics.CompositeSystem NC D)) :=
          congrArg (TensorProduct.map
            (1 : Semantics.Operator (WC.restrictScalars Complex))) htargetInnerIdentity
        _ = 1 := TensorProduct.map_one
    have hRsubIdentity :
        Rsub = TensorProduct.map X
          (1 : Semantics.Operator (Semantics.CompositeSystem H D)) := by
      dsimp [Rsub]
      exact congrArg (TensorProduct.map X) hsourceIdentity
    have htargetMap :
        TensorProduct.map X
            (1 : Semantics.Operator (Semantics.CompositeSystem
              (WC.restrictScalars Complex) (Semantics.CompositeSystem NC D))) =
          TensorProduct.map X
            (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
              (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) :=
      congrArg (TensorProduct.map X) htargetIdentity.symm
    calc
      T.conjOperator Rsub =
          T.conjOperator (TensorProduct.map X
            (1 : Semantics.Operator (Semantics.CompositeSystem H D))) :=
        congrArg T.conjOperator hRsubIdentity
      _ = TensorProduct.map X
          (1 : Semantics.Operator (Semantics.CompositeSystem
            (WC.restrictScalars Complex) (Semantics.CompositeSystem NC D))) := by
        simpa only [T] using unitaryLTensor_conj_tensorMap_right N V X
      _ = TensorProduct.map X
          (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
            (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) :=
        htargetMap
  have hactiveBlock :
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
        T.conjOperator (Kadj.comp (Qsecond.comp K)) := by
    rfl
  have hleftProduct :
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
          TensorProduct.map X
            (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
              (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) =
        T.conjOperator (Kadj.comp (Qsecond.comp K)) * T.conjOperator Rsub :=
    congrArg₂ (fun left right => left * right) hactiveBlock hTprobe.symm
  calc
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
          TensorProduct.map X
            (TensorProduct.map (1 : Semantics.Operator (WC.restrictScalars Complex))
              (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) *
        M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
      (T.conjOperator (Kadj.comp (Qsecond.comp K)) * T.conjOperator Rsub) *
        T.conjOperator (Kadj.comp (Qsecond.comp K)) :=
      congrArg₂ (fun left right => left * right) hleftProduct hactiveBlock
    _ = scalar • T.conjOperator (Kadj.comp (Qsecond.comp K)) := htransfer
    _ = scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond :=
      congrArg (fun operator => scalar • operator) hactiveBlock.symm

end BPTCommutingProjectorModel

end Bounds
end QEC
