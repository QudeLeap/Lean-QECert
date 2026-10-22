import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.ExternalData

/-!
# BPT external-probe scalar-compression transport

Pure transport from one physical external-residual compression equation to the
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

set_option maxHeartbeats 4000000

/-- Transport one fixed external-residual probe through the active `C` sector. -/
theorem externalResidual_scalar_compression_on_actual_active_sector
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
    (Y : Semantics.Operator (WC.restrictScalars Complex))
    (E : Semantics.Operator (ccomponent.1.restrictScalars Complex))
    (Ephysical : Semantics.Operator (M.fourFactorC region)) (scalar : Complex)
    (hPullback : M.ExternalResidualProbePullback
      region ccomponent WC UC Y E Ephysical)
    (hQ : Qsecond.IsSymmetricProjection)
    (hsupport :
      Qsecond.comp
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
            (TensorProduct.map
              (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
              (1 : Semantics.Operator (M.fourFactorD region)))) = Qsecond)
    (hscalar : M.PhysicalExternalResidualProbeCompression
      region Qsecond Ephysical scalar) :
    M.ActualExternalResidualProbeCompression
      region ccomponent WC UC Qsecond Y scalar := by
  change M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
            (1 : Semantics.Operator (M.fourFactorD region)))) *
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
    scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
  rcases hPullback with ⟨hE, hEphysical⟩
  change Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Ephysical (1 : Semantics.Operator (M.fourFactorD region))) *
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
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map Ephysical (1 : Semantics.Operator D))
  let Rsub : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem H D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map E (1 : Semantics.Operator D))
  have hscalar' : Qsecond * R * Qsecond = scalar • Qsecond := by
    simpa [R, N, C, D] using hscalar
  have hintertwines : K.comp Rsub = R.comp K := by
    simpa [K, R, Rsub, N, H, C, D, hEphysical] using
      (subtypeTensor_right_intertwines_zeroExtension (N := N) (D := D)
        (ccomponent.1.restrictScalars Complex) E)
  have htransfer := activeIsometric_unitaryTransport_scalar_compression_of_intertwining
    K Kadj Qsecond R Rsub (unitaryLTensor N V) scalar
      hKadj_eq hQ hright hscalar' hintertwines
  have hEtransport : UC.conjOperator E =
      TensorProduct.map Y (1 : Semantics.Operator NC) := by
    rw [hE, UC.conjOperator_symm_conjOperator]
  have hVprobe : V.conjOperator
        (TensorProduct.map E (1 : Semantics.Operator D)) =
      TensorProduct.map Y
        (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D)) := by
    calc
      V.conjOperator (TensorProduct.map E (1 : Semantics.Operator D)) =
          (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
            ((unitaryRTensor UC D).conjOperator
              (TensorProduct.map E (1 : Semantics.Operator D))) := by
        simpa only [V] using
          composeUnitaryTransport_conjOperator (unitaryRTensor UC D)
            (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D)
            (TensorProduct.map E (1 : Semantics.Operator D))
      _ = (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
          (TensorProduct.map (UC.conjOperator E) (1 : Semantics.Operator D)) :=
        congrArg
          (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
          (unitaryRTensor_conj_tensorMap_left UC D E)
      _ = (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
          (TensorProduct.map
            (TensorProduct.map Y (1 : Semantics.Operator NC))
            (1 : Semantics.Operator D)) :=
        congrArg
          (fun operator =>
            (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
              (TensorProduct.map operator (1 : Semantics.Operator D)))
          hEtransport
      _ = TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D)) :=
        tensorAssociatorUnitary_conj_tensorMap Y
          (1 : Semantics.Operator NC) (1 : Semantics.Operator D)
  have hTprobe : (unitaryLTensor N V).conjOperator Rsub =
      TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) := by
    calc
      (unitaryLTensor N V).conjOperator Rsub =
          TensorProduct.map (1 : Semantics.Operator N)
            (V.conjOperator (TensorProduct.map E (1 : Semantics.Operator D))) := by
        simpa only [Rsub] using
        unitaryLTensor_conj_tensorMap_left N V
          (TensorProduct.map E (1 : Semantics.Operator D))
      _ = TensorProduct.map (1 : Semantics.Operator N)
          (TensorProduct.map Y
            (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) :=
        congrArg (TensorProduct.map (1 : Semantics.Operator N)) hVprobe
  have hactiveBlock :
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
        (unitaryLTensor N V).conjOperator (Kadj.comp (Qsecond.comp K)) := by
    rfl
  have hleftProduct :
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
          TensorProduct.map (1 : Semantics.Operator N)
            (TensorProduct.map Y
              (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) =
        (unitaryLTensor N V).conjOperator (Kadj.comp (Qsecond.comp K)) *
          (unitaryLTensor N V).conjOperator Rsub :=
    congrArg₂ (fun left right => left * right) hactiveBlock hTprobe.symm
  calc
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
          TensorProduct.map (1 : Semantics.Operator N)
            (TensorProduct.map Y
              (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) *
        M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
      ((unitaryLTensor N V).conjOperator (Kadj.comp (Qsecond.comp K)) *
        (unitaryLTensor N V).conjOperator Rsub) *
        (unitaryLTensor N V).conjOperator (Kadj.comp (Qsecond.comp K)) :=
      congrArg₂ (fun left right => left * right) hleftProduct hactiveBlock
    _ = scalar • (unitaryLTensor N V).conjOperator
        (Kadj.comp (Qsecond.comp K)) := htransfer
    _ = scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond :=
      congrArg (fun operator => scalar • operator) hactiveBlock.symm

end BPTCommutingProjectorModel

end Bounds
end QEC
