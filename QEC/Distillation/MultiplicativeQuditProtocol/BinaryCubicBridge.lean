import QEC.Distillation.MultiplicativeQuditProtocol.BinaryTaggedEncoding
import QEC.Distillation.MultiplicativeQuditProtocol.BinaryPhysicalCCZ
import QEC.Coding.FiniteFieldMultiplication.BinaryConversion

/-!
# The RMFE and MFE intertwining equations on complete registers

These are the two source identities surrounding the already proved qudit
encoding equation: the physical selected CCZ product pulls back to the
weighted functional, and that functional restricts to parallel logical CCZ.
The basis calculations are extended to equalities of full linear maps.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The actual selected, inverse-permuted binary monomials reconstruct the weighted field cubic. -/
theorem binarySelectedExponent_physicalWord
    (u : TaggedThreeCopyRegisterLabel F256 J) :
    binarySelectedExponent (taggedPhysicalWordEmbedding J u) =
      f256RMFEpsi (taggedCubicPhaseExponent Finset.univ u) := by
  unfold binarySelectedExponent binarySelectedSites
  erw [Finset.sum_product]
  change (∑ j : J, ∑ q ∈ f256SelectedCoordinates,
    f256MFESigma (u (.first, j)) q * f256MFESigma (u (.second, j)) (f256MFEpi2 q) *
      f256MFESigma (u (.third, j)) (f256MFEpi3 q)) = _
  simp_rw [f256SelectedCoordinates_ternary_identity]
  rw [← map_sum]
  rfl

/-- MFE transversality is an equality on the whole field-labelled Hilbert space. -/
theorem binaryPhysicalCCZ_intertwines_physicalIsometry :
    (binaryPhysicalCCZ (J := J)).toLinearEquiv.toLinearMap.comp
        (taggedPhysicalIsometry J).toLinearMap =
      (taggedPhysicalIsometry J).toLinearMap.comp
        (taggedCubicPhysicalTransport (J := J) f256RMFEpsi).toLinearEquiv.toLinearMap := by
  apply (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F256 J) Complex).toBasis.ext
  intro u
  change binaryPhysicalCCZ (taggedPhysicalIsometry J (registerBasisKet u)) =
    taggedPhysicalIsometry J (taggedCubicPhysicalTransport f256RMFEpsi (registerBasisKet u))
  rw [taggedPhysicalIsometry_basis, binaryPhysicalCCZ_apply_basis,
    taggedCubicPhysicalTransport_apply_basis, map_smul, taggedPhysicalIsometry_basis]
  rw [binarySelectedExponent_physicalWord]
  rfl

/-- Parallel logical CCZ on every logical site is itself the actual finite local-gate product. -/
def binaryLogicalCCZ : UnitaryTransport (TaggedThreeCopyRegister (ZMod 2) J)
    (TaggedThreeCopyRegister (ZMod 2) J) :=
  taggedCubicPhysicalTransport (LinearMap.id : (ZMod 2) →ₗ[ZMod 2] ZMod 2)

omit [DecidableEq J] in
theorem taggedRMFE_cubicExponent (u : TaggedThreeCopyRegisterLabel (ZMod 2) J) :
    f256RMFEpsi (taggedCubicPhaseExponent Finset.univ
      (logicalWordEmbedding (ThreeCopyTag × J) u)) =
      taggedCubicPhaseExponent Finset.univ u := by
  unfold taggedCubicPhaseExponent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact f256RMFE_ternary_reverse_mul (u (.first, j)) (u (.second, j)) (u (.third, j))

/-- RMFE logical restriction intertwines full operators, not only logical basis labels. -/
theorem taggedLogicalIsometry_intertwines_binaryLogicalCCZ :
    (taggedCubicPhaseTransport (J := J) f256RMFEpsi Finset.univ).toLinearEquiv.toLinearMap.comp
        (taggedLogicalIsometry J).toLinearMap =
      (taggedLogicalIsometry J).toLinearMap.comp (binaryLogicalCCZ (J := J)).toLinearEquiv.toLinearMap := by
  apply (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel (ZMod 2) J) Complex).toBasis.ext
  intro u
  change taggedCubicPhaseTransport f256RMFEpsi Finset.univ
      (taggedLogicalIsometry J (registerBasisKet u)) =
    taggedLogicalIsometry J (taggedCubicPhysicalTransport (LinearMap.id : (ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (registerBasisKet u))
  rw [taggedLogicalIsometry_basis, taggedCubicPhaseTransport_apply_basis,
    taggedCubicPhysicalTransport_apply_basis, map_smul, taggedLogicalIsometry_basis]
  unfold taggedCubicPhaseAmplitude
  rw [taggedRMFE_cubicExponent]
  rfl

section SourceEncoding

variable {I Logical : Type} [Fintype I] [Fintype Logical]
local instance binaryCubicLogicalDecidableEq : DecidableEq Logical := Classical.decEq _

/-- The actual selected physical CCZ product implements all logical CCZs on every input state. -/
theorem sourceBinaryTaggedEncoding_intertwining (data : SourceInput F256 I Logical)
    (psi : TaggedThreeCopyRegister (ZMod 2) Logical) :
    binaryPhysicalCCZ (sourceBinaryTaggedEncodingIsometry data psi) =
      sourceBinaryTaggedEncodingIsometry data (binaryLogicalCCZ psi) := by
  change binaryPhysicalCCZ (taggedPhysicalIsometry _
    (taggedEncodingLinearMap data (taggedLogicalIsometry Logical psi))) =
    taggedPhysicalIsometry _ (taggedEncodingLinearMap data
      (taggedLogicalIsometry Logical (binaryLogicalCCZ psi)))
  have hp := LinearMap.congr_fun
    (binaryPhysicalCCZ_intertwines_physicalIsometry (J := data.PivotComplement))
      (taggedEncodingLinearMap data (taggedLogicalIsometry Logical psi))
  change binaryPhysicalCCZ (taggedPhysicalIsometry _ _) = taggedPhysicalIsometry _ _ at hp
  rw [hp]
  have hq := taggedCubicPhysicalTransport_implements_logical data f256RMFEpsi
    (taggedLogicalIsometry Logical psi)
  change taggedCubicPhysicalTransport f256RMFEpsi (taggedEncodingLinearMap data _) =
    taggedEncodingLinearMap data (taggedCubicPhaseTransport f256RMFEpsi Finset.univ _) at hq
  erw [hq]
  have hl := LinearMap.congr_fun
    (taggedLogicalIsometry_intertwines_binaryLogicalCCZ (J := Logical)) psi
  exact congrArg (fun x => taggedPhysicalIsometry data.PivotComplement
    (taggedEncodingLinearMap data x)) hl

end SourceEncoding

end QEC.Distillation.Ngu24Binary
