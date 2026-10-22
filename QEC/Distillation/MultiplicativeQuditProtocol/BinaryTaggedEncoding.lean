import QEC.Distillation.MultiplicativeQuditProtocol.BinaryCSS
import QEC.Distillation.MultiplicativeQuditProtocol.CubicPhase

/-!
# The actual three-tag binary encoding

Logical RMFE restriction and physical MFE concatenation are applied to each
of the three explicitly tagged blocks. Between them is the existing uniform
three-block qudit coset encoder. The tensor-product identification is proved
separately; this module fixes the literal maps and their basis action.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators

variable (J : Type)

/-- The physical MFE acts within each tagged block, without mixing the tags. -/
def taggedPhysicalWordEmbedding : TaggedThreeCopyRegisterLabel F256 J →ₗ[ZMod 2]
    TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512) where
  toFun u x := f256MFESigma (u (x.1, x.2.1)) x.2.2
  map_add' u v := by ext x; exact congrFun (map_add f256MFESigma _ _) x.2.2
  map_smul' c u := by ext x; exact congrFun (f256MFESigma.map_smul c _) x.2.2

theorem taggedPhysicalWordEmbedding_injective : Function.Injective (taggedPhysicalWordEmbedding J) := by
  intro u v h
  funext x
  apply f256MFESigma_injective
  funext q
  exact congrFun h (x.1, (x.2, q))

variable [Fintype J] [DecidableEq J]

/-- The joint logical embedding is the same RMFE on every tag/site pair. -/
def taggedLogicalIsometry : TaggedThreeCopyRegister (ZMod 2) J →ₗᵢ[Complex]
    TaggedThreeCopyRegister F256 J :=
  ComputationalEmbedding.isometry
    ⟨logicalWordEmbedding (ThreeCopyTag × J), logicalWordEmbedding_injective _⟩

/-- The physical label injection extended to the complete tagged Hilbert space. -/
def taggedPhysicalIsometry : TaggedThreeCopyRegister F256 J →ₗᵢ[Complex]
    TaggedThreeCopyRegister (ZMod 2) (J × Fin 512) :=
  ComputationalEmbedding.isometry
    ⟨taggedPhysicalWordEmbedding J, taggedPhysicalWordEmbedding_injective J⟩

theorem taggedLogicalIsometry_basis (u : TaggedThreeCopyRegisterLabel (ZMod 2) J) :
    taggedLogicalIsometry J (registerBasisKet u) =
      registerBasisKet (logicalWordEmbedding (ThreeCopyTag × J) u) :=
  ComputationalEmbedding.isometry_basis _ _

theorem taggedPhysicalIsometry_basis (u : TaggedThreeCopyRegisterLabel F256 J) :
    taggedPhysicalIsometry J (registerBasisKet u) =
      registerBasisKet (taggedPhysicalWordEmbedding J u) :=
  ComputationalEmbedding.isometry_basis _ _

local instance (priority := 2000) binaryTaggedFinDecidableEq {n : Nat} :
    DecidableEq (Fin n) := instDecidableEqFin n

section SourceEncoding

variable {I Logical : Type} [Fintype I] [Fintype Logical]
local instance binaryTaggedLogicalDecidableEq : DecidableEq Logical := Classical.decEq _

/-- Compose the three actual source maps before specializing the AG tower parameters. -/
def sourceBinaryTaggedEncodingIsometry (data : SourceInput F256 I Logical) :
    TaggedThreeCopyRegister (ZMod 2) Logical →ₗᵢ[Complex]
      TaggedThreeCopyRegister (ZMod 2) (data.PivotComplement × Fin 512) :=
  (taggedPhysicalIsometry data.PivotComplement).comp
    ((taggedEncodingIsometry data).comp (taggedLogicalIsometry Logical))

/-- The same joint encoder as a linear map, independent of norm-instance elaboration. -/
def sourceBinaryTaggedEncodingLinearMap (data : SourceInput F256 I Logical) :
    TaggedThreeCopyRegister (ZMod 2) Logical →ₗ[Complex]
      TaggedThreeCopyRegister (ZMod 2) (data.PivotComplement × Fin 512) :=
  (sourceBinaryTaggedEncodingIsometry data).toLinearMap

theorem sourceBinaryTaggedEncodingIsometry_basis (data : SourceInput F256 I Logical)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) Logical) :
    sourceBinaryTaggedEncodingIsometry data (registerBasisKet u) =
      taggedCosetNormalization data • ∑ h : ThreeCopyTag → data.H0,
        registerBasisKet (taggedPhysicalWordEmbedding data.PivotComplement
          (taggedShortenedCosetLabel data (logicalWordEmbedding (ThreeCopyTag × Logical) u) h)) := by
  change taggedPhysicalIsometry _ (taggedEncodingLinearMap data
    (taggedLogicalIsometry Logical (registerBasisKet u))) = _
  rw [taggedLogicalIsometry_basis, taggedEncodingLinearMap_apply_logical_basis]
  unfold taggedShortenedCosetKet
  rw [map_smul, map_sum]
  simp_rw [taggedPhysicalIsometry_basis]

end SourceEncoding

/-- The three-tag source encoding with actual logical and physical embeddings. -/
def binaryTaggedEncodingIsometry (i : Nat) :=
  sourceBinaryTaggedEncodingIsometry (f256SourceInput i)

def binaryTaggedEncodingLinearMap (i : Nat) :
    TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i)) →ₗ[Complex]
      TaggedThreeCopyRegister (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  sourceBinaryTaggedEncodingLinearMap (f256SourceInput i)

/-- Each summand is the independently chosen actual binary coset in each tag. -/
def binaryTaggedCosetLabel (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (h : ThreeCopyTag → (f256SourceInput i).H0) :
    TaggedThreeCopyRegisterLabel (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  assembleTagged fun tag => binaryCosetWordMap i (extractBlock u tag, h tag)

theorem binaryTaggedCosetLabel_eq (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (h : ThreeCopyTag → (f256SourceInput i).H0) :
    taggedPhysicalWordEmbedding (f256SourceInput i).PivotComplement
      (taggedShortenedCosetLabel (f256SourceInput i)
        (logicalWordEmbedding (ThreeCopyTag × Fin (f256MultiplicationLogicalCount i)) u) h) =
      binaryTaggedCosetLabel i u h := by
  funext x
  change _ = binaryCosetWordMap i (extractBlock u x.1, h x.1) x.2
  rw [binaryCosetWordMap_apply]
  rfl

theorem binaryTaggedEncodingIsometry_basis (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryTaggedEncodingIsometry i (registerBasisKet u) =
      taggedCosetNormalization (f256SourceInput i) •
        ∑ h : ThreeCopyTag → (f256SourceInput i).H0,
          registerBasisKet (binaryTaggedCosetLabel i u h) := by
  rw [binaryTaggedEncodingIsometry]
  erw [sourceBinaryTaggedEncodingIsometry_basis]
  simp_rw [binaryTaggedCosetLabel_eq]

end QEC.Distillation.Ngu24Binary
