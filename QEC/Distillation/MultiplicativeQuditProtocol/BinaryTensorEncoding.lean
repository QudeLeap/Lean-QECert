import QEC.Distillation.MultiplicativeQuditProtocol.BinaryTaggedEncoding
import QEC.Distillation.MultiplicativeQuditProtocol.TensorRegister

/-!
# The tagged binary encoder is the literal tensor cube of the one-block encoder

The three independent kernel sums and the cube of the one-block normalization
give exactly the matrix entries of `E tensor (E tensor E)`. Equality on the
computational basis then identifies the full linear maps, including entangled
logical inputs.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators

theorem binaryEncodingIsometry_basis_apply (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (v : Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512)) :
    binaryEncodingIsometry i (EuclideanSpace.basisFun _ Complex u) v =
      SourceInput.cosetNormalization (f256SourceInput i).H0 *
        ∑ h : (f256SourceInput i).H0,
          EuclideanSpace.basisFun _ Complex (binaryCosetWordMap i (u, h)) v := by
  change (binaryEncodedCode i).encode (EuclideanSpace.basisFun _ Complex u) v = _
  rw [binaryEncodedCode_basis_eq_coset]
  simp only [binaryCosetKet, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]

theorem binaryTaggedEncodingIsometry_basis_apply_product (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (v : TaggedThreeCopyRegisterLabel (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512)) :
    binaryTaggedEncodingIsometry i (registerBasisKet u) v =
      binaryEncodingIsometry i (EuclideanSpace.basisFun _ Complex (extractBlock u .first))
          (extractBlock v .first) *
        binaryEncodingIsometry i (EuclideanSpace.basisFun _ Complex (extractBlock u .second))
          (extractBlock v .second) *
        binaryEncodingIsometry i (EuclideanSpace.basisFun _ Complex (extractBlock u .third))
          (extractBlock v .third) := by
  rw [binaryTaggedEncodingIsometry_basis]
  erw [binaryEncodingIsometry_basis_apply i (extractBlock u .first) (extractBlock v .first),
    binaryEncodingIsometry_basis_apply i (extractBlock u .second) (extractBlock v .second),
    binaryEncodingIsometry_basis_apply i (extractBlock u .third) (extractBlock v .third)]
  simp only [taggedCosetNormalization, PiLp.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply]
  rw [sum_threeTag]
  simp_rw [registerBasisKet, taggedBasis_apply_eq_product]
  change (SourceInput.cosetNormalization (f256SourceInput i).H0)^3 *
    (∑ a, ∑ b, ∑ c,
      EuclideanSpace.basisFun _ Complex (binaryCosetWordMap i (extractBlock u .first, a))
          (extractBlock v .first) *
        EuclideanSpace.basisFun _ Complex (binaryCosetWordMap i (extractBlock u .second, b))
          (extractBlock v .second) *
        EuclideanSpace.basisFun _ Complex (binaryCosetWordMap i (extractBlock u .third, c))
          (extractBlock v .third)) = _
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  ring_nf

/-- Full operator identification with the actual one-block encoder's literal tensor cube. -/
theorem binaryTaggedEncodingIsometry_eq_tensorCube (i : Nat)
    (psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryTaggedEncodingIsometry i psi =
      taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
        ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi := by
  let B := EuclideanSpace.basisFun
    (TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) Complex
  change binaryTaggedEncodingLinearMap i psi = _
  rw [← B.sum_repr psi]
  erw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro u _
  erw [map_smul, map_smul]
  congr 1
  ext v
  exact (binaryTaggedEncodingIsometry_basis_apply_product i u v).trans
    (taggedTensorCube_basis_apply (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
      ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap u v).symm

end QEC.Distillation.Ngu24Binary
