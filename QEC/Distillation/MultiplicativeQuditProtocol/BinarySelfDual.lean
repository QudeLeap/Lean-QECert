import QEC.Distillation.MultiplicativeQuditProtocol.BinaryEncoding
import QEC.Coding.FiniteFieldMultiplication.BinaryConversion

/-!
# The source's self-dual expansion followed by the physical MFE

The actual physical encoder factors through the fixed self-dual coordinates
and the map `sigma'_mfe` of [Ngu24, Main-result proof, Step 3]. This identifies
the intermediate encoding maps without identifying the polynomial basis
with the self-dual basis.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth

variable (J : Type)

/-- Expand every field site in the actual fixed self-dual basis. -/
def selfDualWordEquiv : (J → F256) ≃ₗ[ZMod 2] ((J × Fin 8) → ZMod 2) where
  toFun u x := f256SelfDualBasis.equivFun (u x.1) x.2
  invFun v j := f256SelfDualBasis.equivFun.symm (fun b => v (j, b))
  left_inv u := by
    funext j
    exact f256SelfDualBasis.equivFun.symm_apply_apply (u j)
  right_inv v := by
    funext x
    exact congrFun (f256SelfDualBasis.equivFun.apply_symm_apply (fun b => v (x.1, b))) x.2
  map_add' u v := by
    ext x
    exact congrFun (map_add f256SelfDualBasis.equivFun (u x.1) (v x.1)) x.2
  map_smul' c u := by
    ext x
    exact congrFun (f256SelfDualBasis.equivFun.map_smul c (u x.1)) x.2

/-- Apply `sigma'_mfe` independently to each eight-bit self-dual block. -/
def mfeFromSelfDualWordMap : ((J × Fin 8) → ZMod 2) →ₗ[ZMod 2]
    ((J × Fin 512) → ZMod 2) where
  toFun v x := f256MFEFromSelfDual (fun b => v (x.1, b)) x.2
  map_add' u v := by
    ext x
    exact congrFun (map_add f256MFEFromSelfDual _ _) x.2
  map_smul' c u := by
    ext x
    exact congrFun (f256MFEFromSelfDual.map_smul c _) x.2

theorem mfeFromSelfDualWordMap_injective : Function.Injective (mfeFromSelfDualWordMap J) := by
  intro u v h
  funext x
  have hb : (fun b => u (x.1, b)) = (fun b => v (x.1, b)) := by
    apply f256MFEFromSelfDual_injective
    funext q
    exact congrFun h (x.1, q)
  exact congrFun hb x.2

set_option maxRecDepth 2048 in
/-- The word-level basis change gives exactly the physical MFE already used. -/
theorem mfeFromSelfDualWordMap_comp_selfDualWordEquiv :
    (mfeFromSelfDualWordMap J).comp (selfDualWordEquiv J).toLinearMap =
      physicalWordEmbedding J := by
  apply LinearMap.ext
  intro u
  funext x
  change f256MFEFromSelfDual (f256SelfDualBasis.equivFun (u x.1)) x.2 =
    f256MFESigma (u x.1) x.2
  exact congrFun (f256MFEFromSelfDual_apply_basis_coordinates (u x.1)) x.2

section Native

variable [Fintype J] [DecidableEq J]
local instance binarySelfDualFieldWordFintype {A : Type} [Fintype A] :
    Fintype (Word F256 A) := Fintype.ofFinite _

/-- The actual computational-basis isometry for the self-dual expansion. -/
def selfDualIsometry : ComputationalBasisRegister F256 J →ₗᵢ[Complex]
    Qubit.QubitRegister (J × Fin 8) :=
  ComputationalEmbedding.isometry (selfDualWordEquiv J).toEquiv.toEmbedding

/-- The actual computational-basis isometry for `sigma'_mfe`. -/
def mfeFromSelfDualIsometry : Qubit.QubitRegister (J × Fin 8) →ₗᵢ[Complex]
    Qubit.QubitRegister (J × Fin 512) :=
  ComputationalEmbedding.isometry
    ⟨mfeFromSelfDualWordMap J, mfeFromSelfDualWordMap_injective J⟩

/-- Full linear-map factorization of the physical encoder through the source basis change. -/
theorem physicalIsometry_eq_selfDual_comp :
    (physicalIsometry J).toLinearMap =
      (mfeFromSelfDualIsometry J).toLinearMap.comp (selfDualIsometry J).toLinearMap := by
  have he : (selfDualWordEquiv J).toEquiv.toEmbedding.trans
      ⟨mfeFromSelfDualWordMap J, mfeFromSelfDualWordMap_injective J⟩ =
      ⟨physicalWordEmbedding J, physicalWordEmbedding_injective J⟩ := by
    apply Function.Embedding.ext
    intro u
    exact LinearMap.congr_fun (mfeFromSelfDualWordMap_comp_selfDualWordEquiv J) u
  exact (congrArg ComputationalEmbedding.linearMap he).symm.trans
    (ComputationalEmbedding.linearMap_comp _ _)

/-- The actual binary encoder has the self-dual/MFE concatenation in source order. -/
theorem binaryEncodingIsometry_selfDual_factorization (i : Nat) :
    (binaryEncodingIsometry i).toLinearMap =
      (mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement).toLinearMap.comp
        ((selfDualIsometry (f256SourceInput i).PivotComplement).toLinearMap.comp
          ((f256SourceInput i).encodingLinearMap.comp
            (logicalIsometry (Fin (f256MultiplicationLogicalCount i))).toLinearMap)) := by
  change (physicalIsometry _).toLinearMap.comp _ = _
  rw [physicalIsometry_eq_selfDual_comp, LinearMap.comp_assoc]
  rfl

/-- The source-ordered factorization evaluated on an arbitrary logical state. -/
theorem binaryEncodingIsometry_selfDual_apply (i : Nat)
    (psi : Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i))) :
    binaryEncodingIsometry i psi =
      mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement
        (selfDualIsometry (f256SourceInput i).PivotComplement
          ((f256SourceInput i).encodingLinearMap
            (logicalIsometry (Fin (f256MultiplicationLogicalCount i)) psi))) :=
  LinearMap.congr_fun (binaryEncodingIsometry_selfDual_factorization i) psi

end Native

end QEC.Distillation.Ngu24Binary
