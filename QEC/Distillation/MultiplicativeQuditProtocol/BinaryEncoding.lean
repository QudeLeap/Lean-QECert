import QEC.Semantics.Core.ComputationalEmbedding
import QEC.Distillation.MultiplicativeQuditProtocol.NormalClosureFamily
import QEC.Coding.FiniteFieldMultiplication.Selector

/-!
# The actual RMFE-qudit-MFE binary encoder

The logical labels are restricted to the concrete width-one RMFE image,
encoded by the actual shortened qudit CSS encoder, and physically embedded
by the explicit MFE, as in [Ngu24, Main-result proof]. The range, basis action
and dimension are derived. The CSS common-fixed-carrier identification is
proved separately; it is not stored in this encoder definition.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators

variable (J : Type)

/-- Restrict each logical field label to the actual width-one RMFE image. -/
def logicalWordEmbedding : (J → ZMod 2) →ₗ[ZMod 2] (J → F256) where
  toFun u j := f256RMFEphi (u j)
  map_add' u v := by ext j; exact map_add f256RMFEphi _ _
  map_smul' c u := by ext j; exact f256RMFEphi.map_smul c (u j)

theorem logicalWordEmbedding_injective : Function.Injective (logicalWordEmbedding J) := by
  intro u v h
  funext j
  exact f256RMFEphi_injective (congrFun h j)

/-- Encode every physical field site by the explicit length-512 MFE. -/
def physicalWordEmbedding : (J → F256) →ₗ[ZMod 2] ((J × Fin 512) → ZMod 2) where
  toFun u x := f256MFESigma (u x.1) x.2
  map_add' u v := by ext x; exact congrFun (map_add f256MFESigma _ _) x.2
  map_smul' c u := by ext x; exact congrFun (f256MFESigma.map_smul c (u x.1)) x.2

theorem physicalWordEmbedding_injective : Function.Injective (physicalWordEmbedding J) := by
  intro u v h
  funext j
  apply f256MFESigma_injective
  funext q
  exact congrFun h (j, q)

section Native

variable [Fintype J] [DecidableEq J]

local instance {A : Type} [Fintype A] : Fintype (Word F256 A) := Fintype.ofFinite _

def logicalIsometry : Qubit.QubitRegister J →ₗᵢ[Complex] ComputationalBasisRegister F256 J :=
  ComputationalEmbedding.isometry ⟨logicalWordEmbedding J, logicalWordEmbedding_injective J⟩

def physicalIsometry : ComputationalBasisRegister F256 J →ₗᵢ[Complex]
    Qubit.QubitRegister (J × Fin 512) :=
  ComputationalEmbedding.isometry ⟨physicalWordEmbedding J, physicalWordEmbedding_injective J⟩

theorem logicalIsometry_basis (u : J → ZMod 2) :
    logicalIsometry J (EuclideanSpace.basisFun (J → ZMod 2) Complex u) =
      EuclideanSpace.basisFun (J → F256) Complex (logicalWordEmbedding J u) :=
  ComputationalEmbedding.isometry_basis _ _

theorem physicalIsometry_basis (u : J → F256) :
    physicalIsometry J (EuclideanSpace.basisFun (J → F256) Complex u) =
      EuclideanSpace.basisFun ((J × Fin 512) → ZMod 2) Complex (physicalWordEmbedding J u) :=
  ComputationalEmbedding.isometry_basis _ _

/-- The actual logical restriction, qudit encoder, and physical MFE in source order. -/
def binaryEncodingIsometry (i : Nat) :
    Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i)) →ₗᵢ[Complex]
      Qubit.QubitRegister ((f256SourceInput i).PivotComplement × Fin 512) :=
  (physicalIsometry (f256SourceInput i).PivotComplement).comp
    ((f256SourceInput i).encodingIsometry.comp
      (logicalIsometry (Fin (f256MultiplicationLogicalCount i))))

def binaryEncodedCode (i : Nat) :
    EncodedCode (Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i)))
      (Qubit.QubitRegister ((f256SourceInput i).PivotComplement × Fin 512)) where
  code := ⟨(binaryEncodingIsometry i).toLinearMap.range⟩
  encoding := LinearIsometry.equivRange (binaryEncodingIsometry i)

theorem binaryEncodedCode_dimension (i : Nat) :
    (binaryEncodedCode i).code.dimension = 2 ^ f256MultiplicationLogicalCount i := by
  have h := (binaryEncodedCode i).encoding.toLinearEquiv.finrank_eq
  rw [finrank_euclideanSpace] at h
  simp only [Qubit.Bitstring, Fintype.card_fun, Fintype.card_fin] at h
  exact h.symm

theorem binaryEncodedCode_basis (i : Nat) (u : Fin (f256MultiplicationLogicalCount i) → ZMod 2) :
    (binaryEncodedCode i).encode (EuclideanSpace.basisFun _ Complex u) =
      physicalIsometry (f256SourceInput i).PivotComplement
        ((f256SourceInput i).shortenedCosetKet
          (logicalWordEmbedding (Fin (f256MultiplicationLogicalCount i)) u)) := by
  change physicalIsometry _ ((f256SourceInput i).encodingLinearMap
    (logicalIsometry _ (EuclideanSpace.basisFun
      (Fin (f256MultiplicationLogicalCount i) → ZMod 2) Complex u))) = _
  rw [logicalIsometry_basis]
  exact congrArg (physicalIsometry _) ((f256SourceInput i).encodingLinearMap_apply_logical_basis _)

end Native

end QEC.Distillation.Ngu24Binary
