import QEC.Distillation.MultiplicativeQuditProtocol.BinaryEncoding
import QEC.Coding.Stabilizer.BasisAction

/-!
# The actual classical spaces underlying the binary CSS encoder

The source defines a CSS carrier as the span of uniform cosets of a binary
linear subspace inside another one [Ngu24, Section: Preliminaries]. Here both
spaces are literal images of the shortened kernel and RMFE-restricted
systematic representatives under the fixed physical MFE.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators

section ClassicalWords

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

/-- Binary image of the actual punctured shortened kernel. -/
def binaryKernelWordMap (i : Nat) : (f256SourceInput i).H0 →ₗ[ZMod 2]
    Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  (physicalWordEmbedding (f256SourceInput i).PivotComplement).comp
    (((f256SourceInput i).puncture.comp
      ((f256SourceInput i).code.carrier.subtype.comp
        (f256SourceInput i).shortenedKernel.subtype)).restrictScalars (ZMod 2))

/-- Binary image of the actual systematic representative of a logical RMFE word. -/
def binaryRepresentativeWordMap (i : Nat) :
    Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i)) →ₗ[ZMod 2]
      Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  (physicalWordEmbedding (f256SourceInput i).PivotComplement).comp
    ((((f256SourceInput i).puncture.comp
      ((f256SourceInput i).code.carrier.subtype.comp
        (f256SourceInput i).pivotSection)).restrictScalars (ZMod 2)).comp
          (logicalWordEmbedding (Fin (f256MultiplicationLogicalCount i))))

/-- The full binary label map, with independent logical and kernel arguments. -/
def binaryCosetWordMap (i : Nat) :
    (Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i)) × (f256SourceInput i).H0) →ₗ[ZMod 2]
      Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  (binaryRepresentativeWordMap i).coprod (binaryKernelWordMap i)

theorem binaryCosetWordMap_apply (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) (h : (f256SourceInput i).H0) :
    binaryCosetWordMap i (u, h) = physicalWordEmbedding (f256SourceInput i).PivotComplement
      ((f256SourceInput i).shortenedCosetLabel
        (logicalWordEmbedding (Fin (f256MultiplicationLogicalCount i)) u) h) := by
  change physicalWordEmbedding _ ((f256SourceInput i).puncturedLogicalWord
    (logicalWordEmbedding _ u)) + physicalWordEmbedding _ ((f256SourceInput i).puncture h.val.val) = _
  rw [← map_add]
  rfl

theorem binaryCosetWordMap_injective (i : Nat) : Function.Injective (binaryCosetWordMap i) := by
  rintro ⟨u, h⟩ ⟨v, k⟩ heq
  rw [binaryCosetWordMap_apply, binaryCosetWordMap_apply] at heq
  have heq' := physicalWordEmbedding_injective _ heq
  have huv := logicalWordEmbedding_injective _
    ((f256SourceInput i).shortenedCosetLabel_eq_implies_logical_eq _ _ h k heq')
  subst v
  have hhk := (f256SourceInput i).shortenedCosetLabel_injective _ heq'
  exact Prod.ext rfl hhk

theorem binaryKernelWordMap_injective (i : Nat) : Function.Injective (binaryKernelWordMap i) := by
  intro h k heq
  have hpair : binaryCosetWordMap i (0, h) = binaryCosetWordMap i (0, k) := by
    simpa only [binaryCosetWordMap, LinearMap.coprod_apply, map_zero, zero_add] using heq
  exact congrArg Prod.snd (binaryCosetWordMap_injective i hpair)

/-- The actual binary X-check subspace. -/
def binaryXCode (i : Nat) : LinearCode (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  ⟨(binaryKernelWordMap i).range⟩

/-- The actual binary ambient word space spanned by all logical cosets. -/
def binaryAmbientCode (i : Nat) : LinearCode (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  ⟨(binaryCosetWordMap i).range⟩

/-- The actual binary Z-check subspace, orthogonal to every encoded word. -/
def binaryZCode (i : Nat) : LinearCode (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  (binaryAmbientCode i).dual

theorem binaryXCode_le_ambient (i : Nat) : (binaryXCode i).carrier ≤ (binaryAmbientCode i).carrier := by
  rintro x ⟨h, rfl⟩
  refine ⟨(0, h), ?_⟩
  simp only [binaryCosetWordMap, LinearMap.coprod_apply, map_zero, zero_add]

theorem binaryZCode_le_xDual (i : Nat) : (binaryZCode i).carrier ≤ (binaryXCode i).dual.carrier := by
  intro z hz
  apply ((binaryXCode i).mem_dual z).mpr
  exact fun x hx => ((binaryAmbientCode i).mem_dual z).mp hz x (binaryXCode_le_ambient i hx)

theorem binaryAmbientCode_dimension (i : Nat) :
    Dimension (binaryAmbientCode i) = f256MultiplicationLogicalCount i +
      Module.finrank (ZMod 2) (f256SourceInput i).H0 := by
  change Module.finrank (ZMod 2) (binaryCosetWordMap i).range = _
  rw [LinearMap.finrank_range_of_inj (binaryCosetWordMap_injective i), Module.finrank_prod]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem binaryXCode_dimension (i : Nat) :
    Dimension (binaryXCode i) = Module.finrank (ZMod 2) (f256SourceInput i).H0 :=
  LinearMap.finrank_range_of_inj (binaryKernelWordMap_injective i)

end ClassicalWords

/-- The actual binary CSS common-fixed code, not an independently chosen carrier. -/
def binaryCSSCode (i : Nat) : CSSCode (ZMod 2)
    ((f256SourceInput i).PivotComplement × Fin 512)
    (Qubit.QubitRegister ((f256SourceInput i).PivotComplement × Fin 512)) where
  xCode := binaryXCode i
  zCode := binaryZCode i
  stabilizer := PauliSymplectic.binaryCSSStabilizerCodeOfDualLe
    (binaryXCode i) (binaryZCode i) (binaryZCode_le_xDual i)
  orthogonal := by
    intro x hx z hz
    have h := ((binaryXCode i).mem_dual z).mp (binaryZCode_le_xDual i hz) x hx
    simp [symplecticForm, wordPairing_apply, dotProduct_comm] at h ⊢
    exact h

theorem binaryCSSCode_dimension (i : Nat) :
    (binaryCSSCode i).stabilizer.code.dimension = 2 ^ f256MultiplicationLogicalCount i := by
  change Module.finrank Complex
    (PauliSymplectic.binaryCSSQuantumCodeOfDualLe (binaryXCode i) (binaryZCode i)
      (binaryZCode_le_xDual i)).carrier = _
  rw [PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier]
  congr 1
  have h := (binaryAmbientCode i).dimension_add_dual_dimension_eq_length
  rw [binaryAmbientCode_dimension] at h
  rw [binaryXCode_dimension]
  change _ - _ - Dimension (binaryAmbientCode i).dual = _
  omega

local instance binaryCSSFieldWordFintype {A : Type} [Fintype A] :
    Fintype (Word F256 A) := Fintype.ofFinite _

/-- The literal normalized binary coset sum obtained from the source encoder. -/
def binaryCosetKet (i : Nat) (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    Qubit.QubitRegister ((f256SourceInput i).PivotComplement × Fin 512) :=
  SourceInput.cosetNormalization (f256SourceInput i).H0 •
    ∑ h : (f256SourceInput i).H0,
      EuclideanSpace.basisFun (Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512))
        Complex (binaryCosetWordMap i (u, h))

theorem binaryEncodedCode_basis_eq_coset (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    (binaryEncodedCode i).encode (EuclideanSpace.basisFun _ Complex u) = binaryCosetKet i u := by
  rw [binaryEncodedCode_basis]
  unfold SourceInput.shortenedCosetKet
  rw [map_smul, map_sum]
  unfold binaryCosetKet
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [binaryCosetWordMap_apply]
  simpa only [registerBasisKet, EuclideanSpace.basisFun_apply] using
    physicalIsometry_basis (f256SourceInput i).PivotComplement
      ((f256SourceInput i).shortenedCosetLabel
        (logicalWordEmbedding (Fin (f256MultiplicationLogicalCount i)) u) h)

theorem binaryCosetKet_fixed_X (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) (k : (f256SourceInput i).H0) :
    PauliSymplectic.toQubitOperator (PauliSymplectic.cssXCheck (binaryKernelWordMap i k))
      (binaryCosetKet i u) = binaryCosetKet i u := by
  unfold binaryCosetKet
  erw [map_smul, map_sum]
  congr 1
  have htranslate (h : (f256SourceInput i).H0) :
      binaryCosetWordMap i (u, h) + binaryKernelWordMap i k = binaryCosetWordMap i (u, h + k) := by
    simp only [binaryCosetWordMap, LinearMap.coprod_apply, map_add, add_assoc]
  simp_rw [PauliSymplectic.cssXCheck_apply_basis, htranslate]
  apply Fintype.sum_equiv (Equiv.addRight k)
  intro h
  rfl

theorem binaryCosetKet_fixed_Z (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (z : Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512))
    (hz : z ∈ (binaryZCode i).carrier) :
    PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck z)
      (binaryCosetKet i u) = binaryCosetKet i u := by
  unfold binaryCosetKet
  erw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [PauliSymplectic.cssZCheck_apply_basis]
  have hzero : wordPairing z (binaryCosetWordMap i (u, h)) = 0 :=
    ((binaryAmbientCode i).mem_dual z).mp hz _ ⟨(u, h), rfl⟩
  rw [hzero, PauliSymplectic.binaryPhaseScalar_zero, one_smul]

theorem binaryCosetKet_mem_cssCarrier (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryCosetKet i u ∈ (binaryCSSCode i).stabilizer.code.carrier := by
  change binaryCosetKet i u ∈
    (PauliSymplectic.binaryCSSQuantumCodeOfDualLe _ _ (binaryZCode_le_xDual i)).carrier
  rw [PauliSymplectic.mem_binaryCSSQuantumCodeOfDualLe_carrier]
  intro P hP
  rcases hP with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · obtain ⟨k, rfl⟩ := hx
    exact binaryCosetKet_fixed_X i u k
  · exact binaryCosetKet_fixed_Z i u z hz

theorem binaryEncodedCode_carrier_le_cssCarrier (i : Nat) :
    (binaryEncodedCode i).code.carrier ≤ (binaryCSSCode i).stabilizer.code.carrier := by
  rintro x ⟨u, rfl⟩
  let B := EuclideanSpace.basisFun (Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) Complex
  change (binaryEncodingIsometry i).toLinearMap u ∈ _
  rw [← B.sum_repr u]
  erw [map_sum]
  apply Submodule.sum_mem
  intro a _
  erw [map_smul]
  apply Submodule.smul_mem
  change (binaryEncodedCode i).encode (EuclideanSpace.basisFun _ Complex a) ∈ _
  rw [binaryEncodedCode_basis_eq_coset]
  exact binaryCosetKet_mem_cssCarrier i a

/-- The concrete encoder range is exactly the actual CSS common-fixed carrier. -/
theorem binaryEncodedCode_carrier_eq_cssCarrier (i : Nat) :
    (binaryEncodedCode i).code.carrier = (binaryCSSCode i).stabilizer.code.carrier := by
  apply Submodule.eq_of_le_of_finrank_eq (binaryEncodedCode_carrier_le_cssCarrier i)
  exact (binaryEncodedCode_dimension i).trans (binaryCSSCode_dimension i).symm

theorem binaryEncodedCode_code_eq_cssCode (i : Nat) :
    (binaryEncodedCode i).code = (binaryCSSCode i).stabilizer.code := by
  cases hE : (binaryEncodedCode i).code with
  | mk E =>
    cases hC : (binaryCSSCode i).stabilizer.code with
    | mk C =>
      have h := binaryEncodedCode_carrier_eq_cssCarrier i
      rw [hE, hC] at h
      exact congrArg QuantumCode.mk h

end QEC.Distillation.Ngu24Binary
