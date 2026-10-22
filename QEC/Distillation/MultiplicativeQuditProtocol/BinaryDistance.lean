import QEC.Distillation.MultiplicativeQuditProtocol.BinaryEncoding
import QEC.Semantics.ErrorCorrection.QuditMatrixElements

/-!
# Quantum-distance inheritance through the binary MFE encoding

An arbitrary binary-local operator touches at most one field site per selected
bit. Compression through the actual MFE basis isometry satisfies the native
coset locality conditions. The concrete AG interpolation and separation
proved for the qudit family thus imply full-carrier binary detectability.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth

variable {J : Type} [DecidableEq J]

theorem physicalWordEmbedding_difference_outside (S : Finset (J × Fin 512))
    (x y : J → F256) (h : ∃ j, j ∉ S.image Prod.fst ∧ x j ≠ y j) :
    ∃ t, t ∉ S ∧ physicalWordEmbedding J x t ≠ physicalWordEmbedding J y t := by
  classical
  obtain ⟨j, hj, hxy⟩ := h
  have hsigma : f256MFESigma (x j) ≠ f256MFESigma (y j) :=
    fun heq => hxy (f256MFESigma_injective heq)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hsigma
  refine ⟨(j, k), ?_, hk⟩
  intro hmem
  exact hj (Finset.mem_image.mpr ⟨(j, k), hmem, rfl⟩)

theorem physicalWordEmbedding_agrees_on (S : Finset (J × Fin 512))
    (x y : J → F256) (h : ∀ j, j ∈ S.image Prod.fst → x j = y j) :
    ∀ t, t ∈ S → physicalWordEmbedding J x t = physicalWordEmbedding J y t := by
  intro t ht
  change f256MFESigma (x t.1) t.2 = f256MFESigma (y t.1) t.2
  rw [h t.1 (Finset.mem_image.mpr ⟨t, ht, rfl⟩)]

local instance {A : Type} [Fintype A] : Fintype (Word F256 A) := Fintype.ofFinite _

/-- Arbitrary actual binary-local operators pull back to detectable native operators. -/
theorem binaryLocal_compression_detectable (i : Nat)
    (S : QuditSubsystem (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2))
    (hS : S.selected.card < f256QuditDistanceBound i) (E : Operator S.selectedSystem) :
    DetectableOn (f256SourceInput i).quantumCode
      (ComputationalEmbedding.compress
        ⟨physicalWordEmbedding (f256SourceInput i).PivotComplement,
          physicalWordEmbedding_injective (f256SourceInput i).PivotComplement⟩
        (S.extendLocalToRegister E)) := by
  let B := S.selected.image Prod.fst
  have hB : B.card < f256QuditDistanceBound i :=
    (Finset.card_image_le).trans_lt hS
  apply (f256SourceInput i).detectableOn_of_coset_locality _ B
    (f256SourceInput_complement_separates i B hB)
    (f256SourceInput_kernel_restrict_surjective i B hB)
  · intro x y hxy
    change inner Complex (EuclideanSpace.basisFun _ Complex x)
      (ComputationalEmbedding.compress _ _ (EuclideanSpace.basisFun _ Complex y)) = 0
    erw [ComputationalEmbedding.compress_basis_inner]
    apply QuditSubsystem.extendLocal_basis_inner_zero
    exact physicalWordEmbedding_difference_outside S.selected x y hxy
  · intro x y hxy
    change inner Complex (EuclideanSpace.basisFun _ Complex x)
      (ComputationalEmbedding.compress _ _ (EuclideanSpace.basisFun _ Complex x)) =
      inner Complex (EuclideanSpace.basisFun _ Complex y)
        (ComputationalEmbedding.compress _ _ (EuclideanSpace.basisFun _ Complex y))
    let e : Word F256 (f256SourceInput i).PivotComplement ↪
        Qudit.Label (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2) :=
      ⟨physicalWordEmbedding (f256SourceInput i).PivotComplement,
        physicalWordEmbedding_injective (f256SourceInput i).PivotComplement⟩
    exact (ComputationalEmbedding.compress_basis_inner e (S.extendLocalToRegister E) x x).trans
      ((QuditSubsystem.extendLocal_basis_diagonal_eq S E (e x) (e y)
        (physicalWordEmbedding_agrees_on S.selected x y hxy)).trans
        (ComputationalEmbedding.compress_basis_inner e (S.extendLocalToRegister E) y y).symm)

theorem binaryEncodedCode_detectable_local (i : Nat)
    (S : QuditSubsystem (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2))
    (hS : S.selected.card < f256QuditDistanceBound i) (E : Operator S.selectedSystem) :
    DetectableOn (binaryEncodedCode i).code (S.extendLocalToRegister E) := by
  obtain ⟨c, hc⟩ := binaryLocal_compression_detectable i S hS E
  refine ⟨c, ?_⟩
  rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
  change inner Complex
      (physicalIsometry _ ((f256SourceInput i).encodingIsometry (logicalIsometry _ u)))
      (S.extendLocalToRegister E
        (physicalIsometry _ ((f256SourceInput i).encodingIsometry (logicalIsometry _ v)))) =
    c * inner Complex
      (physicalIsometry _ ((f256SourceInput i).encodingIsometry (logicalIsometry _ u)))
      (physicalIsometry _ ((f256SourceInput i).encodingIsometry (logicalIsometry _ v)))
  rw [(physicalIsometry _).inner_map_map]
  have hh := hc _ ⟨logicalIsometry _ u, rfl⟩ _ ⟨logicalIsometry _ v, rfl⟩
  erw [ComputationalEmbedding.compress_inner] at hh
  exact hh

theorem binaryEncodedCode_measurementDistance (i : Nat) :
    QuditSubsystem.BPTMeasurementDistance (binaryEncodedCode i).code (f256QuditDistanceBound i) := by
  intro S hS E _
  apply (QuditSubsystem.scalarCompression_iff_detectableOn _ _).mpr
  apply binaryEncodedCode_detectable_local i S _ E
  simpa only [QuditSubsystem.SelectedCoordinates, Fintype.card_coe] using hS

end QEC.Distillation.Ngu24Binary
