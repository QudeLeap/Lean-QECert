import QEC.Bounds.BPTDisentangling.ScalarCompression.RankOneTransport

/-!
# BPT internal residual scalar compression

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
The common isotypic block transport also carries an operator on the residual
multiplicity factor to the literal `N tensor C` right block.  It is the
operator-level transport used to pass hM no-information from `B` to `B''`.
-/
theorem isotypicSectorBlockTransportLeft_conj_overlapLiftLeft_middle
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (E : Semantics.Operator (Semantics.CompositeSystem A H))
    (X : Semantics.Operator N)
    (hE : (unitaryLTensor A U).conjOperator E =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map (1 : Semantics.Operator W) X)) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftLeft (C := C) E) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
        (TensorProduct.map X (1 : Semantics.Operator C)) := by
  unfold isotypicSectorBlockTransportLeft overlapLiftLeft
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [unitaryRTensor_conj_tensorMap_left, hE]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [unitaryLTensor_conj_tensorMap_left]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [tensorAssociatorUnitary_symm_conj_tensorMap]
  rw [show TensorProduct.map (1 : Semantics.Operator A)
      (1 : Semantics.Operator W) =
        (1 : Semantics.Operator (Semantics.CompositeSystem A W)) from TensorProduct.map_one]

set_option maxHeartbeats 4000000 in
/--
After the hM rank-one `Pi_AB'` reduction, correctability of `M` descends to
scalar compression by every operator on the second-cut multiplicity factor
`B''`.  The proof transports a literal `B''` probe through the active sector,
uses the physical hM relation, and cancels the normalized `Pi_AB'` factor.
-/
theorem secondCut_Qright_all_internalResidual_scalar_compression_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      ∀ X : Semantics.Operator N, ∃ scalar : Complex,
        Qright * TensorProduct.map X (1 : Semantics.Operator CD) * Qright =
          scalar • Qright := by
  intro A H W0 N CD U Pleft Qright hactive hleft hright
  let B := M.fourFactorB region
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  let Jadj := LinearMap.adjoint J
  let R := M.secondCutCodeLift region
  let Rcompressed : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD) :=
    Jadj.comp (R.comp J)
  let T := isotypicSectorBlockTransportLeft A H W0 N CD U
  have hJadjJ : Jadj.comp J =
      (1 : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD)) := by
    simpa [J, Jadj] using
      (adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
        (A := A) (C := CD) H)
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region :=
    (M.secondCutProjectorAB_isSymmetricProjection region).isSymmetric.adjoint_eq
  have hover : Commute
      (overlapLiftLeft (C := CD) (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := A) (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  have hreconstruct : R = J.comp (Rcompressed.comp Jadj) := by
    dsimp [Rcompressed, R, J, Jadj]
    apply active_overlap_product_eq_isotypic_embedding_compression
      (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
      hself hover component
    exact hactive
  rcases M.secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable
    region hcode hM component W U Pleft Qright ⟨hactive, hleft, hright⟩ with
    ⟨phi, hphi, hblock⟩
  intro X
  let Etarget : Semantics.Operator (Semantics.CompositeSystem A
      (Semantics.CompositeSystem W0 N)) :=
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map (1 : Semantics.Operator W0) X)
  let Esub : Semantics.Operator (Semantics.CompositeSystem A H) :=
    (unitaryLTensor A U).symm.conjOperator Etarget
  let E : Semantics.Operator (Semantics.CompositeSystem A B) :=
    overlapLeftSubtypeLift H Esub
  let Lprobe := overlapLiftLeft (C := CD) E
  let Lsub := overlapLiftLeft (C := CD) Esub
  rcases M.secondCut_all_leftLocal_scalar_compression_of_region_recoverable region hM E with
    ⟨scalar, hscalar⟩
  have hprobe : Jadj.comp (Lprobe.comp J) = Lsub := by
    simpa [J, Jadj, E, Esub, Lprobe, Lsub, B] using
      (adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_subtypeLift_comp
        (A := A) (C := CD) H Esub)
  have hcompressedScalar : Rcompressed * Lsub * Rcompressed = scalar • Rcompressed :=
    compressed_scalar_of_named_isometric_reconstruction
      J R Lprobe Rcompressed Lsub scalar hJadjJ hreconstruct hprobe hscalar
  have hprobeTransport : (unitaryLTensor A U).conjOperator Esub = Etarget := by
    simpa [Esub] using (unitaryLTensor A U).conjOperator_symm_conjOperator Etarget
  have hTprobe : T.conjOperator Lsub =
      TensorProduct.map (1 : Semantics.Operator
        (Semantics.CompositeSystem A W0))
        (TensorProduct.map X (1 : Semantics.Operator CD)) := by
    simpa [T, Lsub, Etarget] using
      (isotypicSectorBlockTransportLeft_conj_overlapLiftLeft_middle
        (A := A) (H := H) (W := W0) (N := N) (C := CD)
        U Esub X hprobeTransport)
  refine ⟨scalar, ?_⟩
  exact right_factor_scalar_compression_of_rankOne_transport
    T Rcompressed Lsub phi hphi Qright
    (TensorProduct.map X (1 : Semantics.Operator CD)) scalar
    hblock hTprobe hcompressedScalar


end BPTCommutingProjectorModel

end Bounds
end QEC
