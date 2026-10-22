import QEC.Bounds.BPTDisentangling.Joint.BlockTransport

/-!
# BPT second-cut sequential core

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
The actual second sequential compression of a rank-one BV03 block.  A right
subtype embedding is transported through the first isotypic coordinate change,
then through the next isotypic unitary, yielding the literal `B'' tensor C'`
residual block.  The hypotheses are a source block equation and its concrete
intertwining square, not a preassembled sequential factorization.
-/
theorem sequential_secondCut_block_of_intertwining
    {A H W N C C' X N2 D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup C'] [InnerProductSpace Complex C'] [Semantics.FiniteQuantumSystem C']
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (UB : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport C (Semantics.CompositeSystem X N2))
    (i : C →ₗ[Complex] C')
    (R : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C' D)))
    (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (Q : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C' D)))
    (hblock :
      (isotypicSectorBlockTransportLeft A H W N
        (Semantics.CompositeSystem C' D) UB).conjOperator R =
        TensorProduct.map P Q)
    (hintertwines :
      (isotypicSectorBlockTransportLeft A H W N
        (Semantics.CompositeSystem C' D) UB).toLinearEquiv.toLinearMap.comp
          (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
            (TensorProduct.map i (1 : Semantics.Operator D))) =
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
          (TensorProduct.map (1 : Semantics.Operator N)
            (TensorProduct.map i (1 : Semantics.Operator D)))).comp
          (isotypicSectorBlockTransportLeft A H W N
            (Semantics.CompositeSystem C D) UB).toLinearEquiv.toLinearMap) :
    let K := TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
      (TensorProduct.map i (1 : Semantics.Operator D))
    let Kright := TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map i (1 : Semantics.Operator D))
    let V := composeUnitaryTransport (unitaryRTensor UC D)
      (tensorAssociatorUnitary X N2 D)
    let Qright := (unitaryLTensor N V).conjOperator
      ((LinearMap.adjoint Kright).comp (Q.comp Kright))
    let G := composeUnitaryTransport
      (isotypicSectorBlockTransportLeft A H W N (Semantics.CompositeSystem C D) UB)
      (composeUnitaryTransport
        (unitaryLTensor (Semantics.CompositeSystem A W) (unitaryLTensor N V))
        (unitaryLTensor (Semantics.CompositeSystem A W)
          (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm))
    G.conjOperator ((LinearMap.adjoint K).comp (R.comp K)) =
      (unitaryLTensor (Semantics.CompositeSystem A W)
        (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm).conjOperator
        (TensorProduct.map P Qright) := by
  dsimp
  have hcompressed := unitaryTransport_conj_compression_of_intertwines
    (isotypicSectorBlockTransportLeft A H W N (Semantics.CompositeSystem C' D) UB)
    (isotypicSectorBlockTransportLeft A H W N (Semantics.CompositeSystem C D) UB)
    (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
      (TensorProduct.map i (1 : Semantics.Operator D)))
    (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
      (TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map i (1 : Semantics.Operator D))))
    hintertwines R
  rw [hblock] at hcompressed
  rw [tensorMap_right_compression] at hcompressed
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator, hcompressed,
    unitaryLTensor_conj_tensorMap]

/--
Named-interface adapter for `sequential_secondCut_block_of_intertwining`.
The three equality inputs keep concrete callers from unfolding large transport
and compression definitions while matching the generic theorem conclusion.
The right-factor naturality square is derived here from `UB` and `i`; concrete
callers must not restate that generic fact with a large model-specific type.
-/
theorem sequential_secondCut_named_block
    {A H W N C C' X N2 D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup C'] [InnerProductSpace Complex C'] [Semantics.FiniteQuantumSystem C']
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (UB : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport C (Semantics.CompositeSystem X N2))
    (i : C →ₗ[Complex] C')
    (R : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C' D)))
    (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (Q : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C' D)))
    (Rsequential : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C D)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem N
        (Semantics.CompositeSystem X (Semantics.CompositeSystem N2 D))))
    (G : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C D))
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem N X) (Semantics.CompositeSystem N2 D))))
    (hRsequential :
      let K := TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
        (TensorProduct.map i (1 : Semantics.Operator D))
      Rsequential = (LinearMap.adjoint K).comp (R.comp K))
    (hQright :
      let Kright := TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map i (1 : Semantics.Operator D))
      let V := composeUnitaryTransport (unitaryRTensor UC D)
        (tensorAssociatorUnitary X N2 D)
      Qright = (unitaryLTensor N V).conjOperator
        ((LinearMap.adjoint Kright).comp (Q.comp Kright)))
    (hG :
      let V := composeUnitaryTransport (unitaryRTensor UC D)
        (tensorAssociatorUnitary X N2 D)
      G = composeUnitaryTransport
        (isotypicSectorBlockTransportLeft A H W N (Semantics.CompositeSystem C D) UB)
        (composeUnitaryTransport
          (unitaryLTensor (Semantics.CompositeSystem A W) (unitaryLTensor N V))
          (unitaryLTensor (Semantics.CompositeSystem A W)
            (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm)))
    (hblock :
      (isotypicSectorBlockTransportLeft A H W N
        (Semantics.CompositeSystem C' D) UB).conjOperator R =
        TensorProduct.map P Q) :
    G.conjOperator Rsequential =
      (unitaryLTensor (Semantics.CompositeSystem A W)
        (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm).conjOperator
        (TensorProduct.map P Qright) := by
  dsimp only at hRsequential hQright hG
  subst Rsequential
  subst Qright
  subst G
  have hintertwines := isotypicSectorBlockTransportLeft_comp_tensorMap_right
    (A := A) (H := H) (W := W) (N := N)
    (C := Semantics.CompositeSystem C D)
    (C' := Semantics.CompositeSystem C' D) UB
    (TensorProduct.map i (1 : Semantics.Operator D))
  exact sequential_secondCut_block_of_intertwining UB UC i R P Q hblock hintertwines


end BPTCommutingProjectorModel

end Bounds
end QEC
