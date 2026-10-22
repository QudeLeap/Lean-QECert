import QEC.Bounds.BPTDisentangling.Sectors.Transport

/-!
# BPT compressed sector conjugation

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
The common four-factor coordinate sends the left projector of one BV03 block
to its literal source factor `P_left tensor 1`.  This is the first half of the
block projector equality used below for the physical first cut.
-/
theorem isotypicSectorBlockTransportLeft_conj_overlapLiftLeft
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (hleft : (unitaryLTensor A U).conjOperator P =
      rightTensorExtensionAfterLeft A W N Pleft) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftLeft (C := C) P) =
      TensorProduct.map Pleft
        (1 : Semantics.Operator (Semantics.CompositeSystem N C)) := by
  unfold isotypicSectorBlockTransportLeft
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  unfold overlapLiftLeft
  rw [unitaryRTensor_conj_tensorMap_left, hleft]
  unfold rightTensorExtensionAfterLeft
  rw [← unitaryRTensor_conj_tensorMap_left
    (tensorAssociatorUnitary A W N) C
    (TensorProduct.map Pleft (1 : Semantics.Operator N))]
  rw [← composeUnitaryTransport_conjOperator
    (unitaryRTensor (tensorAssociatorUnitary A W N) C)
    (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C)]
  rw [← composeUnitaryTransport_conjOperator
    (composeUnitaryTransport
      (unitaryRTensor (tensorAssociatorUnitary A W N) C)
      (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C))
    (unitaryLTensor A (tensorAssociatorUnitary W N C))]
  rw [← composeUnitaryTransport_conjOperator
    (composeUnitaryTransport
      (composeUnitaryTransport
        (unitaryRTensor (tensorAssociatorUnitary A W N) C)
        (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C))
      (unitaryLTensor A (tensorAssociatorUnitary W N C)))
    (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm]
  rw [isotypicSectorBlockTransportLeft_associator_coherence]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [show TensorProduct.map (1 : Semantics.Operator N)
      (1 : Semantics.Operator C) =
        (1 : Semantics.Operator (Semantics.CompositeSystem N C)) from
      TensorProduct.map_one]

/--
The same common coordinate sends the right projector of a BV03 block to its
literal source factor `1 tensor Q_right`.  The proof uses the right transport
route and then the already proved route coherence.
-/
theorem isotypicSectorBlockTransportLeft_conj_overlapLiftRight
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (Q : Semantics.Operator (Semantics.CompositeSystem H C))
    (Qright : Semantics.Operator (Semantics.CompositeSystem N C))
    (hright : (unitaryRTensor U C).conjOperator Q =
      leftTensorExtensionBeforeRight W N C Qright) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftRight (A := A) Q) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W)) Qright := by
  rw [isotypicSectorBlockTransportLeft_eq_right A H W N C U]
  unfold isotypicSectorBlockTransportRight
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  unfold overlapLiftRight
  rw [Semantics.UnitaryTransport.conjOperator_symm_conjOperator]
  rw [unitaryLTensor_conj_tensorMap_left, hright]
  unfold leftTensorExtensionBeforeRight
  have hleftTensorSymm :
      (unitaryLTensor A (tensorAssociatorUnitary W N C)).symm =
        unitaryLTensor A (tensorAssociatorUnitary W N C).symm := by
    apply unitaryTransport_ext
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => simp
    | tmul a middle => rfl
    | add first second hfirst hsecond =>
        simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
  rw [← unitaryLTensor_conj_tensorMap_left A
    (tensorAssociatorUnitary W N C).symm
    (TensorProduct.map (1 : Semantics.Operator W) Qright)]
  rw [← hleftTensorSymm]
  rw [Semantics.UnitaryTransport.conjOperator_symm_conjOperator]
  rw [tensorAssociatorUnitary_symm_conj_tensorMap]
  rw [show TensorProduct.map (1 : Semantics.Operator A)
      (1 : Semantics.Operator W) =
        (1 : Semantics.Operator (Semantics.CompositeSystem A W)) from
      TensorProduct.map_one]

/--
One active BV03 sector has the actual source tensor-block product under its
single coherent boundary unitary.  This combines the two preceding projector
equalities and is the block equality consumed by the first physical cut.
-/
theorem isotypicSectorBlockTransportLeft_conj_overlap_product
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Q : Semantics.Operator (Semantics.CompositeSystem H C))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (Qright : Semantics.Operator (Semantics.CompositeSystem N C))
    (hleft : (unitaryLTensor A U).conjOperator P =
      rightTensorExtensionAfterLeft A W N Pleft)
    (hright : (unitaryRTensor U C).conjOperator Q =
      leftTensorExtensionBeforeRight W N C Qright) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) =
      TensorProduct.map Pleft Qright := by
  rw [Semantics.UnitaryTransport.conjOperator_mul]
  rw [isotypicSectorBlockTransportLeft_conj_overlapLiftLeft U P Pleft hleft,
    isotypicSectorBlockTransportLeft_conj_overlapLiftRight U Q Qright hright]
  rw [← TensorProduct.map_mul]
  simp only [mul_one, one_mul]

/--
Compression to a chosen BV03 isotypic sector and its common block transport
commute.  This is the generic form used by both physical BPT cuts: it turns
the actual compressed overlap product, not merely its individual factors,
into `P_left tensor Q_right`.
-/
theorem isotypicSectorBlockTransportLeft_conj_compressed_overlap_product
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Q : Semantics.Operator (Semantics.CompositeSystem H C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) H)
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem W N))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (Qright : Semantics.Operator (Semantics.CompositeSystem N C))
    (hleft : (unitaryLTensor A U).conjOperator
        (overlapProjectorOnIsotypicComponent P component) =
      rightTensorExtensionAfterLeft A W N Pleft)
    (hright : (unitaryRTensor U C).conjOperator
        (overlapRightProjectorOnIsotypicComponent P Q component) =
      leftTensorExtensionBeforeRight W N C Qright) :
    (isotypicSectorBlockTransportLeft A (component.1.restrictScalars Complex) W N C U).conjOperator
        ((LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
          (component.1.restrictScalars Complex))).comp
          ((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
            (tensorTripleSubtypeEmbedding (A := A) (C := C)
              (component.1.restrictScalars Complex)))) =
      TensorProduct.map Pleft Qright := by
  rw [isotypic_compression_overlap_product_eq_sector_block_product
    P Q hselfAdjoint hcommute component]
  exact isotypicSectorBlockTransportLeft_conj_overlap_product U
    (overlapProjectorOnIsotypicComponent P component)
    (overlapRightProjectorOnIsotypicComponent P Q component)
    Pleft Qright hleft hright

end BPTCommutingProjectorModel

end Bounds
end QEC
