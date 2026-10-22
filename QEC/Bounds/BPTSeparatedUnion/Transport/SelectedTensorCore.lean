import QEC.Bounds.BPTSeparatedUnion.Transport.Coordinates

/-!
# Register-factorized tensor compression

The separated-union transport uses this small generic calculation rather than
asking the elaborator to unfold its BPT active-sector coordinates in one step.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped TensorProduct

universe u v

set_option maxHeartbeats 150000 in
set_option synthInstance.maxHeartbeats 50000 in
/--
After factoring a qudit register, a local selected action compressed through a
pair of embeddings acts trivially on the complement coordinate.
-/
theorem registerFactorizedTensor_compression_left
    {iota : Type u} [Fintype iota] [DecidableEq iota] (q : iota → Nat)
    (S : Semantics.QuditSubsystem q)
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (eSel : H →ₗ[Complex] S.selectedSystem) (eComp : K →ₗ[Complex] S.complementSystem)
    (hComp : (LinearMap.adjoint eComp).comp eComp = (1 : Semantics.Operator K))
    (A : Semantics.Operator S.selectedSystem) :
    (LinearMap.adjoint (TensorProduct.map eSel eComp)).comp
        ((S.registerFactorization.conjOperator (S.extendLocalToRegister A)).comp
          (TensorProduct.map eSel eComp)) =
      TensorProduct.map ((LinearMap.adjoint eSel).comp (A.comp eSel))
        (1 : Semantics.Operator K) := by
  rw [BPTCommutingProjectorModel.registerFactorization_conj_extendLocalToRegister]
  exact BPTCommutingProjectorModel.tensorEmbedding_compression_left eSel eComp hComp A

set_option maxHeartbeats 150000 in
set_option synthInstance.maxHeartbeats 50000 in
/-- Compressing through an outer transport and an inner coordinate transport. -/
theorem compression_conj_after_transportPair
    {S T H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (outer : Semantics.UnitaryTransport H K) (coordinates : Semantics.UnitaryTransport H T)
    (embedding : S →ₗ[Complex] T) (P : Semantics.Operator H) :
    (LinearMap.adjoint (outer.toLinearEquiv.toLinearMap.comp
      (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding))).comp
        ((outer.conjOperator P).comp
          (outer.toLinearEquiv.toLinearMap.comp
            (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding))) =
      (LinearMap.adjoint embedding).comp
        ((coordinates.conjOperator P).comp embedding) := by
  calc
    (LinearMap.adjoint (outer.toLinearEquiv.toLinearMap.comp
        (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding))).comp
        ((outer.conjOperator P).comp
          (outer.toLinearEquiv.toLinearMap.comp
            (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding))) =
        (LinearMap.adjoint (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding)).comp
          (P.comp (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding)) :=
      BPTCommutingProjectorModel.compression_conjOperator_comp_unitary outer
        (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding) P
    _ = (LinearMap.adjoint embedding).comp
        ((coordinates.conjOperator P).comp embedding) := by
      simpa using BPTCommutingProjectorModel.compression_conjOperator_comp_unitary
        coordinates.symm embedding (coordinates.conjOperator P)

/-- Reuse a named output-coordinate equality before compressing through two transports. -/
theorem compression_conj_after_transportPair_of_eq
    {S T H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (outer : Semantics.UnitaryTransport H K) (coordinates : Semantics.UnitaryTransport H T)
    (embedding : S →ₗ[Complex] T) (outputEmbedding : S →ₗ[Complex] K)
    (P : Semantics.Operator H)
    (houtput : outputEmbedding = outer.toLinearEquiv.toLinearMap.comp
      (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding)) :
    (LinearMap.adjoint outputEmbedding).comp ((outer.conjOperator P).comp outputEmbedding) =
      (LinearMap.adjoint embedding).comp ((coordinates.conjOperator P).comp embedding) := by
  rw [houtput]
  exact compression_conj_after_transportPair outer coordinates embedding P

/-- Compress a right tensor action through an isometric left embedding. -/
theorem tensorEmbedding_compression_right_of_isometry
    {H K H' K' : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup H'] [InnerProductSpace Complex H'] [Semantics.FiniteQuantumSystem H']
    [NormedAddCommGroup K'] [InnerProductSpace Complex K'] [Semantics.FiniteQuantumSystem K']
    (eH : H →ₗᵢ[Complex] H') (eK : K →ₗ[Complex] K')
    (B : Semantics.Operator K') :
    (LinearMap.adjoint (TensorProduct.map eH.toLinearMap eK)).comp
        ((TensorProduct.map (1 : Semantics.Operator H') B).comp
          (TensorProduct.map eH.toLinearMap eK)) =
      TensorProduct.map (1 : Semantics.Operator H)
        ((LinearMap.adjoint eK).comp (B.comp eK)) := by
  apply BPTCommutingProjectorModel.tensorEmbedding_compression_right eH.toLinearMap eK
  exact BPTCommutingProjectorModel.linearIsometry_adjoint_comp_self eH

end Bounds
end QEC
