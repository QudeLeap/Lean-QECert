import QEC.Bounds.BPTSeparatedUnion.Transport.IntertwiningTensor

/-!
# Intertwining through two unitary coordinate transports

This generic algebraic lemma isolates the transport calculation from the large
dependent BPT endpoint.
-/

noncomputable section

namespace QEC
namespace Bounds

universe u

namespace BPTCommutingProjectorModel

theorem intertwining_after_transportPair_of_eq
    {S H T K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (outer : Semantics.UnitaryTransport H K)
    (coordinates : Semantics.UnitaryTransport H T)
    (embedding : S →ₗ[Complex] T) (outputEmbedding : S →ₗ[Complex] K)
    (A : Semantics.Operator H) (Q : Semantics.Operator T) (D : Semantics.Operator S)
    (houtput : outputEmbedding = outer.toLinearEquiv.toLinearMap.comp
      (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding))
    (hcoordinates : coordinates.conjOperator A = Q)
    (hembedding : Q.comp embedding = embedding.comp D) :
    (outer.conjOperator A).comp outputEmbedding = outputEmbedding.comp D := by
  have hOuter : (outer.conjOperator A).comp outer.toLinearEquiv.toLinearMap =
      outer.toLinearEquiv.toLinearMap.comp A := by
    unfold Semantics.UnitaryTransport.conjOperator
    simp [LinearMap.comp_assoc]
  have hInner : A.comp coordinates.symm.toLinearEquiv.toLinearMap =
      coordinates.symm.toLinearEquiv.toLinearMap.comp
        (coordinates.conjOperator A) := by
    unfold Semantics.UnitaryTransport.conjOperator
    simp [LinearMap.comp_assoc]
  calc
    (outer.conjOperator A).comp outputEmbedding =
        ((outer.conjOperator A).comp outer.toLinearEquiv.toLinearMap).comp
          (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding) := by
            rw [houtput]
            simp only [LinearMap.comp_assoc]
    _ = (outer.toLinearEquiv.toLinearMap.comp A).comp
          (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding) := by
            rw [hOuter]
    _ = outer.toLinearEquiv.toLinearMap.comp
          ((A.comp coordinates.symm.toLinearEquiv.toLinearMap).comp embedding) := by
            simp only [LinearMap.comp_assoc]
    _ = outer.toLinearEquiv.toLinearMap.comp
          ((coordinates.symm.toLinearEquiv.toLinearMap.comp
            (coordinates.conjOperator A)).comp embedding) := by
              rw [hInner]
    _ = outer.toLinearEquiv.toLinearMap.comp
          (coordinates.symm.toLinearEquiv.toLinearMap.comp (Q.comp embedding)) := by
            rw [hcoordinates]
            simp only [LinearMap.comp_assoc]
    _ = outer.toLinearEquiv.toLinearMap.comp
          (coordinates.symm.toLinearEquiv.toLinearMap.comp (embedding.comp D)) := by
            rw [hembedding]
    _ = outputEmbedding.comp D := by
          rw [houtput]
          simp only [LinearMap.comp_assoc]

end BPTCommutingProjectorModel
end Bounds
end QEC
