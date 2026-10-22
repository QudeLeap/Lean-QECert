import QEC.Bounds.BPTDisentangling.Assembly.AssemblyHelpers

/-!
# BPT final transport assembly

The expensive fixed-active-data to output-factorization witness is isolated in
its own build artifact.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem conjOperator_eq_symm_conjOperator_of_transport
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K)
    (W : Semantics.UnitaryTransport H H)
    (V : Semantics.UnitaryTransport K K)
    (C : Semantics.Operator H) (P Q : Semantics.Operator K)
    (htransport : T.conjOperator (W.conjOperator C) =
      V.conjOperator (T.conjOperator C))
    (hproduct : V.conjOperator (T.conjOperator C) = P)
    (hbefore : P = Q) :
    W.conjOperator C = T.symm.conjOperator Q := by
  calc
    W.conjOperator C = T.symm.conjOperator (T.conjOperator (W.conjOperator C)) :=
      (T.symm_conjOperator_conjOperator _).symm
    _ = T.symm.conjOperator (V.conjOperator (T.conjOperator C)) :=
      congrArg T.symm.conjOperator htransport
    _ = T.symm.conjOperator P := congrArg T.symm.conjOperator hproduct
    _ = T.symm.conjOperator Q := congrArg T.symm.conjOperator hbefore

/-- Three unitary coordinate changes followed by an embedding preserve an operator lift. -/
theorem embedding_comp_three_conjOperators
    {A B C D E : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup E] [InnerProductSpace Complex E] [Semantics.FiniteQuantumSystem E]
    (U : Semantics.UnitaryTransport A B)
    (V : Semantics.UnitaryTransport B C)
    (W : Semantics.UnitaryTransport C D)
    (J : D →ₗ[Complex] E) (P : Semantics.Operator A) :
    J.comp ((W.conjOperator (V.conjOperator (U.conjOperator P))).comp
      (LinearMap.adjoint J)) =
      (J.comp (W.toLinearEquiv.toLinearMap.comp
        (V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap))).comp
        (P.comp (LinearMap.adjoint
          (J.comp (W.toLinearEquiv.toLinearMap.comp
            (V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap))))) := by
  have hAdjVU : LinearMap.adjoint
      (V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap) =
      U.symm.toLinearEquiv.toLinearMap.comp V.symm.toLinearEquiv.toLinearMap := by
    rw [LinearMap.adjoint_comp, Semantics.UnitaryTransport.adjoint_toLinearMap,
      Semantics.UnitaryTransport.adjoint_toLinearMap]
    simp only [Semantics.UnitaryTransport.symm_toLinearEquiv]
  have hAdjWVU : LinearMap.adjoint
      (W.toLinearEquiv.toLinearMap.comp
        (V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap)) =
      U.symm.toLinearEquiv.toLinearMap.comp
        (V.symm.toLinearEquiv.toLinearMap.comp W.symm.toLinearEquiv.toLinearMap) := by
    rw [LinearMap.adjoint_comp, hAdjVU,
      Semantics.UnitaryTransport.adjoint_toLinearMap]
    simp only [Semantics.UnitaryTransport.symm_toLinearEquiv, LinearMap.comp_assoc]
  have hAdjJ : LinearMap.adjoint
      (J.comp (W.toLinearEquiv.toLinearMap.comp
        (V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap))) =
      (U.symm.toLinearEquiv.toLinearMap.comp
        (V.symm.toLinearEquiv.toLinearMap.comp W.symm.toLinearEquiv.toLinearMap)).comp
        (LinearMap.adjoint J) := by
    rw [LinearMap.adjoint_comp, hAdjWVU]
  unfold Semantics.UnitaryTransport.conjOperator
  rw [hAdjJ]
  simp only [Semantics.UnitaryTransport.symm_toLinearEquiv, LinearMap.comp_assoc]

end BPTCommutingProjectorModel

end Bounds
end QEC
