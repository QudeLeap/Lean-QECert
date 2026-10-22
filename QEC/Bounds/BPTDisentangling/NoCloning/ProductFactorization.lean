import QEC.Bounds.BPTDisentangling.NoCloning.ProductUnitary

/-!
# BPT product-factor transport

Small model-independent bridge for transporting an exact tensor factorization
through a unitary on its left factor.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u

namespace BPTCommutingProjectorModel

/-- Transport a two-step left-factor identification through a right-tensored unitary. -/
theorem unitaryRTensor_conj_of_two_step_factorization
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem N C) (Semantics.CompositeSystem N C))
    (Q : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem N C) D))
    (Theta A B : Semantics.Operator (Semantics.CompositeSystem N C))
    (P : Semantics.Operator D)
    (hfactor : Q = TensorProduct.map Theta P)
    (hTheta : Theta = A)
    (hconj : U.conjOperator A = B) :
    (unitaryRTensor U D).conjOperator Q = TensorProduct.map B P := by
  calc
    (unitaryRTensor U D).conjOperator Q =
        (unitaryRTensor U D).conjOperator (TensorProduct.map Theta P) := by
      rw [hfactor]
    _ = TensorProduct.map (U.conjOperator Theta) P :=
      unitaryRTensor_conj_tensorMap U Theta P
    _ = TensorProduct.map (U.conjOperator A) P := by
      rw [hTheta]
    _ = TensorProduct.map B P := by
      rw [hconj]

end BPTCommutingProjectorModel

end Bounds
end QEC
