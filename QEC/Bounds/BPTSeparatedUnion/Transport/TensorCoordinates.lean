import QEC.Bounds.BPTDisentangling.InteractionAlgebra

/-!
# Tensor-coordinate transport lemmas

Small generic reassociation identities shared by the separated-union transport
leaves.  Their statements concern only concrete linear maps.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped TensorProduct

universe u

set_option maxHeartbeats 150000 in
set_option synthInstance.maxHeartbeats 50000 in
/-- Moving a final-factor operator through the inverse tensor associator. -/
theorem tensorAssociator_symm_right_intertwines
    {H K J : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J]
    [Semantics.FiniteQuantumSystem J] (R : Semantics.Operator J) :
    (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem H K)) R).comp
        (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).symm.toLinearEquiv.toLinearMap =
      (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).symm.toLinearEquiv.toLinearMap.comp
        (TensorProduct.map (1 : Semantics.Operator H)
          (TensorProduct.map (1 : Semantics.Operator K) R)) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => rfl
  | tmul h kj =>
      induction kj using TensorProduct.induction_on with
      | zero => rfl
      | tmul k j => rfl
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.tmul_add, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

end Bounds
end QEC
