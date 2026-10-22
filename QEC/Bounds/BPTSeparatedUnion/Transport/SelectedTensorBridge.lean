import QEC.Bounds.BPTSeparatedUnion.Transport.SelectedTensorCore

/-!
# Named-embedding tensor compression

This bridge keeps a large concrete embedding named at BPT call sites while
performing its one tensor-map rewrite in a small generic theorem.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped TensorProduct

universe u

set_option maxHeartbeats 150000 in
set_option synthInstance.maxHeartbeats 50000 in
theorem registerFactorizedTensor_compression_left_of_embedding
    {iota : Type u} [Fintype iota] [DecidableEq iota] (q : iota → Nat)
    (S : Semantics.QuditSubsystem q)
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (eSel : H →ₗ[Complex] S.selectedSystem) (eComp : K →ₗ[Complex] S.complementSystem)
    (J : Semantics.CompositeSystem H K →ₗ[Complex] S.factorizedSystem)
    (hJ : J = TensorProduct.map eSel eComp)
    (hComp : (LinearMap.adjoint eComp).comp eComp = (1 : Semantics.Operator K))
    (A : Semantics.Operator S.selectedSystem) :
    (LinearMap.adjoint J).comp
        ((S.registerFactorization.conjOperator (S.extendLocalToRegister A)).comp J) =
      TensorProduct.map ((LinearMap.adjoint eSel).comp (A.comp eSel))
        (1 : Semantics.Operator K) := by
  rw [hJ]
  exact registerFactorizedTensor_compression_left q S eSel eComp hComp A

end Bounds
end QEC
