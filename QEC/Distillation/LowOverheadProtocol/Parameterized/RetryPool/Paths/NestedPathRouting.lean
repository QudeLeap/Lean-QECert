import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Regrouping
import QEC.Distillation.LowOverheadProtocol.Parameterized.PathEnvelope
import QEC.Semantics.Instruments.NestedTensor.Power
/-!
# Routing nested physical retry-tree paths

The recursive path carrier used by `nestedTensorPower` is identified exactly
with the existing finite function of routed logical sites.  This is a pure
reindexing: it changes no protocol state and supplies the literal `k ^ depth`
path count used by the physical union bound.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Semantics.FiniteInstrument

attribute [local instance 100] Fintype.ofFinite

/-- Read a nested tensor leaf as the corresponding routed logical-site path. -/
noncomputable def decodedRetryPoolNestedPathEquiv (m w depth : Nat) :
    nestedTensorPath (logicalOutputCount m w) depth ≃
      routedDepthOutputSlots m w depth :=
  (nestedTensorPathEquiv (logicalOutputCount m w) depth).trans
    { toFun := fun path index =>
        (decodedRetryPoolLogicalSiteFinEquiv m w).symm (path index)
      invFun := fun path index =>
        decodedRetryPoolLogicalSiteFinEquiv m w (path index)
      left_inv := by
        intro path
        funext index
        exact (decodedRetryPoolLogicalSiteFinEquiv m w).apply_symm_apply (path index)
      right_inv := by
        intro path
        funext index
        exact (decodedRetryPoolLogicalSiteFinEquiv m w).symm_apply_apply (path index) }

/-- Appending one finite tensor coordinate is exactly appending its logical
site to the corresponding routed output path. -/
@[simp] theorem decodedRetryPoolNestedPathEquiv_append
    (m w depth : Nat)
    (path : nestedTensorPath (logicalOutputCount m w) depth)
    (trial : Fin (logicalOutputCount m w)) :
    decodedRetryPoolNestedPathEquiv m w (depth + 1) (path, trial) =
      routedDepthOutputPathAppend m w depth
        (decodedRetryPoolNestedPathEquiv m w depth path)
        ((decodedRetryPoolLogicalSiteFinEquiv m w).symm trial) := by
  funext index
  refine Fin.lastCases ?_ (fun previousIndex => ?_) index
  · simp [decodedRetryPoolNestedPathEquiv, routedDepthOutputPathAppend]
    change (decodedRetryPoolLogicalSiteFinEquiv m w).symm
        (Fin.lastCases trial
          (nestedTensorPathEquiv (logicalOutputCount m w) depth path)
          (Fin.last depth)) = _
    simp
  · simp [decodedRetryPoolNestedPathEquiv, routedDepthOutputPathAppend]
    change (decodedRetryPoolLogicalSiteFinEquiv m w).symm
        (Fin.lastCases trial
          (nestedTensorPathEquiv (logicalOutputCount m w) depth path)
          previousIndex.castSucc) = _
    simp

/-- The physical nested path carrier has exactly the existing logical branch
count raised to its depth. -/
theorem decodedRetryPoolNestedPath_card (m w depth : Nat) :
    Fintype.card (nestedTensorPath (logicalOutputCount m w) depth) =
      logicalOutputCount m w ^ depth :=
  nestedTensorPath_card (logicalOutputCount m w) depth

end HH18Parameterized
end Distillation
end QEC
