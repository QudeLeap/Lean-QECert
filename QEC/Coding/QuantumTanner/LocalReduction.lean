import QEC.Coding.QuantumTanner.TensorApproximation
import QEC.Coding.QuantumTanner.TensorPuncture
import QEC.Coding.QuantumTanner.Distance

/-!
# From punctured tensor approximation to local weight reduction

This is the constructive last step of [LZ22, proof of Theorem thm:main].
Actual close column/row witnesses on a retained rectangle produce a full
tensor check. An explicit error-versus-weight margin makes that check reduce
the local weight. Geometric existence of the witnesses is not assumed proved.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe v

variable {A B : Type v} [Fintype A] [Fintype B]

/-- Construct a reducing full tensor word from punctured robustness and
actual close row/column words, paying only the deleted-coordinate budget. -/
theorem exists_tensor_weight_reduction_of_punctured_approximation
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (removedA : Finset A) (removedB : Finset B)
    (dA dB w : Nat)
    (hA : MinimumDistance (puncturedCode CA removedA) dA)
    (hB : MinimumDistance (puncturedCode CB removedB) dB)
    (hRobust : IsRobust (puncturedCode CA removedA) (puncturedCode CB removedB) w)
    (hBudget : 2 * w ≤ dA * dB)
    (x : Word (ZMod 2) (A × B))
    (C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB))
    (hC : C ∈ (columnCode (puncturedCode CA removedA)).carrier)
    (hR : R ∈ (rowCode (puncturedCode CB removedB)).carrier)
    (hClose : HammingWeight (tensorPunctureMap removedA removedB x + C) +
      HammingWeight (tensorPunctureMap removedA removedB x + R) ≤ w)
    (hMargin : 3 * (HammingWeight (tensorPunctureMap removedA removedB x + C) +
      HammingWeight (tensorPunctureMap removedA removedB x + R)) +
        2 * (removedA.card * Fintype.card B + Fintype.card A * removedB.card) <
      2 * HammingWeight x) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (x + c) < HammingWeight x := by
  obtain ⟨cKept, hcKept, hApprox⟩ := exists_tensor_approximation_of_robust
    (puncturedCode CA removedA) (puncturedCode CB removedB)
    dA dB w hA hB hRobust hBudget (tensorPunctureMap removedA removedB x)
    C R hC hR hClose
  obtain ⟨c, hc, hLift⟩ := exists_tensorCode_lift_punctured
    CA CB removedA removedB cKept hcKept
  have hLoss := hammingWeight_tensorPuncture_loss_le removedA removedB (x + c)
  rw [map_add, hLift] at hLoss
  exact ⟨c, hc, by omega⟩

end QEC.Coding.QuantumTanner
