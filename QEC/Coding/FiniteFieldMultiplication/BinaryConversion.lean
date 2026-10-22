import QEC.Coding.FiniteFieldMultiplication.Selector

/-!
# The self-dual MFE bridge and selected cubic contraction

The fixed maps realize the basis change and coefficient expansion used in
[Ngu24, Main-result proof, Step 3]. The MFE permutations remain explicit;
the binary functional is the actual RMFE projection after MFE reconstruction.
-/

noncomputable section

namespace QEC.Coding

open scoped BigOperators

/-- The actual MFE after decoding coordinates in the fixed self-dual basis. -/
def f256MFEFromSelfDual : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 512 → ZMod 2) :=
  f256MFESigma.comp f256SelfDualBasis.equivFun.symm.toLinearMap

theorem f256MFEFromSelfDual_apply_basis_coordinates (x : F256) :
    f256MFEFromSelfDual (f256SelfDualBasis.equivFun x) = f256MFESigma x := by
  simp [f256MFEFromSelfDual]

theorem f256MFEFromSelfDual_injective : Function.Injective f256MFEFromSelfDual :=
  f256MFESigma_injective.comp f256SelfDualBasis.equivFun.symm.injective

theorem f256SelectorFunctional_eq_coefficient_sum (v : Fin 512 → ZMod 2) :
    f256SelectorFunctional v = ∑ q, v q * f256SelectorCoefficient q := by
  have hv : v = ∑ q, v q • Pi.single q 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply]
  calc
    f256SelectorFunctional v = f256SelectorFunctional (∑ q, v q • Pi.single q 1) := congrArg _ hv
    _ = ∑ q, v q * f256SelectorCoefficient q := by
      simp only [map_sum, map_smul, f256SelectorCoefficient, smul_eq_mul]

theorem f256SelectorFunctional_eq_selected_sum (v : Fin 512 → ZMod 2) :
    f256SelectorFunctional v = ∑ q ∈ f256SelectedCoordinates, v q := by
  rw [f256SelectorFunctional_eq_coefficient_sum]
  simp only [f256SelectedCoordinates, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : f256SelectorCoefficient q = 1
  · rw [if_pos h, h, mul_one]
  · have hz : f256SelectorCoefficient q = 0 := by
      apply Fin.ext
      have hlt : (f256SelectorCoefficient q).val < 2 := (f256SelectorCoefficient q).isLt
      have hn : (f256SelectorCoefficient q).val ≠ 1 := by
        intro heq
        exact h (Fin.ext heq)
      change (f256SelectorCoefficient q).val = 0
      omega
    rw [if_neg h, hz, mul_zero]

theorem f256SelectedCoordinates_ternary_identity (x y z : F256) :
    (∑ q ∈ f256SelectedCoordinates,
      f256MFESigma x q * f256MFESigma y (f256MFEpi2 q) *
        f256MFESigma z (f256MFEpi3 q)) = f256RMFEpsi (x * y * z) := by
  have h := f256SelectorFunctional_eq_selected_sum
    (f256MFESigma x * f256MFEpi2Action (f256MFESigma y) *
      f256MFEpi3Action (f256MFESigma z))
  rw [f256SelectorFunctional_apply, f256MFE_ternary_reverse_mul] at h
  exact h.symm

end QEC.Coding
