import QEC.Coding.QuantumTanner.Goodness

/-!
# Robust tensor approximation

The attained-word form of [LZ22, Proposition prop:tensor]. Close column- and
row-code witnesses give a genuine tensor-code witness with the sharp `3/2`
factor. The statement uses integer weights, so no rounding is hidden.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe v

variable {A B : Type v} [Fintype A] [Fintype B]

/-- Robustness below the half-product-distance budget yields an attained
row/column decomposition whose parts have no more weight than their sum. -/
theorem exists_weight_bounded_decomposition_of_robust
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hRobust : IsRobust CA CB w) (hBudget : 2 * w ≤ dA * dB)
    (y : Word (ZMod 2) (A × B))
    (hy : y ∈ (dualTensorCode CA CB).carrier) (hWeight : HammingWeight y ≤ w) :
    ∃ r c : Word (ZMod 2) (A × B),
      r ∈ (rowCode (A := A) CB).carrier ∧
      c ∈ (columnCode (B := B) CA).carrier ∧
      y = r + c ∧ HammingWeight r ≤ HammingWeight y ∧
        HammingWeight c ≤ HammingWeight y := by
  obtain ⟨rows, columns, hCover, hRows, hColumns⟩ :=
    hRobust dA dB hA hB y hy hWeight
  obtain ⟨a, ha, ha0, hwa, hMinA⟩ := hA
  obtain ⟨b, hb, hb0, hwb, hMinB⟩ := hB
  have hPosA : 0 < dA := by
    rw [← hwa]
    exact Nat.pos_of_ne_zero fun hz => ha0 ((HammingWeight_eq_zero_iff a).mp hz)
  have hPosB : 0 < dB := by
    rw [← hwb]
    exact Nat.pos_of_ne_zero fun hz => hb0 ((HammingWeight_eq_zero_iff b).mp hz)
  have hRowsMul := (Nat.le_div_iff_mul_le hPosB).mp hRows
  have hColumnsMul := (Nat.le_div_iff_mul_le hPosA).mp hColumns
  apply exists_weight_bounded_decomposition_of_half_distance_cover
    CA CB dA dB hMinA hMinB hPosA hPosB y hy rows columns ?_ ?_ hCover
  · nlinarith
  · nlinarith

/-- Any close column- and row-code witnesses yield an actual tensor word at
distance at most `3/2` times the sum of their residual weights. -/
theorem exists_tensor_approximation_of_robust
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hRobust : IsRobust CA CB w) (hBudget : 2 * w ≤ dA * dB)
    (x C R : Word (ZMod 2) (A × B))
    (hC : C ∈ (columnCode (B := B) CA).carrier)
    (hR : R ∈ (rowCode (A := A) CB).carrier)
    (hClose : HammingWeight (x + C) + HammingWeight (x + R) ≤ w) :
    ∃ z : Word (ZMod 2) (A × B), z ∈ (tensorCode CA CB).carrier ∧
      2 * HammingWeight (x + z) ≤
        3 * (HammingWeight (x + C) + HammingWeight (x + R)) := by
  have hSelf (y : Word (ZMod 2) (A × B)) : y + y = 0 := by
    ext ab
    exact CharTwo.add_self_eq_zero _
  have hResidual : C + R = (x + C) + (x + R) := by
    calc
      C + R = (x + x) + (C + R) := by rw [hSelf, zero_add]
      _ = (x + C) + (x + R) := by abel
  have hSumWeight : HammingWeight (C + R) ≤
      HammingWeight (x + C) + HammingWeight (x + R) := by
    rw [hResidual]
    exact HammingWeight_add_le _ _
  have hSum : C + R ∈ (dualTensorCode CA CB).carrier :=
    (dualTensorCode CA CB).carrier.add_mem
      (mem_dualTensorCode_of_column CA CB hC) (mem_dualTensorCode_of_row CA CB hR)
  obtain ⟨r, c, hr, hc, hParts, hrWeight, hcWeight⟩ :=
    exists_weight_bounded_decomposition_of_robust CA CB dA dB w hA hB
      hRobust hBudget (C + R) hSum (hSumWeight.trans hClose)
  have hSame : C + c = R + r := by
    have h := congrArg (fun y => y + R + c) hParts
    simpa only [add_assoc, add_comm, add_left_comm, hSelf, add_zero, zero_add] using h
  have hTensor : C + c ∈ (tensorCode CA CB).carrier := by
    constructor
    · exact (columnCode CA).carrier.add_mem hC hc
    · rw [hSame]
      exact (rowCode CB).carrier.add_mem hR hr
  have hLeft : HammingWeight (x + (C + c)) ≤
      2 * HammingWeight (x + C) + HammingWeight (x + R) := by
    have ht := HammingWeight_add_le (x + C) c
    rw [add_assoc] at ht
    omega
  have hRight : HammingWeight (x + (C + c)) ≤
      HammingWeight (x + C) + 2 * HammingWeight (x + R) := by
    rw [hSame]
    have ht := HammingWeight_add_le (x + R) r
    rw [add_assoc] at ht
    omega
  exact ⟨C + c, hTensor, by omega⟩

end QEC.Coding.QuantumTanner
