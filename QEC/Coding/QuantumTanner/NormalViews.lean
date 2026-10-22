import QEC.Coding.QuantumTanner.Goodness

/-!
# Approximate local-code words in a normal view

A small row/column support cover of an actual dual-tensor word produces
attained local-code approximations on every row and column. Nonzero parts
force heavy rows or columns by the actual local minimum distance. These are
the normal-view facts in [LZ22, proof of Theorem thm:main].
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe v

variable {A B : Type v} [Fintype A] [Fintype B]

/-- Column support bounds the weight of every row, without any code premise. -/
theorem rowWeight_le_of_column_support
    (c : Word (ZMod 2) (A × B)) (columns : Finset B)
    (hSupport : ∀ b, b ∉ columns → columnRestriction b c = 0) (a : A) :
    HammingWeight (rowRestriction a c) ≤ columns.card := by
  apply Finset.card_le_card
  intro b hb
  by_contra hNot
  exact (Finset.mem_filter.mp hb).2 (congrFun (hSupport b hNot) a)

/-- Row support bounds the weight of every column. -/
theorem columnWeight_le_of_row_support
    (r : Word (ZMod 2) (A × B)) (rows : Finset A)
    (hSupport : ∀ a, a ∉ rows → rowRestriction a r = 0) (b : B) :
    HammingWeight (columnRestriction b r) ≤ rows.card := by
  apply Finset.card_le_card
  intro a ha
  by_contra hNot
  exact (Finset.mem_filter.mp ha).2 (congrFun (hSupport a hNot) b)

/-- Construct actual local-code approximations, with heavy-edge bounds for
each nonzero approximating word. The approximations are not input witnesses. -/
theorem exists_row_column_approximations_of_cover
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB : Nat)
    (hA : HasMinimumDistanceAtLeast CA dA)
    (hB : HasMinimumDistanceAtLeast CB dB)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < dA) (hColumns : columns.card < dB)
    (hCovered : SupportCovered x rows columns) :
    ∃ r c : Word (ZMod 2) (A × B),
      r ∈ (rowCode (A := A) CB).carrier ∧
      c ∈ (columnCode (B := B) CA).carrier ∧ x = r + c ∧
      (∀ a, HammingWeight (rowRestriction a x + rowRestriction a r) ≤ columns.card) ∧
      (∀ b, HammingWeight (columnRestriction b x + columnRestriction b c) ≤ rows.card) ∧
      (∀ a, rowRestriction a r ≠ 0 →
        dB ≤ HammingWeight (rowRestriction a x) + columns.card) ∧
      (∀ b, columnRestriction b c ≠ 0 →
        dA ≤ HammingWeight (columnRestriction b x) + rows.card) := by
  obtain ⟨r, c, hr, hc, hParts, hRowSupport, hColumnSupport⟩ :=
    exists_supported_decomposition_of_cover CA CB dA dB hA hB
      x hx rows columns hRows hColumns hCovered
  have hCancel {ι : Type v} (p q : Word (ZMod 2) ι) : (p + q) + p = q := by
    have hSelf : p + p = 0 := by
      ext i
      exact CharTwo.add_self_eq_zero _
    calc
      (p + q) + p = (p + p) + q := by abel
      _ = q := by rw [hSelf, zero_add]
  have hRowError (a : A) : rowRestriction a x + rowRestriction a r =
      rowRestriction a c := by
    rw [hParts, map_add]
    exact hCancel _ _
  have hColumnError (b : B) : columnRestriction b x + columnRestriction b c =
      columnRestriction b r := by
    rw [hParts, map_add, add_comm (columnRestriction b r) (columnRestriction b c)]
    exact hCancel _ _
  refine ⟨r, c, hr, hc, hParts, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hRowError]
    exact rowWeight_le_of_column_support c columns hColumnSupport a
  · intro b
    rw [hColumnError]
    exact columnWeight_le_of_row_support r rows hRowSupport b
  · intro a ha
    have hDistance := hB _ (hr a) ha
    have hTriangle := HammingWeight_add_le (rowRestriction a x) (rowRestriction a c)
    have hSame : rowRestriction a x + rowRestriction a c = rowRestriction a r := by
      rw [hParts, map_add, add_comm (rowRestriction a r) (rowRestriction a c)]
      exact hCancel _ _
    rw [hSame] at hTriangle
    have hSmall := rowWeight_le_of_column_support c columns hColumnSupport a
    omega
  · intro b hb
    have hDistance := hA _ (hc b) hb
    have hTriangle := HammingWeight_add_le (columnRestriction b x) (columnRestriction b r)
    have hSame : columnRestriction b x + columnRestriction b r = columnRestriction b c := by
      rw [hParts, map_add]
      exact hCancel _ _
    rw [hSame] at hTriangle
    have hSmall := columnWeight_le_of_row_support r rows hRowSupport b
    omega

/-- A nonzero covered dual-tensor word has a genuinely heavy row or column.
In particular, the edge used to define the opposite set is constructed,
not included in the hypotheses. -/
theorem exists_heavy_line_of_cover
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB cutoff : Nat)
    (hA : HasMinimumDistanceAtLeast CA dA)
    (hB : HasMinimumDistanceAtLeast CB dB)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier)
    (hx0 : x ≠ 0) (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < dA) (hColumns : columns.card < dB)
    (hCovered : SupportCovered x rows columns)
    (hCutoffRow : cutoff + columns.card ≤ dB)
    (hCutoffColumn : cutoff + rows.card ≤ dA) :
    (∃ a, cutoff ≤ HammingWeight (rowRestriction a x)) ∨
      ∃ b, cutoff ≤ HammingWeight (columnRestriction b x) := by
  obtain ⟨r, c, hr, hc, hParts, hRowError, hColumnError, hHeavyRow, hHeavyColumn⟩ :=
    exists_row_column_approximations_of_cover CA CB dA dB hA hB
      x hx rows columns hRows hColumns hCovered
  by_cases hr0 : r = 0
  · have hc0 : c ≠ 0 := by
      intro hc0
      apply hx0
      simpa [hr0, hc0] using hParts
    have hColumn : ∃ b, columnRestriction b c ≠ 0 := by
      by_contra h
      push_neg at h
      apply hc0
      ext ab
      exact congrFun (h ab.2) ab.1
    obtain ⟨b, hb⟩ := hColumn
    have h := hHeavyColumn b hb
    exact Or.inr ⟨b, by omega⟩
  · have hRow : ∃ a, rowRestriction a r ≠ 0 := by
      by_contra h
      push_neg at h
      apply hr0
      ext ab
      exact congrFun (h ab.1) ab.2
    obtain ⟨a, ha⟩ := hRow
    have h := hHeavyRow a ha
    exact Or.inl ⟨a, by omega⟩

end QEC.Coding.QuantumTanner
