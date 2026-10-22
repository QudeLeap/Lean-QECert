import QEC.Coding.QuantumTanner.CayleyLink
import QEC.Coding.QuantumTanner.NormalViews
import QEC.Coding.QuantumTanner.ViewAssembly
import QEC.Coding.QuantumTanner.LocalReduction
import QEC.Coding.QuantumTanner.HeavySelection
import QEC.Coding.QuantumTanner.ExceptionalVertices

/-!
# Reducing checks from normal neighboring views

Actual support covers at the neighboring vertices give close codewords on
each retained row and column, by Cayley link transport. Puncture-resistant
robustness and an explicit numeric margin then construct a reducing check.
This is the constructive final neighborhood argument in
[LZ22, proof of Theorem thm:main]. Selection of such a neighborhood from the
spectral hypotheses is a separate obligation.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

open Classical

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- Normal covers at left/right neighbors produce the actual close
punctured row/column words, with the source's sum-of-line-errors budget. -/
theorem exists_punctured_approximations_of_normal_neighbors
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB : Nat) (hA : HasMinimumDistanceAtLeast CA dA)
    (hB : HasMinimumDistanceAtLeast CB dB)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool)
    (removedA : Finset A) (removedB : Finset B) (rowError columnError : Nat)
    (hLeft : ∀ a : KeptCoordinate removedA, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (X.leftGenerator a.1 * g, !side) x ∈
        (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (X.leftGenerator a.1 * g, !side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧ columns.card ≤ rowError)
    (hRight : ∀ b : KeptCoordinate removedB, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (g * X.rightGenerator b.1, !side) x ∈
        (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (g * X.rightGenerator b.1, !side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧ rows.card ≤ columnError) :
    ∃ C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB),
      C ∈ (columnCode (puncturedCode CA removedA)).carrier ∧
      R ∈ (rowCode (puncturedCode CB removedB)).carrier ∧
      HammingWeight (tensorPunctureMap removedA removedB (X.localRestriction (g, side) x) + C) ≤
        Fintype.card B * columnError ∧
      HammingWeight (tensorPunctureMap removedA removedB (X.localRestriction (g, side) x) + R) ≤
        Fintype.card A * rowError := by
  apply exists_punctured_row_column_approximations CA CB removedA removedB
    (X.localRestriction (g, side) x) rowError columnError
  · intro a
    obtain ⟨rows, columns, hLocal, hCovered, hRows, hColumns, hError⟩ := hLeft a
    obtain ⟨r, c, hr, hc, hParts, hRowError, hColumnError, hHeavyRow, hHeavyColumn⟩ :=
      exists_row_column_approximations_of_cover CA CB dA dB hA hB
        (X.localRestriction (X.leftGenerator a.1 * g, !side) x) hLocal
        rows columns hRows hColumns hCovered
    refine ⟨rowRestriction (X.leftInverse a.1) r, hr _, ?_⟩
    rw [X.rowRestriction_localRestriction_rebase_left hX]
    exact (hRowError _).trans hError
  · intro b
    obtain ⟨rows, columns, hLocal, hCovered, hRows, hColumns, hError⟩ := hRight b
    obtain ⟨r, c, hr, hc, hParts, hRowError, hColumnError, hHeavyRow, hHeavyColumn⟩ :=
      exists_row_column_approximations_of_cover CA CB dA dB hA hB
        (X.localRestriction (g * X.rightGenerator b.1, !side) x) hLocal
        rows columns hRows hColumns hCovered
    refine ⟨columnRestriction (X.rightInverse b.1) c, hc _, ?_⟩
    rw [X.columnRestriction_localRestriction_rebase_right hX]
    exact (hColumnError _).trans hError

/-- A selected normal neighborhood satisfying the numerical error margin
has an attained local tensor check that strictly reduces its weight. -/
theorem exists_local_reduction_of_punctured_line_approximations
    (X : LeftRightCayleySquareComplex G A B Square)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool)
    (removedA : Finset A) (removedB : Finset B)
    (dA dB w rowError columnError : Nat)
    (hA : MinimumDistance (puncturedCode CA removedA) dA)
    (hB : MinimumDistance (puncturedCode CB removedB) dB)
    (hRobust : IsRobust (puncturedCode CA removedA) (puncturedCode CB removedB) w)
    (hBudget : 2 * w ≤ dA * dB)
    (hRows : ∀ a : KeptCoordinate removedA, ∃ r : Word (ZMod 2) B,
      r ∈ CB.carrier ∧
      HammingWeight (rowRestriction a.1 (X.localRestriction (g, side) x) + r) ≤ rowError)
    (hColumns : ∀ b : KeptCoordinate removedB, ∃ c : Word (ZMod 2) A,
      c ∈ CA.carrier ∧
      HammingWeight (columnRestriction b.1 (X.localRestriction (g, side) x) + c) ≤ columnError)
    (hErrors : Fintype.card B * columnError + Fintype.card A * rowError ≤ w)
    (hMargin : 3 * (Fintype.card B * columnError + Fintype.card A * rowError) +
      2 * (removedA.card * Fintype.card B + Fintype.card A * removedB.card) <
      2 * HammingWeight (X.localRestriction (g, side) x)) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, side) x + c) <
        HammingWeight (X.localRestriction (g, side) x) := by
  obtain ⟨C, R, hC, hR, hCError, hRError⟩ :=
    exists_punctured_row_column_approximations CA CB removedA removedB
      (X.localRestriction (g, side) x) rowError columnError hRows hColumns
  apply exists_tensor_weight_reduction_of_punctured_approximation CA CB
    removedA removedB dA dB w hA hB hRobust hBudget
    (X.localRestriction (g, side) x) C R hC hR
  · omega
  · omega

/-- Labels whose left neighbor is actually exceptional. -/
def exceptionalLeftLabels (X : LeftRightCayleySquareComplex G A B Square)
    (g : G) (exceptional : Finset G) : Finset A :=
  Finset.univ.filter fun a => X.leftGenerator a * g ∈ exceptional

/-- Labels whose right neighbor is actually exceptional. -/
def exceptionalRightLabels (X : LeftRightCayleySquareComplex G A B Square)
    (g : G) (exceptional : Finset G) : Finset B :=
  Finset.univ.filter fun b => g * X.rightGenerator b ∈ exceptional

/-- Robustness supplies the actual small covers at every nonexceptional
neighbor, including zero local views outside the active set. -/
theorem exists_normal_cover_of_robust
    (X : LeftRightCayleySquareComplex G A B Square)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w normalCutoff : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hRobust : IsRobust CA CB w) (hCutoff : 0 < normalCutoff)
    (hWeightBudget : normalCutoff - 1 ≤ w)
    (hRows : (normalCutoff - 1) / dB < dA)
    (hColumns : (normalCutoff - 1) / dA < dB)
    (side : Bool) (x : Word (ZMod 2) Square)
    (hLocal : ∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier)
    (g : G) (hg : g ∉ X.exceptionalVerticesOnSide side x normalCutoff) :
    ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (g, side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧
      rows.card ≤ (normalCutoff - 1) / dB ∧
      columns.card ≤ (normalCutoff - 1) / dA := by
  have hWeight : HammingWeight (X.localRestriction (g, side) x) < normalCutoff := by
    by_cases hActive : g ∈ X.activeVerticesOnSide side x
    · by_contra hNot
      exact hg (Finset.mem_filter.mpr ⟨hActive, by omega⟩)
    · have hZero : X.localRestriction (g, side) x = 0 := by
        simpa [activeVerticesOnSide] using hActive
      simpa [hZero, HammingWeight, hammingSupport] using hCutoff
  have hWeight' : HammingWeight (X.localRestriction (g, side) x) ≤ normalCutoff - 1 := by omega
  obtain ⟨rows, columns, hCover, hRowCount, hColumnCount⟩ :=
    hRobust dA dB hA hB _ (hLocal g) (hWeight'.trans hWeightBudget)
  have hRowBound := hRowCount.trans (Nat.div_le_div_right hWeight')
  have hColumnBound := hColumnCount.trans (Nat.div_le_div_right hWeight')
  exact ⟨rows, columns, hLocal g, hCover, hRowBound.trans_lt hRows,
    hColumnBound.trans_lt hColumns, hRowBound, hColumnBound⟩

/-- The selected vertex's bad incoming degree counts both kinds of bad labels. -/
theorem exceptional_labels_card_eq_incoming_degree
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (exceptional : Finset G) :
    (X.exceptionalLeftLabels g exceptional).card +
      (X.exceptionalRightLabels g exceptional).card =
      ∑ h ∈ exceptional, X.unionCayleyGraph h g := by
  unfold exceptionalLeftLabels exceptionalRightLabels
  rw [← X.sum_unionCayleyGraph_eq_labels]
  apply Finset.sum_congr rfl
  intro h hh
  exact X.unionCayleyGraph_symmetric g h

/-- Absorb all actual exceptional labels into matching punctures. Every
retained row and column then has a nonexceptional neighbor. -/
theorem exists_balanced_nonexceptional_neighbor_punctures
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (exceptional : Finset G)
    (p : Nat) (hCard : Fintype.card A = Fintype.card B) (hp : p ≤ Fintype.card A)
    (hBad : (∑ h ∈ exceptional, X.unionCayleyGraph h g) ≤ p) :
    ∃ removedA : Finset A, ∃ removedB : Finset B,
      removedA.card = removedB.card ∧ removedA.card ≤ p ∧
      (∀ a : KeptCoordinate removedA, X.leftGenerator a.1 * g ∉ exceptional) ∧
      (∀ b : KeptCoordinate removedB, g * X.rightGenerator b.1 ∉ exceptional) := by
  have hCount := X.exceptional_labels_card_eq_incoming_degree g exceptional
  have hLeft : (X.exceptionalLeftLabels g exceptional).card ≤ p := by omega
  have hRight : (X.exceptionalRightLabels g exceptional).card ≤ p := by omega
  obtain ⟨removedA, removedB, hContainsA, hContainsB, hEqual, hSize⟩ :=
    exists_balanced_punctures (X.exceptionalLeftLabels g exceptional)
      (X.exceptionalRightLabels g exceptional) p hCard hLeft hRight hp
  refine ⟨removedA, removedB, hEqual, hSize, ?_, ?_⟩
  · intro a ha
    exact a.2 (hContainsA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))
  · intro b hb
    exact b.2 (hContainsB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩))

/-- A genuinely selected heavy vertex produces a reducing tensor check.
Matching punctures, punctured minimum distances, attained approximations and
the check itself are all constructed from the actual codes and incidences. -/
theorem exists_local_reduction_of_selected_heavy_vertex
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w p : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hCard : Fintype.card A = Fintype.card B) (hp : p ≤ Fintype.card A)
    (hpA : p < dA) (hpB : p < dB)
    (hRobust : IsRobustWithPunctureResistance CA CB w p)
    (hBudget : 2 * w ≤ (dA - p) * (dB - p))
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (normal exceptional : Finset G) (g : G) (threshold : ℝ)
    (hHeavy : threshold ≤ (∑ h ∈ normal, X.heavyUnionGraph side x cutoff h g : Nat))
    (hBad : (∑ h ∈ exceptional, X.unionCayleyGraph h g) ≤ p)
    (rowError columnError : Nat)
    (hCovers : ∀ h ∉ exceptional, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (h, side) x ∈ (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (h, side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧
      rows.card ≤ columnError ∧ columns.card ≤ rowError)
    (hErrors : Fintype.card B * columnError + Fintype.card A * rowError ≤ w)
    (hMargin : (3 * (Fintype.card B * columnError + Fintype.card A * rowError) +
      2 * (p * Fintype.card B + Fintype.card A * p) : Nat) <
      (cutoff : ℝ) * threshold) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, !side) x + c) <
        HammingWeight (X.localRestriction (g, !side) x) := by
  obtain ⟨removedA, removedB, hEqual, hSizeA, hLeft, hRight⟩ :=
    X.exists_balanced_nonexceptional_neighbor_punctures g exceptional p hCard hp hBad
  have hSizeB : removedB.card ≤ p := hEqual ▸ hSizeA
  have hLowerA : HasMinimumDistanceAtLeast CA dA := hA.choose_spec.2.2.2
  have hLowerB : HasMinimumDistanceAtLeast CB dB := hB.choose_spec.2.2.2
  obtain ⟨dA', hMinA', hDistanceA⟩ :=
    exists_punctured_minimumDistance CA dA hA removedA (hSizeA.trans_lt hpA)
  obtain ⟨dB', hMinB', hDistanceB⟩ :=
    exists_punctured_minimumDistance CB dB hB removedB (hSizeB.trans_lt hpB)
  have hBudget' : 2 * w ≤ dA' * dB' := by
    have hDA : dA - p ≤ dA' := (by omega : dA - p ≤ dA - removedA.card).trans hDistanceA
    have hDB : dB - p ≤ dB' := (by omega : dB - p ≤ dB - removedB.card).trans hDistanceB
    exact hBudget.trans (Nat.mul_le_mul hDA hDB)
  obtain ⟨C, R, hC, hR, hCError, hRError⟩ :=
    X.exists_punctured_approximations_of_normal_neighbors hX CA CB dA dB hLowerA hLowerB
      x g (!side) removedA removedB rowError columnError
      (fun a => by
        obtain ⟨rows, columns, hLocal, hCover, hRows, hColumns, hRow, hColumn⟩ :=
          hCovers _ (hLeft a)
        exact ⟨rows, columns, by simpa only [Bool.not_not] using hLocal,
          by simpa only [Bool.not_not] using hCover, hRows, hColumns, hColumn⟩)
      (fun b => by
        obtain ⟨rows, columns, hLocal, hCover, hRows, hColumns, hRow, hColumn⟩ :=
          hCovers _ (hRight b)
        exact ⟨rows, columns, by simpa only [Bool.not_not] using hLocal,
          by simpa only [Bool.not_not] using hCover, hRows, hColumns, hRow⟩)
  have hWeight := X.cutoff_mul_incoming_heavyDegree_le_twice_localWeight
    hX side x cutoff normal g
  have hRealWeight : (cutoff : ℝ) * threshold ≤
      (2 * HammingWeight (X.localRestriction (g, !side) x) : Nat) := by
    have hScaled := mul_le_mul_of_nonneg_left hHeavy (Nat.cast_nonneg cutoff)
    have hWeight' : ((cutoff * (∑ h ∈ normal, X.heavyUnionGraph side x cutoff h g) : Nat) : ℝ) ≤
        (2 * HammingWeight (X.localRestriction (g, !side) x) : Nat) := by exact_mod_cast hWeight
    simp only [Nat.cast_mul] at hWeight'
    simpa only [Nat.cast_mul] using hScaled.trans hWeight'
  have hNatMargin : 3 * (Fintype.card B * columnError + Fintype.card A * rowError) +
      2 * (p * Fintype.card B + Fintype.card A * p) <
      2 * HammingWeight (X.localRestriction (g, !side) x) := by
    exact_mod_cast hMargin.trans_le hRealWeight
  have hLoss : removedA.card * Fintype.card B + Fintype.card A * removedB.card ≤
      p * Fintype.card B + Fintype.card A * p :=
    Nat.add_le_add (Nat.mul_le_mul_right _ hSizeA) (Nat.mul_le_mul_left _ hSizeB)
  apply exists_tensor_weight_reduction_of_punctured_approximation CA CB removedA removedB
    dA' dB' w hMinA' hMinB' (hRobust removedA removedB hEqual hSizeA) hBudget'
    (X.localRestriction (g, !side) x) C R hC hR
  · omega
  · omega

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
