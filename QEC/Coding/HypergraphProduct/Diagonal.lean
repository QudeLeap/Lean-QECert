import QEC.Coding.HypergraphProduct.Distance.Formula
import QEC.Coding.HypergraphProduct.Locality

/-!
# Diagonal full-rank hypergraph-product specialization

This module derives the introduction theorem of TZ09 from the general
two-input result.  Full row rank is represented by surjectivity of the parity
check map; the vanishing transpose code is proved from nondegeneracy of the
finite-coordinate pairing rather than accepted as an assumption.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- Use the same parity-check matrix for both HGP inputs. -/
def diagonalData
    {F : Type v} {Row Col : Type u} (H : Matrix Row Col F) :
    Data F Row Col Row Col where
  first := H
  second := H

/-- Surjectivity of a finite-coordinate map forces the kernel of its transpose
to vanish. -/
theorem ker_wordLinearMapTranspose_eq_bot_of_surjective
    {F : Type v} {A B : Type u}
    [Field F] [Fintype F]
    [Fintype A] [Fintype B]
    (f : Word F A →ₗ[F] Word F B) (hf : Function.Surjective f) :
    LinearMap.ker (wordLinearMapTranspose f) = ⊥ := by
  apply le_antisymm
  · intro y hy
    change wordLinearMapTranspose f y = 0 at hy
    have hyZero : y = 0 := by
      apply (wordPairing_nondegenerate (F := F)).left
      intro t
      obtain ⟨x, rfl⟩ := hf t
      rw [← wordPairing_wordLinearMapTranspose]
      rw [hy]
      simp
    rw [hyZero]
    exact Submodule.zero_mem _
  · exact bot_le

/-- A full-row-rank parity-check matrix has zero transpose code. -/
theorem transposeKernelCode_carrier_eq_bot_of_surjective
    {F : Type v} {Row Col : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col F) (hFull : Function.Surjective (Matrix.toLin' H)) :
    (parityCheckKernelCode (Matrix.toLin' H.transpose)).carrier = ⊥ := by
  change LinearMap.ker (Matrix.toLin' H.transpose) = ⊥
  rw [← wordLinearMapTranspose_toLin'_eq]
  exact ker_wordLinearMapTranspose_eq_bot_of_surjective
    (Matrix.toLin' H) hFull

theorem diagonalTransposeCode_carrier_eq_bot
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    (firstTransposeCode (diagonalData H)).carrier = ⊥ ∧
      (secondTransposeCode (diagonalData H)).carrier = ⊥ := by
  constructor <;>
    exact transposeKernelCode_carrier_eq_bot_of_surjective H hFull

theorem diagonalTransposeCode_dimensions_eq_zero
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Dimension (firstTransposeCode (diagonalData H)) = 0 ∧
      Dimension (secondTransposeCode (diagonalData H)) = 0 := by
  rcases diagonalTransposeCode_carrier_eq_bot H hFull with ⟨hFirst, hSecond⟩
  constructor
  · rw [Dimension_eq_finrank_carrier, hFirst]
    simp
  · rw [Dimension_eq_finrank_carrier, hSecond]
    simp

/-- Full row rank identifies the check count with `n - k`. -/
theorem card_row_eq_card_col_sub_dimension_diagonalCode
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Fintype.card Row =
      Fintype.card Col - Dimension (firstCode (diagonalData H)) := by
  have hRelation :=
    first_dimension_add_rows_eq_cols_add_transpose_dimension (diagonalData H)
  have hTranspose := (diagonalTransposeCode_dimensions_eq_zero H hFull).1
  rw [hTranspose, add_zero] at hRelation
  omega

/-- Exact blocklength of the diagonal full-rank construction. -/
theorem card_qubitIndex_diagonal_fullRank
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Fintype.card (QubitIndex Row Col Row Col) =
      Fintype.card Col ^ 2 +
        (Fintype.card Col - Dimension (firstCode (diagonalData H))) ^ 2 := by
  rw [card_qubitIndex,
    card_row_eq_card_col_sub_dimension_diagonalCode H hFull]
  simp [pow_two]

/-- Exact encoded dimension of the diagonal full-rank construction. -/
theorem finrank_middleHomology_diagonal_fullRank
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Module.finrank (ZMod 2) (chainComplex (diagonalData H)).middleHomology =
      Dimension (firstCode (diagonalData H)) ^ 2 := by
  rw [finrank_middleHomology_eq_dimension_products]
  rcases diagonalTransposeCode_dimensions_eq_zero H hFull with
    ⟨hFirstTranspose, hSecondTranspose⟩
  rw [hFirstTranspose, hSecondTranspose]
  simp [secondCode, firstCode, diagonalData, pow_two]

/-- The diagonal full-rank quantum distance equals the source-convention
distance of the classical code, including the zero-code infinity case. -/
theorem extendedAlgebraicCSSMinimumDistance_diagonal_fullRank
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode (diagonalData H)).xCode
        (binaryCSSCode (diagonalData H)).zCode =
      extendedMinimumDistance (firstCode (diagonalData H)) := by
  have hTransposeCarriers := diagonalTransposeCode_carrier_eq_bot H hFull
  have hFirstTransposeTop :
      extendedMinimumDistance (firstTransposeCode (diagonalData H)) = ⊤ :=
    (extendedMinimumDistance_eq_top_iff _).2 hTransposeCarriers.1
  have hSecondTransposeTop :
      extendedMinimumDistance (secondTransposeCode (diagonalData H)) = ⊤ :=
    (extendedMinimumDistance_eq_top_iff _).2 hTransposeCarriers.2
  have hMinimum : inputDistanceMinimum (diagonalData H) =
      extendedMinimumDistance (firstCode (diagonalData H)) := by
    rw [inputDistanceMinimum, hFirstTransposeTop, hSecondTransposeTop]
    simp [secondCode, firstCode, diagonalData]
  by_cases hFinite :
      extendedMinimumDistance (firstCode (diagonalData H)) = ⊤
  · have hLower :=
      inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance
        (diagonalData H)
    rw [hMinimum, hFinite] at hLower
    exact (top_unique hLower).trans hFinite.symm
  · apply le_antisymm
    · exact extendedAlgebraicCSSMinimumDistance_le_first_of_second_ne_top
        (diagonalData H) hFinite
    · rw [← hMinimum]
      exact inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance
        (diagonalData H)

/-- Exact X-check row weights in the diagonal construction. -/
theorem xCheckWeight_diagonal_eq
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2)) (r : Row) (c : Col) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 (diagonalData H))
          (Pi.single (r, c) 1)) =
      rowWeight H r + columnWeight H c := by
  exact xCheckWeight_eq (diagonalData H) r c

/-- Exact Z-check row weights in the diagonal construction. -/
theorem zCheckWeight_diagonal_eq
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2)) (c : Col) (r : Row) :
    HammingWeight (boundary2 (diagonalData H) (Pi.single (c, r) 1)) =
      rowWeight H r + columnWeight H c := by
  exact zCheckWeight_eq (diagonalData H) c r

end QEC.Coding.HypergraphProduct
