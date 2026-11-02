import QEC.Coding.HypergraphProduct.Diagonal

/-!
# Public Tillich--Zémor hypergraph-product parameter theorems

The first declaration is the general two-input theorem frozen by the source
gate.  The second is the full-rank diagonal introduction specialization.  The
distance is `WithTop Nat`-valued so that the source convention assigning
infinity to the zero code is part of the theorem rather than an assumption.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u

/-- The general two-input Tillich--Zémor hypergraph-product parameter theorem:
source validity, exact blocklength and dimension, the four-distance lower
bound and source equality cases, and the exact check/qubit degree formulas. -/
theorem tillichZemorHypergraphProductParameters
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary ∧
    Fintype.card (QubitIndex rowOne colOne rowTwo colTwo) =
      Fintype.card colOne * Fintype.card colTwo +
        Fintype.card rowOne * Fintype.card rowTwo ∧
    Module.finrank (ZMod 2) (chainComplex D).middleHomology =
      Dimension (firstCode D) * Dimension (secondCode D) +
        Dimension (firstTransposeCode D) *
          Dimension (secondTransposeCode D) ∧
    inputDistanceMinimum D ≤
      extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ∧
    (DistanceEqualityCondition D →
      extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode D).xCode (binaryCSSCode D).zCode =
        inputDistanceMinimum D) ∧
    (∀ r₁ c₂, HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single (r₁, c₂) 1)) =
      rowWeight D.first r₁ + columnWeight D.second c₂) ∧
    (∀ c₁ r₂, HammingWeight (boundary2 D (Pi.single (c₁, r₂) 1)) =
      rowWeight D.second r₂ + columnWeight D.first c₁) ∧
    (∀ c₁ c₂, qubitDegree D (Sum.inl (c₁, c₂)) =
      columnWeight D.first c₁ + columnWeight D.second c₂) ∧
    (∀ r₁ r₂, qubitDegree D (Sum.inr (r₁, r₂)) =
      rowWeight D.second r₂ + rowWeight D.first r₁) ∧
    (∀ w,
      (∀ r, rowWeight D.first r ≤ w) →
      (∀ c, columnWeight D.first c ≤ w) →
      (∀ r, rowWeight D.second r ≤ w) →
      (∀ c, columnWeight D.second c ≤ w) →
      ((∀ x₀, HammingWeight
          (wordLinearMapTranspose (boundary1 D) (Pi.single x₀ 1)) ≤ 2 * w) ∧
       (∀ x₂, HammingWeight (boundary2 D (Pi.single x₂ 1)) ≤ 2 * w) ∧
       (∀ q, qubitDegree D q ≤ 2 * w))) := by
  refine ⟨binaryCSSCode_stabilizer_isSourceValidBinary D,
    card_qubitIndex, finrank_middleHomology_eq_dimension_products D,
    inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance D,
    extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum D,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun r₁ c₂ => xCheckWeight_eq D r₁ c₂
  · exact fun c₁ r₂ => zCheckWeight_eq D c₁ r₂
  · exact fun c₁ c₂ => qubitDegree_inl_eq D c₁ c₂
  · exact fun r₁ r₂ => qubitDegree_inr_eq D r₁ r₂
  · intro w hRowOne hColOne hRowTwo hColTwo
    rcases checkWeight_le_two_mul D w
      hRowOne hColOne hRowTwo hColTwo with ⟨hX, hZ⟩
    exact ⟨hX, hZ,
      qubitDegree_le_two_mul D w hRowOne hColOne hRowTwo hColTwo⟩

/-- The diagonal full-rank specialization stated in the introduction of TZ09.
Here `n = card Col`, `k = Dimension (ker H)`, the blocklength is
`n² + (n-k)²`, the encoded dimension is `k²`, the quantum distance is
the classical distance, and every displayed stabilizer row has weight equal
to an input row weight plus an input column weight. -/
theorem tillichZemorHypergraphProductDiagonalFullRank
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Fintype.card (QubitIndex Row Col Row Col) =
      Fintype.card Col ^ 2 +
        (Fintype.card Col - Dimension (firstCode (diagonalData H))) ^ 2 ∧
    Module.finrank (ZMod 2) (chainComplex (diagonalData H)).middleHomology =
      Dimension (firstCode (diagonalData H)) ^ 2 ∧
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode (diagonalData H)).xCode
        (binaryCSSCode (diagonalData H)).zCode =
      extendedMinimumDistance (firstCode (diagonalData H)) ∧
    (∀ r c, HammingWeight
        (wordLinearMapTranspose (boundary1 (diagonalData H))
          (Pi.single (r, c) 1)) =
      rowWeight H r + columnWeight H c) ∧
    (∀ c r, HammingWeight
        (boundary2 (diagonalData H) (Pi.single (c, r) 1)) =
      rowWeight H r + columnWeight H c) := by
  exact ⟨card_qubitIndex_diagonal_fullRank H hFull,
    finrank_middleHomology_diagonal_fullRank H hFull,
    extendedAlgebraicCSSMinimumDistance_diagonal_fullRank H hFull,
    xCheckWeight_diagonal_eq H, zCheckWeight_diagonal_eq H⟩

end QEC.Coding.HypergraphProduct
