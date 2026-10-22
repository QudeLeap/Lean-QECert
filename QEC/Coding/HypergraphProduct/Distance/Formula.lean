import QEC.Coding.HypergraphProduct.Distance.UpperBound

/-!
# Exact equality cases for hypergraph-product distance

This is the four-case source condition from TZ09: a displayed minimum is
attained by one primal distance while the other primal distance is finite, or
by one transpose distance while the other transpose distance is finite.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u

/-- The exact disjunction under which TZ09 proves that its general lower bound
is attained. -/
def DistanceEqualityCondition
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) : Prop :=
  (extendedMinimumDistance (firstCode D) = inputDistanceMinimum D ∧
      extendedMinimumDistance (secondCode D) ≠ ⊤) ∨
  (extendedMinimumDistance (secondCode D) = inputDistanceMinimum D ∧
      extendedMinimumDistance (firstCode D) ≠ ⊤) ∨
  (extendedMinimumDistance (firstTransposeCode D) = inputDistanceMinimum D ∧
      extendedMinimumDistance (secondTransposeCode D) ≠ ⊤) ∨
  (extendedMinimumDistance (secondTransposeCode D) = inputDistanceMinimum D ∧
      extendedMinimumDistance (firstTransposeCode D) ≠ ⊤)

/-- Under exactly the source equality condition, the general HGP distance is
the minimum of the four input distances. -/
theorem extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hEquality : DistanceEqualityCondition D) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode =
      inputDistanceMinimum D := by
  apply le_antisymm
  · rcases hEquality with hFirst | hSecond | hFirstTranspose | hSecondTranspose
    · exact (extendedAlgebraicCSSMinimumDistance_le_first_of_second_ne_top
        D hFirst.2).trans_eq hFirst.1
    · exact (extendedAlgebraicCSSMinimumDistance_le_second_of_first_ne_top
        D hSecond.2).trans_eq hSecond.1
    · exact
        (extendedAlgebraicCSSMinimumDistance_le_firstTranspose_of_secondTranspose_ne_top
          D hFirstTranspose.2).trans_eq hFirstTranspose.1
    · exact
        (extendedAlgebraicCSSMinimumDistance_le_secondTranspose_of_firstTranspose_ne_top
          D hSecondTranspose.2).trans_eq hSecondTranspose.1
  · exact inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance D

end QEC.Coding.HypergraphProduct
