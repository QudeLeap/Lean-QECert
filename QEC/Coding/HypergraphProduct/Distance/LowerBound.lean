import QEC.Coding.HypergraphProduct.Distance.Duality

/-!
# General distance lower bound for the Tillich--Zémor hypergraph product

This module combines the homological and cohomological support-restriction
arguments and translates them to the public algebraic CSS distance.  All four
classical distances use the source convention that the zero code has distance
infinity.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u

/-- The minimum of the two primal and two transpose input distances. -/
def inputDistanceMinimum
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) : WithTop Nat :=
  min
    (min (extendedMinimumDistance (firstCode D))
      (extendedMinimumDistance (secondCode D)))
    (min (extendedMinimumDistance (firstTransposeCode D))
      (extendedMinimumDistance (secondTransposeCode D)))

theorem inputDistanceMinimum_le_first
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    inputDistanceMinimum D ≤ extendedMinimumDistance (firstCode D) := by
  simp [inputDistanceMinimum]

theorem inputDistanceMinimum_le_second
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    inputDistanceMinimum D ≤ extendedMinimumDistance (secondCode D) := by
  simp [inputDistanceMinimum]

theorem inputDistanceMinimum_le_firstTranspose
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    inputDistanceMinimum D ≤
      extendedMinimumDistance (firstTransposeCode D) := by
  simp [inputDistanceMinimum]

theorem inputDistanceMinimum_le_secondTranspose
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    inputDistanceMinimum D ≤
      extendedMinimumDistance (secondTransposeCode D) := by
  simp [inputDistanceMinimum]

/-- Every nontrivial pure CSS logical representative has weight at least the
minimum of the four source-convention input distances. -/
theorem inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    inputDistanceMinimum D ≤
      extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode := by
  classical
  rw [extendedAlgebraicCSSMinimumDistance]
  apply le_finitePredicateMinimum
  intro x hxLogical
  rcases hxLogical with hxCohomology | hxHomology
  · have hxCocycle : x ∈ (chainComplex D).middleCocycleCode.carrier := by
      simpa only [binaryCSSCode_zCode,
        ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
        using hxCohomology.1
    have hxNotCoboundary :
        x ∉ (chainComplex D).firstCoboundaryCheckCode.carrier := by
      simpa only [binaryCSSCode_xCode] using hxCohomology.2
    by_contra hLower
    have hxSmall : (HammingWeight x : WithTop Nat) <
        inputDistanceMinimum D := lt_of_not_ge hLower
    have hxSecond : (HammingWeight x : WithTop Nat) <
        extendedMinimumDistance (secondCode D) :=
      hxSmall.trans_le (inputDistanceMinimum_le_second D)
    have hxFirstTranspose : (HammingWeight x : WithTop Nat) <
        extendedMinimumDistance (firstTransposeCode D) :=
      hxSmall.trans_le (inputDistanceMinimum_le_firstTranspose D)
    exact hxNotCoboundary
      (middleCocycle_mem_firstCoboundaryCheckCode_of_weight_lt
        D x hxCocycle hxSecond hxFirstTranspose)
  · have hxCycle : x ∈ (chainComplex D).middleCycleCode.carrier := by
      simpa only [binaryCSSCode_xCode,
        ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
        using hxHomology.1
    have hxNotBoundary : x ∉ (chainComplex D).middleBoundaryCode.carrier := by
      simpa only [binaryCSSCode_zCode] using hxHomology.2
    by_contra hLower
    have hxSmall : (HammingWeight x : WithTop Nat) <
        inputDistanceMinimum D := lt_of_not_ge hLower
    have hxFirst : (HammingWeight x : WithTop Nat) <
        extendedMinimumDistance (firstCode D) :=
      hxSmall.trans_le (inputDistanceMinimum_le_first D)
    have hxSecondTranspose : (HammingWeight x : WithTop Nat) <
        extendedMinimumDistance (secondTransposeCode D) :=
      hxSmall.trans_le (inputDistanceMinimum_le_secondTranspose D)
    exact hxNotBoundary
      (middleCycle_mem_middleBoundaryCode_of_weight_lt
        D x hxCycle hxFirst hxSecondTranspose)

end QEC.Coding.HypergraphProduct
