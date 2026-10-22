import QEC.Coding.HypergraphProduct.Distance.Witness

/-!
# Equality-case upper bounds for the Tillich--Zémor hypergraph product

Each theorem below is the corresponding case of TZ09's upper-bound lemma.
The other input distance being finite supplies a nonzero word in the opposite
input code; no minimum-distance witness or conclusion-bearing assumption is
accepted as construction data.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

theorem exists_nonzero_mem_of_extendedMinimumDistance_ne_top
    {F : Type v} {A : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A]
    (C : LinearCode F A) (hFinite : extendedMinimumDistance C ≠ ⊤) :
    ∃ x, x ∈ C.carrier ∧ x ≠ 0 := by
  have hNeBot : C.carrier ≠ ⊥ := by
    intro hBot
    exact hFinite ((extendedMinimumDistance_eq_top_iff C).2 hBot)
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hNeBot with ⟨x, hx, hx0⟩
  exact ⟨x, hx, hx0⟩

/-- If the second primal code is nonzero, the quantum distance is at most the
first primal distance. -/
theorem extendedAlgebraicCSSMinimumDistance_le_first_of_second_ne_top
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hSecond : extendedMinimumDistance (secondCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (firstCode D) := by
  classical
  obtain ⟨y, hy, hy0⟩ :=
    exists_nonzero_mem_of_extendedMinimumDistance_ne_top
      (secondCode D) hSecond
  rw [extendedMinimumDistance, finitePredicateMinimum]
  apply Finset.le_inf
  intro x _hxUniv
  by_cases hx : x ∈ (firstCode D).carrier ∧ x ≠ 0
  · obtain ⟨z, hzCycle, hzNotBoundary, hzWeight⟩ :=
      exists_homology_witness_of_first_second_nonzero
        D x hx.1 hx.2 y hy hy0
    have hzLogical :
        IsCSSLogical (binaryCSSCode D).xCode (binaryCSSCode D).zCode z :=
      Or.inr ⟨by
          simpa only [binaryCSSCode_xCode,
            ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
            using hzCycle,
        by simpa only [binaryCSSCode_zCode] using hzNotBoundary⟩
    calc
      extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
          (HammingWeight z : WithTop Nat) := by
        rw [extendedAlgebraicCSSMinimumDistance]
        exact finitePredicateMinimum_le_of hzLogical
      _ = (HammingWeight x : WithTop Nat) := by rw [hzWeight]
      _ = if x ∈ (firstCode D).carrier ∧ x ≠ 0 then
          (HammingWeight x : WithTop Nat) else ⊤ := by simp [hx]
  · split
    · next hMatrix =>
        exfalso
        apply hx
        exact ⟨(mem_firstCode_iff D x).2 hMatrix.1, hMatrix.2⟩
    · exact le_top

/-- If the first primal code is nonzero, the quantum distance is at most the
second primal distance. -/
theorem extendedAlgebraicCSSMinimumDistance_le_second_of_first_ne_top
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hFirst : extendedMinimumDistance (firstCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (secondCode D) := by
  classical
  obtain ⟨x, hx, hx0⟩ :=
    exists_nonzero_mem_of_extendedMinimumDistance_ne_top
      (firstCode D) hFirst
  rw [extendedMinimumDistance, finitePredicateMinimum]
  apply Finset.le_inf
  intro y _hyUniv
  by_cases hy : y ∈ (secondCode D).carrier ∧ y ≠ 0
  · obtain ⟨z, hzCocycle, hzNotCoboundary, hzWeight⟩ :=
      exists_cohomology_witness_of_first_second_nonzero
        D x hx hx0 y hy.1 hy.2
    have hzLogical :
        IsCSSLogical (binaryCSSCode D).xCode (binaryCSSCode D).zCode z :=
      Or.inl ⟨by
          simpa only [binaryCSSCode_zCode,
            ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
            using hzCocycle,
        by simpa only [binaryCSSCode_xCode] using hzNotCoboundary⟩
    calc
      extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
          (HammingWeight z : WithTop Nat) := by
        rw [extendedAlgebraicCSSMinimumDistance]
        exact finitePredicateMinimum_le_of hzLogical
      _ = (HammingWeight y : WithTop Nat) := by rw [hzWeight]
      _ = if y ∈ (secondCode D).carrier ∧ y ≠ 0 then
          (HammingWeight y : WithTop Nat) else ⊤ := by simp [hy]
  · split
    · next hMatrix =>
        exfalso
        apply hy
        exact ⟨(mem_secondCode_iff D y).2 hMatrix.1, hMatrix.2⟩
    · exact le_top

/-- If the second transpose code is nonzero, the quantum distance is at most
the first transpose distance. -/
theorem extendedAlgebraicCSSMinimumDistance_le_firstTranspose_of_secondTranspose_ne_top
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hSecondTranspose :
      extendedMinimumDistance (secondTransposeCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (firstTransposeCode D) := by
  classical
  obtain ⟨y, hy, hy0⟩ :=
    exists_nonzero_mem_of_extendedMinimumDistance_ne_top
      (secondTransposeCode D) hSecondTranspose
  rw [extendedMinimumDistance, finitePredicateMinimum]
  apply Finset.le_inf
  intro x _hxUniv
  by_cases hx : x ∈ (firstTransposeCode D).carrier ∧ x ≠ 0
  · obtain ⟨z, hzCocycle, hzNotCoboundary, hzWeight⟩ :=
      exists_cohomology_witness_of_transpose_nonzero
        D x hx.1 hx.2 y hy hy0
    have hzLogical :
        IsCSSLogical (binaryCSSCode D).xCode (binaryCSSCode D).zCode z :=
      Or.inl ⟨by
          simpa only [binaryCSSCode_zCode,
            ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
            using hzCocycle,
        by simpa only [binaryCSSCode_xCode] using hzNotCoboundary⟩
    calc
      extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
          (HammingWeight z : WithTop Nat) := by
        rw [extendedAlgebraicCSSMinimumDistance]
        exact finitePredicateMinimum_le_of hzLogical
      _ = (HammingWeight x : WithTop Nat) := by rw [hzWeight]
      _ = if x ∈ (firstTransposeCode D).carrier ∧ x ≠ 0 then
          (HammingWeight x : WithTop Nat) else ⊤ := by simp [hx]
  · split
    · next hMatrix =>
        exfalso
        apply hx
        exact ⟨(mem_firstTransposeCode_iff D x).2 hMatrix.1, hMatrix.2⟩
    · exact le_top

/-- If the first transpose code is nonzero, the quantum distance is at most
the second transpose distance. -/
theorem extendedAlgebraicCSSMinimumDistance_le_secondTranspose_of_firstTranspose_ne_top
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hFirstTranspose :
      extendedMinimumDistance (firstTransposeCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (secondTransposeCode D) := by
  classical
  obtain ⟨x, hx, hx0⟩ :=
    exists_nonzero_mem_of_extendedMinimumDistance_ne_top
      (firstTransposeCode D) hFirstTranspose
  rw [extendedMinimumDistance, finitePredicateMinimum]
  apply Finset.le_inf
  intro y _hyUniv
  by_cases hy : y ∈ (secondTransposeCode D).carrier ∧ y ≠ 0
  · obtain ⟨z, hzCycle, hzNotBoundary, hzWeight⟩ :=
      exists_homology_witness_of_transpose_nonzero
        D x hx hx0 y hy.1 hy.2
    have hzLogical :
        IsCSSLogical (binaryCSSCode D).xCode (binaryCSSCode D).zCode z :=
      Or.inr ⟨by
          simpa only [binaryCSSCode_xCode,
            ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
            using hzCycle,
        by simpa only [binaryCSSCode_zCode] using hzNotBoundary⟩
    calc
      extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
          (HammingWeight z : WithTop Nat) := by
        rw [extendedAlgebraicCSSMinimumDistance]
        exact finitePredicateMinimum_le_of hzLogical
      _ = (HammingWeight y : WithTop Nat) := by rw [hzWeight]
      _ = if y ∈ (secondTransposeCode D).carrier ∧ y ≠ 0 then
          (HammingWeight y : WithTop Nat) else ⊤ := by simp [hy]
  · split
    · next hMatrix =>
        exfalso
        apply hy
        exact ⟨(mem_secondTransposeCode_iff D y).2 hMatrix.1, hMatrix.2⟩
    · exact le_top

end QEC.Coding.HypergraphProduct
