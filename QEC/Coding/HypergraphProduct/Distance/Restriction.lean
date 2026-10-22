import QEC.Coding.HypergraphProduct.Distance.Support

/-!
# Restricted hypergraph products for the TZ09 distance argument

For a middle word, the first active set is the projection of its
`colOne × colTwo` support to `colOne`; the second active set is the projection
of its `rowOne × rowTwo` support to `rowTwo`.  The source proof restricts the
two Tanner matrices to exactly these coordinates.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- First-factor columns touched by the first physical block of a word. -/
def activeFirstColumns
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo)) : Finset colOne :=
  (hammingSupport z).biUnion fun q =>
    match q with
    | Sum.inl p => {p.1}
    | Sum.inr _ => ∅

/-- Second-factor rows touched by the second physical block of a word. -/
def activeSecondRows
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo)) : Finset rowTwo :=
  (hammingSupport z).biUnion fun q =>
    match q with
    | Sum.inl _ => ∅
    | Sum.inr p => {p.2}

theorem card_activeFirstColumns_le_HammingWeight
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo)) :
    (activeFirstColumns z).card ≤ HammingWeight z := by
  classical
  calc
    (activeFirstColumns z).card ≤
        ∑ q ∈ hammingSupport z,
          (match q with
            | Sum.inl p => ({p.1} : Finset colOne)
            | Sum.inr _ => ∅).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ hammingSupport z, 1 := by
      apply Finset.sum_le_sum
      intro q _hq
      cases q <;> simp
    _ = HammingWeight z := by
      simp [HammingWeight]

theorem card_activeSecondRows_le_HammingWeight
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo)) :
    (activeSecondRows z).card ≤ HammingWeight z := by
  classical
  calc
    (activeSecondRows z).card ≤
        ∑ q ∈ hammingSupport z,
          (match q with
            | Sum.inl _ => (∅ : Finset rowTwo)
            | Sum.inr p => {p.2}).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ hammingSupport z, 1 := by
      apply Finset.sum_le_sum
      intro q _hq
      cases q <;> simp
    _ = HammingWeight z := by
      simp [HammingWeight]

theorem inl_eq_zero_of_not_mem_activeFirstColumns
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    {c₁ : colOne} (hc₁ : c₁ ∉ activeFirstColumns z) (c₂ : colTwo) :
    z (Sum.inl (c₁, c₂)) = 0 := by
  by_contra hz
  apply hc₁
  apply Finset.mem_biUnion.mpr
  refine ⟨Sum.inl (c₁, c₂), ?_, ?_⟩
  · simp [hammingSupport, hz]
  · simp

theorem inr_eq_zero_of_not_mem_activeSecondRows
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (r₁ : rowOne) {r₂ : rowTwo} (hr₂ : r₂ ∉ activeSecondRows z) :
    z (Sum.inr (r₁, r₂)) = 0 := by
  by_contra hz
  apply hr₂
  apply Finset.mem_biUnion.mpr
  refine ⟨Sum.inr (r₁, r₂), ?_, ?_⟩
  · simp [hammingSupport, hz]
  · simp

/-- The Tanner matrices restricted to the coordinate projections of `z`. -/
def supportRestrictedData
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)) :
    Data (ZMod 2) rowOne {c // c ∈ activeFirstColumns z}
      {r // r ∈ activeSecondRows z} colTwo where
  first := restrictColumns D.first (activeFirstColumns z)
  second := fun r c => D.second r.1 c

/-- Below the first primal distance, the first restricted classical code is
the zero code. -/
theorem supportRestrictedData_firstCode_dimension_eq_zero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (firstCode D)) :
    Dimension (firstCode (supportRestrictedData D z)) = 0 := by
  have hcard : ((activeFirstColumns z).card : WithTop Nat) <
      extendedMinimumDistance (firstCode D) :=
    (WithTop.coe_le_coe.mpr
      (card_activeFirstColumns_le_HammingWeight z)).trans_lt hz
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank (ZMod 2)
    (LinearMap.ker
      (Matrix.toLin' (restrictColumns D.first (activeFirstColumns z)))) = 0
  rw [ker_restrictColumns_eq_bot_of_card_lt_extendedMinimumDistance
    D.first (activeFirstColumns z) hcard]
  simpa using (finrank_bot (ZMod 2)
    (Word (ZMod 2) {c // c ∈ activeFirstColumns z}))

/-- Below the second transpose distance, the second restricted transpose code
is the zero code. -/
theorem supportRestrictedData_secondTransposeCode_dimension_eq_zero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (secondTransposeCode D)) :
    Dimension (secondTransposeCode (supportRestrictedData D z)) = 0 := by
  have hcard : ((activeSecondRows z).card : WithTop Nat) <
      extendedMinimumDistance (secondTransposeCode D) :=
    (WithTop.coe_le_coe.mpr
      (card_activeSecondRows_le_HammingWeight z)).trans_lt hz
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank (ZMod 2)
    (LinearMap.ker
      (Matrix.toLin'
        (restrictColumns D.second.transpose (activeSecondRows z)))) = 0
  rw [ker_restrictColumns_eq_bot_of_card_lt_extendedMinimumDistance
    D.second.transpose (activeSecondRows z) hcard]
  simpa using (finrank_bot (ZMod 2)
    (Word (ZMod 2) {r // r ∈ activeSecondRows z}))

end QEC.Coding.HypergraphProduct
