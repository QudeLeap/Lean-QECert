import QEC.Coding.HypergraphProduct.Distance.Embedding

/-!
# Dual distance sector for the Tillich--Zémor hypergraph product

Transposing both Tanner matrices reverses the hypergraph-product complex.
Its middle coordinates differ only by exchanging the two sum blocks.  This
module proves that coordinate identification directly, including preservation
of Hamming weight, and then transports the first distance-sector theorem to
the cohomological sector.  No second support-restriction proof is duplicated.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- Exchange the two blocks of a word indexed by a sum. -/
def swapWord {F A B : Type*} (x : Word F (Sum A B)) : Word F (Sum B A)
  | Sum.inl b => x (Sum.inr b)
  | Sum.inr a => x (Sum.inl a)

@[simp]
theorem swapWord_inl_apply {F A B : Type*} (x : Word F (Sum A B)) (b : B) :
    swapWord x (Sum.inl b) = x (Sum.inr b) := rfl

@[simp]
theorem swapWord_inr_apply {F A B : Type*} (x : Word F (Sum A B)) (a : A) :
    swapWord x (Sum.inr a) = x (Sum.inl a) := rfl

@[simp]
theorem swapWord_swapWord {F A B : Type*} (x : Word F (Sum A B)) :
    swapWord (swapWord x) = x := by
  funext q
  cases q <;> rfl

/-- Exchanging the two coordinate blocks preserves Hamming weight exactly. -/
theorem hammingWeight_swapWord
    {F A B : Type*} [Zero F] [DecidableEq F] [Fintype A] [Fintype B]
    (x : Word F (Sum A B)) :
    HammingWeight (swapWord x) = HammingWeight x := by
  classical
  let e :
      {q : Sum B A // swapWord x q ≠ 0} ≃
        {q : Sum A B // x q ≠ 0} :=
    { toFun := fun q =>
        match q with
        | ⟨Sum.inl b, hb⟩ => ⟨Sum.inr b, hb⟩
        | ⟨Sum.inr a, ha⟩ => ⟨Sum.inl a, ha⟩
      invFun := fun q =>
        match q with
        | ⟨Sum.inl a, ha⟩ => ⟨Sum.inr a, ha⟩
        | ⟨Sum.inr b, hb⟩ => ⟨Sum.inl b, hb⟩
      left_inv := by rintro ⟨q, hq⟩; cases q <;> rfl
      right_inv := by rintro ⟨q, hq⟩; cases q <;> rfl }
  calc
    HammingWeight (swapWord x) =
        Fintype.card {q : Sum B A // swapWord x q ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {q : Sum A B // x q ≠ 0} := Fintype.card_congr e
    _ = HammingWeight x := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

/-- Transpose both input Tanner matrices.  Degree zero and degree two exchange,
while the two middle-coordinate blocks exchange order. -/
def transposeData
    {F rowOne colOne rowTwo colTwo : Type*}
    (D : Data F rowOne colOne rowTwo colTwo) :
    Data F colOne rowOne colTwo rowTwo where
  first := D.first.transpose
  second := D.second.transpose

@[simp]
theorem firstCode_transposeData
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) :
    firstCode (transposeData D) = firstTransposeCode D := rfl

@[simp]
theorem secondTransposeCode_transposeData
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    secondTransposeCode (transposeData D) = secondCode D := by
  rfl

/-- The first boundary after transposing both Tanner matrices is the transpose
of the original second boundary, after exchanging the middle blocks. -/
theorem boundary1_transposeData_swapWord
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)) :
    boundary1 (transposeData D) (swapWord z) =
      wordLinearMapTranspose (boundary2 D) z := by
  funext p
  rcases p with ⟨c₁, r₂⟩
  rw [boundary1_apply, boundary2, wordLinearMapTranspose_toLin'_apply]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
    boundary2Matrix_inl_apply, boundary2Matrix_inr_apply]
  simp [transposeData, swapWord, ZMod.neg_eq_self_mod_two, mul_comm, add_comm]

/-- The second boundary after transposing both Tanner matrices becomes the
transpose of the original first boundary after exchanging middle blocks. -/
theorem swapWord_boundary2_transposeData
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (w : Word (ZMod 2) (C0Index rowOne colTwo)) :
    swapWord (boundary2 (transposeData D) w) =
      wordLinearMapTranspose (boundary1 D) w := by
  funext q
  cases q with
  | inl p =>
      rcases p with ⟨c₁, c₂⟩
      rw [swapWord_inl_apply, boundary2_inr_apply,
        boundary1Transpose_inl_apply]
      simp [transposeData, mul_comm]
  | inr p =>
      rcases p with ⟨r₁, r₂⟩
      rw [swapWord_inr_apply, boundary2_inl_apply,
        boundary1Transpose_inr_apply]
      simp [transposeData, ZMod.neg_eq_self_mod_two, mul_comm]

/-- An original cocycle becomes a cycle for the transposed input data. -/
theorem swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : z ∈ (chainComplex D).middleCocycleCode.carrier) :
    swapWord z ∈ (chainComplex (transposeData D)).middleCycleCode.carrier := by
  rw [(chainComplex (transposeData D)).mem_middleCycleCode_iff]
  rw [chainComplex_boundary1, boundary1_transposeData_swapWord]
  exact ((chainComplex D).mem_middleCocycleCode_iff z).mp hz

/-- If the exchanged word is a boundary for the transposed data, the original
word is a coboundary. -/
theorem mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : swapWord z ∈
      (chainComplex (transposeData D)).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by
  rcases ((chainComplex (transposeData D)).mem_middleBoundaryCode_iff
    (swapWord z)).mp hz with ⟨w, hw⟩
  have hw' : boundary2 (transposeData D) w = swapWord z := by
    simpa using hw
  apply ((chainComplex D).mem_firstCoboundaryCheckCode_iff z).mpr
  refine ⟨w, ?_⟩
  calc
    wordLinearMapTranspose (chainComplex D).boundary1 w =
        swapWord (boundary2 (transposeData D) w) := by
      rw [chainComplex_boundary1, swapWord_boundary2_transposeData]
    _ = swapWord (swapWord z) := by rw [hw']
    _ = z := swapWord_swapWord z

/-- A cohomological logical word cannot have weight below both the second
primal distance and the first transpose distance. -/
theorem middleCocycle_mem_firstCoboundaryCheckCode_of_weight_lt
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hzCocycle : z ∈ (chainComplex D).middleCocycleCode.carrier)
    (hzSecond : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (secondCode D))
    (hzFirstTranspose : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (firstTransposeCode D)) :
    z ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by
  have hzCycle' : swapWord z ∈
      (chainComplex (transposeData D)).middleCycleCode.carrier :=
    swapWord_mem_middleCycleCode_of_mem_middleCocycleCode D z hzCocycle
  have hzFirst' : (HammingWeight (swapWord z) : WithTop Nat) <
      extendedMinimumDistance (firstCode (transposeData D)) := by
    rw [hammingWeight_swapWord, firstCode_transposeData]
    exact hzFirstTranspose
  have hzSecondTranspose' : (HammingWeight (swapWord z) : WithTop Nat) <
      extendedMinimumDistance (secondTransposeCode (transposeData D)) := by
    rw [hammingWeight_swapWord, secondTransposeCode_transposeData]
    exact hzSecond
  have hzBoundary' := middleCycle_mem_middleBoundaryCode_of_weight_lt
    (transposeData D) (swapWord z) hzCycle' hzFirst' hzSecondTranspose'
  exact mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
    D z hzBoundary'

end QEC.Coding.HypergraphProduct
