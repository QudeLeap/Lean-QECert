import QEC.Coding.HypergraphProduct.Distance.Restriction

/-!
# Embedding the support-restricted hypergraph product

This module proves the two compatibility statements used in the TZ09 lower
bound: restriction preserves the first boundary of the supported middle word,
and a restricted second-boundary witness extends by zero to an original
second-boundary witness.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- Coordinate formula for the first hypergraph-product boundary. -/
theorem boundary1_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (r₁ : rowOne) (c₂ : colTwo) :
    boundary1 D z (r₁, c₂) =
      (∑ c₁ : colOne, D.first r₁ c₁ * z (Sum.inl (c₁, c₂))) +
        ∑ r₂ : rowTwo, (-D.second r₂ c₂) * z (Sum.inr (r₁, r₂)) := by
  rw [boundary1]
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_prod_type,
    boundary1Matrix_inl_apply, boundary1Matrix_inr_apply]
  simp

/-- Restrict a middle word to the two physical blocks selected by its support
projections. -/
def supportRestrictedWord
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)) :
    Word (ZMod 2)
      (QubitIndex rowOne {c // c ∈ activeFirstColumns z}
        {r // r ∈ activeSecondRows z} colTwo) :=
  fun q =>
    match q with
    | Sum.inl p => z (Sum.inl (p.1.1, p.2))
    | Sum.inr p => z (Sum.inr (p.1, p.2.1))

/-- Restricting to the two support projections preserves the first boundary
of the supported word. -/
theorem boundary1_supportRestrictedWord
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)) :
    boundary1 (supportRestrictedData D z) (supportRestrictedWord z) =
      boundary1 D z := by
  funext p
  rcases p with ⟨r₁, c₂⟩
  rw [boundary1_apply, boundary1_apply]
  change
    (∑ c₁ : {c // c ∈ activeFirstColumns z},
        D.first r₁ c₁.1 * z (Sum.inl (c₁.1, c₂))) +
      (∑ r₂ : {r // r ∈ activeSecondRows z},
        (-D.second r₂.1 c₂) * z (Sum.inr (r₁, r₂.1))) = _
  congr 1
  · refine sum_subtype_eq_sum_of_not_mem_eq_zero
      (activeFirstColumns z)
      (fun c₁ => D.first r₁ c₁ * z (Sum.inl (c₁, c₂))) ?_
    intro c₁ hc₁
    change D.first r₁ c₁ * z (Sum.inl (c₁, c₂)) = 0
    rw [inl_eq_zero_of_not_mem_activeFirstColumns z hc₁ c₂]
    simp
  · refine sum_subtype_eq_sum_of_not_mem_eq_zero
      (activeSecondRows z)
      (fun r₂ => (-D.second r₂ c₂) * z (Sum.inr (r₁, r₂))) ?_
    intro r₂ hr₂
    change (-D.second r₂ c₂) * z (Sum.inr (r₁, r₂)) = 0
    rw [inr_eq_zero_of_not_mem_activeSecondRows z r₁ hr₂]
    simp

/-- An original middle cycle restricts to a middle cycle of the support
restricted hypergraph product. -/
theorem supportRestrictedWord_mem_middleCycleCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier) :
    supportRestrictedWord z ∈
      (chainComplex (supportRestrictedData D z)).middleCycleCode.carrier := by
  change boundary1 D z = 0 at hz
  change boundary1 (supportRestrictedData D z) (supportRestrictedWord z) = 0
  rw [boundary1_supportRestrictedWord]
  exact hz

/-- Extend a restricted degree-two witness by zero in both selected
coordinates. -/
def supportExtendedWitness
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (w : Word (ZMod 2)
      (C2Index {c // c ∈ activeFirstColumns z}
        {r // r ∈ activeSecondRows z})) :
    Word (ZMod 2) (C2Index colOne rowTwo) :=
  fun p =>
    if hc : p.1 ∈ activeFirstColumns z then
      if hr : p.2 ∈ activeSecondRows z then
        w (⟨p.1, hc⟩, ⟨p.2, hr⟩)
      else 0
    else 0

@[simp]
theorem supportExtendedWitness_apply_mem
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (w : Word (ZMod 2)
      (C2Index {c // c ∈ activeFirstColumns z}
        {r // r ∈ activeSecondRows z}))
    (c : {c // c ∈ activeFirstColumns z})
    (r : {r // r ∈ activeSecondRows z}) :
    supportExtendedWitness z w (c.1, r.1) = w (c, r) := by
  simp [supportExtendedWitness, c.2, r.2]

/-- A restricted second-boundary equality extends to the corresponding
original second-boundary equality. -/
theorem boundary2_supportExtendedWitness
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (w : Word (ZMod 2)
      (C2Index {c // c ∈ activeFirstColumns z}
        {r // r ∈ activeSecondRows z}))
    (hw : boundary2 (supportRestrictedData D z) w =
      supportRestrictedWord z) :
    boundary2 D (supportExtendedWitness z w) = z := by
  funext q
  cases q with
  | inl p =>
      rcases p with ⟨c₁, c₂⟩
      by_cases hc₁ : c₁ ∈ activeFirstColumns z
      · have hwc := congrFun hw
          (Sum.inl (⟨c₁, hc₁⟩, c₂))
        rw [boundary2_inl_apply] at hwc
        change
          (∑ r₂ : {r // r ∈ activeSecondRows z},
              D.second r₂.1 c₂ * w (⟨c₁, hc₁⟩, r₂)) =
            z (Sum.inl (c₁, c₂)) at hwc
        rw [boundary2_inl_apply]
        calc
          (∑ r₂ : rowTwo,
              D.second r₂ c₂ * supportExtendedWitness z w (c₁, r₂)) =
              ∑ r₂ : {r // r ∈ activeSecondRows z},
                D.second r₂.1 c₂ *
                  supportExtendedWitness z w (c₁, r₂.1) := by
            symm
            refine sum_subtype_eq_sum_of_not_mem_eq_zero
              (activeSecondRows z)
              (fun r₂ => D.second r₂ c₂ *
                supportExtendedWitness z w (c₁, r₂)) ?_
            intro r₂ hr₂
            simp [supportExtendedWitness, hc₁, hr₂]
          _ =
              ∑ r₂ : {r // r ∈ activeSecondRows z},
                D.second r₂.1 c₂ * w (⟨c₁, hc₁⟩, r₂) := by
            apply Finset.sum_congr rfl
            intro r₂ _hr₂
            rw [supportExtendedWitness_apply_mem z w ⟨c₁, hc₁⟩ r₂]
          _ = z (Sum.inl (c₁, c₂)) := hwc
      · rw [boundary2_inl_apply,
          inl_eq_zero_of_not_mem_activeFirstColumns z hc₁ c₂]
        simp [supportExtendedWitness, hc₁]
  | inr p =>
      rcases p with ⟨r₁, r₂⟩
      by_cases hr₂ : r₂ ∈ activeSecondRows z
      · have hwc := congrFun hw
          (Sum.inr (r₁, ⟨r₂, hr₂⟩))
        rw [boundary2_inr_apply] at hwc
        change
          (∑ c₁ : {c // c ∈ activeFirstColumns z},
              D.first r₁ c₁.1 * w (c₁, ⟨r₂, hr₂⟩)) =
            z (Sum.inr (r₁, r₂)) at hwc
        rw [boundary2_inr_apply]
        calc
          (∑ c₁ : colOne,
              D.first r₁ c₁ * supportExtendedWitness z w (c₁, r₂)) =
              ∑ c₁ : {c // c ∈ activeFirstColumns z},
                D.first r₁ c₁.1 *
                  supportExtendedWitness z w (c₁.1, r₂) := by
            symm
            refine sum_subtype_eq_sum_of_not_mem_eq_zero
              (activeFirstColumns z)
              (fun c₁ => D.first r₁ c₁ *
                supportExtendedWitness z w (c₁, r₂)) ?_
            intro c₁ hc₁
            simp [supportExtendedWitness, hc₁]
          _ =
              ∑ c₁ : {c // c ∈ activeFirstColumns z},
                D.first r₁ c₁.1 * w (c₁, ⟨r₂, hr₂⟩) := by
            apply Finset.sum_congr rfl
            intro c₁ _hc₁
            rw [supportExtendedWitness_apply_mem z w c₁ ⟨r₂, hr₂⟩]
          _ = z (Sum.inr (r₁, r₂)) := hwc
      · rw [boundary2_inr_apply,
          inr_eq_zero_of_not_mem_activeSecondRows z r₁ hr₂]
        simp [supportExtendedWitness, hr₂]

/-- Membership in the restricted boundary code implies membership of the
original supported word in the original boundary code. -/
theorem mem_middleBoundaryCode_of_supportRestrictedWord_mem
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : supportRestrictedWord z ∈
      (chainComplex (supportRestrictedData D z)).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).middleBoundaryCode.carrier := by
  change ∃ w, boundary2 (supportRestrictedData D z) w =
    supportRestrictedWord z at hz
  change ∃ w, boundary2 D w = z
  rcases hz with ⟨w, hw⟩
  exact ⟨supportExtendedWitness z w,
    boundary2_supportExtendedWitness D z w hw⟩

/-- A homological logical word cannot have weight below both the first primal
distance and the second transpose distance. -/
theorem middleCycle_mem_middleBoundaryCode_of_weight_lt
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hzCycle : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hzFirst : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (firstCode D))
    (hzSecondTranspose : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (secondTransposeCode D)) :
    z ∈ (chainComplex D).middleBoundaryCode.carrier := by
  let D' := supportRestrictedData D z
  have hzCycle' : supportRestrictedWord z ∈
      (chainComplex D').middleCycleCode.carrier := by
    exact supportRestrictedWord_mem_middleCycleCode D z hzCycle
  have hFirstZero : Dimension (firstCode D') = 0 := by
    exact supportRestrictedData_firstCode_dimension_eq_zero D z hzFirst
  have hSecondTransposeZero :
      Dimension (secondTransposeCode D') = 0 := by
    exact supportRestrictedData_secondTransposeCode_dimension_eq_zero
      D z hzSecondTranspose
  have hHomologyZero :
      Module.finrank (ZMod 2) (chainComplex D').middleHomology = 0 := by
    rw [finrank_middleHomology_eq_dimension_products,
      hFirstZero, hSecondTransposeZero]
    simp
  let zCycle : (chainComplex D').middleCycleCode.carrier :=
    ⟨supportRestrictedWord z, hzCycle'⟩
  have hClassZero :
      (chainComplex D').middleBoundaryInCycles.mkQ zCycle = 0 :=
    (finrank_zero_iff_forall_zero.mp hHomologyZero) _
  have hzBoundaryInCycles :
      zCycle ∈ (chainComplex D').middleBoundaryInCycles :=
    (Submodule.Quotient.mk_eq_zero _).mp hClassZero
  have hzBoundary' : supportRestrictedWord z ∈
      (chainComplex D').middleBoundaryCode.carrier :=
    hzBoundaryInCycles
  exact mem_middleBoundaryCode_of_supportRestrictedWord_mem D z hzBoundary'

end QEC.Coding.HypergraphProduct
