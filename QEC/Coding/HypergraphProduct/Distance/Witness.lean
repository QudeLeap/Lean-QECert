import QEC.Coding.HypergraphProduct.Distance.LowerBound
import QEC.Coding.HypergraphProduct.Locality

/-!
# Explicit logical witnesses for hypergraph-product distance upper bounds

The source equality cases are witnessed by product words.  This module keeps
the construction coordinate-level: it proves their weights, cycle/cocycle
conditions, and nontriviality from a nonzero pairing with a representative in
the opposite sector.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- A product word supported on the `colOne × colTwo` qubit block. -/
def firstBlockWord
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Mul F] [Zero F]
    (x : Word F colOne) (y : Word F colTwo) :
    Word F (QubitIndex rowOne colOne rowTwo colTwo)
  | Sum.inl p => x p.1 * y p.2
  | Sum.inr _ => 0

/-- A product word supported on the `rowOne × rowTwo` qubit block. -/
def secondBlockWord
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Mul F] [Zero F]
    (x : Word F rowOne) (y : Word F rowTwo) :
    Word F (QubitIndex rowOne colOne rowTwo colTwo)
  | Sum.inl _ => 0
  | Sum.inr p => x p.1 * y p.2

/-- Pairing factorization on the first physical block. -/
theorem wordPairing_firstBlockWord
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (x x' : Word F colOne) (y y' : Word F colTwo) :
    wordPairing
        (firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo) x y)
        (firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo) x' y') =
      wordPairing x x' * wordPairing y y' := by
  classical
  simp only [wordPairing_apply, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_prod_type, firstBlockWord, zero_mul, Finset.sum_const_zero,
    add_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c₁ _hc₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c₂ _hc₂
  ring

/-- Pairing factorization on the second physical block. -/
theorem wordPairing_secondBlockWord
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (x x' : Word F rowOne) (y y' : Word F rowTwo) :
    wordPairing
        (secondBlockWord (colOne := colOne) (colTwo := colTwo) x y)
        (secondBlockWord (colOne := colOne) (colTwo := colTwo) x' y') =
      wordPairing x x' * wordPairing y y' := by
  classical
  simp only [wordPairing_apply, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_prod_type, secondBlockWord, zero_mul, Finset.sum_const_zero,
    zero_add]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r₁ _hr₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r₂ _hr₂
  ring

/-- A basis word pairs with a word by evaluation. -/
theorem wordPairing_single_left
    {F : Type v} {A : Type u}
    [Field F] [Fintype F] [Fintype A] [DecidableEq A]
    (a : A) (x : Word F A) :
    wordPairing (Pi.single a 1) x = x a := by
  classical
  rw [wordPairing_apply, dotProduct, Finset.sum_eq_single a]
  · simp
  · intro b _hb hba
    simp [hba]
  · simp

/-- Evaluation is also the pairing with a basis word on the right. -/
theorem wordPairing_single_right
    {F : Type v} {A : Type u}
    [Field F] [Fintype F] [Fintype A] [DecidableEq A]
    (x : Word F A) (a : A) :
    wordPairing x (Pi.single a 1) = x a := by
  classical
  rw [wordPairing_apply, dotProduct, Finset.sum_eq_single a]
  · simp
  · intro b _hb hba
    simp [hba]
  · simp

/-- A first-block product with a basis word in the second factor has the
weight of its first factor. -/
theorem hammingWeight_firstBlockWord_single_right
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [Fintype colTwo] [DecidableEq colTwo]
    (x : Word F colOne) (c₂ : colTwo) :
    HammingWeight
        (firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
          x (Pi.single c₂ 1)) =
      HammingWeight x := by
  classical
  rw [show firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
      x (Pi.single c₂ 1) =
      Sum.elim
        (fun p : colOne × colTwo => if c₂ = p.2 then x p.1 else 0)
        (0 : Word F (rowOne × rowTwo)) by
    funext q
    cases q with
    | inl p =>
        rcases p with ⟨c₁, c₂'⟩
        by_cases h : c₂ = c₂'
        · subst c₂'
          simp [firstBlockWord]
        · simp [firstBlockWord, h]
    | inr p => simp [firstBlockWord]]
  rw [hammingWeight_sum_elim, hammingWeight_fixed_second]
  simp

/-- A first-block product with a basis word in the first factor has the
weight of its second factor. -/
theorem hammingWeight_firstBlockWord_single_left
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (c₁ : colOne) (y : Word F colTwo) :
    HammingWeight
        (firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
          (Pi.single c₁ 1) y) =
      HammingWeight y := by
  classical
  rw [show firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
      (Pi.single c₁ 1) y =
      Sum.elim
        (fun p : colOne × colTwo => if c₁ = p.1 then y p.2 else 0)
        (0 : Word F (rowOne × rowTwo)) by
    funext q
    cases q with
    | inl p =>
        rcases p with ⟨c₁', c₂⟩
        by_cases h : c₁ = c₁'
        · subst c₁'
          simp [firstBlockWord]
        · simp [firstBlockWord, h]
    | inr p => simp [firstBlockWord]]
  rw [hammingWeight_sum_elim, hammingWeight_fixed_first]
  simp

/-- A second-block product with a basis word in the second factor has the
weight of its first factor. -/
theorem hammingWeight_secondBlockWord_single_right
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (x : Word F rowOne) (r₂ : rowTwo) :
    HammingWeight
        (secondBlockWord (colOne := colOne) (colTwo := colTwo)
          x (Pi.single r₂ 1)) =
      HammingWeight x := by
  classical
  rw [show secondBlockWord (colOne := colOne) (colTwo := colTwo)
      x (Pi.single r₂ 1) =
      Sum.elim (0 : Word F (colOne × colTwo))
        (fun p : rowOne × rowTwo => if r₂ = p.2 then x p.1 else 0) by
    funext q
    cases q with
    | inl p => simp [secondBlockWord]
    | inr p =>
        rcases p with ⟨r₁, r₂'⟩
        by_cases h : r₂ = r₂'
        · subst r₂'
          simp [secondBlockWord]
        · simp [secondBlockWord, h]]
  rw [hammingWeight_sum_elim, hammingWeight_fixed_second]
  simp

/-- A second-block product with a basis word in the first factor has the
weight of its second factor. -/
theorem hammingWeight_secondBlockWord_single_left
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne] [Fintype colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (r₁ : rowOne) (y : Word F rowTwo) :
    HammingWeight
        (secondBlockWord (colOne := colOne) (colTwo := colTwo)
          (Pi.single r₁ 1) y) =
      HammingWeight y := by
  classical
  rw [show secondBlockWord (colOne := colOne) (colTwo := colTwo)
      (Pi.single r₁ 1) y =
      Sum.elim (0 : Word F (colOne × colTwo))
        (fun p : rowOne × rowTwo => if r₁ = p.1 then y p.2 else 0) by
    funext q
    cases q with
    | inl p => simp [secondBlockWord]
    | inr p =>
        rcases p with ⟨r₁', r₂⟩
        by_cases h : r₁ = r₁'
        · subst r₁'
          simp [secondBlockWord]
        · simp [secondBlockWord, h]]
  rw [hammingWeight_sum_elim, hammingWeight_fixed_first]
  simp

/-- Coordinate formula for the transpose of the second HGP boundary. -/
theorem boundary2Transpose_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (c₁ : colOne) (r₂ : rowTwo) :
    wordLinearMapTranspose (boundary2 D) z (c₁, r₂) =
      (∑ c₂ : colTwo, z (Sum.inl (c₁, c₂)) * D.second r₂ c₂) +
        ∑ r₁ : rowOne, z (Sum.inr (r₁, r₂)) * D.first r₁ c₁ := by
  classical
  rw [boundary2, wordLinearMapTranspose_toLin'_apply]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
    boundary2Matrix_inl_apply, boundary2Matrix_inr_apply]
  simp

/-- A first-block product is a cycle when its first factor is in the first
primal code. -/
theorem firstBlockWord_mem_middleCycleCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F colOne) (y : Word F colTwo)
    (hx : x ∈ (firstCode D).carrier) :
    firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo) x y ∈
      (chainComplex D).middleCycleCode.carrier := by
  rw [(chainComplex D).mem_middleCycleCode_iff]
  funext p
  rcases p with ⟨r₁, c₂⟩
  rw [chainComplex_boundary1, boundary1_apply]
  have hxZero := congrFun ((mem_firstCode_iff D x).mp hx) r₁
  change (∑ c₁ : colOne, D.first r₁ c₁ * x c₁) = 0 at hxZero
  simp only [firstBlockWord,
    mul_zero, Finset.sum_const_zero, add_zero]
  change (∑ c₁ : colOne, D.first r₁ c₁ * (x c₁ * y c₂)) = 0
  calc
    ∑ c₁ : colOne, D.first r₁ c₁ * (x c₁ * y c₂) =
        (∑ c₁ : colOne, D.first r₁ c₁ * x c₁) * y c₂ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c₁ _hc₁
      ring
    _ = 0 := by rw [hxZero, zero_mul]

/-- A first-block product is a cocycle when its second factor is in the second
primal code. -/
theorem firstBlockWord_mem_middleCocycleCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F colOne) (y : Word F colTwo)
    (hy : y ∈ (secondCode D).carrier) :
    firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo) x y ∈
      (chainComplex D).middleCocycleCode.carrier := by
  rw [(chainComplex D).mem_middleCocycleCode_iff]
  funext p
  rcases p with ⟨c₁, r₂⟩
  rw [chainComplex_boundary2, boundary2Transpose_apply]
  have hyZero := congrFun ((mem_secondCode_iff D y).mp hy) r₂
  change (∑ c₂ : colTwo, D.second r₂ c₂ * y c₂) = 0 at hyZero
  simp only [firstBlockWord,
    zero_mul, Finset.sum_const_zero, add_zero]
  calc
    ∑ c₂ : colTwo, (x c₁ * y c₂) * D.second r₂ c₂ =
        x c₁ * ∑ c₂ : colTwo, D.second r₂ c₂ * y c₂ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c₂ _hc₂
      ring
    _ = 0 := by rw [hyZero, mul_zero]

/-- A second-block product is a cycle when its second factor is in the second
transpose code. -/
theorem secondBlockWord_mem_middleCycleCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F rowOne) (y : Word F rowTwo)
    (hy : y ∈ (secondTransposeCode D).carrier) :
    secondBlockWord (colOne := colOne) (colTwo := colTwo) x y ∈
      (chainComplex D).middleCycleCode.carrier := by
  rw [(chainComplex D).mem_middleCycleCode_iff]
  funext p
  rcases p with ⟨r₁, c₂⟩
  rw [chainComplex_boundary1, boundary1_apply]
  have hyZero := congrFun ((mem_secondTransposeCode_iff D y).mp hy) c₂
  change (∑ r₂ : rowTwo, D.second r₂ c₂ * y r₂) = 0 at hyZero
  simp only [secondBlockWord,
    mul_zero, Finset.sum_const_zero, zero_add]
  calc
    ∑ r₂ : rowTwo, (-D.second r₂ c₂) * (x r₁ * y r₂) =
        ∑ r₂ : rowTwo,
          -(x r₁ * (D.second r₂ c₂ * y r₂)) := by
      apply Finset.sum_congr rfl
      intro r₂ _hr₂
      ring
    _ = -(∑ r₂ : rowTwo,
          x r₁ * (D.second r₂ c₂ * y r₂)) := by
      rw [Finset.sum_neg_distrib]
    _ = -(x r₁ * ∑ r₂ : rowTwo,
          D.second r₂ c₂ * y r₂) := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [hyZero, mul_zero, neg_zero]

/-- A second-block product is a cocycle when its first factor is in the first
transpose code. -/
theorem secondBlockWord_mem_middleCocycleCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F rowOne) (y : Word F rowTwo)
    (hx : x ∈ (firstTransposeCode D).carrier) :
    secondBlockWord (colOne := colOne) (colTwo := colTwo) x y ∈
      (chainComplex D).middleCocycleCode.carrier := by
  rw [(chainComplex D).mem_middleCocycleCode_iff]
  funext p
  rcases p with ⟨c₁, r₂⟩
  rw [chainComplex_boundary2, boundary2Transpose_apply]
  have hxZero := congrFun ((mem_firstTransposeCode_iff D x).mp hx) c₁
  change (∑ r₁ : rowOne, D.first r₁ c₁ * x r₁) = 0 at hxZero
  simp only [secondBlockWord,
    zero_mul, Finset.sum_const_zero, zero_add]
  calc
    ∑ r₁ : rowOne, (x r₁ * y r₂) * D.first r₁ c₁ =
        y r₂ * ∑ r₁ : rowOne, D.first r₁ c₁ * x r₁ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r₁ _hr₁
      ring
    _ = 0 := by rw [hxZero, mul_zero]

/-- A nonzero word has a nonzero coordinate. -/
theorem exists_apply_ne_zero_of_ne_zero
    {F : Type v} {A : Type u} [Zero F]
    (x : Word F A) (hx : x ≠ 0) : ∃ a, x a ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  funext a
  exact h a

/-- A cycle that pairs nontrivially with a cocycle cannot be a boundary. -/
theorem not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (z u : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (huCocycle : u ∈ (chainComplex D).middleCocycleCode.carrier)
    (hPair : wordPairing u z ≠ 0) :
    z ∉ (chainComplex D).middleBoundaryCode.carrier := by
  intro hzBoundary
  rcases ((chainComplex D).mem_middleBoundaryCode_iff z).mp hzBoundary with
    ⟨w, hw⟩
  have hw' : boundary2 D w = z := by simpa using hw
  have huZero : wordLinearMapTranspose (boundary2 D) u = 0 := by
    simpa using ((chainComplex D).mem_middleCocycleCode_iff u).mp huCocycle
  apply hPair
  calc
    wordPairing u z = wordPairing u (boundary2 D w) := by rw [hw']
    _ = wordPairing (wordLinearMapTranspose (boundary2 D) u) w :=
      (wordPairing_wordLinearMapTranspose (boundary2 D) u w).symm
    _ = 0 := by rw [huZero]; simp

/-- A cocycle that pairs nontrivially with a cycle cannot be a coboundary. -/
theorem not_mem_firstCoboundaryCheckCode_of_pairing_cycle_ne_zero
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (z u : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (huCycle : u ∈ (chainComplex D).middleCycleCode.carrier)
    (hPair : wordPairing z u ≠ 0) :
    z ∉ (chainComplex D).firstCoboundaryCheckCode.carrier := by
  intro hzCoboundary
  rcases ((chainComplex D).mem_firstCoboundaryCheckCode_iff z).mp
    hzCoboundary with ⟨w, hw⟩
  have hw' : wordLinearMapTranspose (boundary1 D) w = z := by
    simpa using hw
  have huZero : boundary1 D u = 0 := by
    simpa using ((chainComplex D).mem_middleCycleCode_iff u).mp huCycle
  apply hPair
  calc
    wordPairing z u =
        wordPairing (wordLinearMapTranspose (boundary1 D) w) u := by rw [hw']
    _ = wordPairing w (boundary1 D u) :=
      wordPairing_wordLinearMapTranspose (boundary1 D) w u
    _ = 0 := by rw [huZero]; simp

/-- A nonzero first-code word has a homologically nontrivial first-block
representative of the same weight whenever the second code is nonzero. -/
theorem exists_homology_witness_of_first_second_nonzero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (x : Word (ZMod 2) colOne) (hx : x ∈ (firstCode D).carrier)
    (hx0 : x ≠ 0)
    (y : Word (ZMod 2) colTwo) (hy : y ∈ (secondCode D).carrier)
    (hy0 : y ≠ 0) :
    ∃ z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo),
      z ∈ (chainComplex D).middleCycleCode.carrier ∧
      z ∉ (chainComplex D).middleBoundaryCode.carrier ∧
      HammingWeight z = HammingWeight x := by
  obtain ⟨c₁, hc₁⟩ := exists_apply_ne_zero_of_ne_zero x hx0
  obtain ⟨c₂, hc₂⟩ := exists_apply_ne_zero_of_ne_zero y hy0
  let z := firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
    x (Pi.single c₂ 1)
  let u := firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
    (Pi.single c₁ 1) y
  have hzCycle : z ∈ (chainComplex D).middleCycleCode.carrier :=
    firstBlockWord_mem_middleCycleCode D x (Pi.single c₂ 1) hx
  have huCocycle : u ∈ (chainComplex D).middleCocycleCode.carrier :=
    firstBlockWord_mem_middleCocycleCode D (Pi.single c₁ 1) y hy
  have hPair : wordPairing u z ≠ 0 := by
    rw [wordPairing_firstBlockWord, wordPairing_single_left,
      wordPairing_single_right]
    exact mul_ne_zero hc₁ hc₂
  refine ⟨z, hzCycle,
    not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero
      D z u huCocycle hPair, ?_⟩
  exact hammingWeight_firstBlockWord_single_right x c₂

/-- A nonzero second-code word has a cohomologically nontrivial first-block
representative of the same weight whenever the first code is nonzero. -/
theorem exists_cohomology_witness_of_first_second_nonzero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (x : Word (ZMod 2) colOne) (hx : x ∈ (firstCode D).carrier)
    (hx0 : x ≠ 0)
    (y : Word (ZMod 2) colTwo) (hy : y ∈ (secondCode D).carrier)
    (hy0 : y ≠ 0) :
    ∃ z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo),
      z ∈ (chainComplex D).middleCocycleCode.carrier ∧
      z ∉ (chainComplex D).firstCoboundaryCheckCode.carrier ∧
      HammingWeight z = HammingWeight y := by
  obtain ⟨c₁, hc₁⟩ := exists_apply_ne_zero_of_ne_zero x hx0
  obtain ⟨c₂, hc₂⟩ := exists_apply_ne_zero_of_ne_zero y hy0
  let z := firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
    (Pi.single c₁ 1) y
  let u := firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
    x (Pi.single c₂ 1)
  have hzCocycle : z ∈ (chainComplex D).middleCocycleCode.carrier :=
    firstBlockWord_mem_middleCocycleCode D (Pi.single c₁ 1) y hy
  have huCycle : u ∈ (chainComplex D).middleCycleCode.carrier :=
    firstBlockWord_mem_middleCycleCode D x (Pi.single c₂ 1) hx
  have hPair : wordPairing z u ≠ 0 := by
    rw [wordPairing_firstBlockWord, wordPairing_single_left,
      wordPairing_single_right]
    exact mul_ne_zero hc₁ hc₂
  refine ⟨z, hzCocycle,
    not_mem_firstCoboundaryCheckCode_of_pairing_cycle_ne_zero
      D z u huCycle hPair, ?_⟩
  exact hammingWeight_firstBlockWord_single_left c₁ y

/-- A nonzero first-transpose-code word has a cohomologically nontrivial
second-block representative of the same weight when the other transpose code
is nonzero. -/
theorem exists_cohomology_witness_of_transpose_nonzero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (x : Word (ZMod 2) rowOne)
    (hx : x ∈ (firstTransposeCode D).carrier) (hx0 : x ≠ 0)
    (y : Word (ZMod 2) rowTwo)
    (hy : y ∈ (secondTransposeCode D).carrier) (hy0 : y ≠ 0) :
    ∃ z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo),
      z ∈ (chainComplex D).middleCocycleCode.carrier ∧
      z ∉ (chainComplex D).firstCoboundaryCheckCode.carrier ∧
      HammingWeight z = HammingWeight x := by
  obtain ⟨r₁, hr₁⟩ := exists_apply_ne_zero_of_ne_zero x hx0
  obtain ⟨r₂, hr₂⟩ := exists_apply_ne_zero_of_ne_zero y hy0
  let z := secondBlockWord (colOne := colOne) (colTwo := colTwo)
    x (Pi.single r₂ 1)
  let u := secondBlockWord (colOne := colOne) (colTwo := colTwo)
    (Pi.single r₁ 1) y
  have hzCocycle : z ∈ (chainComplex D).middleCocycleCode.carrier :=
    secondBlockWord_mem_middleCocycleCode D x (Pi.single r₂ 1) hx
  have huCycle : u ∈ (chainComplex D).middleCycleCode.carrier :=
    secondBlockWord_mem_middleCycleCode D (Pi.single r₁ 1) y hy
  have hPair : wordPairing z u ≠ 0 := by
    rw [wordPairing_secondBlockWord, wordPairing_single_right,
      wordPairing_single_left]
    exact mul_ne_zero hr₁ hr₂
  refine ⟨z, hzCocycle,
    not_mem_firstCoboundaryCheckCode_of_pairing_cycle_ne_zero
      D z u huCycle hPair, ?_⟩
  exact hammingWeight_secondBlockWord_single_right x r₂

/-- A nonzero second-transpose-code word has a homologically nontrivial
second-block representative of the same weight when the other transpose code
is nonzero. -/
theorem exists_homology_witness_of_transpose_nonzero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (x : Word (ZMod 2) rowOne)
    (hx : x ∈ (firstTransposeCode D).carrier) (hx0 : x ≠ 0)
    (y : Word (ZMod 2) rowTwo)
    (hy : y ∈ (secondTransposeCode D).carrier) (hy0 : y ≠ 0) :
    ∃ z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo),
      z ∈ (chainComplex D).middleCycleCode.carrier ∧
      z ∉ (chainComplex D).middleBoundaryCode.carrier ∧
      HammingWeight z = HammingWeight y := by
  obtain ⟨r₁, hr₁⟩ := exists_apply_ne_zero_of_ne_zero x hx0
  obtain ⟨r₂, hr₂⟩ := exists_apply_ne_zero_of_ne_zero y hy0
  let z := secondBlockWord (colOne := colOne) (colTwo := colTwo)
    (Pi.single r₁ 1) y
  let u := secondBlockWord (colOne := colOne) (colTwo := colTwo)
    x (Pi.single r₂ 1)
  have hzCycle : z ∈ (chainComplex D).middleCycleCode.carrier :=
    secondBlockWord_mem_middleCycleCode D (Pi.single r₁ 1) y hy
  have huCocycle : u ∈ (chainComplex D).middleCocycleCode.carrier :=
    secondBlockWord_mem_middleCocycleCode D x (Pi.single r₂ 1) hx
  have hPair : wordPairing u z ≠ 0 := by
    rw [wordPairing_secondBlockWord, wordPairing_single_right,
      wordPairing_single_left]
    exact mul_ne_zero hr₁ hr₂
  refine ⟨z, hzCycle,
    not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero
      D z u huCocycle hPair, ?_⟩
  exact hammingWeight_secondBlockWord_single_left r₁ y

end QEC.Coding.HypergraphProduct
