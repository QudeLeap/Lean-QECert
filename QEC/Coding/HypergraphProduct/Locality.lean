import QEC.Coding.HypergraphProduct.Core
/-!
# Exact locality formulas for the Tillich--Zémor hypergraph product

The formulas in this module are proved from the two boundary matrices.  They
serve both as the LDPC-locality proof and as a coordinate-level regression
test for the two physical-qubit blocks.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

theorem hammingWeight_sum_elim
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [Fintype B]
    (x : Word F A) (y : Word F B) :
    HammingWeight (Sum.elim x y) = HammingWeight x + HammingWeight y := by
  classical
  let e :
      {s : Sum A B // Sum.elim x y s ≠ 0} ≃
        Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0} :=
    { toFun := fun s =>
        match s with
        | ⟨Sum.inl a, ha⟩ => Sum.inl ⟨a, ha⟩
        | ⟨Sum.inr b, hb⟩ => Sum.inr ⟨b, hb⟩
      invFun := fun s =>
        match s with
        | Sum.inl a => ⟨Sum.inl a.1, a.2⟩
        | Sum.inr b => ⟨Sum.inr b.1, b.2⟩
      left_inv := by rintro ⟨a | b, h⟩ <;> rfl
      right_inv := by rintro (a | b) <;> rfl }
  calc
    HammingWeight (Sum.elim x y) =
        Fintype.card {s : Sum A B // Sum.elim x y s ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card (Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0}) :=
      Fintype.card_congr e
    _ = HammingWeight x + HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

theorem hammingWeight_fixed_first
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [DecidableEq A] [Fintype B]
    (a : A) (x : Word F B) :
    HammingWeight (fun p : A × B => if a = p.1 then x p.2 else 0) =
      HammingWeight x := by
  classical
  let sourceWord : Word F (A × B) :=
    fun p => if a = p.1 then x p.2 else 0
  let e : {p : A × B // sourceWord p ≠ 0} ≃ {b : B // x b ≠ 0} :=
    { toFun := fun p =>
        ⟨p.1.2, by
          by_contra hx
          exact p.2 (by simp [sourceWord, hx])⟩
      invFun := fun b =>
        ⟨(a, b.1), by
          dsimp [sourceWord]
          simpa using b.2⟩
      left_inv := by
        rintro ⟨⟨a', b⟩, hp⟩
        apply Subtype.ext
        change (a, b) = (a', b)
        apply Prod.ext
        · dsimp [sourceWord] at hp
          by_cases haa : a = a'
          · exact haa
          · simp [haa] at hp
        · rfl
      right_inv := by
        rintro ⟨b, hb⟩
        rfl }
  calc
    HammingWeight sourceWord =
        Fintype.card {p : A × B // sourceWord p ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {b : B // x b ≠ 0} := Fintype.card_congr e
    _ = HammingWeight x := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

theorem hammingWeight_fixed_second
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [Fintype B] [DecidableEq B]
    (b : B) (x : Word F A) :
    HammingWeight (fun p : A × B => if b = p.2 then x p.1 else 0) =
      HammingWeight x := by
  classical
  let sourceWord : Word F (A × B) :=
    fun p => if b = p.2 then x p.1 else 0
  let e : {p : A × B // sourceWord p ≠ 0} ≃ {a : A // x a ≠ 0} :=
    { toFun := fun p =>
        ⟨p.1.1, by
          by_contra hx
          exact p.2 (by simp [sourceWord, hx])⟩
      invFun := fun a =>
        ⟨(a.1, b), by
          dsimp [sourceWord]
          simpa using a.2⟩
      left_inv := by
        rintro ⟨⟨a, b'⟩, hp⟩
        apply Subtype.ext
        change (a, b) = (a, b')
        apply Prod.ext
        · rfl
        · dsimp [sourceWord] at hp
          by_cases hbb : b = b'
          · exact hbb
          · simp [hbb] at hp
      right_inv := by
        rintro ⟨a, ha⟩
        rfl }
  calc
    HammingWeight sourceWord =
        Fintype.card {p : A × B // sourceWord p ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {a : A // x a ≠ 0} := Fintype.card_congr e
    _ = HammingWeight x := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

private theorem hammingWeight_neg
    {F A : Type*} [AddGroup F] [DecidableEq F] [Fintype A]
    (x : Word F A) :
    HammingWeight (fun a => -x a) = HammingWeight x := by
  classical
  unfold HammingWeight hammingSupport
  congr 1
  ext a
  simp

private theorem wordLinearMapTranspose_toLin_single
    {F Row Col : Type*} [Field F] [Fintype F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col F) (r : Row) :
    wordLinearMapTranspose (Matrix.toLin' M) (Pi.single r 1) =
      fun c => M r c := by
  ext c
  unfold wordLinearMapTranspose
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_eq_single r]
  · simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _hc' hne
      simp [hne]
    · simp
  · intro r' hr'
    simp [hr']

private theorem toLin_single
    {F Row Col : Type*} [Field F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col F) (c : Col) :
    Matrix.toLin' M (Pi.single c 1) = fun r => M r c := by
  ext r
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _hc' hne
    simp [hne]
  · simp

/-- Hamming weight of a selected row of a matrix. -/
def rowWeight
    {F Row Col : Type*} [Zero F] [DecidableEq F] [Fintype Col]
    (H : Matrix Row Col F) (r : Row) : Nat :=
  HammingWeight (H r)

/-- Hamming weight of a selected column of a matrix. -/
def columnWeight
    {F Row Col : Type*} [Zero F] [DecidableEq F] [Fintype Row]
    (H : Matrix Row Col F) (c : Col) : Nat :=
  HammingWeight (fun r => H r c)

/-- Exact weight of an X-check row: a row of `H₁` plus a column of
`H₂`. -/
theorem xCheckWeight_eq
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ : rowOne) (c₂ : colTwo) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single (r₁, c₂) 1)) =
      rowWeight D.first r₁ + columnWeight D.second c₂ := by
  rw [boundary1, wordLinearMapTranspose_toLin_single]
  have hWord : (fun q => boundary1Matrix D (r₁, c₂) q) =
      Sum.elim
        (fun p : colOne × colTwo =>
          if c₂ = p.2 then D.first r₁ p.1 else 0)
        (fun p : rowOne × rowTwo =>
          if r₁ = p.1 then -D.second p.2 c₂ else 0) := by
    funext q
    cases q <;> rfl
  rw [hWord]
  change HammingWeight
      (Sum.elim
        (fun p : colOne × colTwo =>
          if c₂ = p.2 then D.first r₁ p.1 else 0)
        (fun p : rowOne × rowTwo =>
          if r₁ = p.1 then -D.second p.2 c₂ else 0)) = _
  rw [hammingWeight_sum_elim, hammingWeight_fixed_second]
  have hRight :
      HammingWeight
          (fun p : rowOne × rowTwo =>
            if r₁ = p.1 then -D.second p.2 c₂ else 0) =
        columnWeight D.second c₂ := by
    calc
      _ = HammingWeight (fun r₂ => -D.second r₂ c₂) :=
        hammingWeight_fixed_first r₁ (fun r₂ => -D.second r₂ c₂)
      _ = HammingWeight (fun r₂ => D.second r₂ c₂) :=
        hammingWeight_neg (fun r₂ => D.second r₂ c₂)
      _ = columnWeight D.second c₂ := rfl
  rw [hRight]
  rfl

/-- Exact weight of a Z-check row: a row of `H₂` plus a column of
`H₁`. -/
theorem zCheckWeight_eq
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (c₁ : colOne) (r₂ : rowTwo) :
    HammingWeight (boundary2 D (Pi.single (c₁, r₂) 1)) =
      rowWeight D.second r₂ + columnWeight D.first c₁ := by
  rw [boundary2, toLin_single]
  have hWord : (fun q => boundary2Matrix D q (c₁, r₂)) =
      Sum.elim
        (fun p : colOne × colTwo =>
          if p.1 = c₁ then D.second r₂ p.2 else 0)
        (fun p : rowOne × rowTwo =>
          if p.2 = r₂ then D.first p.1 c₁ else 0) := by
    funext q
    cases q <;> rfl
  rw [hWord]
  change HammingWeight
      (Sum.elim
        (fun p : colOne × colTwo =>
          if p.1 = c₁ then D.second r₂ p.2 else 0)
        (fun p : rowOne × rowTwo =>
          if p.2 = r₂ then D.first p.1 c₁ else 0)) = _
  rw [hammingWeight_sum_elim]
  simpa [eq_comm, rowWeight, columnWeight] using
    congrArg₂ (fun a b : Nat => a + b)
      (hammingWeight_fixed_first c₁ (D.second r₂))
      (hammingWeight_fixed_second r₂ (fun r₁ => D.first r₁ c₁))

/-- The total number of X- and Z-check incidences at a physical qubit. -/
def qubitDegree
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (q : QubitIndex rowOne colOne rowTwo colTwo) : Nat :=
  HammingWeight (boundary1 D (Pi.single q 1)) +
    HammingWeight (wordLinearMapTranspose (boundary2 D) (Pi.single q 1))

/-- A qubit in `V₁ × V₂` has degree equal to the sum of the two
corresponding input column weights. -/
theorem qubitDegree_inl_eq
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (c₁ : colOne) (c₂ : colTwo) :
    qubitDegree D (Sum.inl (c₁, c₂)) =
      columnWeight D.first c₁ + columnWeight D.second c₂ := by
  rw [qubitDegree, boundary1, toLin_single, boundary2,
    wordLinearMapTranspose_toLin_single]
  change
    HammingWeight
        (fun p : rowOne × colTwo =>
          if p.2 = c₂ then D.first p.1 c₁ else 0) +
      HammingWeight
        (fun p : colOne × rowTwo =>
          if c₁ = p.1 then D.second p.2 c₂ else 0) = _
  rw [show HammingWeight
      (fun p : rowOne × colTwo =>
        if p.2 = c₂ then D.first p.1 c₁ else 0) =
      columnWeight D.first c₁ by
        simpa [eq_comm, columnWeight] using
          hammingWeight_fixed_second c₂ (fun r₁ => D.first r₁ c₁)]
  rw [show HammingWeight
      (fun p : colOne × rowTwo =>
        if c₁ = p.1 then D.second p.2 c₂ else 0) =
      columnWeight D.second c₂ by
        simpa [columnWeight] using
          hammingWeight_fixed_first c₁ (fun r₂ => D.second r₂ c₂)]

/-- A qubit in `C₁ × C₂` has degree equal to the sum of the two
corresponding input row weights. -/
theorem qubitDegree_inr_eq
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ : rowOne) (r₂ : rowTwo) :
    qubitDegree D (Sum.inr (r₁, r₂)) =
      rowWeight D.second r₂ + rowWeight D.first r₁ := by
  rw [qubitDegree, boundary1, toLin_single, boundary2,
    wordLinearMapTranspose_toLin_single]
  change
    HammingWeight
        (fun p : rowOne × colTwo =>
          if p.1 = r₁ then -D.second r₂ p.2 else 0) +
      HammingWeight
        (fun p : colOne × rowTwo =>
          if r₂ = p.2 then D.first r₁ p.1 else 0) = _
  rw [show HammingWeight
      (fun p : rowOne × colTwo =>
        if p.1 = r₁ then -D.second r₂ p.2 else 0) =
      rowWeight D.second r₂ by
        calc
          HammingWeight
              (fun p : rowOne × colTwo =>
                if p.1 = r₁ then -D.second r₂ p.2 else 0) =
              HammingWeight (fun c₂ => -D.second r₂ c₂) := by
                simpa [eq_comm] using
                  hammingWeight_fixed_first r₁
                    (fun c₂ => -D.second r₂ c₂)
          _ = HammingWeight (D.second r₂) := hammingWeight_neg (D.second r₂)
          _ = rowWeight D.second r₂ := rfl]
  rw [show HammingWeight
      (fun p : colOne × rowTwo =>
        if r₂ = p.2 then D.first r₁ p.1 else 0) =
      rowWeight D.first r₁ by
        simpa [rowWeight] using
          hammingWeight_fixed_second r₂ (D.first r₁)]

/-- Uniform input row/column bound implies the same uniform sum bound on all
output checks. -/
theorem checkWeight_le_two_mul
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) (w : Nat)
    (hRowOne : ∀ r, rowWeight D.first r ≤ w)
    (hColOne : ∀ c, columnWeight D.first c ≤ w)
    (hRowTwo : ∀ r, rowWeight D.second r ≤ w)
    (hColTwo : ∀ c, columnWeight D.second c ≤ w) :
    (∀ x₀, HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single x₀ 1)) ≤ 2 * w) ∧
      (∀ x₂, HammingWeight (boundary2 D (Pi.single x₂ 1)) ≤ 2 * w) := by
  constructor
  · rintro ⟨r₁, c₂⟩
    rw [xCheckWeight_eq]
    simpa [two_mul] using Nat.add_le_add (hRowOne r₁) (hColTwo c₂)
  · rintro ⟨c₁, r₂⟩
    rw [zCheckWeight_eq]
    simpa [two_mul] using Nat.add_le_add (hRowTwo r₂) (hColOne c₁)

/-- Uniform input row/column bound implies the same uniform sum bound on all
output qubit degrees. -/
theorem qubitDegree_le_two_mul
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) (w : Nat)
    (hRowOne : ∀ r, rowWeight D.first r ≤ w)
    (hColOne : ∀ c, columnWeight D.first c ≤ w)
    (hRowTwo : ∀ r, rowWeight D.second r ≤ w)
    (hColTwo : ∀ c, columnWeight D.second c ≤ w) :
    ∀ q, qubitDegree D q ≤ 2 * w := by
  rintro (q | q)
  · rcases q with ⟨c₁, c₂⟩
    rw [qubitDegree_inl_eq]
    simpa [two_mul] using Nat.add_le_add (hColOne c₁) (hColTwo c₂)
  · rcases q with ⟨r₁, r₂⟩
    rw [qubitDegree_inr_eq]
    simpa [two_mul, add_comm] using Nat.add_le_add (hRowTwo r₂) (hRowOne r₁)

end QEC.Coding.HypergraphProduct
