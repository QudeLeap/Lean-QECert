import QEC.Coding.BalancedProduct.PKDistance
import QEC.Coding.QLDPC.Core
/-!
# Locality of cyclic balanced products

The cyclic factor contributes the genuine group-algebra boundary `1+x`, whose
regular rows and columns have weight at most two.  This file combines that
fact with basis-column bounds for an equivariant Tanner action; it stores no
locality conclusion in construction data.
-/

noncomputable section

namespace QEC.Coding.BalancedProduct.CyclicLocality

open QEC.Coding
open PKDistance

universe u v

/-- Remove the proof-irrelevant `Unit` coordinate from a lifted block. -/
private def dropUnitEquiv (I G : Type*) : I × Unit × G ≃ I × G where
  toFun p := (p.1, p.2.2)
  invFun p := (p.1, (), p.2)
  left_inv p := by rcases p with ⟨i, u, g⟩; cases u; rfl
  right_inv p := by rcases p with ⟨i, g⟩; rfl

private theorem HammingWeight_dropUnit
    {F I G : Type*} [Zero F] [DecidableEq F]
    [Fintype I] [Fintype G] (z : Word F (I × G)) :
    HammingWeight (fun p : I × Unit × G => z (p.1, p.2.2)) =
      HammingWeight z := by
  exact HammingWeight_precomp_equiv (dropUnitEquiv I G) z

private theorem HammingWeight_sum_elim
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [Fintype B] (x : Word F A) (y : Word F B) :
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
      left_inv := by rintro ⟨a | b, ha⟩ <;> rfl
      right_inv := by rintro (a | b) <;> rfl }
  calc
    HammingWeight (Sum.elim x y) =
        Fintype.card {s : Sum A B // Sum.elim x y s ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card
        (Sum {a : A // x a ≠ 0} {b : B // y b ≠ 0}) :=
      Fintype.card_congr e
    _ = HammingWeight x + HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

private theorem HammingWeight_fixed_first
    {F B I : Type*} [Zero F] [DecidableEq F]
    [Fintype B] [DecidableEq B] [Fintype I]
    (b : B) (y : Word F I) :
    HammingWeight (fun p : B × I => if b = p.1 then y p.2 else 0) =
      HammingWeight y := by
  classical
  let sourceWord : Word F (B × I) :=
    fun p => if b = p.1 then y p.2 else 0
  let e : {p : B × I // sourceWord p ≠ 0} ≃ {i : I // y i ≠ 0} :=
    { toFun := fun p =>
        ⟨p.1.2, by
          by_contra hy
          exact p.2 (by simp [sourceWord, hy])⟩
      invFun := fun i =>
        ⟨(b, i.1), by
          dsimp [sourceWord]
          simpa using i.2⟩
      left_inv := by
        rintro ⟨⟨b', i⟩, hp⟩
        apply Subtype.ext
        change (b, i) = (b', i)
        apply Prod.ext
        · dsimp [sourceWord] at hp
          by_cases hbb : b = b'
          · exact hbb
          · simp [hbb] at hp
        · rfl
      right_inv := by
        rintro ⟨i, hi⟩
        rfl }
  calc
    HammingWeight sourceWord =
        Fintype.card {p : B × I // sourceWord p ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {i : I // y i ≠ 0} := Fintype.card_congr e
    _ = HammingWeight y := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

private theorem HammingWeight_cyclicBoundaryElement
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] (x : G) :
    HammingWeight (fun g => (Cyclic.cyclicBoundaryElement x).coeff g) =
      (Cyclic.cyclicBoundaryElement x).coeff.support.card := by
  apply congrArg Finset.card
  ext g
  simp [hammingSupport]

/-- Every row of the left-regular `1+x` cyclic boundary has weight at most
two. -/
theorem HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (x go : G) :
    HammingWeight (fun gi =>
      LiftedProduct.leftRegularMatrix (Cyclic.cyclicBoundaryElement x) go gi) ≤
      2 := by
  let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft go)
  calc
    HammingWeight (fun gi =>
        LiftedProduct.leftRegularMatrix
          (Cyclic.cyclicBoundaryElement x) go gi) =
        HammingWeight (fun g => (Cyclic.cyclicBoundaryElement x).coeff g) := by
      simpa [LiftedProduct.leftRegularMatrix, e] using
        (HammingWeight_precomp_equiv e
          (fun g => (Cyclic.cyclicBoundaryElement x).coeff g))
    _ = (Cyclic.cyclicBoundaryElement x).coeff.support.card :=
      HammingWeight_cyclicBoundaryElement x
    _ ≤ 2 := Cyclic.cyclicBoundaryElement_support_card_le_two x

/-- Every column of the left-regular `1+x` cyclic boundary has weight at most
two. -/
theorem HammingWeight_leftRegular_cyclicBoundaryElement_col_le_two
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (x gi : G) :
    HammingWeight (fun go =>
      LiftedProduct.leftRegularMatrix (Cyclic.cyclicBoundaryElement x) go gi) ≤
      2 := by
  let e : G ≃ G := Equiv.mulRight gi⁻¹
  calc
    HammingWeight (fun go =>
        LiftedProduct.leftRegularMatrix
          (Cyclic.cyclicBoundaryElement x) go gi) =
        HammingWeight (fun g => (Cyclic.cyclicBoundaryElement x).coeff g) := by
      simpa [LiftedProduct.leftRegularMatrix, e] using
        (HammingWeight_precomp_equiv e
          (fun g => (Cyclic.cyclicBoundaryElement x).coeff g))
    _ = (Cyclic.cyclicBoundaryElement x).coeff.support.card :=
      HammingWeight_cyclicBoundaryElement x
    _ ≤ 2 := Cyclic.cyclicBoundaryElement_support_card_le_two x

private theorem tannerAction_single_apply
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (c : aCol) (gi : G) (r : aRow) (go : G) :
    tannerAction A (Pi.single (c, gi) 1) (r, go) =
      LiftedProduct.rightRegularMatrix (A r c) go gi := by
  rw [tannerAction_apply, Fintype.sum_eq_single c]
  · rw [Fintype.sum_eq_single gi]
    · simp
    · intro g hne
      simp [hne]
  · intro c' hne
    simp [hne]

/-- A degree-zero lifted-product check row consists of one star-transposed
Tanner basis column and one row of the cyclic `1+x` boundary. -/
theorem HammingWeight_transpose_boundary1_basis_le
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    {tannerBound : Nat}
    (hTanner : ∀ i : aRow × G,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤
          tannerBound)
    (c0 : LiftedProduct.C0Index aRow Unit G) :
    HammingWeight
        (wordLinearMapTranspose
          (LiftedProduct.boundary1 (Cyclic.liftedProductData A x))
          (canonicalBasisWord (F := ZMod 2) c0)) ≤
      tannerBound + 2 := by
  rcases c0 with ⟨r, ⟨u, go⟩⟩
  cases u
  let D := Cyclic.liftedProductData A x
  let left : Word (ZMod 2) (aCol × Unit × G) := fun p =>
    tannerAction (LiftedProduct.starTranspose A) (Pi.single (r, go) 1)
      (p.1, p.2.2)
  let right : Word (ZMod 2) (aRow × Unit × G) := fun p =>
    if r = p.1 then
      LiftedProduct.leftRegularMatrix
        (Cyclic.cyclicBoundaryElement x) go p.2.2
    else 0
  have hword :
      wordLinearMapTranspose (LiftedProduct.boundary1 D)
          (canonicalBasisWord (F := ZMod 2) (r, (), go)) =
        Sum.elim left right := by
    funext q
    rw [LiftedProduct.transpose_boundary1_canonicalBasisWord_apply]
    cases q with
    | inl p =>
        rcases p with ⟨c, ⟨u, gi⟩⟩
        cases u
        simp [left, tannerAction_apply, D,
          LiftedProduct.boundary1Matrix_inl_apply,
          LiftedProduct.starTranspose_apply,
          LiftedProduct.rightRegularMatrix, Pi.single_apply]
        rw [Fintype.sum_eq_single r]
        · rw [Fintype.sum_eq_single go]
          · simp
          · intro g hne
            simp [hne]
        · intro r' hne
          simp [hne]
    | inr p =>
        rcases p with ⟨r', ⟨u, gi⟩⟩
        cases u
        simp [right, D]
  rw [hword, HammingWeight_sum_elim]
  have hLeft : HammingWeight left =
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single (r, go) 1)) :=
    HammingWeight_dropUnit _
  have hRight : HammingWeight right = HammingWeight (fun gi =>
      LiftedProduct.leftRegularMatrix (Cyclic.cyclicBoundaryElement x) go gi) := by
    rw [show HammingWeight right = HammingWeight
        (fun p : aRow × G => if r = p.1 then
          LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) go p.2 else 0) by
      simpa [right] using (HammingWeight_dropUnit
        (z := fun p : aRow × G => if r = p.1 then
          LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) go p.2 else 0))]
    exact HammingWeight_fixed_first r _
  rw [hLeft, hRight]
  exact Nat.add_le_add (hTanner (r, go))
    (HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two x go)

/-- A degree-two lifted-product check row consists of one column of the
cyclic `1+x` boundary and one ordinary Tanner basis column. -/
theorem HammingWeight_boundary2_basis_le
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    {tannerBound : Nat}
    (hTanner : ∀ i : aCol × G,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ tannerBound)
    (c2 : LiftedProduct.C2Index aCol Unit G) :
    HammingWeight
        (LiftedProduct.boundary2 (Cyclic.liftedProductData A x)
          (canonicalBasisWord (F := ZMod 2) c2)) ≤
      tannerBound + 2 := by
  rcases c2 with ⟨c, ⟨u, gi⟩⟩
  cases u
  let D := Cyclic.liftedProductData A x
  let left : Word (ZMod 2) (aCol × Unit × G) := fun p =>
    if c = p.1 then
      LiftedProduct.leftRegularMatrix
        (Cyclic.cyclicBoundaryElement x) p.2.2 gi
    else 0
  let right : Word (ZMod 2) (aRow × Unit × G) := fun p =>
    tannerAction A (Pi.single (c, gi) 1) (p.1, p.2.2)
  have hword :
      LiftedProduct.boundary2 D
          (canonicalBasisWord (F := ZMod 2) (c, (), gi)) =
        Sum.elim left right := by
    funext q
    cases q with
    | inl p =>
        rcases p with ⟨c', ⟨u, go⟩⟩
        cases u
        rw [LiftedProduct.boundary2_canonicalBasisWord_apply]
        by_cases h : c' = c
        · simp [left, D, h]
        · simp [left, D, h, Ne.symm h]
    | inr p =>
        rcases p with ⟨r, ⟨u, go⟩⟩
        cases u
        rw [LiftedProduct.boundary2_canonicalBasisWord_apply]
        simp only [D, LiftedProduct.boundary2Matrix_inr_apply, if_pos,
          right]
        exact (tannerAction_single_apply A c gi r go).symm
  rw [hword, HammingWeight_sum_elim]
  have hLeft : HammingWeight left = HammingWeight (fun go =>
      LiftedProduct.leftRegularMatrix
        (Cyclic.cyclicBoundaryElement x) go gi) := by
    rw [show HammingWeight left = HammingWeight
        (fun p : aCol × G => if c = p.1 then
          LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) p.2 gi else 0) by
      simpa [left] using (HammingWeight_dropUnit
        (z := fun p : aCol × G => if c = p.1 then
          LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) p.2 gi else 0))]
    exact HammingWeight_fixed_first c
      (fun go : G => LiftedProduct.leftRegularMatrix
        (Cyclic.cyclicBoundaryElement x) go gi)
  have hRight : HammingWeight right =
      HammingWeight (tannerAction A (Pi.single (c, gi) 1)) :=
    HammingWeight_dropUnit _
  rw [hLeft, hRight]
  calc
    HammingWeight (fun go => LiftedProduct.leftRegularMatrix
        (Cyclic.cyclicBoundaryElement x) go gi) +
        HammingWeight (tannerAction A (Pi.single (c, gi) 1)) ≤
      2 + tannerBound := Nat.add_le_add
        (HammingWeight_leftRegular_cyclicBoundaryElement_col_le_two x gi)
        (hTanner (c, gi))
    _ = tannerBound + 2 := Nat.add_comm _ _

/-- For either type of lifted-product qubit, its two boundary columns have
combined weight at most the larger Tanner bound plus the cyclic contribution
two. -/
theorem HammingWeight_boundary_columns_basis_le
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    {forwardBound transposeBound : Nat}
    (hForward : ∀ i : aCol × G,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ forwardBound)
    (hTranspose : ∀ i : aRow × G,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤
          transposeBound)
    (q : LiftedProduct.QubitIndex aRow aCol Unit Unit G) :
    HammingWeight
        (LiftedProduct.boundary1 (Cyclic.liftedProductData A x)
          (canonicalBasisWord (F := ZMod 2) q)) +
      HammingWeight
        (wordLinearMapTranspose
          (LiftedProduct.boundary2 (Cyclic.liftedProductData A x))
          (canonicalBasisWord (F := ZMod 2) q)) ≤
      max forwardBound transposeBound + 2 := by
  let D := Cyclic.liftedProductData A x
  cases q with
  | inl p =>
      rcases p with ⟨c, ⟨u, gi⟩⟩
      cases u
      have hBoundary1 :
          HammingWeight
              (LiftedProduct.boundary1 D
                (canonicalBasisWord (F := ZMod 2) (Sum.inl (c, (), gi)))) =
            HammingWeight (tannerAction A (Pi.single (c, gi) 1)) := by
        rw [show LiftedProduct.boundary1 D
            (canonicalBasisWord (F := ZMod 2) (Sum.inl (c, (), gi))) =
            fun p : aRow × Unit × G =>
              tannerAction A (Pi.single (c, gi) 1) (p.1, p.2.2) by
          funext p
          rcases p with ⟨r, ⟨u, go⟩⟩
          cases u
          rw [LiftedProduct.boundary1_canonicalBasisWord_apply]
          rw [tannerAction_single_apply]
          rfl]
        exact HammingWeight_dropUnit _
      have hBoundary2 :
          HammingWeight
              (wordLinearMapTranspose (LiftedProduct.boundary2 D)
                (canonicalBasisWord (F := ZMod 2) (Sum.inl (c, (), gi)))) =
            HammingWeight (fun go =>
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) gi go) := by
        rw [show HammingWeight
            (wordLinearMapTranspose (LiftedProduct.boundary2 D)
              (canonicalBasisWord (F := ZMod 2) (Sum.inl (c, (), gi)))) =
            HammingWeight (fun p : aCol × Unit × G =>
              if c = p.1 then
                LiftedProduct.leftRegularMatrix
                  (Cyclic.cyclicBoundaryElement x) gi p.2.2 else 0) by
          apply congrArg HammingWeight
          funext p
          rcases p with ⟨c', ⟨u, go⟩⟩
          cases u
          rw [LiftedProduct.transpose_boundary2_canonicalBasisWord_apply]
          simp [D, LiftedProduct.boundary2Matrix_inl_apply]]
        rw [show HammingWeight
            (fun p : aCol × Unit × G => if c = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) gi p.2.2 else 0) =
            HammingWeight (fun p : aCol × G => if c = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) gi p.2 else 0) by
          simpa using (HammingWeight_dropUnit
            (z := fun p : aCol × G => if c = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) gi p.2 else 0))]
        exact HammingWeight_fixed_first c
          (fun go : G => LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) gi go)
      rw [hBoundary1, hBoundary2]
      exact Nat.add_le_add
        ((hForward (c, gi)).trans (Nat.le_max_left _ _))
        (HammingWeight_leftRegular_cyclicBoundaryElement_row_le_two x gi)
  | inr p =>
      rcases p with ⟨r, ⟨u, gi⟩⟩
      cases u
      have hBoundary1 :
          HammingWeight
              (LiftedProduct.boundary1 D
                (canonicalBasisWord (F := ZMod 2) (Sum.inr (r, (), gi)))) =
            HammingWeight (fun go =>
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) go gi) := by
        rw [show HammingWeight
            (LiftedProduct.boundary1 D
              (canonicalBasisWord (F := ZMod 2) (Sum.inr (r, (), gi)))) =
            HammingWeight (fun p : aRow × Unit × G =>
              if r = p.1 then
                LiftedProduct.leftRegularMatrix
                  (Cyclic.cyclicBoundaryElement x) p.2.2 gi else 0) by
          apply congrArg HammingWeight
          funext p
          rcases p with ⟨r', ⟨u, go⟩⟩
          cases u
          rw [LiftedProduct.boundary1_canonicalBasisWord_apply]
          by_cases h : r' = r
          · simp [D, h]
          · simp [D, h, Ne.symm h]]
        rw [show HammingWeight
            (fun p : aRow × Unit × G => if r = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) p.2.2 gi else 0) =
            HammingWeight (fun p : aRow × G => if r = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) p.2 gi else 0) by
          simpa using (HammingWeight_dropUnit
            (z := fun p : aRow × G => if r = p.1 then
              LiftedProduct.leftRegularMatrix
                (Cyclic.cyclicBoundaryElement x) p.2 gi else 0))]
        exact HammingWeight_fixed_first r
          (fun go : G => LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) go gi)
      have hBoundary2 :
          HammingWeight
              (wordLinearMapTranspose (LiftedProduct.boundary2 D)
                (canonicalBasisWord (F := ZMod 2) (Sum.inr (r, (), gi)))) =
            HammingWeight
              (tannerAction (LiftedProduct.starTranspose A)
                (Pi.single (r, gi) 1)) := by
        rw [show wordLinearMapTranspose (LiftedProduct.boundary2 D)
            (canonicalBasisWord (F := ZMod 2) (Sum.inr (r, (), gi))) =
            fun p : aCol × Unit × G =>
              tannerAction (LiftedProduct.starTranspose A)
                (Pi.single (r, gi) 1) (p.1, p.2.2) by
          funext p
          rcases p with ⟨c, ⟨u, go⟩⟩
          cases u
          rw [LiftedProduct.transpose_boundary2_canonicalBasisWord_apply]
          rw [tannerAction_single_apply]
          simp [D, Cyclic.liftedProductData,
            LiftedProduct.boundary2Matrix_inr_apply,
            LiftedProduct.starTranspose_apply,
            LiftedProduct.rightRegularMatrix]]
        exact HammingWeight_dropUnit _
      rw [hBoundary1, hBoundary2]
      calc
        HammingWeight (fun go => LiftedProduct.leftRegularMatrix
            (Cyclic.cyclicBoundaryElement x) go gi) +
            HammingWeight
              (tannerAction (LiftedProduct.starTranspose A)
                (Pi.single (r, gi) 1)) ≤
          2 + max forwardBound transposeBound := Nat.add_le_add
            (HammingWeight_leftRegular_cyclicBoundaryElement_col_le_two x gi)
            ((hTranspose (r, gi)).trans (Nat.le_max_right _ _))
        _ = max forwardBound transposeBound + 2 := Nat.add_comm _ _

/-- Tanner column bounds and the actual cyclic `1+x` matrix yield uniform
bounded locality for the cyclic balanced product. -/
theorem boundaryIncidence_boundedLocality_of_tannerAction_bounds
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    {forwardBound transposeBound : Nat}
    (hForward : ∀ i : aCol × G,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ forwardBound)
    (hTranspose : ∀ i : aRow × G,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤
          transposeBound) :
    BoundedLocality
      (LiftedProduct.boundaryIncidence
        (Cyclic.liftedProductData A x)).localityProfile
      (max forwardBound transposeBound + 2) := by
  let D := Cyclic.liftedProductData A x
  apply LiftedProduct.boundaryIncidence_boundedLocality_of_bounds D
  · intro c0
    have hBasis : (Pi.single c0 (1 : ZMod 2)) =
        canonicalBasisWord (F := ZMod 2) c0 := by
      funext c0'
      by_cases h : c0' = c0
      · subst c0'
        simp [canonicalBasisWord]
      · simp [canonicalBasisWord, h]
    have hCard :
        (LiftedProduct.boundary1RowSupport D c0).card =
        HammingWeight
          (wordLinearMapTranspose (LiftedProduct.boundary1 D)
            (canonicalBasisWord (F := ZMod 2) c0)) := by
      unfold LiftedProduct.boundary1RowSupport HammingWeight
      apply congrArg Finset.card
      rw [hBasis]
      ext q
      simp [hammingSupport]
    calc
      (LiftedProduct.boundary1RowSupport D c0).card =
          HammingWeight
            (wordLinearMapTranspose (LiftedProduct.boundary1 D)
              (canonicalBasisWord (F := ZMod 2) c0)) := hCard
      _ ≤ max forwardBound transposeBound + 2 := by
        simpa only [D] using
          ((HammingWeight_transpose_boundary1_basis_le
            (tannerBound := transposeBound) A x hTranspose c0).trans
              (Nat.add_le_add_right
                (Nat.le_max_right forwardBound transposeBound) 2))
  · intro c2
    have hBasis : (Pi.single c2 (1 : ZMod 2)) =
        canonicalBasisWord (F := ZMod 2) c2 := by
      funext c2'
      by_cases h : c2' = c2
      · subst c2'
        simp [canonicalBasisWord]
      · simp [canonicalBasisWord, h]
    have hCard :
        (LiftedProduct.boundary2RowSupport D c2).card =
        HammingWeight
          (LiftedProduct.boundary2 D
            (canonicalBasisWord (F := ZMod 2) c2)) := by
      unfold LiftedProduct.boundary2RowSupport HammingWeight
      apply congrArg Finset.card
      rw [hBasis]
      ext q
      simp [hammingSupport]
    calc
      (LiftedProduct.boundary2RowSupport D c2).card =
          HammingWeight
            (LiftedProduct.boundary2 D
              (canonicalBasisWord (F := ZMod 2) c2)) := hCard
      _ ≤ max forwardBound transposeBound + 2 := by
        simpa only [D] using
          ((HammingWeight_boundary2_basis_le
            (tannerBound := forwardBound) A x hForward c2).trans
              (Nat.add_le_add_right
                (Nat.le_max_left forwardBound transposeBound) 2))
  · intro q
    change ((QEC.QLDPC.chainComplexBoundaryIncidence
      (LiftedProduct.chainComplex D)).variableSupport q).card ≤ _
    rw [QEC.QLDPC.chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns]
    simpa only [D, LiftedProduct.chainComplex_boundary1,
      LiftedProduct.chainComplex_boundary2] using
      HammingWeight_boundary_columns_basis_le A x hForward hTranspose q

end QEC.Coding.BalancedProduct.CyclicLocality
