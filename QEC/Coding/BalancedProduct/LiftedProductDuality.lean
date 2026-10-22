import QEC.Coding.ChainComplex.Cohomology
import QEC.Coding.ChainComplex.Duality
import QEC.Coding.BalancedProduct.Cyclic

/-!
# Duality for binary lifted products

Transposing both group-algebra matrices reverses the lifted-product complex.
The middle coordinates differ only by exchanging the two sum blocks.  This
module proves that coordinate identification directly and records exact
Hamming-weight preservation.  It contains no distance or expansion claim.
-/

namespace QEC.Coding.BalancedProduct.LiftedProductDuality

open QEC.Coding

universe u v

/-- Exchange the two middle-coordinate blocks of a lifted-product word. -/
def swapWord {F A B : Type*} (z : Word F (Sum A B)) : Word F (Sum B A)
  | Sum.inl b => z (Sum.inr b)
  | Sum.inr a => z (Sum.inl a)

@[simp]
theorem swapWord_inl_apply {F A B : Type*}
    (z : Word F (Sum A B)) (b : B) :
    swapWord z (Sum.inl b) = z (Sum.inr b) := rfl

@[simp]
theorem swapWord_inr_apply {F A B : Type*}
    (z : Word F (Sum A B)) (a : A) :
    swapWord z (Sum.inr a) = z (Sum.inl a) := rfl

@[simp]
theorem swapWord_swapWord {F A B : Type*} (z : Word F (Sum A B)) :
    swapWord (swapWord z) = z := by
  funext q
  cases q <;> rfl

/-- Exchanging the two coordinate blocks preserves Hamming weight exactly. -/
theorem HammingWeight_swapWord
    {F A B : Type*} [Zero F] [DecidableEq F] [Fintype A] [Fintype B]
    (z : Word F (Sum A B)) :
    HammingWeight (swapWord z) = HammingWeight z := by
  classical
  let e :
      {q : Sum B A // swapWord z q ≠ 0} ≃ {q : Sum A B // z q ≠ 0} :=
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
    HammingWeight (swapWord z) =
        Fintype.card {q : Sum B A // swapWord z q ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {q : Sum A B // z q ≠ 0} := Fintype.card_congr e
    _ = HammingWeight z := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

/-- Star-transpose both group-algebra matrices.  Degree zero and degree two
exchange, while the two middle-coordinate blocks exchange order. -/
def dualData
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : LiftedProduct.Data F G aRow aCol bRow bCol) :
    LiftedProduct.Data F G aCol aRow bCol bRow where
  A := LiftedProduct.starTranspose D.A
  B := LiftedProduct.starTranspose D.B

@[simp]
theorem dualData_A
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : LiftedProduct.Data F G aRow aCol bRow bCol) :
    (dualData D).A = LiftedProduct.starTranspose D.A := rfl

@[simp]
theorem dualData_B
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : LiftedProduct.Data F G aRow aCol bRow bCol) :
    (dualData D).B = LiftedProduct.starTranspose D.B := rfl

@[simp]
theorem dualData_dualData
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : LiftedProduct.Data F G aRow aCol bRow bCol) :
    dualData (dualData D) = D := by
  cases D
  simp [dualData]

/-- Dualizing a cyclic lifted product star-transposes the Tanner matrix and
reverses the orientation of the cyclic generator. -/
theorem dualData_cyclicLiftedProductData
    {G aRow aCol : Type u} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    dualData (Cyclic.liftedProductData A x) =
      Cyclic.liftedProductData (LiftedProduct.starTranspose A) x⁻¹ := by
  unfold dualData Cyclic.liftedProductData
  rw [Cyclic.starTranspose_cyclicBoundaryMatrix]

/-- The first dual boundary is the transpose of the original second boundary,
after exchanging the middle blocks. -/
theorem boundary1_dualData_swapWord
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol bRow bCol G)) :
    LiftedProduct.boundary1 (dualData D) (swapWord z) =
      wordLinearMapTranspose (LiftedProduct.boundary2 D) z := by
  funext p
  rcases p with ⟨ac, bc, go⟩
  rw [LiftedProduct.boundary1, LiftedProduct.boundary2,
    wordLinearMapTranspose_toLin'_apply]
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_prod_type,
    LiftedProduct.boundary1Matrix_inl_apply,
    LiftedProduct.boundary1Matrix_inr_apply_zmod2,
    LiftedProduct.boundary2Matrix_inl_apply,
    LiftedProduct.boundary2Matrix_inr_apply,
    dualData_A, dualData_B, swapWord_inl_apply, swapWord_inr_apply]
  have hleft (a : MonoidAlgebra (ZMod 2) G) (g h : G) :
      LiftedProduct.leftRegularMatrix (LiftedProduct.groupConj a) g h =
        LiftedProduct.leftRegularMatrix a h g := by
    exact (congrFun (congrFun
      (LiftedProduct.leftRegularMatrix_groupConj_transpose a) g) h).symm
  have hright (a : MonoidAlgebra (ZMod 2) G) (g h : G) :
      LiftedProduct.rightRegularMatrix (LiftedProduct.groupConj a) g h =
        LiftedProduct.rightRegularMatrix a h g := by
    exact (congrFun (congrFun
      (LiftedProduct.rightRegularMatrix_groupConj_transpose a) g) h).symm
  conv_rhs => rw [add_comm]
  congr 1
  · apply Fintype.sum_congr
    intro ar
    apply Fintype.sum_congr
    intro br
    apply Fintype.sum_congr
    intro gi
    by_cases hbr : bc = br
    · subst br
      simp only [if_pos, LiftedProduct.starTranspose_apply, hright, mul_comm]
    · have hbr' : br ≠ bc := fun h => hbr h.symm
      simp only [if_neg hbr, if_neg hbr', mul_zero, zero_mul]
  · apply Fintype.sum_congr
    intro ac'
    apply Fintype.sum_congr
    intro br
    apply Fintype.sum_congr
    intro gi
    by_cases hac : ac = ac'
    · subst ac'
      simp only [if_pos, LiftedProduct.starTranspose_apply, hleft, mul_comm]
    · have hac' : ac' ≠ ac := fun h => hac h.symm
      simp only [if_neg hac, if_neg hac', mul_zero, zero_mul]

/-- The second dual boundary becomes the transpose of the original first
boundary after exchanging the middle blocks. -/
theorem swapWord_boundary2_dualData
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (w : Word (ZMod 2) (LiftedProduct.C0Index aRow bRow G)) :
    swapWord (LiftedProduct.boundary2 (dualData D) w) =
      wordLinearMapTranspose (LiftedProduct.boundary1 D) w := by
  funext q
  cases q with
  | inl p =>
      rcases p with ⟨ar, bc, go⟩
      rw [swapWord_inl_apply, LiftedProduct.boundary2,
        LiftedProduct.boundary1,
        wordLinearMapTranspose_toLin'_apply]
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, LiftedProduct.boundary2Matrix_inr_apply,
        LiftedProduct.boundary1Matrix_inl_apply, dualData_A]
      have hright (a : MonoidAlgebra (ZMod 2) G) (g h : G) :
          LiftedProduct.rightRegularMatrix (LiftedProduct.groupConj a) g h =
            LiftedProduct.rightRegularMatrix a h g := by
        exact (congrFun (congrFun
          (LiftedProduct.rightRegularMatrix_groupConj_transpose a) g) h).symm
      simp only [LiftedProduct.starTranspose_apply, hright, eq_comm, mul_comm]
  | inr p =>
      rcases p with ⟨ac, br, go⟩
      rw [swapWord_inr_apply, LiftedProduct.boundary2,
        LiftedProduct.boundary1,
        wordLinearMapTranspose_toLin'_apply]
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, LiftedProduct.boundary2Matrix_inl_apply,
        LiftedProduct.boundary1Matrix_inr_apply_zmod2, dualData_B]
      have hleft (a : MonoidAlgebra (ZMod 2) G) (g h : G) :
          LiftedProduct.leftRegularMatrix (LiftedProduct.groupConj a) g h =
            LiftedProduct.leftRegularMatrix a h g := by
        exact (congrFun (congrFun
          (LiftedProduct.leftRegularMatrix_groupConj_transpose a) g) h).symm
      simp only [LiftedProduct.starTranspose_apply, hleft, eq_comm, mul_comm]

/-- An original cocycle becomes a cycle for the dual lifted-product data. -/
theorem swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol bRow bCol G))
    (hz : z ∈ (LiftedProduct.chainComplex D).middleCocycleCode.carrier) :
    swapWord z ∈
      (LiftedProduct.chainComplex (dualData D)).middleCycleCode.carrier := by
  rw [(LiftedProduct.chainComplex (dualData D)).mem_middleCycleCode_iff]
  rw [LiftedProduct.chainComplex_boundary1, boundary1_dualData_swapWord]
  exact ((LiftedProduct.chainComplex D).mem_middleCocycleCode_iff z).1 hz

/-- If the exchanged dual word is a boundary, the original word is an
original coboundary. -/
theorem mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol bRow bCol G))
    (hz : swapWord z ∈
      (LiftedProduct.chainComplex (dualData D)).middleBoundaryCode.carrier) :
    z ∈ (LiftedProduct.chainComplex D).firstCoboundaryCheckCode.carrier := by
  rcases ((LiftedProduct.chainComplex (dualData D)).mem_middleBoundaryCode_iff
    (swapWord z)).1 hz with ⟨w, hw⟩
  have hw' : LiftedProduct.boundary2 (dualData D) w = swapWord z := by
    simpa using hw
  apply ((LiftedProduct.chainComplex D).mem_firstCoboundaryCheckCode_iff z).2
  refine ⟨w, ?_⟩
  calc
    wordLinearMapTranspose (LiftedProduct.chainComplex D).boundary1 w =
        swapWord (LiftedProduct.boundary2 (dualData D) w) := by
      rw [LiftedProduct.chainComplex_boundary1,
        swapWord_boundary2_dualData]
    _ = swapWord (swapWord z) := by rw [hw']
    _ = z := swapWord_swapWord z

end QEC.Coding.BalancedProduct.LiftedProductDuality
