import QEC.Coding.ExpanderCodes.LiftedProduct
import QEC.Coding.ChainComplex.Duality

/-!
# Signed duality for lifted products over arbitrary fields

Over a field of characteristic different from two, exchanging the two middle
blocks of a lifted product must retain the minus sign in the first boundary.
This module records the signed coordinate exchange and identifies the dual
lifted-product complex without specializing the coefficient field.
-/

namespace QEC.Coding.LiftedProduct

universe u v

/-- Exchange the two middle-coordinate blocks, with the sign required by the
lifted-product boundary convention. -/
def signedSwapWord {F A B : Type*} [Neg F]
    (z : Word F (Sum A B)) : Word F (Sum B A)
  | Sum.inl b => z (Sum.inr b)
  | Sum.inr a => -z (Sum.inl a)

@[simp]
theorem signedSwapWord_inl_apply {F A B : Type*} [Neg F]
    (z : Word F (Sum A B)) (b : B) :
    signedSwapWord z (Sum.inl b) = z (Sum.inr b) := rfl

@[simp]
theorem signedSwapWord_inr_apply {F A B : Type*} [Neg F]
    (z : Word F (Sum A B)) (a : A) :
    signedSwapWord z (Sum.inr a) = -z (Sum.inl a) := rfl

@[simp]
theorem signedSwapWord_signedSwapWord {F A B : Type*} [AddGroup F]
    (z : Word F (Sum A B)) :
    signedSwapWord (signedSwapWord z) = -z := by
  funext q
  cases q <;> simp [signedSwapWord]

@[simp]
theorem signedSwapWord_neg {F A B : Type*} [AddGroup F]
    (z : Word F (Sum A B)) :
    signedSwapWord (-z) = -signedSwapWord z := by
  funext q
  cases q <;> simp [signedSwapWord]

/-- The inverse signed exchange. -/
def signedUnswapWord {F A B : Type*} [Neg F]
    (z : Word F (Sum B A)) : Word F (Sum A B) :=
  -signedSwapWord z

@[simp]
theorem signedUnswapWord_signedSwapWord {F A B : Type*} [AddGroup F]
    (z : Word F (Sum A B)) :
    signedUnswapWord (signedSwapWord z) = z := by
  simp [signedUnswapWord]

@[simp]
theorem signedSwapWord_signedUnswapWord {F A B : Type*} [AddGroup F]
    (z : Word F (Sum B A)) :
    signedSwapWord (signedUnswapWord z) = z := by
  simp [signedUnswapWord]

/-- Signed block exchange preserves Hamming weight. -/
theorem HammingWeight_signedSwapWord
    {F A B : Type*} [AddGroup F] [DecidableEq F]
    [Fintype A] [Fintype B] (z : Word F (Sum A B)) :
    HammingWeight (signedSwapWord z) = HammingWeight z := by
  classical
  let e :
      {q : Sum B A // signedSwapWord z q ≠ 0} ≃
        {q : Sum A B // z q ≠ 0} :=
    { toFun := fun q =>
        match q with
        | ⟨Sum.inl b, hb⟩ => ⟨Sum.inr b, hb⟩
        | ⟨Sum.inr a, ha⟩ => ⟨Sum.inl a, by simpa using ha⟩
      invFun := fun q =>
        match q with
        | ⟨Sum.inl a, ha⟩ => ⟨Sum.inr a, by simpa using ha⟩
        | ⟨Sum.inr b, hb⟩ => ⟨Sum.inl b, hb⟩
      left_inv := by rintro ⟨q, hq⟩; cases q <;> rfl
      right_inv := by rintro ⟨q, hq⟩; cases q <;> rfl }
  calc
    HammingWeight (signedSwapWord z) =
        Fintype.card {q : Sum B A // signedSwapWord z q ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ = Fintype.card {q : Sum A B // z q ≠ 0} := Fintype.card_congr e
    _ = HammingWeight z := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]

/-- Star-transpose both group-algebra matrices. Degree zero and degree two
exchange, while the two middle-coordinate blocks exchange order. -/
def dualData
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : Data F G aRow aCol bRow bCol) :
    Data F G aCol aRow bCol bRow where
  A := starTranspose D.A
  B := starTranspose D.B

@[simp]
theorem dualData_A
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : Data F G aRow aCol bRow bCol) :
    (dualData D).A = starTranspose D.A := rfl

@[simp]
theorem dualData_B
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : Data F G aRow aCol bRow bCol) :
    (dualData D).B = starTranspose D.B := rfl

@[simp]
theorem dualData_dualData
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : Data F G aRow aCol bRow bCol) :
    dualData (dualData D) = D := by
  cases D
  simp [dualData]

/-- The first boundary of the dual data is the transpose of the original
second boundary after signed middle-coordinate exchange. -/
theorem boundary1_dualData_signedSwapWord
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (z : Word F (QubitIndex aRow aCol bRow bCol G)) :
    boundary1 (dualData D) (signedSwapWord z) =
      wordLinearMapTranspose (boundary2 D) z := by
  funext p
  rcases p with ⟨ac, bc, go⟩
  rw [boundary1, boundary2, wordLinearMapTranspose_toLin'_apply]
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_prod_type,
    boundary1Matrix_inl_apply, boundary1Matrix_inr_apply,
    boundary2Matrix_inl_apply, boundary2Matrix_inr_apply,
    dualData_A, dualData_B, signedSwapWord_inl_apply,
    signedSwapWord_inr_apply]
  have hleft (a : MonoidAlgebra F G) (g h : G) :
      leftRegularMatrix (groupConj a) g h =
        leftRegularMatrix a h g := by
    exact (congrFun (congrFun
      (leftRegularMatrix_groupConj_transpose a) g) h).symm
  have hright (a : MonoidAlgebra F G) (g h : G) :
      rightRegularMatrix (groupConj a) g h =
        rightRegularMatrix a h g := by
    exact (congrFun (congrFun
      (rightRegularMatrix_groupConj_transpose a) g) h).symm
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
      simp only [if_pos, starTranspose_apply, hright, mul_comm]
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
      simp only [if_pos, starTranspose_apply, hleft]
      ring
    · have hac' : ac' ≠ ac := fun h => hac h.symm
      simp only [if_neg hac, if_neg hac', mul_zero, zero_mul]

/-- The second boundary of the dual data becomes the transpose of the
original first boundary after the same signed coordinate exchange. -/
theorem signedSwapWord_boundary2_dualData
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (w : Word F (C0Index aRow bRow G)) :
    signedSwapWord (boundary2 (dualData D) w) =
      wordLinearMapTranspose (boundary1 D) w := by
  funext q
  cases q with
  | inl p =>
      rcases p with ⟨ac, br, go⟩
      rw [signedSwapWord_inl_apply, boundary2, boundary1,
        wordLinearMapTranspose_toLin'_apply]
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, boundary2Matrix_inr_apply,
        boundary1Matrix_inl_apply, dualData_A]
      have hright (a : MonoidAlgebra F G) (g h : G) :
          rightRegularMatrix (groupConj a) g h =
            rightRegularMatrix a h g := by
        exact (congrFun (congrFun
          (rightRegularMatrix_groupConj_transpose a) g) h).symm
      simp only [starTranspose_apply, hright, eq_comm, mul_comm]
  | inr p =>
      rcases p with ⟨ar, bc, go⟩
      rw [signedSwapWord_inr_apply, boundary2, boundary1,
        wordLinearMapTranspose_toLin'_apply]
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, boundary2Matrix_inl_apply,
        boundary1Matrix_inr_apply, dualData_B]
      have hleft (a : MonoidAlgebra F G) (g h : G) :
          leftRegularMatrix (groupConj a) g h =
            leftRegularMatrix a h g := by
        exact (congrFun (congrFun
          (leftRegularMatrix_groupConj_transpose a) g) h).symm
      simp only [starTranspose_apply, hleft, eq_comm]
      simp_rw [mul_comm]
      simp

/-- An original cocycle becomes a cycle for the signed dual lifted product. -/
theorem signedSwapWord_mem_middleCycleCode_of_mem_middleCocycleCode
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (z : Word F (QubitIndex aRow aCol bRow bCol G))
    (hz : z ∈ (chainComplex D).middleCocycleCode.carrier) :
    signedSwapWord z ∈
      (chainComplex (dualData D)).middleCycleCode.carrier := by
  rw [(chainComplex (dualData D)).mem_middleCycleCode_iff]
  rw [chainComplex_boundary1, boundary1_dualData_signedSwapWord]
  exact ((chainComplex D).mem_middleCocycleCode_iff z).1 hz

/-- If the signed dual word is a boundary, the original word is an original
coboundary. -/
theorem mem_firstCoboundaryCheckCode_of_signedSwapWord_mem_middleBoundaryCode
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (z : Word F (QubitIndex aRow aCol bRow bCol G))
    (hz : signedSwapWord z ∈
      (chainComplex (dualData D)).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by
  rcases ((chainComplex (dualData D)).mem_middleBoundaryCode_iff
    (signedSwapWord z)).1 hz with ⟨w, hw⟩
  have hw' : boundary2 (dualData D) w = signedSwapWord z := by
    simpa using hw
  apply ((chainComplex D).mem_firstCoboundaryCheckCode_iff z).2
  refine ⟨-w, ?_⟩
  calc
    wordLinearMapTranspose (chainComplex D).boundary1 (-w) =
        -wordLinearMapTranspose (boundary1 D) w := by
      rw [chainComplex_boundary1]
      exact map_neg _ _
    _ = -signedSwapWord (boundary2 (dualData D) w) := by
      rw [signedSwapWord_boundary2_dualData]
    _ = -signedSwapWord (signedSwapWord z) := by rw [hw']
    _ = z := by simp

end QEC.Coding.LiftedProduct
