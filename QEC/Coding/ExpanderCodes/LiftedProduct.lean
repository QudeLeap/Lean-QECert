import QEC.Coding.QLDPC.SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Lifted-product source data

This module records the matrix-valued source data and coordinate types used by
the lifted-product construction. The interface is traced to these audited local
source anchors:

* `panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`
* `panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`
* `leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`

These citations provide provenance for the interface; no results from the
papers are asserted here.
-/

namespace QEC.Coding.LiftedProduct

universe u v

/-- The two group-algebra-valued matrices defining a lifted product. -/
structure Data (F G aRow aCol bRow bCol : Type*) [Semiring F] where
  A : Matrix aRow aCol (MonoidAlgebra F G)
  B : Matrix bRow bCol (MonoidAlgebra F G)

/-- Coordinates of degree-zero chains. -/
abbrev C0Index (aRow bRow G : Type*) := aRow × bRow × G

/-- Coordinates of the two qubit blocks. -/
abbrev QubitIndex (aRow aCol bRow bCol G : Type*) :=
  Sum (aCol × bRow × G) (aRow × bCol × G)

/-- The exact number of qubit coordinates in the two lifted-product blocks. -/
theorem card_qubitIndex
    {aRow aCol bRow bCol G : Type*}
    [Fintype aRow] [Fintype aCol] [Fintype bRow] [Fintype bCol] [Fintype G] :
    Fintype.card (QubitIndex aRow aCol bRow bCol G) =
      Fintype.card G *
        (Fintype.card aCol * Fintype.card bRow +
         Fintype.card aRow * Fintype.card bCol) := by
  simp only [QubitIndex, Fintype.card_sum, Fintype.card_prod]
  calc
    _ = (Fintype.card aCol * Fintype.card bRow) * Fintype.card G +
        (Fintype.card aRow * Fintype.card bCol) * Fintype.card G := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    _ = _ := by
      simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]

/-- Coordinates of degree-two chains. -/
abbrev C2Index (aCol bCol G : Type*) := aCol × bCol × G

/-! ## Canonical regular actions -/

/-- Invert the group coordinate of a group-algebra element. -/
def groupConj {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) : MonoidAlgebra F G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivCongrLeft (Equiv.inv G) a.coeff)

/-- The canonical left regular matrix of a group-algebra element. -/
def leftRegularMatrix {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) : Matrix G G F :=
  fun i j => a.coeff (i * j⁻¹)

/-- The canonical right regular matrix of a group-algebra element. -/
def rightRegularMatrix {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) : Matrix G G F :=
  fun i j => a.coeff (j⁻¹ * i)

@[simp]
theorem groupConj_apply {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) (g : G) :
    (groupConj a).coeff g = a.coeff g⁻¹ := by
  rfl

@[simp]
theorem groupConj_zero {F G : Type*} [Semiring F] [Group G] :
    groupConj (0 : MonoidAlgebra F G) = 0 := by
  ext g
  change (0 : MonoidAlgebra F G).coeff g⁻¹ = 0
  rfl

@[simp]
theorem groupConj_add {F G : Type*} [Semiring F] [Group G]
    (a b : MonoidAlgebra F G) :
    groupConj (a + b) = groupConj a + groupConj b := by
  ext g
  simp

@[simp]
theorem groupConj_smul {F G : Type*} [Semiring F] [Group G]
    (c : F) (a : MonoidAlgebra F G) :
    groupConj (c • a) = c • groupConj a := by
  ext g
  simp

@[simp]
theorem groupConj_groupConj {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) :
    groupConj (groupConj a) = a := by
  ext g
  simp

private theorem mul_apply_left_fintype {F G : Type*}
    [CommSemiring F] [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra F G) (g : G) :
    (a * b).coeff g = ∑ x : G, a.coeff x * b.coeff (x⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro x
  simp

/-- Inverting group coordinates reverses convolution order. -/
theorem groupConj_mul {F G : Type*}
    [CommSemiring F] [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra F G) :
    groupConj (a * b) = groupConj b * groupConj a := by
  ext g
  rw [groupConj_apply, mul_apply_left_fintype, mul_apply_left_fintype]
  rw [← Equiv.sum_comp (Equiv.mulLeft g)
    (fun y : G ↦ (groupConj b).coeff y * (groupConj a).coeff (y⁻¹ * g))]
  apply Fintype.sum_congr
  intro x
  simp only [groupConj_apply]
  simp [mul_comm, mul_assoc]

@[simp]
theorem leftRegularMatrix_zero {F G : Type*} [Semiring F] [Group G] :
    leftRegularMatrix (0 : MonoidAlgebra F G) = 0 := by
  ext i j
  rfl

@[simp]
theorem leftRegularMatrix_add {F G : Type*} [Semiring F] [Group G]
    (a b : MonoidAlgebra F G) :
    leftRegularMatrix (a + b) = leftRegularMatrix a + leftRegularMatrix b := by
  ext i j
  rfl

@[simp]
theorem leftRegularMatrix_smul {F G : Type*} [Semiring F] [Group G]
    (c : F) (a : MonoidAlgebra F G) :
    leftRegularMatrix (c • a) = c • leftRegularMatrix a := by
  ext i j
  rfl

@[simp]
theorem rightRegularMatrix_zero {F G : Type*} [Semiring F] [Group G] :
    rightRegularMatrix (0 : MonoidAlgebra F G) = 0 := by
  ext i j
  rfl

@[simp]
theorem rightRegularMatrix_add {F G : Type*} [Semiring F] [Group G]
    (a b : MonoidAlgebra F G) :
    rightRegularMatrix (a + b) = rightRegularMatrix a + rightRegularMatrix b := by
  ext i j
  rfl

@[simp]
theorem rightRegularMatrix_smul {F G : Type*} [Semiring F] [Group G]
    (c : F) (a : MonoidAlgebra F G) :
    rightRegularMatrix (c • a) = c • rightRegularMatrix a := by
  ext i j
  rfl

/-- The left regular matrix preserves convolution. -/
theorem leftRegularMatrix_mul {F G : Type*}
    [CommSemiring F] [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra F G) :
    leftRegularMatrix (a * b) = leftRegularMatrix a * leftRegularMatrix b := by
  ext i j
  rw [show leftRegularMatrix (a * b) i j = (a * b).coeff (i * j⁻¹) by rfl,
    mul_apply_left_fintype]
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft i))
    (fun x : G ↦ a.coeff x * b.coeff (x⁻¹ * (i * j⁻¹)))]
  apply Fintype.sum_congr
  intro k
  simp [leftRegularMatrix]

/-- The right regular matrix reverses convolution order. -/
theorem rightRegularMatrix_mul {F G : Type*}
    [CommSemiring F] [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra F G) :
    rightRegularMatrix (a * b) = rightRegularMatrix b * rightRegularMatrix a := by
  ext i j
  rw [show rightRegularMatrix (a * b) i j = (a * b).coeff (j⁻¹ * i) by rfl,
    mul_apply_left_fintype]
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp (Equiv.mulLeft j⁻¹)
    (fun x : G ↦ a.coeff x * b.coeff (x⁻¹ * (j⁻¹ * i)))]
  apply Fintype.sum_congr
  intro k
  simp [rightRegularMatrix, mul_comm, mul_assoc]

/-- The canonical left and right regular actions commute. -/
theorem leftRegularMatrix_mul_rightRegularMatrix {F G : Type*}
    [CommSemiring F] [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra F G) :
    leftRegularMatrix a * rightRegularMatrix b =
      rightRegularMatrix b * leftRegularMatrix a := by
  ext i j
  simp only [Matrix.mul_apply, leftRegularMatrix, rightRegularMatrix]
  calc
    (∑ k : G, a.coeff (i * k⁻¹) * b.coeff (j⁻¹ * k)) =
        ∑ x : G, a.coeff x * b.coeff (j⁻¹ * (x⁻¹ * i)) := by
      rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft i))
        (fun x : G ↦ a.coeff x * b.coeff (j⁻¹ * (x⁻¹ * i)))]
      apply Fintype.sum_congr
      intro k
      simp [mul_assoc]
    _ = ∑ k : G, b.coeff (k⁻¹ * i) * a.coeff (k * j⁻¹) := by
      rw [← Equiv.sum_comp (Equiv.mulRight j⁻¹)
        (fun x : G ↦ a.coeff x * b.coeff (j⁻¹ * (x⁻¹ * i)))]
      apply Fintype.sum_congr
      intro k
      simp [mul_comm, mul_assoc]

@[simp]
theorem leftRegularMatrix_groupConj_transpose {F G : Type*}
    [Semiring F] [Group G] (a : MonoidAlgebra F G) :
    (leftRegularMatrix a).transpose = leftRegularMatrix (groupConj a) := by
  ext i j
  simp [leftRegularMatrix]

@[simp]
theorem rightRegularMatrix_groupConj_transpose {F G : Type*}
    [Semiring F] [Group G] (a : MonoidAlgebra F G) :
    (rightRegularMatrix a).transpose = rightRegularMatrix (groupConj a) := by
  ext i j
  simp [rightRegularMatrix]

/-! ## Group-algebra matrix dual -/

/--
Transpose the outer matrix indices and invert each group-algebra coordinate.

The interface has provenance in the audited local anchors
`panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`,
`panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`, and
`leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`.
These citations record provenance only; no theorem from those papers is claimed
to be formalized by this definition.
-/
def starTranspose {F G m n : Type*} [Semiring F] [Group G]
    (M : Matrix m n (MonoidAlgebra F G)) :
    Matrix n m (MonoidAlgebra F G) :=
  fun j i => groupConj (M i j)

@[simp]
theorem starTranspose_apply {F G m n : Type*} [Semiring F] [Group G]
    (M : Matrix m n (MonoidAlgebra F G)) (j : n) (i : m) :
    (starTranspose M) j i = groupConj (M i j) := by
  rfl

@[simp]
theorem starTranspose_zero {F G m n : Type*} [Semiring F] [Group G] :
    starTranspose (0 : Matrix m n (MonoidAlgebra F G)) = 0 := by
  ext j i
  simp [starTranspose]

@[simp]
theorem starTranspose_add {F G m n : Type*} [Semiring F] [Group G]
    (M N : Matrix m n (MonoidAlgebra F G)) :
    starTranspose (M + N) = starTranspose M + starTranspose N := by
  ext j i
  simp [starTranspose]

@[simp]
theorem starTranspose_smul {F G m n : Type*} [Semiring F] [Group G]
    (c : F) (M : Matrix m n (MonoidAlgebra F G)) :
    starTranspose (c • M) = c • starTranspose M := by
  ext j i
  simp [starTranspose]

@[simp]
theorem starTranspose_starTranspose {F G m n : Type*}
    [Semiring F] [Group G] (M : Matrix m n (MonoidAlgebra F G)) :
    starTranspose (starTranspose M) = M := by
  ext i j
  simp [starTranspose]

/-- Entrywise bridge from the matrix dual to transposed left regular blocks. -/
theorem leftRegularMatrix_starTranspose_entry {F G m n : Type*}
    [Semiring F] [Group G] (M : Matrix m n (MonoidAlgebra F G))
    (i : m) (j : n) :
    leftRegularMatrix ((starTranspose M) j i) =
      (leftRegularMatrix (M i j)).transpose := by
  simp [starTranspose]

/-- Entrywise bridge from the matrix dual to transposed right regular blocks. -/
theorem rightRegularMatrix_starTranspose_entry {F G m n : Type*}
    [Semiring F] [Group G] (M : Matrix m n (MonoidAlgebra F G))
    (i : m) (j : n) :
    rightRegularMatrix ((starTranspose M) j i) =
      (rightRegularMatrix (M i j)).transpose := by
  simp [starTranspose]

/-! ## Boundary matrices -/

/--
The first lifted-product boundary matrix, with the `A` right-regular block
followed by the negative `B` left-regular block.

The interface has provenance in the audited local anchors
`panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`,
`panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`, and
`leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`.
These citations record provenance only; no theorem from those papers is claimed
to be formalized by this definition.
-/
def boundary1Matrix {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Matrix (C0Index aRow bRow G)
      (QubitIndex aRow aCol bRow bCol G) F :=
  fun (ar, br, go) q =>
    match q with
    | Sum.inl (ac, br', gi) =>
        if br = br' then rightRegularMatrix (D.A ar ac) go gi else 0
    | Sum.inr (ar', bc, gi) =>
        if ar = ar' then - leftRegularMatrix (D.B br bc) go gi else 0

/--
The second lifted-product boundary matrix, with the `B` left-regular block
followed by the `A` right-regular block.

The interface has provenance in the audited local anchors
`panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`,
`panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`, and
`leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`.
These citations record provenance only; no theorem from those papers is claimed
to be formalized by this definition.
-/
def boundary2Matrix {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Matrix (QubitIndex aRow aCol bRow bCol G)
      (C2Index aCol bCol G) F :=
  fun q (ac', bc', gi) =>
    match q with
    | Sum.inl (ac, br, go) =>
        if ac = ac' then leftRegularMatrix (D.B br bc') go gi else 0
    | Sum.inr (ar, bc, go) =>
        if bc = bc' then rightRegularMatrix (D.A ar ac') go gi else 0

@[simp]
theorem boundary1Matrix_inl_apply {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar : aRow) (br br' : bRow) (ac : aCol) (go gi : G) :
    boundary1Matrix D (ar, br, go) (Sum.inl (ac, br', gi)) =
      if br = br' then rightRegularMatrix (D.A ar ac) go gi else 0 := by
  rfl

@[simp]
theorem boundary1Matrix_inr_apply {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar ar' : aRow) (br : bRow) (bc : bCol) (go gi : G) :
    boundary1Matrix D (ar, br, go) (Sum.inr (ar', bc, gi)) =
      if ar = ar' then - leftRegularMatrix (D.B br bc) go gi else 0 := by
  rfl

@[simp]
theorem boundary2Matrix_inl_apply {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ac ac' : aCol) (br : bRow) (bc : bCol) (go gi : G) :
    boundary2Matrix D (Sum.inl (ac, br, go)) (ac', bc, gi) =
      if ac = ac' then leftRegularMatrix (D.B br bc) go gi else 0 := by
  rfl

@[simp]
theorem boundary2Matrix_inr_apply {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar : aRow) (ac : aCol) (bc bc' : bCol) (go gi : G) :
    boundary2Matrix D (Sum.inr (ar, bc, go)) (ac, bc', gi) =
      if bc = bc' then rightRegularMatrix (D.A ar ac) go gi else 0 := by
  rfl

@[simp]
theorem neg_leftRegularMatrix_apply_zmod2 {G : Type*} [Group G]
    (a : MonoidAlgebra (ZMod 2) G) (go gi : G) :
    - leftRegularMatrix a go gi = leftRegularMatrix a go gi := by
  exact ZMod.neg_eq_self_mod_two _

@[simp]
theorem boundary1Matrix_inr_apply_zmod2
    {G aRow aCol bRow bCol : Type*}
    [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol)
    (ar ar' : aRow) (br : bRow) (bc : bCol) (go gi : G) :
    boundary1Matrix D (ar, br, go) (Sum.inr (ar', bc, gi)) =
      if ar = ar' then leftRegularMatrix (D.B br bc) go gi else 0 := by
  simp only [boundary1Matrix_inr_apply, neg_leftRegularMatrix_apply_zmod2]

/-! ## Chain complex -/

/-- The first lifted-product boundary as a linear map on finite-coordinate words. -/
noncomputable def boundary1 {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Word F (QubitIndex aRow aCol bRow bCol G) →ₗ[F]
      Word F (C0Index aRow bRow G) :=
  Matrix.toLin' (boundary1Matrix D)

/-- The second lifted-product boundary as a linear map on finite-coordinate words. -/
noncomputable def boundary2 {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Word F (C2Index aCol bCol G) →ₗ[F]
      Word F (QubitIndex aRow aCol bRow bCol G) :=
  Matrix.toLin' (boundary2Matrix D)

/-- The two lifted-product boundary matrices multiply to zero. -/
theorem boundary1Matrix_mul_boundary2Matrix
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    boundary1Matrix D * boundary2Matrix D = 0 := by
  ext ⟨ar, br, go⟩ ⟨ac, bc, gi⟩
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, boundary1Matrix_inl_apply,
    boundary1Matrix_inr_apply, boundary2Matrix_inl_apply,
    boundary2Matrix_inr_apply]
  calc
    (∑ x : aCol, ∑ x_1 : bRow, ∑ x_2 : G,
          (if br = x_1 then rightRegularMatrix (D.A ar x) go x_2 else 0) *
            (if x = ac then leftRegularMatrix (D.B x_1 bc) x_2 gi else 0)) +
        ∑ x : aRow, ∑ x_1 : bCol, ∑ x_2 : G,
          (if ar = x then -leftRegularMatrix (D.B br x_1) go x_2 else 0) *
            (if x_1 = bc then rightRegularMatrix (D.A x ac) x_2 gi else 0) =
      (rightRegularMatrix (D.A ar ac) *
          leftRegularMatrix (D.B br bc)) go gi -
        (leftRegularMatrix (D.B br bc) *
          rightRegularMatrix (D.A ar ac)) go gi := by
      simp [Matrix.mul_apply, sub_eq_add_neg]
    _ = 0 := by
      rw [leftRegularMatrix_mul_rightRegularMatrix]
      exact sub_self _

/-- The two lifted-product boundary maps compose to zero. -/
theorem boundary_squared {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    (boundary1 D).comp (boundary2 D) = 0 := by
  change (Matrix.toLin' (boundary1Matrix D)).comp
    (Matrix.toLin' (boundary2Matrix D)) = 0
  rw [← Matrix.toLin'_mul]
  rw [boundary1Matrix_mul_boundary2Matrix]
  simp

/-- The honest three-term chain complex of lifted-product boundary maps. -/
noncomputable def chainComplex
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    ChainComplexData F
      (Word F (C0Index aRow bRow G))
      (Word F (QubitIndex aRow aCol bRow bCol G))
      (Word F (C2Index aCol bCol G)) where
  boundary1 := boundary1 D
  boundary2 := boundary2 D
  boundary_squared := boundary_squared D

@[simp]
theorem chainComplex_boundary1
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    (chainComplex D).boundary1 = boundary1 D := by
  rfl

@[simp]
theorem chainComplex_boundary2
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    (chainComplex D).boundary2 = boundary2 D := by
  rfl

/-- The lifted-product middle homology loses at most one dimension per endpoint cell. -/
theorem card_qubitIndex_le_finrank_middleHomology_add_endpoints
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Fintype.card (QubitIndex aRow aCol bRow bCol G) ≤
      Module.finrank F (chainComplex D).middleHomology +
        Fintype.card (C0Index aRow bRow G) +
        Fintype.card (C2Index aCol bCol G) := by
  let K := chainComplex D
  change Fintype.card (QubitIndex aRow aCol bRow bCol G) ≤
    Module.finrank F K.middleHomology +
      Fintype.card (C0Index aRow bRow G) +
      Fintype.card (C2Index aCol bCol G)
  have hRankNullity := K.boundary1.finrank_range_add_finrank_ker
  have hRankNullity2 := K.boundary2.finrank_range_add_finrank_ker
  have hRange1 : Module.finrank F (LinearMap.range K.boundary1) ≤
      Fintype.card (C0Index aRow bRow G) := by
    calc
      Module.finrank F (LinearMap.range K.boundary1) ≤
          Module.finrank F (Word F (C0Index aRow bRow G)) :=
        Submodule.finrank_le _
      _ = _ := finrank_word_eq_length
  have hRange2 : Module.finrank F (LinearMap.range K.boundary2) ≤
      Fintype.card (C2Index aCol bCol G) := by
    change Module.finrank F (LinearMap.range K.boundary2) +
      Module.finrank F (LinearMap.ker K.boundary2) =
      Module.finrank F (Word F (C2Index aCol bCol G)) at hRankNullity2
    rw [finrank_word_eq_length] at hRankNullity2
    simp only [Length] at hRankNullity2
    omega
  have hBoundaryLeCycle : Module.finrank F (LinearMap.range K.boundary2) ≤
      Module.finrank F (LinearMap.ker K.boundary1) :=
    Submodule.finrank_mono K.middleBoundaryCode_le_middleCycleCode
  have hHomology := K.finrank_middleHomology_eq
  change Module.finrank F (LinearMap.range K.boundary1) +
    Module.finrank F (LinearMap.ker K.boundary1) =
    Module.finrank F (Word F (QubitIndex aRow aCol bRow bCol G)) at hRankNullity
  rw [finrank_word_eq_length] at hRankNullity
  simp only [Length] at hRankNullity
  change Module.finrank F K.middleHomology =
    Module.finrank F (LinearMap.ker K.boundary1) -
      Module.finrank F (LinearMap.range K.boundary2) at hHomology
  omega

/-- Endpoint-cell bounds give the encoded-rate estimate in the PK22 construction. -/
theorem rate_le_finrank_middleHomology_of_endpoint_bound
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (rate : ℝ)
    (hEndpoints :
      (Fintype.card (C0Index aRow bRow G) : ℝ) +
        (Fintype.card (C2Index aCol bCol G) : ℝ) ≤
        (1 - rate) * Fintype.card (QubitIndex aRow aCol bRow bCol G)) :
    rate * Fintype.card (QubitIndex aRow aCol bRow bCol G) ≤
      (Module.finrank F (chainComplex D).middleHomology : ℝ) := by
  have hCells :
      (Fintype.card (QubitIndex aRow aCol bRow bCol G) : ℝ) ≤
        (Module.finrank F (chainComplex D).middleHomology : ℝ) +
          Fintype.card (C0Index aRow bRow G) +
          Fintype.card (C2Index aCol bCol G) := by
    exact_mod_cast card_qubitIndex_le_finrank_middleHomology_add_endpoints D
  nlinarith

/-! ## Constructed boundary incidence and locality -/

/-- The support of a row of the first lifted-product boundary. -/
noncomputable def boundary1RowSupport
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (c0 : C0Index aRow bRow G) :
    Finset (QubitIndex aRow aCol bRow bCol G) := by
  classical
  exact hammingSupport
    (wordLinearMapTranspose (boundary1 D) (Pi.single c0 (1 : F)))

/-- The support of a row of the second lifted-product boundary. -/
noncomputable def boundary2RowSupport
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (c2 : C2Index aCol bCol G) :
    Finset (QubitIndex aRow aCol bRow bCol G) := by
  classical
  exact hammingSupport (boundary2 D (Pi.single c2 (1 : F)))

/-- The check-variable incidence constructed from the lifted-product chain complex. -/
noncomputable def boundaryIncidence
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    QEC.QLDPC.CheckIncidence
      (Sum (C0Index aRow bRow G) (C2Index aCol bCol G))
      (QubitIndex aRow aCol bRow bCol G) := by
  classical
  exact QEC.QLDPC.chainComplexBoundaryIncidence (chainComplex D)

private theorem transpose_boundary1_single_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    [decC0 : DecidableEq (C0Index aRow bRow G)]
    (D : Data F G aRow aCol bRow bCol)
    (c0 : C0Index aRow bRow G) (q : QubitIndex aRow aCol bRow bCol G) :
    (wordLinearMapTranspose (boundary1 D) (Pi.single c0 (1 : F))) q =
      boundary1Matrix D c0 q := by
  classical
  unfold wordLinearMapTranspose
  dsimp
  rw [Fintype.sum_eq_single c0]
  · simp [boundary1]
  · intro c0' hne
    rw [Pi.single_eq_of_ne hne, zero_mul]

private theorem boundary2_single_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    [decC2 : DecidableEq (C2Index aCol bCol G)]
    (D : Data F G aRow aCol bRow bCol)
    (c2 : C2Index aCol bCol G) (q : QubitIndex aRow aCol bRow bCol G) :
    boundary2 D (Pi.single c2 (1 : F)) q = boundary2Matrix D q c2 := by
  classical
  simp [boundary2, Matrix.toLin'_apply, Matrix.mulVec]

theorem transpose_boundary1_canonicalBasisWord_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (c0 : C0Index aRow bRow G) (q : QubitIndex aRow aCol bRow bCol G) :
    (wordLinearMapTranspose (boundary1 D) (canonicalBasisWord (F := F) c0)) q =
      boundary1Matrix D c0 q := by
  classical
  unfold canonicalBasisWord wordLinearMapTranspose
  dsimp
  rw [Fintype.sum_eq_single c0]
  · simp [boundary1]
  · intro c0' hne
    have hne' : c0 ≠ c0' := Ne.symm hne
    simp [hne']

theorem boundary2_canonicalBasisWord_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (c2 : C2Index aCol bCol G) (q : QubitIndex aRow aCol bRow bCol G) :
    boundary2 D (canonicalBasisWord (F := F) c2) q = boundary2Matrix D q c2 := by
  classical
  simp [canonicalBasisWord, boundary2, Matrix.toLin'_apply, Matrix.mulVec]

theorem boundary1_canonicalBasisWord_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (q : QubitIndex aRow aCol bRow bCol G) (c0 : C0Index aRow bRow G) :
    boundary1 D (canonicalBasisWord (F := F) q) c0 = boundary1Matrix D c0 q := by
  classical
  simp [canonicalBasisWord, boundary1, Matrix.toLin'_apply, Matrix.mulVec]

theorem transpose_boundary2_canonicalBasisWord_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (q : QubitIndex aRow aCol bRow bCol G) (c2 : C2Index aCol bCol G) :
    (wordLinearMapTranspose (boundary2 D)
      (canonicalBasisWord (F := F) q)) c2 = boundary2Matrix D q c2 := by
  classical
  unfold canonicalBasisWord wordLinearMapTranspose
  dsimp
  rw [Fintype.sum_eq_single q]
  · simp [boundary2]
  · intro q' hne
    have hne' : q ≠ q' := Ne.symm hne
    simp [hne']

@[simp]
theorem mem_boundary1RowSupport_inl
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar : aRow) (br br' : bRow) (ac : aCol) (go gi : G) :
    Sum.inl (ac, br', gi) ∈ boundary1RowSupport D (ar, br, go) ↔
      br = br' ∧ (D.A ar ac).coeff (gi⁻¹ * go) ≠ 0 := by
  classical
  simp [boundary1RowSupport, hammingSupport, transpose_boundary1_single_apply,
    boundary1Matrix_inl_apply, rightRegularMatrix]

@[simp]
theorem mem_boundary1RowSupport_inr
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar ar' : aRow) (br : bRow) (bc : bCol) (go gi : G) :
    Sum.inr (ar', bc, gi) ∈ boundary1RowSupport D (ar, br, go) ↔
      ar = ar' ∧ (D.B br bc).coeff (go * gi⁻¹) ≠ 0 := by
  classical
  simp [boundary1RowSupport, hammingSupport, transpose_boundary1_single_apply,
    boundary1Matrix_inr_apply, leftRegularMatrix]

@[simp]
theorem mem_boundary2RowSupport_inl
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ac ac' : aCol) (br : bRow) (bc : bCol) (go gi : G) :
    Sum.inl (ac, br, go) ∈ boundary2RowSupport D (ac', bc, gi) ↔
      ac = ac' ∧ (D.B br bc).coeff (go * gi⁻¹) ≠ 0 := by
  classical
  simp [boundary2RowSupport, hammingSupport, boundary2_single_apply,
    boundary2Matrix_inl_apply, leftRegularMatrix]

@[simp]
theorem mem_boundary2RowSupport_inr
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar : aRow) (ac : aCol) (bc bc' : bCol) (go gi : G) :
    Sum.inr (ar, bc, go) ∈ boundary2RowSupport D (ac, bc', gi) ↔
      bc = bc' ∧ (D.A ar ac).coeff (gi⁻¹ * go) ≠ 0 := by
  classical
  simp [boundary2RowSupport, hammingSupport, boundary2_single_apply,
    boundary2Matrix_inr_apply, rightRegularMatrix]

@[simp]
theorem boundaryIncidence_checkSupport_inl
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (c0 : C0Index aRow bRow G) :
    (boundaryIncidence D).checkSupport (Sum.inl c0) = boundary1RowSupport D c0 := by
  classical
  unfold boundaryIncidence
  ext q
  simp [QEC.QLDPC.CheckIncidence.checkSupport,
    QEC.QLDPC.chainComplexBoundaryIncidence, boundary1RowSupport,
    hammingSupport, transpose_boundary1_canonicalBasisWord_apply,
    transpose_boundary1_single_apply]

@[simp]
theorem boundaryIncidence_checkSupport_inr
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (c2 : C2Index aCol bCol G) :
    (boundaryIncidence D).checkSupport (Sum.inr c2) = boundary2RowSupport D c2 := by
  classical
  unfold boundaryIncidence
  ext q
  simp [QEC.QLDPC.CheckIncidence.checkSupport,
    QEC.QLDPC.chainComplexBoundaryIncidence, boundary2RowSupport,
    hammingSupport, boundary2_canonicalBasisWord_apply, boundary2_single_apply]

theorem boundaryIncidence_variableSupport
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (q : QubitIndex aRow aCol bRow bCol G) :
    (boundaryIncidence D).variableSupport q =
      (Finset.univ.filter
          (fun c0 : C0Index aRow bRow G => boundary1Matrix D c0 q ≠ 0)).map
        ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (Finset.univ.filter
          (fun c2 : C2Index aCol bCol G => boundary2Matrix D q c2 ≠ 0)).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by
  classical
  ext c
  cases c with
  | inl c0 =>
      rw [QEC.QLDPC.CheckIncidence.mem_variableSupport]
      unfold boundaryIncidence QEC.QLDPC.chainComplexBoundaryIncidence
      dsimp only
      rw [chainComplex_boundary1]
      change (wordLinearMapTranspose (boundary1 D)
        (canonicalBasisWord (F := F) c0)) q ≠ 0 ↔ _
      rw [transpose_boundary1_canonicalBasisWord_apply]
      simp
  | inr c2 =>
      rw [QEC.QLDPC.CheckIncidence.mem_variableSupport]
      unfold boundaryIncidence QEC.QLDPC.chainComplexBoundaryIncidence
      dsimp only
      rw [chainComplex_boundary2]
      change boundary2 D (canonicalBasisWord (F := F) c2) q ≠ 0 ↔ _
      rw [boundary2_canonicalBasisWord_apply]
      simp

/-- Explicit row and column bounds imply bounded locality for the constructed incidence. -/
theorem boundaryIncidence_boundedLocality_of_bounds
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) {B : Nat}
    (hrow1 : ∀ c0, (boundary1RowSupport D c0).card ≤ B)
    (hrow2 : ∀ c2, (boundary2RowSupport D c2).card ≤ B)
    (hcol : ∀ q, ((boundaryIncidence D).variableSupport q).card ≤ B) :
    QEC.Coding.BoundedLocality (boundaryIncidence D).localityProfile B := by
  apply (boundaryIncidence D).boundedLocality_of_row_col_bounds
  · intro c
    cases c with
    | inl c0 => simpa using hrow1 c0
    | inr c2 => simpa using hrow2 c2
  · exact hcol

/-! ## Binary semantic adapters -/

/--
The binary CSS code induced by the lifted-product chain complex.

Provenance anchors:
`panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`
`panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`
`leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`
These anchors record interface provenance only; no numerical distance bound is
formalized here.
-/
noncomputable def binaryCSSCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    CSSCode (ZMod 2) (QubitIndex aRow aCol bRow bCol G)
      (Semantics.Qubit.QubitRegister (QubitIndex aRow aCol bRow bCol G)) :=
  (chainComplex D).binaryCSSCode

/-- The induced X code is the constructed complex's first coboundary check code. -/
@[simp]
theorem binaryCSSCode_xCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    (binaryCSSCode D).xCode = (chainComplex D).firstCoboundaryCheckCode := by
  rfl

/-- The induced Z code is the constructed complex's middle boundary code. -/
@[simp]
theorem binaryCSSCode_zCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    (binaryCSSCode D).zCode = (chainComplex D).middleBoundaryCode := by
  rfl

/--
Package the binary CSS code induced by the lifted-product chain complex as a
chain-complex code.
-/
noncomputable def binaryChainComplexCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :=
  (chainComplex D).binaryChainComplexCode

/-- The exact stabilizer of the induced binary CSS code satisfies source validity. -/
theorem binaryCSSCode_stabilizer_isSourceValidBinary
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary := by
  exact (chainComplex D).binaryCSSCode_stabilizer_isSourceValidBinary

/-- Package the exact induced binary CSS stabilizer together with source validity. -/
noncomputable def binarySourceValidStabilizer
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    StabilizerCode.SourceValidBinary (QubitIndex aRow aCol bRow bCol G) :=
  (chainComplex D).binaryCSSSourceValidStabilizer

/--
The semantic carrier dimension of the induced binary CSS code is `2` to the
middle-homology dimension of its lifted-product chain complex.
-/
theorem binaryCSSCode_finrank_carrier
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    Module.finrank Complex (binaryCSSCode D).stabilizer.code.carrier =
      2 ^ Module.finrank (ZMod 2) (chainComplex D).middleHomology := by
  exact
    QEC.Coding.ChainComplexData.binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology
      (chainComplex D)

/-- Exact pure-X minimum distance for the binary CSS code induced by `D`. -/
abbrev BinaryPureXMinimumDistance
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) (dX : Nat) :=
  PureXLogicalMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode dX

/-- Exact pure-Z minimum distance for the binary CSS code induced by `D`. -/
abbrev BinaryPureZMinimumDistance
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) (dZ : Nat) :=
  PureZLogicalMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode dZ

/-- Exact algebraic CSS minimum distance for the binary CSS code induced by `D`. -/
abbrev BinaryAlgebraicCSSMinimumDistance
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) (d : Nat) :=
  AlgebraicCSSMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode d

/-- The two exact sector minima combine into the minimum for the induced code. -/
theorem binaryAlgebraicCSSMinimumDistance_of_sector_minima
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol)
    {dX dZ : Nat}
    (hX : BinaryPureXMinimumDistance D dX)
    (hZ : BinaryPureZMinimumDistance D dZ) :
    BinaryAlgebraicCSSMinimumDistance D (min dX dZ) := by
  exact algebraicCSSMinimumDistance_of_sector_minima hX hZ

/-! ## Qubit-block decomposition -/

/-- The canonical embedding of the first summand. -/
def firstEmbedding {α β : Type*} : α ↪ Sum α β :=
  Function.Embedding.inl

/-- The canonical embedding of the second summand. -/
def secondEmbedding {α β : Type*} : β ↪ Sum α β :=
  Function.Embedding.inr

/-- Restrict a lifted-product word to its first qubit block.

Provenance anchors:
`panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`
`panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`
`leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`
These anchors record interface provenance only; no paper theorem or decoding result is formalized here. -/
def firstRestriction {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (_D : Data F G aRow aCol bRow bCol) :
    Word F (QubitIndex aRow aCol bRow bCol G) →ₗ[F]
      Word F (aCol × bRow × G) where
  toFun x i := x (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict a lifted-product word to its second qubit block.

Provenance anchors:
`panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`
`panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`
`leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`
These anchors record interface provenance only; no paper theorem or decoding result is formalized here. -/
def secondRestriction {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (_D : Data F G aRow aCol bRow bCol) :
    Word F (QubitIndex aRow aCol bRow bCol G) →ₗ[F]
      Word F (aRow × bCol × G) where
  toFun x i := x (Sum.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend a first-block word by zero on the second qubit block.

Provenance anchors:
`panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`
`panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`
`leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`
These anchors record interface provenance only; no paper theorem or decoding result is formalized here. -/
def firstZeroExtension {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (_D : Data F G aRow aCol bRow bCol) :
    Word F (aCol × bRow × G) →ₗ[F]
      Word F (QubitIndex aRow aCol bRow bCol G) where
  toFun x q := q.elim x (fun _ => 0)
  map_add' _ _ := by
    funext q
    cases q <;> simp
  map_smul' _ _ := by
    funext q
    cases q <;> simp

/-- Extend a second-block word by zero on the first qubit block.

Provenance anchors:
`panteleev-kalachev-2020-almost-linear/main.tex:605-630,733-774`
`panteleev-kalachev-2021-good/main.tex:248-273,349-410,589-620`
`leverrier-zemor-2022-efficient-decoding/decoding-v3.tex:2211-2258`
These anchors record interface provenance only; no paper theorem or decoding result is formalized here. -/
def secondZeroExtension {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (_D : Data F G aRow aCol bRow bCol) :
    Word F (aRow × bCol × G) →ₗ[F]
      Word F (QubitIndex aRow aCol bRow bCol G) where
  toFun x q := q.elim (fun _ => 0) x
  map_add' _ _ := by
    funext q
    cases q <;> simp
  map_smul' _ _ := by
    funext q
    cases q <;> simp

@[simp]
theorem firstRestriction_firstZeroExtension
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    (firstRestriction D).comp (firstZeroExtension D) = LinearMap.id := by
  ext x i
  rfl

@[simp]
theorem secondRestriction_secondZeroExtension
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    (secondRestriction D).comp (secondZeroExtension D) = LinearMap.id := by
  ext x i
  rfl

@[simp]
theorem firstRestriction_secondZeroExtension
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    (firstRestriction D).comp (secondZeroExtension D) = 0 := by
  ext x i
  rfl

@[simp]
theorem secondRestriction_firstZeroExtension
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    (secondRestriction D).comp (firstZeroExtension D) = 0 := by
  ext x i
  rfl

theorem firstZeroExtension_injective
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    Function.Injective (firstZeroExtension D) := by
  intro x y hxy
  funext i
  exact congrFun hxy (Sum.inl i)

theorem secondZeroExtension_injective
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    Function.Injective (secondZeroExtension D) := by
  intro x y hxy
  funext i
  exact congrFun hxy (Sum.inr i)

theorem hammingSupport_firstZeroExtension
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (x : Word F (aCol × bRow × G)) :
    hammingSupport (firstZeroExtension D x) =
      (hammingSupport x).map firstEmbedding := by
  ext q
  simp only [hammingSupport, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  cases q <;> simp [firstZeroExtension, firstEmbedding]

theorem hammingSupport_secondZeroExtension
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (x : Word F (aRow × bCol × G)) :
    hammingSupport (secondZeroExtension D x) =
      (hammingSupport x).map secondEmbedding := by
  ext q
  simp only [hammingSupport, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  cases q <;> simp [secondZeroExtension, secondEmbedding]

theorem hammingSupport_sum_blocks
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (x : Word F (QubitIndex aRow aCol bRow bCol G)) :
    hammingSupport x =
      (hammingSupport (firstRestriction D x)).map firstEmbedding ∪
        (hammingSupport (secondRestriction D x)).map secondEmbedding := by
  ext q
  simp only [hammingSupport, Finset.mem_union, Finset.mem_map,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases q <;>
    simp [firstRestriction, secondRestriction,
      firstEmbedding, secondEmbedding]

theorem disjoint_hammingSupport_first_second_zeroExtension
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (x : Word F (aCol × bRow × G))
    (y : Word F (aRow × bCol × G)) :
    Disjoint (hammingSupport (firstZeroExtension D x))
      (hammingSupport (secondZeroExtension D y)) := by
  rw [Finset.disjoint_left]
  intro q hqFirst hqSecond
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hqFirst hqSecond
  cases q <;>
    simp [firstZeroExtension, secondZeroExtension] at hqFirst hqSecond

end QEC.Coding.LiftedProduct
