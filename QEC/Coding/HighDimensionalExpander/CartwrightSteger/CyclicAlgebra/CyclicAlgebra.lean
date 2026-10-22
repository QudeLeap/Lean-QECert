import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The cyclic-algebra generator in the Cartwright--Steger construction

We realize the cyclic algebra inside matrices after extending constants from
`F_q(y)` to `F_(q^d)(y)`.  This file starts with the explicit shift matrix for
`z`, proves its inverse from the entries, and proves the defining relation
`z^d = (1 + y) I` in both ranks used by the LSV hierarchy.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups RatFunc

/-- Constant-field splitting extension of the rational function field. -/
abbrev SplittingFunctionField (P : BasePrime) (r : Rank) :=
  RatFunc (ConstantExtension P r)

/-- Extension of constants from `F_q(y)` to `F_(q^d)(y)`. -/
noncomputable def functionFieldEmbedding (P : BasePrime) (r : Rank) :
    RingHom (FunctionField P) (SplittingFunctionField P r) :=
  let f := Polynomial.mapRingHom
    (algebraMap (BaseField P) (ConstantExtension P r))
  RatFunc.mapRingHom f
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f
      (Polynomial.map_injective
        (algebraMap (BaseField P) (ConstantExtension P r))
        (RingHom.injective
          (algebraMap (BaseField P) (ConstantExtension P r)))))

noncomputable instance splittingFunctionFieldAlgebra
    (P : BasePrime) (r : Rank) :
    Algebra (FunctionField P) (SplittingFunctionField P r) :=
  (functionFieldEmbedding P r).toAlgebra

theorem functionFieldEmbedding_injective (P : BasePrime) (r : Rank) :
    Function.Injective (functionFieldEmbedding P r) := by
  exact RingHom.injective _

/-- The rational function `1 + y`, viewed in the splitting field. -/
noncomputable def onePlusY (P : BasePrime) (r : Rank) :
    SplittingFunctionField P r :=
  1 + RatFunc.X

theorem onePlusY_ne_zero (P : BasePrime) (r : Rank) :
    Not (onePlusY P r = 0) := by
  rw [onePlusY]
  have hpoly : Not ((1 + Polynomial.X :
      Polynomial (ConstantExtension P r)) = 0) := by
    intro h
    have hc := congrArg
      (Polynomial.eval (0 : ConstantExtension P r)) h
    simp at hc
  simpa using (RatFunc.algebraMap_ne_zero hpoly)

theorem shiftThree_mul_inverse {K : Type*} [Field K] (a : K)
    (ha : Not (a = 0)) :
    !![0, 0, a; 1, 0, 0; 0, 1, 0] *
        !![0, 1, 0; 0, 0, 1; a⁻¹, 0, 0] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]

theorem shiftThree_inverse_mul {K : Type*} [Field K] (a : K)
    (ha : Not (a = 0)) :
    !![0, 1, 0; 0, 0, 1; a⁻¹, 0, 0] *
        !![0, 0, a; 1, 0, 0; 0, 1, 0] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]

theorem shiftFour_mul_inverse {K : Type*} [Field K] (a : K)
    (ha : Not (a = 0)) :
    !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] *
        !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; a⁻¹, 0, 0, 0] =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]

theorem shiftFour_inverse_mul {K : Type*} [Field K] (a : K)
    (ha : Not (a = 0)) :
    !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; a⁻¹, 0, 0, 0] *
        !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]

theorem shiftThree_pow (K : Type*) [CommRing K] (a : K) :
    !![0, 0, a; 1, 0, 0; 0, 1, 0] ^ 3 =
      a • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

theorem shiftFour_pow (K : Type*) [CommRing K] (a : K) :
    !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] ^ 4 =
      a • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

/-- The explicit cyclic shift representing `z`.  The wraparound entry is
`1 + y`, so the third or fourth power is scalar multiplication by `1 + y`. -/
noncomputable def cyclicGeneratorMatrix (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) := by
  cases r with
  | three =>
      exact !![0, 0, onePlusY P .three;
               1, 0, 0;
               0, 1, 0]
  | four =>
      exact !![0, 0, 0, onePlusY P .four;
               1, 0, 0, 0;
               0, 1, 0, 0;
               0, 0, 1, 0]

/-- Entrywise inverse candidate for the cyclic generator. -/
noncomputable def cyclicGeneratorInverseMatrix (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) := by
  cases r with
  | three =>
      exact !![0, 1, 0;
               0, 0, 1;
               (onePlusY P .three)⁻¹, 0, 0]
  | four =>
      exact !![0, 1, 0, 0;
               0, 0, 1, 0;
               0, 0, 0, 1;
               (onePlusY P .four)⁻¹, 0, 0, 0]

theorem cyclicGenerator_mul_inverse (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r * cyclicGeneratorInverseMatrix P r = 1 := by
  cases r with
  | three => exact shiftThree_mul_inverse _ (onePlusY_ne_zero P .three)
  | four => exact shiftFour_mul_inverse _ (onePlusY_ne_zero P .four)

theorem cyclicGenerator_inverse_mul (P : BasePrime) (r : Rank) :
    cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r = 1 := by
  cases r with
  | three => exact shiftThree_inverse_mul _ (onePlusY_ne_zero P .three)
  | four => exact shiftFour_inverse_mul _ (onePlusY_ne_zero P .four)

/-- The generator as an actual unit of the matrix algebra. -/
noncomputable def cyclicGenerator (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (SplittingFunctionField P r) where
  val := cyclicGeneratorMatrix P r
  inv := cyclicGeneratorInverseMatrix P r
  val_inv := cyclicGenerator_mul_inverse P r
  inv_val := cyclicGenerator_inverse_mul P r

@[simp] theorem cyclicGenerator_val (P : BasePrime) (r : Rank) :
    (cyclicGenerator P r : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) = cyclicGeneratorMatrix P r :=
  rfl

/-- The first defining relation of the cyclic algebra, checked from the
rank-three and rank-four matrices. -/
theorem cyclicGenerator_pow_matrixRank (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r ^ r.matrixRank =
      (onePlusY P r) • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) := by
  cases r with
  | three => exact shiftThree_pow _ _
  | four => exact shiftFour_pow _ _

/-- The constant field inside the split cyclic algebra.  Coordinate `i`
contains the `i`-fold inverse Frobenius conjugate, which is the convention
making left multiplication by `z` implement Frobenius. -/
noncomputable def constantMatrix (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  Matrix.diagonal fun i =>
    algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
      (((constantFrobenius P r).symm ^ i.val) c)

/-- The constant-field embedding is derived from the diagonal matrices. -/
noncomputable def constantMatrixEmbedding (P : BasePrime) (r : Rank) :
    RingHom (ConstantExtension P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) where
  toFun := constantMatrix P r
  map_zero' := by simp [constantMatrix]
  map_one' := by
    ext i j
    simp [constantMatrix]
  map_add' c d := by
    rw [constantMatrix, constantMatrix, constantMatrix,
      Matrix.diagonal_add]
    congr 1
    funext i
    simp
  map_mul' c d := by
    rw [constantMatrix, constantMatrix, constantMatrix,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp

@[simp] theorem constantMatrixEmbedding_apply (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    constantMatrixEmbedding P r c = constantMatrix P r c :=
  rfl

theorem constantMatrixEmbedding_injective (P : BasePrime) (r : Rank) :
    Function.Injective (constantMatrixEmbedding P r) := by
  intro c d h
  let i0 : Fin r.matrixRank :=
    ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩
  have h00 := congrFun (congrFun h i0) i0
  simp [constantMatrix, i0] at h00
  exact RingHom.injective _ h00

theorem constantFrobenius_pow_matrixRank (P : BasePrime) (r : Rank) :
    constantFrobenius P r ^ r.matrixRank = 1 := by
  apply (orderOf_dvd_iff_pow_eq_one).mp
  rw [constantFrobenius_order]

/-- The arithmetic Frobenius generates the complete Galois group of the
constant extension. -/
theorem zpowers_constantFrobenius_eq_top
    (P : BasePrime) (r : Rank) :
    Subgroup.zpowers (constantFrobenius P r) = ⊤ := by
  apply (Subgroup.card_eq_iff_eq_top
    (Subgroup.zpowers (constantFrobenius P r))).mp
  rw [Nat.card_zpowers, constantFrobenius_order,
    IsGalois.card_aut_eq_finrank,
    GaloisField.finrank P.q (by cases r <;> simp [Rank.matrixRank])]

/-- The only constants fixed by arithmetic Frobenius are base-field
scalars. -/
theorem exists_eq_algebraMap_of_constantFrobenius_eq
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (hc : constantFrobenius P r c = c) :
    ∃ a : BaseField P,
      algebraMap (BaseField P) (ConstantExtension P r) a = c := by
  rw [← Set.mem_range]
  apply (IsGalois.mem_range_algebraMap_iff_fixed
    (F := BaseField P) (E := ConstantExtension P r) c).mpr
  intro f
  have hle :
      Subgroup.zpowers (constantFrobenius P r) ≤
        MulAction.stabilizer
          (ConstantExtension P r ≃ₐ[BaseField P] ConstantExtension P r) c := by
    rw [Subgroup.zpowers_le]
    exact MulAction.mem_stabilizer_iff.mpr hc
  exact MulAction.mem_stabilizer_iff.mp
    (hle (by rw [zpowers_constantFrobenius_eq_top P r]; exact Subgroup.mem_top f))

/-- The rank-indexed matrix chosen for Frobenius has the same order relation
as the underlying finite-field automorphism. -/
theorem frobeniusGL_pow_matrixRank (P : BasePrime) (r : Rank) :
    frobeniusGL P r ^ r.matrixRank = 1 := by
  apply (Matrix.GeneralLinearGroup.toLin' (constantBasis P r)).injective
  rw [map_pow, map_one]
  simp only [frobeniusGL, MulEquiv.apply_symm_apply]
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv
    (BaseField P) (ConstantExtension P r)).injective
  rw [map_pow, map_one]
  change (constantFrobenius P r).toLinearEquiv ^ r.matrixRank = 1
  have hpow : ∀ n : Nat,
      (constantFrobenius P r).toLinearEquiv ^ n =
        (constantFrobenius P r ^ n).toLinearEquiv := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ, pow_succ, ih]
        rfl
  rw [hpow, constantFrobenius_pow_matrixRank]
  rfl

/-- The matrix selected for Frobenius is literally the matrix of the
constant-field Frobenius in the fixed basis. -/
theorem frobeniusGL_coe (P : BasePrime) (r : Rank) :
    (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) =
      LinearMap.toMatrix (constantBasis P r) (constantBasis P r)
        (constantFrobenius P r).toLinearEquiv.toLinearMap := by
  apply (Matrix.toLin (constantBasis P r) (constantBasis P r)).injective
  rw [Matrix.toLin_toMatrix]
  have hlin :
      Matrix.toLin (constantBasis P r) (constantBasis P r)
          (frobeniusGL P r :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) =
        ((Matrix.GeneralLinearGroup.toLin' (constantBasis P r))
          (frobeniusGL P r)).toLinearEquiv.toLinearMap := by
    ext x
    change
      Matrix.toLin (constantBasis P r) (constantBasis P r)
          (frobeniusGL P r :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) x =
        ((Matrix.GeneralLinearGroup.toLin' (constantBasis P r))
          (frobeniusGL P r)).toLinearEquiv x
    rw [Matrix.GeneralLinearGroup.toLin'_apply, Matrix.toLin_apply]
    simp [Fintype.linearCombination_apply]
  rw [hlin, frobeniusGL, MulEquiv.apply_symm_apply]
  rfl

/-- Matrix form of the skew relation `Phi c = Frobenius(c) Phi`. -/
theorem frobeniusGL_mul_constantRegularMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) *
        constantRegularMatrix P r c =
      constantRegularMatrix P r (constantFrobenius P r c) *
        (frobeniusGL P r :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) := by
  rw [frobeniusGL_coe, constantRegularMatrix,
    Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
    ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  simp [Module.End.mul_apply]

theorem constantFrobenius_symm_pow_pred (P : BasePrime) (r : Rank) :
    (constantFrobenius P r).symm ^ (r.matrixRank - 1) =
      constantFrobenius P r := by
  change (constantFrobenius P r)⁻¹ ^ (r.matrixRank - 1) =
    constantFrobenius P r
  calc
    (constantFrobenius P r)⁻¹ ^ (r.matrixRank - 1) =
        (constantFrobenius P r ^ r.matrixRank)⁻¹ *
          constantFrobenius P r := by
      cases r <;> simp [Rank.matrixRank] <;> group
    _ = constantFrobenius P r := by
      rw [constantFrobenius_pow_matrixRank]
      simp

/-- The second defining relation of the cyclic algebra. -/
theorem cyclicGenerator_mul_constantMatrix (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    cyclicGeneratorMatrix P r * constantMatrix P r c =
      constantMatrix P r (constantFrobenius P r c) *
        cyclicGeneratorMatrix P r := by
  have hwrap := congrArg (fun e :
      ConstantExtension P r ≃ₐ[BaseField P] ConstantExtension P r => e c)
    (constantFrobenius_symm_pow_pred P r)
  cases r with
  | three =>
      ext i j
      simp only [constantMatrix]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;>
        simp [cyclicGeneratorMatrix] at hwrap ⊢
      rw [hwrap]
      exact mul_comm _ _
  | four =>
      ext i j
      simp only [constantMatrix]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;>
        simp [cyclicGeneratorMatrix] at hwrap ⊢
      rw [hwrap]
      exact mul_comm _ _

/-- The cyclic algebra is the `F_q(y)`-subalgebra generated by the embedded
constant field and the explicit element `z`.  Thus its carrier and all later
units are construction-owned. -/
noncomputable def CyclicAlgebra (P : BasePrime) (r : Rank) :
    Subalgebra (FunctionField P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Algebra.adjoin (FunctionField P)
    (Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})

theorem constantMatrix_mem_cyclicAlgebra (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    constantMatrix P r c ∈ CyclicAlgebra P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_left _ ⟨c, rfl⟩

theorem cyclicGeneratorMatrix_mem_cyclicAlgebra (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r ∈ CyclicAlgebra P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_right _ (Set.mem_insert _ _)

theorem cyclicGeneratorInverseMatrix_mem_cyclicAlgebra
    (P : BasePrime) (r : Rank) :
    cyclicGeneratorInverseMatrix P r ∈ CyclicAlgebra P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_right _ (Set.mem_insert_iff.mpr (Or.inr rfl))

/-- The Cartwright--Steger element `b = 1 - z⁻¹`. -/
noncomputable def cartwrightStegerBMatrix (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  1 - cyclicGeneratorInverseMatrix P r

theorem cartwrightStegerBMatrix_mem_cyclicAlgebra
    (P : BasePrime) (r : Rank) :
    cartwrightStegerBMatrix P r ∈ CyclicAlgebra P r := by
  exact (CyclicAlgebra P r).sub_mem (CyclicAlgebra P r).one_mem
    (cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r)

/-- The rational parameter `y` in the splitting function field. -/
noncomputable def splittingY (P : BasePrime) (r : Rank) :
    SplittingFunctionField P r := RatFunc.X

theorem splittingY_ne_zero (P : BasePrime) (r : Rank) :
    Not (splittingY P r = 0) := by
  rw [splittingY]
  apply RatFunc.algebraMap_ne_zero
  exact Polynomial.X_ne_zero

theorem onePlusY_eq_one_add_splittingY (P : BasePrime) (r : Rank) :
    onePlusY P r = 1 + splittingY P r := by
  rfl

/-- The explicit inverse from LSV05b:
`b⁻¹ = 1 + y⁻¹ * sum_{i=0}^{d-1} z^i`. -/
noncomputable def cartwrightStegerBInverseMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  1 + (splittingY P r)⁻¹ •
    ∑ i ∈ Finset.range r.matrixRank, cyclicGeneratorMatrix P r ^ i

private theorem bThree_mul_inverse {K : Type*} [Field K]
    (y : K) (hy : Not (y = 0)) (ha : Not (1 + y = 0)) :
    (1 - !![0, 1, 0; 0, 0, 1; (1 + y)⁻¹, 0, 0]) *
        (1 + y⁻¹ • ∑ i ∈ Finset.range 3,
          (!![0, 0, 1 + y; 1, 0, 0; 0, 1, 0] :
            Matrix (Fin 3) (Fin 3) K) ^ i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Finset.sum_range_succ, pow_succ] <;>
    field_simp [hy, ha] <;>
    ring

private theorem bThree_inverse_mul {K : Type*} [Field K]
    (y : K) (hy : Not (y = 0)) (ha : Not (1 + y = 0)) :
    (1 + y⁻¹ • ∑ i ∈ Finset.range 3,
        (!![0, 0, 1 + y; 1, 0, 0; 0, 1, 0] :
          Matrix (Fin 3) (Fin 3) K) ^ i) *
      (1 - !![0, 1, 0; 0, 0, 1; (1 + y)⁻¹, 0, 0]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Finset.sum_range_succ, pow_succ] <;>
    field_simp [hy, ha] <;>
    ring

private theorem bFour_mul_inverse {K : Type*} [Field K]
    (y : K) (hy : Not (y = 0)) (ha : Not (1 + y = 0)) :
    (1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
        (1 + y)⁻¹, 0, 0, 0]) *
      (1 + y⁻¹ • ∑ i ∈ Finset.range 4,
        (!![0, 0, 0, 1 + y; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] :
          Matrix (Fin 4) (Fin 4) K) ^ i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Finset.sum_range_succ, pow_succ] <;>
    field_simp [hy, ha] <;>
    ring

private theorem bFour_inverse_mul {K : Type*} [Field K]
    (y : K) (hy : Not (y = 0)) (ha : Not (1 + y = 0)) :
    (1 + y⁻¹ • ∑ i ∈ Finset.range 4,
        (!![0, 0, 0, 1 + y; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] :
          Matrix (Fin 4) (Fin 4) K) ^ i) *
      (1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
        (1 + y)⁻¹, 0, 0, 0]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Finset.sum_range_succ, pow_succ] <;>
    field_simp [hy, ha] <;>
    ring

theorem cartwrightStegerB_mul_inverse (P : BasePrime) (r : Rank) :
    cartwrightStegerBMatrix P r *
      cartwrightStegerBInverseMatrix P r = 1 := by
  cases r with
  | three =>
      exact bThree_mul_inverse _ (splittingY_ne_zero P .three) (by
        exact onePlusY_ne_zero P .three)
  | four =>
      exact bFour_mul_inverse _ (splittingY_ne_zero P .four) (by
        exact onePlusY_ne_zero P .four)

theorem cartwrightStegerB_inverse_mul (P : BasePrime) (r : Rank) :
    cartwrightStegerBInverseMatrix P r *
      cartwrightStegerBMatrix P r = 1 := by
  cases r with
  | three =>
      exact bThree_inverse_mul _ (splittingY_ne_zero P .three) (by
        exact onePlusY_ne_zero P .three)
  | four =>
      exact bFour_inverse_mul _ (splittingY_ne_zero P .four) (by
        exact onePlusY_ne_zero P .four)

/-- `b` as a proved unit, with its inverse computed from the source formula. -/
noncomputable def cartwrightStegerB (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (SplittingFunctionField P r) where
  val := cartwrightStegerBMatrix P r
  inv := cartwrightStegerBInverseMatrix P r
  val_inv := cartwrightStegerB_mul_inverse P r
  inv_val := cartwrightStegerB_inverse_mul P r

/-- Scalar units from the base field inside the constant extension. -/
noncomputable def baseScalarUnitHom (P : BasePrime) (r : Rank) :
    MonoidHom (Units (BaseField P)) (Units (ConstantExtension P r)) :=
  Units.map (algebraMap (BaseField P) (ConstantExtension P r))

theorem baseScalarUnitHom_injective (P : BasePrime) (r : Rank) :
    Function.Injective (baseScalarUnitHom P r) :=
  Units.map_injective (algebraMap (BaseField P)
    (ConstantExtension P r)).injective

/-- The central scalar subgroup `F_qˣ` of `F_(q^d)ˣ`. -/
noncomputable def baseScalarUnits (P : BasePrime) (r : Rank) :
    Subgroup (Units (ConstantExtension P r)) :=
  (baseScalarUnitHom P r).range

/-- The actual source index `F_(q^d)ˣ / F_qˣ` for the Cartwright--Steger
generators. -/
abbrev ConstantProjectiveClass (P : BasePrime) (r : Rank) :=
  Units (ConstantExtension P r) ⧸ baseScalarUnits P r

noncomputable instance (P : BasePrime) (r : Rank) :
    Fintype (ConstantProjectiveClass P r) :=
  Fintype.ofFinite _

/-- The central scalar subgroup has exactly `q - 1` elements. -/
theorem natCard_baseScalarUnits (P : BasePrime) (r : Rank) :
    Nat.card (baseScalarUnits P r) = P.q - 1 := by
  calc
    Nat.card (baseScalarUnits P r) =
        Nat.card (Units (BaseField P)) :=
      (Nat.card_congr
        (Equiv.ofInjective (baseScalarUnitHom P r)
          (baseScalarUnitHom_injective P r))).symm
    _ = Nat.card (BaseField P) - 1 := Nat.card_units _
    _ = P.q - 1 := by rw [Nat.card_zmod]

/-- Exact size equation for the source generator index
`F_(q^d)^× / F_q^×`. -/
theorem natCard_constantProjectiveClass_mul_baseScalar
    (P : BasePrime) (r : Rank) :
    Nat.card (ConstantProjectiveClass P r) * (P.q - 1) =
      P.q ^ r.matrixRank - 1 := by
  calc
    Nat.card (ConstantProjectiveClass P r) * (P.q - 1) =
        Nat.card (ConstantProjectiveClass P r) *
          Nat.card (baseScalarUnits P r) := by
      rw [natCard_baseScalarUnits]
    _ = Nat.card (Units (ConstantExtension P r)) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup
        (baseScalarUnits P r)).symm
    _ = Nat.card (ConstantExtension P r) - 1 := Nat.card_units _
    _ = P.q ^ r.matrixRank - 1 := by
      rw [natCard_constantExtension]

/-- The projective constant classes have the geometric-series cardinality
of the projective points over the base field. -/
theorem natCard_constantProjectiveClass
    (P : BasePrime) (r : Rank) :
    Nat.card (ConstantProjectiveClass P r) =
      ∑ i ∈ Finset.range r.matrixRank, P.q ^ i := by
  apply Nat.mul_right_cancel (m := P.q - 1)
  · have hq := P.five_le
    omega
  · rw [natCard_constantProjectiveClass_mul_baseScalar]
    exact (geom_sum_mul_of_one_le P.one_le r.matrixRank).symm

/-- A representative selected internally from a projective constant class. -/
noncomputable def constantClassRepresentative (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) : Units (ConstantExtension P r) :=
  u.out

/-- The regular diagonal matrix of a nonzero constant as a matrix unit. -/
noncomputable def constantUnitMatrix (P : BasePrime) (r : Rank)
    (u : Units (ConstantExtension P r)) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (SplittingFunctionField P r) :=
  Units.map (constantMatrixEmbedding P r) u

@[simp] theorem constantUnitMatrix_val (P : BasePrime) (r : Rank)
    (u : Units (ConstantExtension P r)) :
    (constantUnitMatrix P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) = constantMatrix P r u :=
  rfl

/-- The explicit generator `b_u = u b u⁻¹`, with exactly one internally
selected representative for every class in `F_(q^d)ˣ / F_qˣ`. -/
noncomputable def cartwrightStegerGenerator (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (SplittingFunctionField P r) :=
  constantUnitMatrix P r (constantClassRepresentative P r u) *
    cartwrightStegerB P r *
      (constantUnitMatrix P r (constantClassRepresentative P r u))⁻¹

/-- The generated Cartwright--Steger matrix group. -/
noncomputable def CartwrightStegerMatrixGroup (P : BasePrime) (r : Rank) :
    Subgroup
      (Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Subgroup.closure (Set.range (cartwrightStegerGenerator P r))

theorem cartwrightStegerGenerator_mem_group (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    cartwrightStegerGenerator P r u ∈ CartwrightStegerMatrixGroup P r :=
  Subgroup.subset_closure ⟨u, rfl⟩

/-- Projectivization of the constructed matrix group. -/
noncomputable def cartwrightStegerToProjective (P : BasePrime) (r : Rank) :
    MonoidHom
      (Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r))
      (Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Matrix.ProjGenLinGroup.mk

/-- The construction-owned projective Cartwright--Steger group. -/
noncomputable def CartwrightStegerProjectiveGroup (P : BasePrime) (r : Rank) :
    Subgroup
      (Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  (CartwrightStegerMatrixGroup P r).map
    (cartwrightStegerToProjective P r)

theorem projective_generator_mem (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    cartwrightStegerToProjective P r (cartwrightStegerGenerator P r u) ∈
      CartwrightStegerProjectiveGroup P r := by
  exact ⟨cartwrightStegerGenerator P r u,
    cartwrightStegerGenerator_mem_group P r u, rfl⟩

/-- The central base function `1 + y` acts by a scalar matrix in the cyclic
algebra, as follows from the proved power relation. -/
theorem onePlusY_smul_one_mem_cyclicAlgebra (P : BasePrime) (r : Rank) :
    (onePlusY P r) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) ∈
      CyclicAlgebra P r := by
  rw [← cyclicGenerator_pow_matrixRank]
  exact (CyclicAlgebra P r).pow_mem
    (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) _

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
