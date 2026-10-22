import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Order.Core
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.IndexRepresentation
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.Congruence
import Mathlib.Tactic

/-!
# Coefficient reduction for the Cartwright--Steger order

The split cyclic-algebra order has coefficients in the constant extension of
`F_q[y, 1/y, 1/(1+y)]`.  This module constructs its actual reduction to the
selected finite residue field, using the compatible constant embedding and
the construction-owned value of `y`.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- Polynomial coefficients after extending constants to `F_(q^d)`. -/
abbrev ConstantPolynomialRing (P : BasePrime) (r : Rank) :=
  Polynomial (ConstantExtension P r)

/-- The constant extension of the localized arithmetic coefficient ring. -/
abbrev ConstantArithmeticRing (P : BasePrime) (r : Rank) :=
  Localization.Away
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)

/-- Evaluate constant-extension polynomials at the selected residue value of
`y`, using the compatible embedding of `F_(q^d)`. -/
noncomputable def indexConstantPolynomialEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r →+* ResidueField P r level :=
  Polynomial.eval₂RingHom
    (indexConstantEmbedding P r level).toRingHom
    (indexPlaceY P r level)

@[simp] theorem indexConstantPolynomialEval_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexConstantPolynomialEval P r level Polynomial.X =
      indexPlaceY P r level := by
  simp [indexConstantPolynomialEval]

@[simp] theorem indexConstantPolynomialEval_C
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    indexConstantPolynomialEval P r level (Polynomial.C c) =
      indexConstantEmbedding P r level c := by
  simp [indexConstantPolynomialEval]

theorem indexConstantPolynomialEval_denominator_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexConstantPolynomialEval P r level
      (Polynomial.X * (1 + Polynomial.X))) := by
  rw [map_mul, indexConstantPolynomialEval_X, map_add, map_one,
    indexConstantPolynomialEval_X, isUnit_iff_ne_zero]
  exact mul_ne_zero (indexPlaceY_ne_zero P r level)
    (indexPlaceY_one_add_ne_zero P r level)

/-- Genuine reduction of the constant-extended localized coefficient ring. -/
noncomputable def indexConstantArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantArithmeticRing P r →+* ResidueField P r level :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
    (S := ConstantArithmeticRing P r)
    (g := indexConstantPolynomialEval P r level)
    (indexConstantPolynomialEval_denominator_isUnit P r level)

@[simp] theorem indexConstantArithmeticEval_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : ConstantPolynomialRing P r) :
    indexConstantArithmeticEval P r level
        (algebraMap (ConstantPolynomialRing P r)
          (ConstantArithmeticRing P r) f) =
      indexConstantPolynomialEval P r level f := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- Extending coefficients in a base-field polynomial and then evaluating is
the same as the original base arithmetic polynomial evaluation. -/
theorem indexConstantPolynomialEval_map_base
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : PolynomialRing P) :
    indexConstantPolynomialEval P r level
        (Polynomial.map (algebraMap (BaseField P)
          (ConstantExtension P r)) f) =
      indexPolynomialEval P r level f := by
  change Polynomial.eval₂
      (indexConstantEmbedding P r level).toRingHom
      (indexPlaceY P r level)
      (Polynomial.map (algebraMap (BaseField P)
        (ConstantExtension P r)) f) =
    Polynomial.eval₂ (algebraMap (BaseField P)
      (ResidueField P r level)) (indexPlaceY P r level) f
  rw [Polynomial.eval₂_map]
  congr 1
  ext a
  exact (indexConstantEmbedding P r level).commutes a

/-- The constant-extended polynomial evaluation remains onto, since its
base-field polynomial subring already reaches the full selected residue
field. -/
theorem indexConstantPolynomialEval_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexConstantPolynomialEval P r level) := by
  intro x
  obtain ⟨f, hf⟩ := indexPolynomialEval_surjective P r level x
  exact ⟨Polynomial.map
    (algebraMap (BaseField P) (ConstantExtension P r)) f,
      (indexConstantPolynomialEval_map_base P r level f).trans hf⟩

/-- Localization does not reduce the image: constant-extension polynomial
representatives already hit every residue-field element. -/
theorem indexConstantArithmeticEval_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexConstantArithmeticEval P r level) := by
  intro x
  obtain ⟨f, rfl⟩ := indexConstantPolynomialEval_surjective P r level x
  exact ⟨algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r) f,
    indexConstantArithmeticEval_algebraMap P r level f⟩

/-! ## Explicit localized coordinate units -/

/-- The coordinate `y` in the constant-extended arithmetic ring. -/
noncomputable def constantArithmeticY
    (P : BasePrime) (r : Rank) : ConstantArithmeticRing P r :=
  algebraMap (ConstantPolynomialRing P r)
    (ConstantArithmeticRing P r) Polynomial.X

/-- The inverse of the localized product `y(1+y)`. -/
noncomputable def constantArithmeticDenominatorInv
    (P : BasePrime) (r : Rank) : ConstantArithmeticRing P r :=
  IsLocalization.Away.invSelf
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)

/-- The explicitly constructed inverse of `y`. -/
noncomputable def constantArithmeticYInv
    (P : BasePrime) (r : Rank) : ConstantArithmeticRing P r :=
  algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r) (1 + Polynomial.X) *
    constantArithmeticDenominatorInv P r

/-- The explicitly constructed inverse of `1+y`. -/
noncomputable def constantArithmeticOnePlusYInv
    (P : BasePrime) (r : Rank) : ConstantArithmeticRing P r :=
  algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r) Polynomial.X *
    constantArithmeticDenominatorInv P r

theorem constantArithmeticY_mul_inv
    (P : BasePrime) (r : Rank) :
    constantArithmeticY P r * constantArithmeticYInv P r = 1 := by
  rw [constantArithmeticY, constantArithmeticYInv,
    constantArithmeticDenominatorInv, ← mul_assoc, ← map_mul]
  exact IsLocalization.Away.mul_invSelf
    (S := ConstantArithmeticRing P r)
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)

theorem constantArithmeticY_inv_mul
    (P : BasePrime) (r : Rank) :
    constantArithmeticYInv P r * constantArithmeticY P r = 1 := by
  rw [mul_comm]
  exact constantArithmeticY_mul_inv P r

theorem constantArithmeticOnePlusY_mul_inv
    (P : BasePrime) (r : Rank) :
    (1 + constantArithmeticY P r) *
        constantArithmeticOnePlusYInv P r = 1 := by
  let ι := algebraMap (ConstantPolynomialRing P r)
    (ConstantArithmeticRing P r)
  have hOne : 1 + ι Polynomial.X = ι (1 + Polynomial.X) := by
    rw [map_add, map_one]
  rw [constantArithmeticY, constantArithmeticOnePlusYInv,
    constantArithmeticDenominatorInv, hOne]
  calc
    ι (1 + Polynomial.X) *
          (ι Polynomial.X *
            IsLocalization.Away.invSelf
              (Polynomial.X * (1 + Polynomial.X) :
                ConstantPolynomialRing P r)) =
        ι (Polynomial.X * (1 + Polynomial.X)) *
          IsLocalization.Away.invSelf
            (Polynomial.X * (1 + Polynomial.X) :
              ConstantPolynomialRing P r) := by
      rw [← mul_assoc, mul_comm (ι (1 + Polynomial.X))
        (ι Polynomial.X), map_mul]
    _ = 1 := IsLocalization.Away.mul_invSelf
      (S := ConstantArithmeticRing P r)
      (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)

theorem constantArithmeticOnePlusY_inv_mul
    (P : BasePrime) (r : Rank) :
    constantArithmeticOnePlusYInv P r *
        (1 + constantArithmeticY P r) = 1 := by
  rw [mul_comm]
  exact constantArithmeticOnePlusY_mul_inv P r

/-- `y` as a unit of the actual localized coefficient ring. -/
noncomputable def constantArithmeticYUnit
    (P : BasePrime) (r : Rank) : (ConstantArithmeticRing P r)ˣ where
  val := constantArithmeticY P r
  inv := constantArithmeticYInv P r
  val_inv := constantArithmeticY_mul_inv P r
  inv_val := constantArithmeticY_inv_mul P r

/-- `1+y` as a unit of the actual localized coefficient ring. -/
noncomputable def constantArithmeticOnePlusYUnit
    (P : BasePrime) (r : Rank) : (ConstantArithmeticRing P r)ˣ where
  val := 1 + constantArithmeticY P r
  inv := constantArithmeticOnePlusYInv P r
  val_inv := constantArithmeticOnePlusY_mul_inv P r
  inv_val := constantArithmeticOnePlusY_inv_mul P r

@[simp] theorem indexConstantArithmeticEval_constantArithmeticY
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexConstantArithmeticEval P r level (constantArithmeticY P r) =
      indexPlaceY P r level := by
  rw [constantArithmeticY,
    indexConstantArithmeticEval_algebraMap,
    indexConstantPolynomialEval_X]

@[simp] theorem indexConstantArithmeticEval_one_add_constantArithmeticY
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexConstantArithmeticEval P r level
        (1 + constantArithmeticY P r) =
      1 + indexPlaceY P r level := by
  simp

@[simp] theorem indexConstantArithmeticEval_onePlusYInv
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexConstantArithmeticEval P r level
        (constantArithmeticOnePlusYInv P r) =
      (1 + indexPlaceY P r level)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (indexConstantArithmeticEval P r level)
    (constantArithmeticOnePlusY_mul_inv P r)
  simpa [map_mul] using h

/-! ## Comparison with the global split cyclic algebra -/

/-- Embed the constant-extended localized coefficient ring into the global
splitting function field. -/
noncomputable def constantArithmeticToSplittingFunctionField
    (P : BasePrime) (r : Rank) :
    ConstantArithmeticRing P r →+* SplittingFunctionField P r :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
    (S := ConstantArithmeticRing P r)
    (g := algebraMap (ConstantPolynomialRing P r)
      (SplittingFunctionField P r)) (by
      rw [isUnit_iff_ne_zero]
      apply RatFunc.algebraMap_ne_zero
      exact mul_ne_zero Polynomial.X_ne_zero (by
        intro hp
        have h := congrArg
          (Polynomial.eval (0 : ConstantExtension P r)) hp
        simp at h))

@[simp] theorem constantArithmeticToSplittingFunctionField_algebraMap
    (P : BasePrime) (r : Rank) (f : ConstantPolynomialRing P r) :
    constantArithmeticToSplittingFunctionField P r
        (algebraMap (ConstantPolynomialRing P r)
          (ConstantArithmeticRing P r) f) =
      algebraMap (ConstantPolynomialRing P r)
        (SplittingFunctionField P r) f := by
  exact IsLocalization.Away.lift_eq _ _ _

@[simp] theorem constantArithmeticToSplittingFunctionField_y
    (P : BasePrime) (r : Rank) :
    constantArithmeticToSplittingFunctionField P r
        (constantArithmeticY P r) = splittingY P r := by
  rw [constantArithmeticY,
    constantArithmeticToSplittingFunctionField_algebraMap]
  rfl

@[simp] theorem constantArithmeticToSplittingFunctionField_onePlusYInv
    (P : BasePrime) (r : Rank) :
    constantArithmeticToSplittingFunctionField P r
        (constantArithmeticOnePlusYInv P r) =
      (onePlusY P r)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (constantArithmeticToSplittingFunctionField P r)
    (constantArithmeticOnePlusY_mul_inv P r)
  simpa [map_mul, onePlusY_eq_one_add_splittingY] using h

/-! ## The integral split matrix model and its reduction -/

/-- Compatible diagonal representation of a constant over the localized
constant-extension coefficient ring. -/
noncomputable def orderSplitConstantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  Matrix.diagonal fun i =>
    algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r)
      (Polynomial.C (((constantFrobenius P r).symm ^ i.val) c))

/-- Weighted cyclic shift over the actual localized coefficient ring. -/
noncomputable def orderSplitCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) := by
  cases r with
  | three =>
      exact !![0, 0, 1 + constantArithmeticY P .three;
               1, 0, 0;
               0, 1, 0]
  | four =>
      exact !![0, 0, 0, 1 + constantArithmeticY P .four;
               1, 0, 0, 0;
               0, 1, 0, 0;
               0, 0, 1, 0]

/-- Explicit inverse weighted shift over the localized coefficient ring. -/
noncomputable def orderSplitCyclicInverseMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) := by
  cases r with
  | three =>
      exact !![0, 1, 0;
               0, 0, 1;
               constantArithmeticOnePlusYInv P .three, 0, 0]
  | four =>
      exact !![0, 1, 0, 0;
               0, 0, 1, 0;
               0, 0, 0, 1;
               constantArithmeticOnePlusYInv P .four, 0, 0, 0]

theorem map_orderSplitConstantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    (orderSplitConstantMatrix P r c).map
        (indexConstantArithmeticEval P r level) =
      indexConstantMatrix P r level c := by
  ext i j
  by_cases h : i = j <;>
    simp [orderSplitConstantMatrix, indexConstantMatrix, h]

theorem map_orderSplitCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    (orderSplitCyclicGeneratorMatrix P r).map
        (indexConstantArithmeticEval P r level) =
      indexCyclicGeneratorMatrix P r level := by
  cases r <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [orderSplitCyclicGeneratorMatrix, indexCyclicGeneratorMatrix]

theorem map_orderSplitCyclicInverseMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    (orderSplitCyclicInverseMatrix P r).map
        (indexConstantArithmeticEval P r level) =
      indexCyclicGeneratorInverseMatrix P r level := by
  cases r <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [orderSplitCyclicInverseMatrix,
        indexCyclicGeneratorInverseMatrix]

theorem map_orderSplitConstantMatrix_to_global
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    (orderSplitConstantMatrix P r c).map
        (constantArithmeticToSplittingFunctionField P r) =
      constantMatrix P r c := by
  ext i j
  by_cases h : i = j <;>
    simp [orderSplitConstantMatrix, constantMatrix, h]

theorem map_orderSplitCyclicGeneratorMatrix_to_global
    (P : BasePrime) (r : Rank) :
    (orderSplitCyclicGeneratorMatrix P r).map
        (constantArithmeticToSplittingFunctionField P r) =
      cyclicGeneratorMatrix P r := by
  cases r <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [orderSplitCyclicGeneratorMatrix, cyclicGeneratorMatrix,
        onePlusY_eq_one_add_splittingY]

theorem map_orderSplitCyclicInverseMatrix_to_global
    (P : BasePrime) (r : Rank) :
    (orderSplitCyclicInverseMatrix P r).map
        (constantArithmeticToSplittingFunctionField P r) =
      cyclicGeneratorInverseMatrix P r := by
  cases r <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [orderSplitCyclicInverseMatrix, cyclicGeneratorInverseMatrix]

private theorem shiftThree_mul_explicitInverse
    {K : Type*} [CommRing K] (a aInv : K)
    (h : a * aInv = 1) :
    !![0, 0, a; 1, 0, 0; 0, 1, 0] *
        !![0, 1, 0; 0, 0, 1; aInv, 0, 0] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h]

private theorem shiftThree_explicitInverse_mul
    {K : Type*} [CommRing K] (a aInv : K)
    (h : aInv * a = 1) :
    !![0, 1, 0; 0, 0, 1; aInv, 0, 0] *
        !![0, 0, a; 1, 0, 0; 0, 1, 0] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h]

private theorem shiftFour_mul_explicitInverse
    {K : Type*} [CommRing K] (a aInv : K)
    (h : a * aInv = 1) :
    !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] *
        !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; aInv, 0, 0, 0] =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h]

private theorem shiftFour_explicitInverse_mul
    {K : Type*} [CommRing K] (a aInv : K)
    (h : aInv * a = 1) :
    !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; aInv, 0, 0, 0] *
        !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h]

theorem orderSplitCyclicGenerator_mul_inverse
    (P : BasePrime) (r : Rank) :
    orderSplitCyclicGeneratorMatrix P r *
      orderSplitCyclicInverseMatrix P r = 1 := by
  cases r with
  | three =>
      exact shiftThree_mul_explicitInverse
        (1 + constantArithmeticY P .three)
        (constantArithmeticOnePlusYInv P .three)
        (constantArithmeticOnePlusY_mul_inv P .three)
  | four =>
      exact shiftFour_mul_explicitInverse
        (1 + constantArithmeticY P .four)
        (constantArithmeticOnePlusYInv P .four)
        (constantArithmeticOnePlusY_mul_inv P .four)

theorem orderSplitCyclicInverse_mul_generator
    (P : BasePrime) (r : Rank) :
    orderSplitCyclicInverseMatrix P r *
      orderSplitCyclicGeneratorMatrix P r = 1 := by
  cases r with
  | three =>
      exact shiftThree_explicitInverse_mul
        (1 + constantArithmeticY P .three)
        (constantArithmeticOnePlusYInv P .three)
        (constantArithmeticOnePlusY_inv_mul P .three)
  | four =>
      exact shiftFour_explicitInverse_mul
        (1 + constantArithmeticY P .four)
        (constantArithmeticOnePlusYInv P .four)
        (constantArithmeticOnePlusY_inv_mul P .four)

/-- The integral weighted shift as a genuine general-linear element. -/
noncomputable def orderSplitCyclicGeneratorGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) where
  val := orderSplitCyclicGeneratorMatrix P r
  inv := orderSplitCyclicInverseMatrix P r
  val_inv := orderSplitCyclicGenerator_mul_inverse P r
  inv_val := orderSplitCyclicInverse_mul_generator P r

/-- Reduction of the integral weighted shift is exactly the previously
constructed finite cyclic generator. -/
theorem map_orderSplitCyclicGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitCyclicGeneratorGL P r) =
      indexCyclicGeneratorGL P r level := by
  apply Units.ext
  exact map_orderSplitCyclicGeneratorMatrix P r level

/-- Constants act functorially by units in the integral split model. -/
noncomputable def orderSplitConstantGLHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
  Units.map ({
    toFun := orderSplitConstantMatrix P r
    map_zero' := by ext i j; simp [orderSplitConstantMatrix]
    map_one' := by ext i j; simp [orderSplitConstantMatrix]
    map_add' := by
      intro c d
      ext i j
      by_cases h : i = j <;>
        simp [orderSplitConstantMatrix, h]
    map_mul' := by
      intro c d
      rw [orderSplitConstantMatrix, orderSplitConstantMatrix,
        orderSplitConstantMatrix, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp
  } : ConstantExtension P r →+*
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)).toMonoidHom

theorem map_orderSplitConstantGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitConstantGLHom P r u) =
      indexConstantGL P r level u := by
  apply Units.ext
  exact map_orderSplitConstantMatrix P r level u

/-! ## The integral Cartwright--Steger element -/

theorem orderSplitCyclicGeneratorMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    orderSplitCyclicGeneratorMatrix P r ^ r.matrixRank =
      (1 + constantArithmeticY P r) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  cases r with
  | three =>
      exact shiftThree_pow _ (1 + constantArithmeticY P .three)
  | four =>
      exact shiftFour_pow _ (1 + constantArithmeticY P .four)

/-- Ring-valued geometric-series certificate for the invertibility of
`1 - z⁻¹`.  Unlike the field version, the coefficient hypothesis is carried
by an actual unit. -/
private theorem isUnit_one_sub_inv_of_pow_eq_one_add_unit_smul_one
    {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (z : Matrix.GeneralLinearGroup n K) (d : Nat) (gamma : Kˣ)
    (hpow : (z : Matrix n n K) ^ d =
      (1 + (gamma : K)) • (1 : Matrix n n K)) :
    IsUnit
      ((1 : Matrix n n K) -
        (z⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
  let Z : Matrix n n K := z
  let Zi : Matrix n n K :=
    (z⁻¹ : Matrix.GeneralLinearGroup n K)
  let S : Matrix n n K := ∑ i ∈ Finset.range d, Z ^ i
  let B : Matrix n n K := 1 - Zi
  let C : Matrix n n K := 1 + ((↑(gamma⁻¹) : K) • S)
  change IsUnit B
  have hZiZ : Zi * Z = 1 := by
    dsimp [Zi, Z]
    exact congrArg Units.val (inv_mul_cancel z)
  have hgeom : (Z - 1) * S = Z ^ d - 1 := by
    exact mul_geom_sum Z d
  have hpow' : Z ^ d - 1 = (gamma : K) • (1 : Matrix n n K) := by
    rw [hpow]
    simp [add_smul]
  have hBS : B * S = (gamma : K) • Zi := by
    calc
      B * S = Zi * ((Z - 1) * S) := by
        dsimp [B]
        symm
        rw [← mul_assoc, mul_sub, hZiZ, mul_one]
      _ = Zi * (Z ^ d - 1) := by rw [hgeom]
      _ = Zi * ((gamma : K) • (1 : Matrix n n K)) := by rw [hpow']
      _ = (gamma : K) • Zi := by
        rw [Matrix.mul_smul]
        simp
  have hBC : B * C = 1 := by
    calc
      B * C = B * (1 + ((↑(gamma⁻¹) : K) • S)) := rfl
      _ = B + (↑(gamma⁻¹) : K) • (B * S) := by
        rw [mul_add, mul_one, Matrix.mul_smul]
      _ = B + (↑(gamma⁻¹) : K) • ((gamma : K) • Zi) := by rw [hBS]
      _ = 1 := by
        rw [smul_smul]
        have hunit : (↑(gamma⁻¹) : K) * (gamma : K) = 1 := by
          exact congrArg Units.val (inv_mul_cancel gamma)
        rw [hunit, one_smul]
        simp [B]
  refine ⟨Units.mkOfMulEqOne B C hBC, ?_⟩
  exact Units.val_mkOfMulEqOne hBC

/-- The integral split form of the Cartwright--Steger element
`b = 1 - z⁻¹`. -/
noncomputable def orderSplitBMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  1 - ((orderSplitCyclicGeneratorGL P r)⁻¹ :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r))

theorem orderSplitBMatrix_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit (orderSplitBMatrix P r) := by
  apply isUnit_one_sub_inv_of_pow_eq_one_add_unit_smul_one
    (orderSplitCyclicGeneratorGL P r) r.matrixRank
    (constantArithmeticYUnit P r)
  exact orderSplitCyclicGeneratorMatrix_pow_matrixRank P r

/-- The integral split `b` as a genuine general-linear element. -/
noncomputable def orderSplitBGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  (orderSplitBMatrix_isUnit P r).unit

@[simp] theorem orderSplitBGL_coe
    (P : BasePrime) (r : Rank) :
    (orderSplitBGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) =
      orderSplitBMatrix P r :=
  IsUnit.unit_spec (orderSplitBMatrix_isUnit P r)

/-- Coefficient reduction sends the integral `b` exactly to the previously
constructed finite Cartwright--Steger `b`. -/
theorem map_orderSplitBGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitBGL P r) =
      indexBGL P r level := by
  apply Units.ext
  change (orderSplitBMatrix P r).map
      (indexConstantArithmeticEval P r level) =
    indexBMatrix P r level
  rw [orderSplitBMatrix]
  have hmapinv :
      Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          ((orderSplitCyclicGeneratorGL P r)⁻¹) =
        (indexCyclicGeneratorGL P r level)⁻¹ := by
    rw [map_inv, map_orderSplitCyclicGeneratorGL]
  have hzinv :
      (((orderSplitCyclicGeneratorGL P r)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)).map
          (indexConstantArithmeticEval P r level) =
        ((indexCyclicGeneratorGL P r level)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ResidueField P r level)) :=
    congrArg Units.val hmapinv
  rw [indexBMatrix_eq_one_sub_indexCyclicGenerator_inv]
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    map_sub]
  have hentry := congrFun (congrFun hzinv i) j
  simp only [Matrix.map_apply] at hentry
  rw [hentry]
  simp

/-- Base change from the integral split general-linear group to the global
splitting-field model. -/
noncomputable def orderSplitBaseChangeGLHom
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Matrix.GeneralLinearGroup.map
    (constantArithmeticToSplittingFunctionField P r)

theorem map_orderSplitCyclicGeneratorGL_to_global
    (P : BasePrime) (r : Rank) :
    orderSplitBaseChangeGLHom P r
        (orderSplitCyclicGeneratorGL P r) =
      cyclicGenerator P r := by
  apply Units.ext
  exact map_orderSplitCyclicGeneratorMatrix_to_global P r

theorem map_orderSplitConstantGL_to_global
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    orderSplitBaseChangeGLHom P r
        (orderSplitConstantGLHom P r u) =
      constantUnitMatrix P r u := by
  apply Units.ext
  exact map_orderSplitConstantMatrix_to_global P r u

theorem map_orderSplitBGL_to_global
    (P : BasePrime) (r : Rank) :
    orderSplitBaseChangeGLHom P r (orderSplitBGL P r) =
      cartwrightStegerB P r := by
  apply Units.ext
  change (orderSplitBMatrix P r).map
      (constantArithmeticToSplittingFunctionField P r) =
    cartwrightStegerBMatrix P r
  rw [orderSplitBMatrix, cartwrightStegerBMatrix]
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    map_sub]
  have hmatrix := map_orderSplitCyclicInverseMatrix_to_global P r
  have hentry := congrFun (congrFun hmatrix i) j
  have hinvEntry :
      constantArithmeticToSplittingFunctionField P r
        (((orderSplitCyclicGeneratorGL P r)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) i j) =
      cyclicGeneratorInverseMatrix P r i j := by
    simpa [orderSplitCyclicGeneratorGL] using hentry
  rw [hinvEntry]
  simp

/-- The integral split generator `b_u = u b u⁻¹`. -/
noncomputable def orderSplitCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  orderSplitConstantGLHom P r u * orderSplitBGL P r *
    (orderSplitConstantGLHom P r u)⁻¹

/-- Every integral split generator reduces exactly to its finite
Cartwright--Steger counterpart. -/
theorem map_orderSplitCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitCartwrightStegerGeneratorGL P r u) =
      indexCartwrightStegerGeneratorGL P r level u := by
  rw [orderSplitCartwrightStegerGeneratorGL,
    indexCartwrightStegerGeneratorGL, map_mul, map_mul, map_inv,
    map_orderSplitConstantGL, map_orderSplitBGL]

/-- Base change identifies the class-indexed integral generator with the
original global Cartwright--Steger generator. -/
theorem map_orderSplitCartwrightStegerClassGeneratorGL_to_global
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    orderSplitBaseChangeGLHom P r
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u)) =
      cartwrightStegerGenerator P r u := by
  rw [orderSplitCartwrightStegerGeneratorGL, cartwrightStegerGenerator,
    map_mul, map_mul, map_inv, map_orderSplitConstantGL_to_global,
    map_orderSplitBGL_to_global]

/-- Reduction homomorphism from the integral split general-linear group. -/
noncomputable def orderSplitReductionGLHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Matrix.GeneralLinearGroup.map
    (indexConstantArithmeticEval P r level)

/-- Projectivized coefficient reduction. -/
noncomputable def orderSplitReductionPGLHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) →*
      PGL P r level :=
  Matrix.ProjGenLinGroup.mk.comp
    (orderSplitReductionGLHom P r level)

/-- The subgroup generated by all integral split Cartwright--Steger
generators. -/
noncomputable def OrderSplitCartwrightStegerGroup
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  Subgroup.closure
    (Set.range (orderSplitCartwrightStegerGeneratorGL P r))

/-- Class-indexed integral lattice, matching the global construction's
source indexing exactly. -/
noncomputable def OrderSplitCartwrightStegerLattice
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  Subgroup.closure (Set.range fun u : ConstantProjectiveClass P r =>
    orderSplitCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r u))

/-- Base change recovers the original global Cartwright--Steger matrix
group exactly. -/
theorem map_OrderSplitCartwrightStegerLattice_to_global
    (P : BasePrime) (r : Rank) :
    (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitBaseChangeGLHom P r) =
      CartwrightStegerMatrixGroup P r := by
  rw [OrderSplitCartwrightStegerLattice, MonoidHom.map_closure,
    CartwrightStegerMatrixGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u,
      (map_orderSplitCartwrightStegerClassGeneratorGL_to_global
        P r u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u),
      ⟨u, rfl⟩,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global P r u⟩

theorem orderSplitReductionPGLHom_generator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    orderSplitReductionPGLHom P r level
        (orderSplitCartwrightStegerGeneratorGL P r u) =
      indexCartwrightStegerGenerator P r level u := by
  change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitCartwrightStegerGeneratorGL P r u)) = _
  rw [map_orderSplitCartwrightStegerGeneratorGL]
  rfl

theorem orderSplitReductionPGLHom_classGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    orderSplitReductionPGLHom P r level
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u)) =
      indexCartwrightStegerClassGenerator P r level u := by
  exact orderSplitReductionPGLHom_generator P r level
    (constantClassRepresentative P r u)

/-- The selected finite image is also exactly the projective reduction of
the class-indexed integral lattice. -/
theorem map_OrderSplitCartwrightStegerLattice
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitReductionPGLHom P r level) =
      IndexCartwrightStegerImage P r level := by
  rw [OrderSplitCartwrightStegerLattice, MonoidHom.map_closure,
    IndexCartwrightStegerImage]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u,
      (orderSplitReductionPGLHom_classGenerator P r level u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u),
      ⟨u, rfl⟩,
      orderSplitReductionPGLHom_classGenerator P r level u⟩

/-- Reduction of the integral lattice, with codomain restricted to the
actual finite Cartwright--Steger image. -/
noncomputable def orderSplitLatticeReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderSplitCartwrightStegerLattice P r →*
      IndexCartwrightStegerImage P r level where
  toFun g := ⟨orderSplitReductionPGLHom P r level g, by
    have hmem : orderSplitReductionPGLHom P r level g ∈
        (OrderSplitCartwrightStegerLattice P r).map
          (orderSplitReductionPGLHom P r level) :=
      ⟨g, g.property, rfl⟩
    rw [map_OrderSplitCartwrightStegerLattice] at hmem
    exact hmem⟩
  map_one' := Subtype.ext (map_one (orderSplitReductionPGLHom P r level))
  map_mul' g h :=
    Subtype.ext (map_mul (orderSplitReductionPGLHom P r level)
      (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (h : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)))

theorem orderSplitLatticeReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderSplitLatticeReduction P r level) := by
  intro y
  have hy : (y : PGL P r level) ∈
      (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitReductionPGLHom P r level) := by
    rw [map_OrderSplitCartwrightStegerLattice]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- The genuine principal congruence subgroup of the constructed integral
Cartwright--Steger lattice at the selected place. -/
noncomputable def OrderSplitCartwrightStegerCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderSplitCartwrightStegerLattice P r) :=
  (orderSplitLatticeReduction P r level).ker

noncomputable instance orderSplitCartwrightStegerCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSplitCartwrightStegerCongruenceSubgroup P r level).Normal := by
  dsimp [OrderSplitCartwrightStegerCongruenceSubgroup]
  infer_instance

/-- First isomorphism theorem for the actual integral lattice reduction. -/
noncomputable def orderSplitLatticeQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderSplitCartwrightStegerLattice P r ⧸
        OrderSplitCartwrightStegerCongruenceSubgroup P r level ≃*
      IndexCartwrightStegerImage P r level :=
  QuotientGroup.quotientKerEquivOfSurjective
    (orderSplitLatticeReduction P r level)
    (orderSplitLatticeReduction_surjective P r level)

/-- Exact vertex-count identity for the congruence quotient. -/
theorem natCard_orderSplitLatticeQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (OrderSplitCartwrightStegerLattice P r ⧸
          OrderSplitCartwrightStegerCongruenceSubgroup P r level) =
      Nat.card (IndexCartwrightStegerImage P r level) :=
  Nat.card_congr (orderSplitLatticeQuotientEquiv P r level).toEquiv

/-- The complete finite Cartwright--Steger image is the projective reduction
of the subgroup generated over the actual localized coefficient ring. -/
theorem map_OrderSplitCartwrightStegerGroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSplitCartwrightStegerGroup P r).map
        (orderSplitReductionPGLHom P r level) =
      IndexCartwrightStegerImage P r level := by
  rw [OrderSplitCartwrightStegerGroup, MonoidHom.map_closure,
    ← IndexCartwrightStegerUnitImage_eq_image,
    IndexCartwrightStegerUnitImage]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (orderSplitReductionPGLHom_generator P r level u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨orderSplitCartwrightStegerGeneratorGL P r u,
      ⟨u, rfl⟩, orderSplitReductionPGLHom_generator P r level u⟩

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
