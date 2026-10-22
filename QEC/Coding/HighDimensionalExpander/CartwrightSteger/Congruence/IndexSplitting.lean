import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.CyclicAlgebra
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# A compatible split model at the index-controlled residue place

The selected residue degrees are divisible by the cyclic-algebra rank.  We
therefore embed the constant field into every selected residue field and use
the diagonal conjugate representation of that constant field.  The weighted
cyclic shift for `z` then satisfies both defining cyclic-algebra relations at
the actual full-order value of `y`.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- Every selected residue degree is divisible by the constant-extension
degree. -/
theorem matrixRank_dvd_residueExponent (r : Rank) (level : Nat) :
    r.matrixRank ∣ r.residueExponent level := by
  exact ⟨3 + level, by simp [Rank.residueExponent]⟩

/-- A construction-owned embedding of the degree-`d` constant field into the
selected residue field. -/
noncomputable def indexConstantEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantExtension P r →ₐ[BaseField P] ResidueField P r level := by
  classical
  exact Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [GaloisField.finrank P.q
        (by cases r <;> simp [Rank.matrixRank]),
      GaloisField.finrank P.q (Rank.residueExponent_ne_zero r level)]
    exact matrixRank_dvd_residueExponent r level))

/-- The constant field in the compatible split model.  Coordinate `i`
contains the `i`-fold inverse Frobenius conjugate. -/
noncomputable def indexConstantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) :=
  Matrix.diagonal fun i =>
    indexConstantEmbedding P r level
      (((constantFrobenius P r).symm ^ i.val) c)

/-- The diagonal constant representation is a genuine ring embedding. -/
noncomputable def indexConstantMatrixEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantExtension P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) where
  toFun := indexConstantMatrix P r level
  map_zero' := by simp [indexConstantMatrix]
  map_one' := by
    ext i j
    simp [indexConstantMatrix]
  map_add' c d := by
    rw [indexConstantMatrix, indexConstantMatrix, indexConstantMatrix,
      Matrix.diagonal_add]
    congr 1
    funext i
    simp
  map_mul' c d := by
    rw [indexConstantMatrix, indexConstantMatrix, indexConstantMatrix,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp

theorem indexConstantMatrixEmbedding_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexConstantMatrixEmbedding P r level) := by
  intro c d h
  let i0 : Fin r.matrixRank :=
    ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩
  have h00 := congrFun (congrFun h i0) i0
  simp [indexConstantMatrixEmbedding, indexConstantMatrix, i0] at h00
  exact (indexConstantEmbedding P r level).injective h00

/-- The weighted cyclic shift representing `z` at the selected place. -/
noncomputable def indexCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) := by
  cases r with
  | three =>
      exact !![0, 0, 1 + indexPlaceY P .three level;
               1, 0, 0;
               0, 1, 0]
  | four =>
      exact !![0, 0, 0, 1 + indexPlaceY P .four level;
               1, 0, 0, 0;
               0, 1, 0, 0;
               0, 0, 1, 0]

/-- Explicit inverse of the weighted cyclic shift. -/
noncomputable def indexCyclicGeneratorInverseMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) := by
  cases r with
  | three =>
      exact !![0, 1, 0;
               0, 0, 1;
               (1 + indexPlaceY P .three level)⁻¹, 0, 0]
  | four =>
      exact !![0, 1, 0, 0;
               0, 0, 1, 0;
               0, 0, 0, 1;
               (1 + indexPlaceY P .four level)⁻¹, 0, 0, 0]

theorem indexCyclicGenerator_mul_inverse
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorMatrix P r level *
      indexCyclicGeneratorInverseMatrix P r level = 1 := by
  cases r with
  | three =>
      exact shiftThree_mul_inverse _
        (indexPlaceY_one_add_ne_zero P .three level)
  | four =>
      exact shiftFour_mul_inverse _
        (indexPlaceY_one_add_ne_zero P .four level)

theorem indexCyclicGenerator_inverse_mul
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorInverseMatrix P r level *
      indexCyclicGeneratorMatrix P r level = 1 := by
  cases r with
  | three =>
      exact shiftThree_inverse_mul _
        (indexPlaceY_one_add_ne_zero P .three level)
  | four =>
      exact shiftFour_inverse_mul _
        (indexPlaceY_one_add_ne_zero P .four level)

/-- The compatible cyclic generator as an actual matrix unit. -/
noncomputable def indexCyclicGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) where
  val := indexCyclicGeneratorMatrix P r level
  inv := indexCyclicGeneratorInverseMatrix P r level
  val_inv := indexCyclicGenerator_mul_inverse P r level
  inv_val := indexCyclicGenerator_inverse_mul P r level

@[simp] theorem indexCyclicGeneratorGL_coe
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexCyclicGeneratorGL P r level :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      indexCyclicGeneratorMatrix P r level :=
  rfl

/-- The first cyclic-algebra relation at the actual selected place. -/
theorem indexCyclicGeneratorMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorMatrix P r level ^ r.matrixRank =
      (1 + indexPlaceY P r level) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
  cases r with
  | three => exact shiftThree_pow _ _
  | four => exact shiftFour_pow _ _

/-- The second cyclic-algebra relation at the actual selected place. -/
theorem indexCyclicGenerator_mul_constantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    indexCyclicGeneratorMatrix P r level *
        indexConstantMatrix P r level c =
      indexConstantMatrix P r level (constantFrobenius P r c) *
        indexCyclicGeneratorMatrix P r level := by
  have hwrap := congrArg
    (fun e : ConstantExtension P r ≃ₐ[BaseField P]
        ConstantExtension P r => indexConstantEmbedding P r level (e c))
    (constantFrobenius_symm_pow_pred P r)
  cases r with
  | three =>
      ext i j
      simp only [indexConstantMatrix]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;>
        simp [indexCyclicGeneratorMatrix] at hwrap ⊢
      rw [hwrap]
      exact mul_comm _ _
  | four =>
      ext i j
      simp only [indexConstantMatrix]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;>
        simp [indexCyclicGeneratorMatrix] at hwrap ⊢
      rw [hwrap]
      exact mul_comm _ _

/-- Nonzero constants act functorially by units in the compatible diagonal
model. -/
noncomputable def indexConstantGLHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ConstantExtension P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Units.map (indexConstantMatrixEmbedding P r level).toMonoidHom

noncomputable def indexConstantGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  indexConstantGLHom P r level u

/-- A base-field unit viewed in the selected residue field. -/
noncomputable def indexBaseScalarUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    (BaseField P)ˣ →* (ResidueField P r level)ˣ :=
  Units.map (algebraMap (BaseField P) (ResidueField P r level))

/-- Base-field constants act by scalar matrices in the compatible split
model. -/
theorem indexConstantGL_baseScalar
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : (BaseField P)ˣ) :
    indexConstantGL P r level (baseScalarUnitHom P r a) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (indexBaseScalarUnit P r level a) := by
  apply Units.ext
  ext i j
  simp [indexConstantGL, indexConstantGLHom,
    indexConstantMatrixEmbedding, indexConstantMatrix,
    baseScalarUnitHom, indexBaseScalarUnit]

/-- Frobenius on nonzero constants. -/
noncomputable def indexConstantFrobeniusUnit
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →* (ConstantExtension P r)ˣ :=
  Units.map (constantFrobenius P r).toRingEquiv.toRingHom

@[simp] theorem indexConstantGL_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    (indexConstantGL P r level u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      indexConstantMatrix P r level u :=
  rfl

/-- Bundled form of the proved skew relation. -/
theorem indexCyclicGeneratorGL_mul_indexConstantGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCyclicGeneratorGL P r level * indexConstantGL P r level u =
      indexConstantGL P r level
          (indexConstantFrobeniusUnit P r u) *
        indexCyclicGeneratorGL P r level := by
  apply Units.ext
  exact indexCyclicGenerator_mul_constantMatrix P r level
      (u : ConstantExtension P r)

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
