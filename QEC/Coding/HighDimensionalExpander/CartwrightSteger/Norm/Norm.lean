import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.FiniteImage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The Cartwright--Steger norm computation

This file formalizes the determinant calculation in LSV Proposition `normb`:
if the cyclic generator has characteristic polynomial
`X^d - (1 + y)`, then `b = 1 - z⁻¹` has determinant `y / (1 + y)`.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

/-- Matrix form of LSV Proposition `normb`, specialized only to the two
construction ranks. -/
theorem det_one_sub_inv_of_charpoly_eq_X_pow_sub_C_one_add
    {K : Type*} [Field K] (r : Rank)
    (z : Matrix.GeneralLinearGroup (Fin r.matrixRank) K) (y : K)
    (hchar : (z : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K).charpoly =
      Polynomial.X ^ r.matrixRank - Polynomial.C (1 + y)) :
    Matrix.det
        ((1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K) -
          ((z⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank) K) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) K)) =
      y / (1 + y) := by
  let Z : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K := z
  let Zi : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K :=
    (z⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank) K)
  have hZiZ : Zi * Z = 1 := by
    dsimp [Zi, Z]
    exact congrArg Units.val (inv_mul_cancel z)
  have hfactor : 1 - Zi = Zi * (Z - 1) := by
    rw [mul_sub, hZiZ, mul_one]
  have hdetZ : Matrix.det Z =
      (-1 : K) ^ r.matrixRank * (-(1 + y)) := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hchar]
    cases r <;> norm_num [Rank.matrixRank]
  have hdetOneSubZ : Matrix.det (1 - Z) = -y := by
    have h := Matrix.eval_charpoly Z 1
    rw [hchar] at h
    have hscalar :
        Matrix.scalar (Fin r.matrixRank) (1 : K) = 1 := by
      ext i j
      simp [Matrix.scalar_apply]
    rw [← hscalar]
    calc
      Matrix.det (Matrix.scalar (Fin r.matrixRank) 1 - Z) =
          (Polynomial.X ^ r.matrixRank -
            Polynomial.C (1 + y)).eval 1 := h.symm
      _ = -y := by simp
  have hdetZSubOne : Matrix.det (Z - 1) =
      (-1 : K) ^ r.matrixRank * (-y) := by
    have heq : Z - 1 = -(1 - Z) := (neg_sub 1 Z).symm
    rw [heq, Matrix.det_neg, Fintype.card_fin, hdetOneSubZ]
  have hdetZi : Matrix.det Zi = (Matrix.det Z)⁻¹ := by
    simp [Zi, Z]
  have hdetZne : Matrix.det Z ≠ 0 := by
    dsimp [Z]
    exact Units.ne_zero (Matrix.GeneralLinearGroup.det z)
  have honeaddy : 1 + y ≠ 0 := by
    intro h
    apply hdetZne
    rw [hdetZ, h]
    simp
  rw [hfactor, Matrix.det_mul, hdetZi, hdetZSubOne]
  field_simp [hdetZne, honeaddy]
  rw [hdetZ]
  cases r <;> norm_num [Rank.matrixRank] <;> ring

private theorem det_bThree {K : Type*} [Field K]
    (y : K) (hy : 1 + y ≠ 0) :
    Matrix.det
        (1 - !![0, 1, 0; 0, 0, 1; (1 + y)⁻¹, 0, 0] :
          Matrix (Fin 3) (Fin 3) K) =
      y / (1 + y) := by
  rw [Matrix.det_fin_three]
  simp
  field_simp [hy]
  ring

private theorem det_bFour {K : Type*} [Field K]
    (y : K) (hy : 1 + y ≠ 0) :
    Matrix.det
        (1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
          (1 + y)⁻¹, 0, 0, 0] : Matrix (Fin 4) (Fin 4) K) =
      y / (1 + y) := by
  let B : Matrix (Fin 4) (Fin 4) K :=
    1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
      (1 + y)⁻¹, 0, 0, 0]
  change Matrix.det B = _
  have hminor0Matrix :
      B.submatrix Fin.succ (0 : Fin 4).succAbove =
        !![1, -1, 0; 0, 1, -1; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B]
  have hminor0 : Matrix.det
      (B.submatrix Fin.succ (0 : Fin 4).succAbove) = 1 := by
    rw [hminor0Matrix, Matrix.det_fin_three]
    simp
  have hminor1Matrix :
      B.submatrix Fin.succ (1 : Fin 4).succAbove =
        !![0, -1, 0; 0, 1, -1; -(1 + y)⁻¹, 0, 1] := by
    have hlast : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, hlast]
  have hminor1 : Matrix.det
      (B.submatrix Fin.succ (1 : Fin 4).succAbove) =
        -(1 + y)⁻¹ := by
    rw [hminor1Matrix, Matrix.det_fin_three]
    simp
  have hB00 : B 0 0 = 1 := by simp [B]
  have hB01 : B 0 1 = -1 := by simp [B]
  have hB02 : B 0 2 = 0 := by simp [B]
  have hB03 : B 0 3 = 0 := by simp [B]
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_four]
  rw [hB00, hB01, hB02, hB03, hminor0, hminor1]
  simp
  field_simp [hy]
  ring

/-- The matrix formula `b = 1 - z⁻¹` after assigning a value to the central
coordinate `y`.  It is defined uniformly for the two construction ranks. -/
noncomputable def cyclicBMatrix {K : Type*} [Field K]
    (r : Rank) (y : K) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) K := by
  cases r with
  | three =>
      change Matrix (Fin 3) (Fin 3) K
      exact 1 - !![0, 1, 0; 0, 0, 1; (1 + y)⁻¹, 0, 0]
  | four =>
      change Matrix (Fin 4) (Fin 4) K
      exact 1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
        (1 + y)⁻¹, 0, 0, 0]

theorem cyclicBMatrix_det {K : Type*} [Field K]
    (r : Rank) (y : K) (hy : 1 + y ≠ 0) :
    Matrix.det (cyclicBMatrix r y) = y / (1 + y) := by
  cases r with
  | three => exact det_bThree y hy
  | four => exact det_bFour y hy

/-- LSV Proposition `normb` for the construction-owned split cyclic algebra:
the determinant (hence reduced norm) of `b = 1 - z⁻¹` is exactly
`y / (1 + y)`. -/
theorem cartwrightStegerBMatrix_det (P : BasePrime) (r : Rank) :
    Matrix.det (cartwrightStegerBMatrix P r) =
      splittingY P r / (1 + splittingY P r) := by
  cases r with
  | three =>
      exact det_bThree _ (onePlusY_ne_zero P .three)
  | four =>
      exact det_bFour _ (onePlusY_ne_zero P .four)

/-- The nonzero reduced-norm value as a unit of the splitting function
field. -/
noncomputable def cartwrightStegerNormUnit (P : BasePrime) (r : Rank) :
    (SplittingFunctionField P r)ˣ :=
  Units.mk0 (splittingY P r / (1 + splittingY P r))
    (div_ne_zero (splittingY_ne_zero P r) (onePlusY_ne_zero P r))

@[simp] theorem cartwrightStegerNormUnit_coe (P : BasePrime) (r : Rank) :
    (cartwrightStegerNormUnit P r : SplittingFunctionField P r) =
      splittingY P r / (1 + splittingY P r) :=
  rfl

/-- Unit-valued version of LSV Proposition `normb`. -/
theorem cartwrightStegerB_det (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup.det (cartwrightStegerB P r) =
      cartwrightStegerNormUnit P r := by
  apply Units.ext
  exact cartwrightStegerBMatrix_det P r

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
