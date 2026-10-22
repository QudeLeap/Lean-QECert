import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingStabilizer

/-!
# The infinity conjugation action of the Cartwright--Steger generators

This module formalizes the global cyclic-algebra identities used in
LSV05b Definition 4.7, equation (9), and Proposition 4.8.  In particular,
the identities below are equalities in the constructed matrix algebra;
they do not accept a triangularity or stabilizer conclusion as data.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- The constant-field representation in the global splitting matrix
algebra, bundled as a group homomorphism. -/
noncomputable def constantUnitMatrixHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Units.map (constantMatrixEmbedding P r).toMonoidHom

@[simp]
theorem constantUnitMatrixHom_apply
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    constantUnitMatrixHom P r u = constantUnitMatrix P r u :=
  rfl

theorem constantUnitMatrix_inv
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantUnitMatrix P r u)⁻¹ = constantUnitMatrix P r u⁻¹ := by
  change (constantUnitMatrixHom P r u)⁻¹ = constantUnitMatrixHom P r u⁻¹
  rw [map_inv]

/-- Conjugation by the global cyclic generator realizes arithmetic
Frobenius on constant units. -/
theorem cyclicGenerator_conj_constantUnit
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    cyclicGenerator P r * constantUnitMatrix P r u *
        (cyclicGenerator P r)⁻¹ =
      constantUnitMatrix P r (constantFrobeniusUnitEquiv P r u) := by
  apply mul_right_cancel (b := cyclicGenerator P r)
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply Units.ext
  simp only [Units.val_mul]
  rw [cyclicGenerator_val, constantUnitMatrix_val,
    constantUnitMatrix_val, constantFrobeniusUnitEquiv_coe]
  exact cyclicGenerator_mul_constantMatrix P r u

/-- Natural powers of the global cyclic generator realize the
corresponding powers of Frobenius. -/
theorem cyclicGenerator_pow_conj_constantUnit
    (P : BasePrime) (r : Rank) (j : ℕ)
    (u : (ConstantExtension P r)ˣ) :
    cyclicGenerator P r ^ j * constantUnitMatrix P r u *
        (cyclicGenerator P r ^ j)⁻¹ =
      constantUnitMatrix P r
        ((constantFrobeniusUnitEquiv P r ^ j) u) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
      calc
        cyclicGenerator P r ^ (j + 1) * constantUnitMatrix P r u *
              (cyclicGenerator P r ^ (j + 1))⁻¹ =
            cyclicGenerator P r ^ j *
              (cyclicGenerator P r * constantUnitMatrix P r u *
                (cyclicGenerator P r)⁻¹) *
              (cyclicGenerator P r ^ j)⁻¹ := by
                rw [pow_succ]
                group
        _ = cyclicGenerator P r ^ j *
              constantUnitMatrix P r
                (constantFrobeniusUnitEquiv P r u) *
              (cyclicGenerator P r ^ j)⁻¹ := by
                rw [cyclicGenerator_conj_constantUnit]
        _ = constantUnitMatrix P r
              ((constantFrobeniusUnitEquiv P r ^ j)
                (constantFrobeniusUnitEquiv P r u)) :=
              ih (constantFrobeniusUnitEquiv P r u)
        _ = constantUnitMatrix P r
              ((constantFrobeniusUnitEquiv P r ^ (j + 1)) u) := by
                rw [pow_succ, MulAut.mul_apply]

/-- Matrix skew relation for every natural power and every constant,
including zero.  This is the workhorse for expanding equation (9). -/
theorem cyclicGeneratorMatrix_pow_mul_constantMatrix
    (P : BasePrime) (r : Rank) (j : ℕ) (c : ConstantExtension P r) :
    cyclicGeneratorMatrix P r ^ j * constantMatrix P r c =
      constantMatrix P r ((constantFrobenius P r ^ j) c) *
        cyclicGeneratorMatrix P r ^ j := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
      calc
        cyclicGeneratorMatrix P r ^ (j + 1) * constantMatrix P r c =
            cyclicGeneratorMatrix P r ^ j *
              (cyclicGeneratorMatrix P r * constantMatrix P r c) := by
                rw [pow_succ, mul_assoc]
        _ = cyclicGeneratorMatrix P r ^ j *
              (constantMatrix P r (constantFrobenius P r c) *
                cyclicGeneratorMatrix P r) := by
                  rw [cyclicGenerator_mul_constantMatrix]
        _ = (cyclicGeneratorMatrix P r ^ j *
              constantMatrix P r (constantFrobenius P r c)) *
                cyclicGeneratorMatrix P r := by rw [mul_assoc]
        _ = constantMatrix P r
              ((constantFrobenius P r ^ j) (constantFrobenius P r c)) *
                cyclicGeneratorMatrix P r ^ j * cyclicGeneratorMatrix P r := by
                  rw [ih]
        _ = constantMatrix P r
              ((constantFrobenius P r ^ (j + 1)) c) *
                cyclicGeneratorMatrix P r ^ (j + 1) := by
                  rw [pow_succ, AlgEquiv.mul_apply, pow_succ, mul_assoc]

/-- The inverse cyclic generator obeys the inverse-Frobenius skew
relation on arbitrary constants. -/
theorem cyclicGeneratorInverseMatrix_mul_constantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    cyclicGeneratorInverseMatrix P r * constantMatrix P r c =
      constantMatrix P r ((constantFrobenius P r).symm c) *
        cyclicGeneratorInverseMatrix P r := by
  have hforward := cyclicGenerator_mul_constantMatrix P r
    ((constantFrobenius P r).symm c)
  rw [(constantFrobenius P r).apply_symm_apply] at hforward
  calc
    cyclicGeneratorInverseMatrix P r * constantMatrix P r c =
        cyclicGeneratorInverseMatrix P r *
          (constantMatrix P r c * cyclicGeneratorMatrix P r) *
          cyclicGeneratorInverseMatrix P r := by
            simp [mul_assoc, cyclicGenerator_mul_inverse]
    _ = cyclicGeneratorInverseMatrix P r *
          (cyclicGeneratorMatrix P r *
            constantMatrix P r ((constantFrobenius P r).symm c)) *
          cyclicGeneratorInverseMatrix P r := by rw [hforward]
    _ = constantMatrix P r ((constantFrobenius P r).symm c) *
          cyclicGeneratorInverseMatrix P r := by
            rw [← mul_assoc, cyclicGenerator_inverse_mul, one_mul]

/-- The inverse cyclic generator is the normalized `(d - 1)`-st power.
This converts the only negative cyclic exponent in equation (9) into the
finite basis range `0, ..., d - 1`. -/
theorem cyclicGeneratorInverseMatrix_eq_inv_smul_pow_pred
    (P : BasePrime) (r : Rank) :
    cyclicGeneratorInverseMatrix P r =
      (onePlusY P r)⁻¹ •
        cyclicGeneratorMatrix P r ^ (r.matrixRank - 1) := by
  apply Matrix.mul_left_injective_of_inv
    (cyclicGeneratorMatrix P r) (cyclicGeneratorInverseMatrix P r)
    (cyclicGenerator_mul_inverse P r)
  change
    cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r =
      ((onePlusY P r)⁻¹ •
        cyclicGeneratorMatrix P r ^ (r.matrixRank - 1)) *
          cyclicGeneratorMatrix P r
  rw [cyclicGenerator_inverse_mul]
  rw [smul_mul_assoc, ← pow_succ]
  have hrankPos : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrankPos))]
  rw [cyclicGenerator_pow_matrixRank]
  simp [smul_smul, onePlusY_ne_zero]

/-- Crossing the finite cyclic basis boundary contributes the central
factor `1 + y`. -/
theorem cyclicGeneratorMatrix_pow_rank_add
    (P : BasePrime) (r : Rank) (n : ℕ) :
    cyclicGeneratorMatrix P r ^ (r.matrixRank + n) =
      (onePlusY P r) • cyclicGeneratorMatrix P r ^ n := by
  rw [pow_add, cyclicGenerator_pow_matrixRank]
  rw [smul_mul_assoc, one_mul]

/-- Cancellation of the inverse cyclic generator against a positive
power, in the exact predecessor form used by equation (9). -/
theorem cyclicGeneratorInverseMatrix_mul_pow_succ
    (P : BasePrime) (r : Rank) (n : ℕ) :
    cyclicGeneratorInverseMatrix P r *
        cyclicGeneratorMatrix P r ^ (n + 1) =
      cyclicGeneratorMatrix P r ^ n := by
  have hgl :
      (cyclicGenerator P r)⁻¹ * cyclicGenerator P r ^ (n + 1) =
        cyclicGenerator P r ^ n := by group
  have hmatrix := congrArg Units.val hgl
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, cyclicGenerator_val] at hmatrix
  exact hmatrix

/-- Split a shifted full cyclic-basis sum at the wrap point.  The wrapped
tail contributes exactly one central factor `1 + y`; no asymptotic or
valuation argument is hidden in this reindexing lemma. -/
theorem sum_mul_cyclicGeneratorMatrix_pow_shift
    (P : BasePrime) (r : Rank) (k : ℕ) (hk : k ≤ r.matrixRank)
    (A : ℕ → Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    ∑ i ∈ Finset.range r.matrixRank,
        A i * cyclicGeneratorMatrix P r ^ (k + i) =
      (∑ i ∈ Finset.range (r.matrixRank - k),
        A i * cyclicGeneratorMatrix P r ^ (k + i)) +
      (onePlusY P r) •
        ∑ j ∈ Finset.range k,
          A (r.matrixRank - k + j) * cyclicGeneratorMatrix P r ^ j := by
  have hrank : r.matrixRank - k + k = r.matrixRank :=
    Nat.sub_add_cancel hk
  have hrange :
      Finset.range r.matrixRank = Finset.range (r.matrixRank - k + k) :=
    congrArg Finset.range hrank.symm
  rw [hrange, Finset.sum_range_add]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hexponent : k + (r.matrixRank - k + j) = r.matrixRank + j := by
    omega
  rw [hexponent, cyclicGeneratorMatrix_pow_rank_add]
  exact mul_smul_comm (onePlusY P r) (A (r.matrixRank - k + j))
    (cyclicGeneratorMatrix P r ^ j)

/-- The coefficient `u / phi^k(u)` appearing in LSV05b equation (9). -/
noncomputable def infinityCyclicCoefficient
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    (ConstantExtension P r)ˣ :=
  u * ((constantFrobeniusUnitEquiv P r ^ k) u)⁻¹

/-- Coercing the cyclic coefficient gives the corresponding quotient in
the constant field. -/
theorem infinityCyclicCoefficient_coe
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    (infinityCyclicCoefficient P r u k : ConstantExtension P r) =
      (u : ConstantExtension P r) *
        ((constantFrobenius P r ^ k) (u : ConstantExtension P r))⁻¹ := by
  simp only [infinityCyclicCoefficient, Units.val_mul, Units.val_inv_eq_inv_val,
    constantFrobeniusUnitEquiv_pow_coe]

/-- Frobenius powers are periodic with the cyclic-algebra degree. -/
theorem constantFrobenius_pow_rank_add_apply
    (P : BasePrime) (r : Rank) (n : ℕ) (c : ConstantExtension P r) :
    (constantFrobenius P r ^ (r.matrixRank + n)) c =
      (constantFrobenius P r ^ n) c := by
  rw [pow_add, constantFrobenius_pow_matrixRank]
  rfl

/-- The inverse-expansion coefficients are periodic with period `d`. -/
theorem infinityCyclicCoefficient_rank_add
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (n : ℕ) :
    infinityCyclicCoefficient P r u (r.matrixRank + n) =
      infinityCyclicCoefficient P r u n := by
  apply Units.ext
  rw [infinityCyclicCoefficient_coe, infinityCyclicCoefficient_coe]
  rw [constantFrobenius_pow_rank_add_apply]

@[simp]
theorem infinityCyclicCoefficient_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    infinityCyclicCoefficient P r u 0 = 1 := by
  rw [infinityCyclicCoefficient]
  simp

@[simp]
theorem infinityCyclicCoefficient_rank
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    infinityCyclicCoefficient P r u r.matrixRank = 1 := by
  simpa using infinityCyclicCoefficient_rank_add P r u 0

/-- Frobenius shifts both indices in a cyclic coefficient. -/
theorem constantFrobenius_pow_infinityCyclicCoefficient
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) :
    (constantFrobenius P r ^ k)
        (infinityCyclicCoefficient P r u i : ConstantExtension P r) =
      (constantFrobenius P r ^ k) (u : ConstantExtension P r) *
        ((constantFrobenius P r ^ (k + i))
          (u : ConstantExtension P r))⁻¹ := by
  rw [infinityCyclicCoefficient_coe]
  rw [map_mul]
  rw [map_inv₀]
  have hcomp :
      (constantFrobenius P r ^ k)
          ((constantFrobenius P r ^ i) (u : ConstantExtension P r)) =
        (constantFrobenius P r ^ (k + i))
          (u : ConstantExtension P r) := by
    rw [← AlgEquiv.mul_apply, ← pow_add]
  rw [hcomp]

/-- Applying inverse Frobenius removes one positive Frobenius step. -/
theorem constantFrobenius_symm_pow_succ_apply
    (P : BasePrime) (r : Rank) (n : ℕ) (c : ConstantExtension P r) :
    (constantFrobenius P r).symm
        ((constantFrobenius P r ^ (n + 1)) c) =
      (constantFrobenius P r ^ n) c := by
  have hcancel :
      (constantFrobenius P r)⁻¹ *
          constantFrobenius P r ^ (n + 1) =
        constantFrobenius P r ^ n := by
    rw [pow_succ]
    group
  change
    ((constantFrobenius P r)⁻¹ *
        constantFrobenius P r ^ (n + 1)) c = _
  rw [hcancel]

/-- The shifted predecessor coefficient has the same terminal denominator
as the leading coefficient. -/
theorem constantFrobenius_symm_pow_infinityCyclicCoefficient_succ
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) :
    (constantFrobenius P r).symm
        ((constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u (i + 1) :
            ConstantExtension P r)) =
      (constantFrobenius P r).symm
          ((constantFrobenius P r ^ k) (u : ConstantExtension P r)) *
        ((constantFrobenius P r ^ (k + i))
          (u : ConstantExtension P r))⁻¹ := by
  rw [constantFrobenius_pow_infinityCyclicCoefficient]
  rw [map_mul, map_inv₀]
  have hexponent : k + (i + 1) = (k + i) + 1 := by omega
  rw [hexponent, constantFrobenius_symm_pow_succ_apply]

/-- The source coefficient `f_{u,k}(ζ)` in LSV05b equation (9).  Integer
powers are used so that the displayed `k - 1` and `-1` exponents are
represented literally, including the case `k = 0`. -/
noncomputable def infinityConjugationCoefficient
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ConstantExtension P r :=
  ((constantFrobenius P r ^ (k : ℤ)) (u : ConstantExtension P r) /
      (u : ConstantExtension P r)) * ζ -
    ((constantFrobenius P r ^ ((k : ℤ) - 1))
        (u : ConstantExtension P r) /
      (constantFrobenius P r ^ (-1 : ℤ))
        (u : ConstantExtension P r)) *
      (constantFrobenius P r ^ (-1 : ℤ)) ζ

/-- At `k = 0`, the source coefficient reduces to
`ζ - phi⁻¹(ζ)`, independently of `u`. -/
theorem infinityConjugationCoefficient_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (ζ : ConstantExtension P r) :
    infinityConjugationCoefficient P r u 0 ζ =
      ζ - (constantFrobenius P r ^ (-1 : ℤ)) ζ := by
  rw [infinityConjugationCoefficient]
  norm_num

/-- A natural-power form of the source coefficient, arranged for the
finite cyclic-basis calculation. -/
noncomputable def infinityConjugationCoefficientNat
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ConstantExtension P r :=
  ((constantFrobenius P r ^ k) (u : ConstantExtension P r) /
      (u : ConstantExtension P r)) * ζ -
    ((constantFrobenius P r).symm
          ((constantFrobenius P r ^ k) (u : ConstantExtension P r)) /
        (constantFrobenius P r).symm (u : ConstantExtension P r)) *
      (constantFrobenius P r).symm ζ

/-- The natural-power coefficient is exactly the literal integer-power
coefficient printed in LSV05b equation (9). -/
theorem infinityConjugationCoefficientNat_eq
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityConjugationCoefficientNat P r u k ζ =
      infinityConjugationCoefficient P r u k ζ := by
  have hpred :
      constantFrobenius P r ^ ((k : ℤ) - 1) =
        (constantFrobenius P r)⁻¹ *
          constantFrobenius P r ^ (k : ℤ) := by
    group
  rw [infinityConjugationCoefficientNat, infinityConjugationCoefficient]
  rw [hpred, AlgEquiv.mul_apply]
  simp only [zpow_natCast, zpow_neg_one]
  rfl

/-- The equation-(9) correction sum, with either upper bound `k` or `d`.
Its coefficients are completely computed from `u`, `k`, and `ζ`. -/
noncomputable def infinityConjugationCorrectionSum
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  ∑ i ∈ Finset.range bound,
    constantMatrix P r
        (infinityConjugationCoefficient P r u k ζ *
          (infinityCyclicCoefficient P r u i : ConstantExtension P r)) *
      cyclicGeneratorMatrix P r ^ i

@[simp]
theorem infinityConjugationCorrectionSum_bound_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityConjugationCorrectionSum P r u k 0 ζ = 0 := by
  simp [infinityConjugationCorrectionSum]

/-- The precise right-hand side asserted by LSV05b equation (9). -/
noncomputable def infinityConjugationFormula
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k +
    infinityConjugationCorrectionSum P r u k k ζ +
    (splittingY P r)⁻¹ •
      infinityConjugationCorrectionSum P r u k r.matrixRank ζ

/-- Constant conjugation of `z^k` produces exactly the source coefficient
`u / phi^k(u)`. -/
theorem constantUnit_conj_cyclicGenerator_pow
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    constantUnitMatrix P r u * cyclicGenerator P r ^ k *
        (constantUnitMatrix P r u)⁻¹ =
      constantUnitMatrix P r (infinityCyclicCoefficient P r u k) *
        cyclicGenerator P r ^ k := by
  have huInv := cyclicGenerator_pow_conj_constantUnit P r k u⁻¹
  have hconstantInv :
      (constantUnitMatrix P r u)⁻¹ = constantUnitMatrix P r u⁻¹ := by
    change (constantUnitMatrixHom P r u)⁻¹ = constantUnitMatrixHom P r u⁻¹
    rw [map_inv]
  have hFrobeniusInv :
      (constantFrobeniusUnitEquiv P r ^ k) u⁻¹ =
        ((constantFrobeniusUnitEquiv P r ^ k) u)⁻¹ := by
    exact map_inv _ _
  have hconstantMul
      (a b : (ConstantExtension P r)ˣ) :
      constantUnitMatrix P r a * constantUnitMatrix P r b =
        constantUnitMatrix P r (a * b) := by
    change constantUnitMatrixHom P r a * constantUnitMatrixHom P r b =
      constantUnitMatrixHom P r (a * b)
    rw [map_mul]
  calc
    constantUnitMatrix P r u * cyclicGenerator P r ^ k *
          (constantUnitMatrix P r u)⁻¹ =
        constantUnitMatrix P r u *
          (cyclicGenerator P r ^ k * constantUnitMatrix P r u⁻¹ *
            (cyclicGenerator P r ^ k)⁻¹) *
          cyclicGenerator P r ^ k := by
            rw [hconstantInv]
            group
    _ = constantUnitMatrix P r u *
          constantUnitMatrix P r
            ((constantFrobeniusUnitEquiv P r ^ k) u⁻¹) *
          cyclicGenerator P r ^ k := by rw [huInv]
    _ = constantUnitMatrix P r (infinityCyclicCoefficient P r u k) *
          cyclicGenerator P r ^ k := by
            rw [hFrobeniusInv, infinityCyclicCoefficient, hconstantMul]

/-- The global Cartwright--Steger element `u b u⁻¹` for an arbitrary
nonzero constant, before quotienting constants by base scalars. -/
noncomputable def constantConjugatedCartwrightStegerB
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantUnitMatrix P r u * cartwrightStegerB P r *
    (constantUnitMatrix P r u)⁻¹

/-- The arbitrary-unit conjugate specializes definitionally to every
construction-owned Cartwright--Steger generator. -/
theorem cartwrightStegerGenerator_eq_constantConjugatedB
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    cartwrightStegerGenerator P r x =
      constantConjugatedCartwrightStegerB P r
        (constantClassRepresentative P r x) :=
  rfl

/-- The coefficient of `z⁻¹` in `u b u⁻¹`, under the proved convention
`z c z⁻¹ = phi(c)`. -/
noncomputable def infinityCyclicInverseCoefficient
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    ConstantExtension P r :=
  (u : ConstantExtension P r) *
    ((constantFrobenius P r).symm (u : ConstantExtension P r))⁻¹

/-- Consecutive tail coefficients differ by the exact equation-(9)
coefficient.  The resulting cyclic coefficient is indexed by the actual
exponent `k + i`, before reduction modulo the cyclic degree. -/
theorem infinityTailCoefficient_sub_succ
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    ζ * (constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u i : ConstantExtension P r) -
        (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
          (constantFrobenius P r).symm
            ((constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u (i + 1) :
                ConstantExtension P r)) =
      infinityConjugationCoefficient P r u k ζ *
        (infinityCyclicCoefficient P r u (k + i) :
          ConstantExtension P r) := by
  rw [constantFrobenius_pow_infinityCyclicCoefficient]
  rw [constantFrobenius_symm_pow_infinityCyclicCoefficient_succ]
  rw [infinityCyclicCoefficient_coe]
  rw [← infinityConjugationCoefficientNat_eq]
  rw [infinityConjugationCoefficientNat, infinityCyclicInverseCoefficient]
  field_simp

/-- The conjugated generator itself is `1 - (u / phi⁻¹(u)) z⁻¹` in the
constructed global matrix algebra. -/
theorem constantConjugatedCartwrightStegerB_val
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantConjugatedCartwrightStegerB P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      1 - constantMatrix P r (infinityCyclicInverseCoefficient P r u) *
        cyclicGeneratorInverseMatrix P r := by
  rw [constantConjugatedCartwrightStegerB, constantUnitMatrix_inv]
  change
    constantMatrix P r u * cartwrightStegerBMatrix P r *
        constantMatrix P r
          ((u⁻¹ : (ConstantExtension P r)ˣ) : ConstantExtension P r) = _
  rw [cartwrightStegerBMatrix, mul_sub, sub_mul, mul_one]
  have hconstantCancel :
      constantMatrix P r u *
          constantMatrix P r
            ((u⁻¹ : (ConstantExtension P r)ˣ) : ConstantExtension P r) = 1 := by
    calc
      constantMatrix P r (u : ConstantExtension P r) *
            constantMatrix P r
              ((u⁻¹ : (ConstantExtension P r)ˣ) : ConstantExtension P r) =
          constantMatrix P r
            ((u : ConstantExtension P r) *
              ((u⁻¹ : (ConstantExtension P r)ˣ) : ConstantExtension P r)) := by
                exact (map_mul (constantMatrixEmbedding P r) _ _).symm
      _ = constantMatrix P r 1 := by simp
      _ = 1 := (constantMatrixEmbedding P r).map_one
  rw [hconstantCancel]
  congr 1
  rw [mul_assoc, cyclicGeneratorInverseMatrix_mul_constantMatrix,
    ← mul_assoc]
  change
    constantMatrixEmbedding P r (u : ConstantExtension P r) *
          constantMatrixEmbedding P r
            ((constantFrobenius P r).symm
              ((u⁻¹ : (ConstantExtension P r)ˣ) : ConstantExtension P r)) *
        cyclicGeneratorInverseMatrix P r =
      constantMatrixEmbedding P r (infinityCyclicInverseCoefficient P r u) *
        cyclicGeneratorInverseMatrix P r
  rw [← map_mul]
  congr 2
  simp [infinityCyclicInverseCoefficient]

/-- Left multiplication by the conjugated generator on a cyclic monomial,
before inserting the proved finite-sum inverse. -/
theorem constantConjugatedCartwrightStegerB_mul_monomial
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    (constantConjugatedCartwrightStegerB P r u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k) =
      constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k -
        constantMatrix P r
          (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
          cyclicGeneratorInverseMatrix P r *
            cyclicGeneratorMatrix P r ^ k := by
  rw [constantConjugatedCartwrightStegerB_val, sub_mul, one_mul]
  rw [mul_assoc]
  rw [← mul_assoc (cyclicGeneratorInverseMatrix P r)
    (constantMatrix P r ζ) (cyclicGeneratorMatrix P r ^ k)]
  rw [cyclicGeneratorInverseMatrix_mul_constantMatrix]
  rw [← mul_assoc
    (constantMatrix P r (infinityCyclicInverseCoefficient P r u))
    (constantMatrix P r ((constantFrobenius P r).symm ζ) *
      cyclicGeneratorInverseMatrix P r)
    (cyclicGeneratorMatrix P r ^ k)]
  rw [← mul_assoc
    (constantMatrix P r (infinityCyclicInverseCoefficient P r u))
    (constantMatrix P r ((constantFrobenius P r).symm ζ))
    (cyclicGeneratorInverseMatrix P r)]
  change
    constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k -
        (constantMatrixEmbedding P r (infinityCyclicInverseCoefficient P r u) *
          constantMatrixEmbedding P r ((constantFrobenius P r).symm ζ)) *
          cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r ^ k = _
  rw [← map_mul]
  rfl

/-- Inverting the conjugated generator preserves the outer constant
conjugation. -/
theorem constantConjugatedCartwrightStegerB_inv
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantConjugatedCartwrightStegerB P r u)⁻¹ =
      constantUnitMatrix P r u * (cartwrightStegerB P r)⁻¹ *
        constantUnitMatrix P r u⁻¹ := by
  rw [constantConjugatedCartwrightStegerB]
  simp only [mul_inv_rev, inv_inv, constantUnitMatrix_inv]
  exact (mul_assoc _ _ _).symm

/-- The source finite sum in
`b_u⁻¹ = 1 + y⁻¹ Σ_i (u / phi^i(u)) z^i`. -/
noncomputable def constantConjugatedBInverseExpansion
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  1 + (splittingY P r)⁻¹ •
    ∑ i ∈ Finset.range r.matrixRank,
      constantMatrix P r (infinityCyclicCoefficient P r u i) *
        cyclicGeneratorMatrix P r ^ i

/-- The finite cyclic-basis tail of the inverse expansion, before its
explicit `1/y` scalar. -/
noncomputable def constantConjugatedBInverseTail
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  ∑ i ∈ Finset.range r.matrixRank,
    constantMatrix P r (infinityCyclicCoefficient P r u i) *
      cyclicGeneratorMatrix P r ^ i

theorem constantConjugatedBInverseExpansion_eq
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    constantConjugatedBInverseExpansion P r u =
      1 + (splittingY P r)⁻¹ •
        constantConjugatedBInverseTail P r u := by
  rfl

/-- Distribute a computed leading term and defect across an explicit
`1 + s S` inverse.  This noncommutative identity leaves the scalar outside
the matrix products, ready for the cyclic wrap-sum lemma. -/
theorem matrix_sub_mul_one_add_smul
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (X N S : Matrix n n K) (s : K) :
    (X - N) * (1 + s • S) =
      X - N + s • (X * S - N * S) := by
  rw [mul_add, mul_one, mul_smul_comm, sub_mul, smul_sub]

/-- LSV05b's displayed inverse formula for every constant conjugate of
`b`, proved in the constructed global matrix algebra. -/
theorem constantConjugatedCartwrightStegerB_inv_val
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      constantConjugatedBInverseExpansion P r u := by
  rw [constantConjugatedCartwrightStegerB_inv]
  simp only [Units.val_mul]
  change
    constantMatrix P r u * cartwrightStegerBInverseMatrix P r *
        constantMatrix P r (u⁻¹ : (ConstantExtension P r)ˣ) =
      constantConjugatedBInverseExpansion P r u
  rw [cartwrightStegerBInverseMatrix]
  have hconstantCancel :
      constantMatrix P r u *
          constantMatrix P r ((u⁻¹ : (ConstantExtension P r)ˣ) :
            ConstantExtension P r) = 1 := by
    have hgl :
        constantUnitMatrix P r u * constantUnitMatrix P r u⁻¹ = 1 := by
      rw [← constantUnitMatrix_inv]
      exact mul_inv_cancel _
    simpa only [Units.val_mul, constantUnitMatrix_val, Units.val_one] using
      congrArg Units.val hgl
  have hmonomial (i : ℕ) :
      constantMatrix P r u * cyclicGeneratorMatrix P r ^ i *
          constantMatrix P r ((u⁻¹ : (ConstantExtension P r)ˣ) :
            ConstantExtension P r) =
        constantMatrix P r (infinityCyclicCoefficient P r u i) *
          cyclicGeneratorMatrix P r ^ i := by
    have hgl := constantUnit_conj_cyclicGenerator_pow P r u i
    rw [constantUnitMatrix_inv] at hgl
    simpa only [Units.val_mul, constantUnitMatrix_val, cyclicGenerator_val,
      Units.val_pow_eq_pow_val] using congrArg Units.val hgl
  rw [constantConjugatedBInverseExpansion]
  calc
    constantMatrix P r u *
          (1 + (splittingY P r)⁻¹ •
            ∑ i ∈ Finset.range r.matrixRank,
              cyclicGeneratorMatrix P r ^ i) *
        constantMatrix P r ((u⁻¹ : (ConstantExtension P r)ˣ) :
          ConstantExtension P r) =
      constantMatrix P r u *
          constantMatrix P r ((u⁻¹ : (ConstantExtension P r)ˣ) :
            ConstantExtension P r) +
        (splittingY P r)⁻¹ •
          (constantMatrix P r u *
            (∑ i ∈ Finset.range r.matrixRank,
              cyclicGeneratorMatrix P r ^ i) *
            constantMatrix P r ((u⁻¹ : (ConstantExtension P r)ˣ) :
              ConstantExtension P r)) := by
              rw [mul_add, add_mul, mul_one]
              rw [mul_smul_comm, smul_mul_assoc]
    _ = 1 + (splittingY P r)⁻¹ •
          (∑ i ∈ Finset.range r.matrixRank,
              constantMatrix P r u * cyclicGeneratorMatrix P r ^ i *
              constantMatrix P r ((u⁻¹ : (ConstantExtension P r)ˣ) :
                ConstantExtension P r)) := by
            rw [hconstantCancel]
            simp only [Finset.mul_sum, Finset.sum_mul]
    _ = 1 + (splittingY P r)⁻¹ •
          ∑ i ∈ Finset.range r.matrixRank,
            constantMatrix P r (infinityCyclicCoefficient P r u i) *
              cyclicGeneratorMatrix P r ^ i := by
            congr 2
            apply Finset.sum_congr rfl
            intro i hi
            exact hmonomial i

/-- Exact conjugation before collecting equal cyclic powers.  Both
factors on the right have already been computed from the construction;
the remaining equation-(9) step is finite-sum reindexing and coefficient
collection. -/
theorem constantConjugatedCartwrightStegerB_conj_monomial_preExpansion
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k)) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k -
        constantMatrix P r
          (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
          cyclicGeneratorInverseMatrix P r *
            cyclicGeneratorMatrix P r ^ k) *
        constantConjugatedBInverseExpansion P r u := by
  rw [constantConjugatedCartwrightStegerB_mul_monomial]
  rw [constantConjugatedCartwrightStegerB_inv_val]

/-- The leading cyclic monomial in equation (9). -/
noncomputable def infinityLeadingMonomial
    (P : BasePrime) (r : Rank) (k : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k

/-- The single predecessor defect produced by left multiplication with
`u b u⁻¹`. -/
noncomputable def infinityDefectMonomial
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      (infinityCyclicInverseCoefficient P r u *
        (constantFrobenius P r).symm ζ) *
    cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r ^ k

/-- Separate the exact conjugation into its non-`1/y` part and its
explicit `1/y` tail. -/
theorem constantConjugatedCartwrightStegerB_conj_monomial_split
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        infinityLeadingMonomial P r k ζ) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityLeadingMonomial P r k ζ -
          infinityDefectMonomial P r u k ζ +
        (splittingY P r)⁻¹ •
          (infinityLeadingMonomial P r k ζ *
              constantConjugatedBInverseTail P r u -
            infinityDefectMonomial P r u k ζ *
              constantConjugatedBInverseTail P r u) := by
  rw [infinityLeadingMonomial, infinityDefectMonomial]
  rw [constantConjugatedCartwrightStegerB_conj_monomial_preExpansion]
  rw [constantConjugatedBInverseExpansion_eq]
  exact matrix_sub_mul_one_add_smul _ _ _ _

/-- Expand the leading monomial against the inverse tail using the skew
relation. -/
theorem infinityLeadingMonomial_mul_inverseTail
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityLeadingMonomial P r k ζ *
        constantConjugatedBInverseTail P r u =
      ∑ i ∈ Finset.range r.matrixRank,
        constantMatrix P r
            (ζ * (constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u i : ConstantExtension P r)) *
          cyclicGeneratorMatrix P r ^ (k + i) := by
  rw [infinityLeadingMonomial, constantConjugatedBInverseTail]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc (constantMatrix P r ζ)
    (cyclicGeneratorMatrix P r ^ k)
    (constantMatrix P r
        (infinityCyclicCoefficient P r u i : ConstantExtension P r) *
      cyclicGeneratorMatrix P r ^ i)]
  rw [← mul_assoc (cyclicGeneratorMatrix P r ^ k)
    (constantMatrix P r
      (infinityCyclicCoefficient P r u i : ConstantExtension P r))
    (cyclicGeneratorMatrix P r ^ i)]
  rw [cyclicGeneratorMatrix_pow_mul_constantMatrix]
  rw [mul_assoc
    (constantMatrix P r
      ((constantFrobenius P r ^ k)
        (infinityCyclicCoefficient P r u i : ConstantExtension P r)))
    (cyclicGeneratorMatrix P r ^ k)
    (cyclicGeneratorMatrix P r ^ i)]
  rw [← mul_assoc]
  change
    (constantMatrixEmbedding P r ζ *
        constantMatrixEmbedding P r
          ((constantFrobenius P r ^ k)
            (infinityCyclicCoefficient P r u i : ConstantExtension P r))) *
        (cyclicGeneratorMatrix P r ^ k * cyclicGeneratorMatrix P r ^ i) = _
  rw [← map_mul, ← pow_add]
  simp only [constantMatrixEmbedding_apply]

/-- Expand the predecessor defect against the inverse tail.  The inverse
skew relation contributes the literal `phi⁻¹` appearing in equation (9). -/
theorem infinityDefectMonomial_mul_inverseTail
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityDefectMonomial P r u k ζ *
        constantConjugatedBInverseTail P r u =
      ∑ i ∈ Finset.range r.matrixRank,
        constantMatrix P r
            ((infinityCyclicInverseCoefficient P r u *
                (constantFrobenius P r).symm ζ) *
              (constantFrobenius P r).symm
                ((constantFrobenius P r ^ k)
                  (infinityCyclicCoefficient P r u i :
                    ConstantExtension P r))) *
          cyclicGeneratorInverseMatrix P r *
            cyclicGeneratorMatrix P r ^ (k + i) := by
  rw [infinityDefectMonomial, constantConjugatedBInverseTail]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc
    (constantMatrix P r
        (infinityCyclicInverseCoefficient P r u *
          (constantFrobenius P r).symm ζ) *
      cyclicGeneratorInverseMatrix P r)
    (cyclicGeneratorMatrix P r ^ k)
    (constantMatrix P r
        (infinityCyclicCoefficient P r u i : ConstantExtension P r) *
      cyclicGeneratorMatrix P r ^ i)]
  rw [← mul_assoc (cyclicGeneratorMatrix P r ^ k)
    (constantMatrix P r
      (infinityCyclicCoefficient P r u i : ConstantExtension P r))
    (cyclicGeneratorMatrix P r ^ i)]
  rw [cyclicGeneratorMatrix_pow_mul_constantMatrix]
  rw [mul_assoc
    (constantMatrix P r
      ((constantFrobenius P r ^ k)
        (infinityCyclicCoefficient P r u i : ConstantExtension P r)))
    (cyclicGeneratorMatrix P r ^ k)
    (cyclicGeneratorMatrix P r ^ i)]
  rw [mul_assoc
    (constantMatrix P r
      (infinityCyclicInverseCoefficient P r u *
        (constantFrobenius P r).symm ζ))
    (cyclicGeneratorInverseMatrix P r)]
  rw [← mul_assoc (cyclicGeneratorInverseMatrix P r),
    cyclicGeneratorInverseMatrix_mul_constantMatrix]
  rw [mul_assoc
    (constantMatrix P r
      ((constantFrobenius P r).symm
        ((constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u i : ConstantExtension P r))))
    (cyclicGeneratorInverseMatrix P r)]
  rw [← mul_assoc
    (constantMatrix P r
      (infinityCyclicInverseCoefficient P r u *
        (constantFrobenius P r).symm ζ))
    (constantMatrix P r
      ((constantFrobenius P r).symm
        ((constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u i : ConstantExtension P r))))
    (cyclicGeneratorInverseMatrix P r *
      (cyclicGeneratorMatrix P r ^ k * cyclicGeneratorMatrix P r ^ i))]
  change
    (constantMatrixEmbedding P r
          (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
        constantMatrixEmbedding P r
          ((constantFrobenius P r).symm
            ((constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u i : ConstantExtension P r)))) *
        (cyclicGeneratorInverseMatrix P r *
          (cyclicGeneratorMatrix P r ^ k * cyclicGeneratorMatrix P r ^ i)) = _
  rw [← map_mul, ← pow_add]
  simp only [constantMatrixEmbedding_apply]
  rw [← mul_assoc]

/-- The `i`-th leading summand after multiplying by the inverse tail. -/
noncomputable def infinityLeadingTailTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      (ζ * (constantFrobenius P r ^ k)
        (infinityCyclicCoefficient P r u i : ConstantExtension P r)) *
    cyclicGeneratorMatrix P r ^ (k + i)

/-- The `i`-th predecessor summand after multiplying by the inverse tail. -/
noncomputable def infinityDefectTailTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      ((infinityCyclicInverseCoefficient P r u *
          (constantFrobenius P r).symm ζ) *
        (constantFrobenius P r).symm
          ((constantFrobenius P r ^ k)
            (infinityCyclicCoefficient P r u i : ConstantExtension P r))) *
    cyclicGeneratorInverseMatrix P r *
      cyclicGeneratorMatrix P r ^ (k + i)

/-- The shifted correction summand before reducing its exponent modulo `d`. -/
noncomputable def infinityShiftedCorrectionTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      (infinityConjugationCoefficient P r u k ζ *
        (infinityCyclicCoefficient P r u (k + i) :
          ConstantExtension P r)) *
    cyclicGeneratorMatrix P r ^ (k + i)

/-- An unshifted summand of either correction sum in equation (9). -/
noncomputable def infinityCorrectionTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r
      (infinityConjugationCoefficient P r u k ζ *
        (infinityCyclicCoefficient P r u i : ConstantExtension P r)) *
    cyclicGeneratorMatrix P r ^ i

theorem infinityConjugationCorrectionSum_eq_sum_terms
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (ζ : ConstantExtension P r) :
    infinityConjugationCorrectionSum P r u k bound ζ =
      ∑ i ∈ Finset.range bound, infinityCorrectionTerm P r u k i ζ :=
  rfl

/-- Pairing a leading tail term with the next predecessor term produces
one shifted equation-(9) correction term. -/
theorem infinityLeadingTailTerm_sub_defectTailTerm_succ
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    infinityLeadingTailTerm P r u k i ζ -
        infinityDefectTailTerm P r u k (i + 1) ζ =
      infinityShiftedCorrectionTerm P r u k i ζ := by
  rw [infinityLeadingTailTerm, infinityDefectTailTerm,
    infinityShiftedCorrectionTerm]
  have hexponent : k + (i + 1) = (k + i) + 1 := by omega
  rw [hexponent]
  rw [mul_assoc
    (constantMatrix P r
      ((infinityCyclicInverseCoefficient P r u *
          (constantFrobenius P r).symm ζ) *
        (constantFrobenius P r).symm
          ((constantFrobenius P r ^ k)
            (infinityCyclicCoefficient P r u (i + 1) :
              ConstantExtension P r))))
    (cyclicGeneratorInverseMatrix P r)
    (cyclicGeneratorMatrix P r ^ (k + i + 1))]
  rw [cyclicGeneratorInverseMatrix_mul_pow_succ]
  rw [← sub_mul]
  change
    (constantMatrixEmbedding P r
          (ζ * (constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u i : ConstantExtension P r)) -
      constantMatrixEmbedding P r
          ((infinityCyclicInverseCoefficient P r u *
              (constantFrobenius P r).symm ζ) *
            (constantFrobenius P r).symm
              ((constantFrobenius P r ^ k)
                (infinityCyclicCoefficient P r u (i + 1) :
                  ConstantExtension P r)))) *
        cyclicGeneratorMatrix P r ^ (k + i) = _
  rw [← map_sub, infinityTailCoefficient_sub_succ]
  rfl

/-- The omitted terminal predecessor is the initial predecessor multiplied
by the central wrap factor `1 + y`. -/
theorem infinityDefectTailTerm_rank
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityDefectTailTerm P r u k r.matrixRank ζ =
      (onePlusY P r) • infinityDefectTailTerm P r u k 0 ζ := by
  rw [infinityDefectTailTerm, infinityDefectTailTerm]
  simp only [infinityCyclicCoefficient_rank, infinityCyclicCoefficient_zero,
    Units.val_one, map_one, mul_one, Nat.add_zero]
  rw [Nat.add_comm k r.matrixRank, cyclicGeneratorMatrix_pow_rank_add]
  simp only [mul_smul_comm]

/-- A finite telescoping identity that retains both boundary terms. -/
theorem sum_sub_sum_eq_sum_sub_succ_add_boundary
    {A : Type*} [AddCommGroup A] (L D : ℕ → A) (n : ℕ) :
    (∑ i ∈ Finset.range n, L i) - (∑ i ∈ Finset.range n, D i) =
      (∑ i ∈ Finset.range n, (L i - D (i + 1))) + D n - D 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range n, L i) + L n -
              ((∑ i ∈ Finset.range n, D i) + D n) =
            ((∑ i ∈ Finset.range n, L i) -
              (∑ i ∈ Finset.range n, D i)) + (L n - D n) := by
                abel
        _ = ((∑ i ∈ Finset.range n, (L i - D (i + 1))) + D n - D 0) +
              (L n - D n) := by rw [ih]
        _ = (∑ i ∈ Finset.range n, (L i - D (i + 1))) +
              (L n - D (n + 1)) + D (n + 1) - D 0 := by
                abel

/-- The full inverse-tail difference telescopes to the shifted correction
sum plus the explicit cyclic-boundary contribution. -/
theorem inverseTailDifference_eq_shiftedCorrection_add_boundary
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityLeadingMonomial P r k ζ *
          constantConjugatedBInverseTail P r u -
        infinityDefectMonomial P r u k ζ *
          constantConjugatedBInverseTail P r u =
      (∑ i ∈ Finset.range r.matrixRank,
          infinityShiftedCorrectionTerm P r u k i ζ) +
        (onePlusY P r) • infinityDefectTailTerm P r u k 0 ζ -
          infinityDefectTailTerm P r u k 0 ζ := by
  rw [infinityLeadingMonomial_mul_inverseTail,
    infinityDefectMonomial_mul_inverseTail]
  change
    (∑ i ∈ Finset.range r.matrixRank,
        infinityLeadingTailTerm P r u k i ζ) -
      (∑ i ∈ Finset.range r.matrixRank,
        infinityDefectTailTerm P r u k i ζ) = _
  rw [sum_sub_sum_eq_sum_sub_succ_add_boundary]
  rw [infinityDefectTailTerm_rank]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact infinityLeadingTailTerm_sub_defectTailTerm_succ P r u k i ζ

/-- The zeroth predecessor summand is exactly the non-tail defect. -/
theorem infinityDefectTailTerm_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityDefectTailTerm P r u k 0 ζ =
      infinityDefectMonomial P r u k ζ := by
  rw [infinityDefectTailTerm, infinityDefectMonomial]
  simp only [infinityCyclicCoefficient_zero, Units.val_one, map_one, mul_one,
    Nat.add_zero]

/-- Multiplication by `y⁻¹` cancels the retained cyclic boundary exactly. -/
theorem inv_splittingY_smul_wrap_boundary
    (P : BasePrime) (r : Rank)
    (S D : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    -D + (splittingY P r)⁻¹ •
        (S + (onePlusY P r) • D - D) =
      (splittingY P r)⁻¹ • S := by
  rw [smul_sub, smul_add, smul_smul]
  have hscalar :
      (splittingY P r)⁻¹ * onePlusY P r =
        (splittingY P r)⁻¹ + 1 := by
    rw [onePlusY_eq_one_add_splittingY]
    field_simp [splittingY_ne_zero]
  rw [hscalar, add_smul, one_smul]
  abel

/-- Before reducing cyclic exponents modulo `d`, conjugation is the leading
monomial plus `y⁻¹` times the shifted correction sum. -/
theorem constantConjugatedCartwrightStegerB_conj_monomial_shifted
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        infinityLeadingMonomial P r k ζ) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityLeadingMonomial P r k ζ +
        (splittingY P r)⁻¹ •
          ∑ i ∈ Finset.range r.matrixRank,
            infinityShiftedCorrectionTerm P r u k i ζ := by
  rw [constantConjugatedCartwrightStegerB_conj_monomial_split]
  rw [inverseTailDifference_eq_shiftedCorrection_add_boundary]
  rw [infinityDefectTailTerm_zero]
  rw [sub_eq_add_neg]
  rw [add_assoc]
  congr 1
  exact inv_splittingY_smul_wrap_boundary P r _ _

/-- Rotating the full cyclic correction sum by a basis exponent `k`
produces the unshifted full sum and one extra `y` times its first `k`
terms. -/
theorem sum_infinityShiftedCorrectionTerm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (hk : k ≤ r.matrixRank) (ζ : ConstantExtension P r) :
    (∑ i ∈ Finset.range r.matrixRank,
        infinityShiftedCorrectionTerm P r u k i ζ) =
      infinityConjugationCorrectionSum P r u k r.matrixRank ζ +
        (splittingY P r) •
          infinityConjugationCorrectionSum P r u k k ζ := by
  let A : ℕ → Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) := fun i =>
    constantMatrix P r
      (infinityConjugationCoefficient P r u k ζ *
        (infinityCyclicCoefficient P r u (k + i) :
          ConstantExtension P r))
  change
    (∑ i ∈ Finset.range r.matrixRank,
        A i * cyclicGeneratorMatrix P r ^ (k + i)) = _
  rw [sum_mul_cyclicGeneratorMatrix_pow_shift P r k hk A]
  have hwrapped :
      (∑ j ∈ Finset.range k,
          A (r.matrixRank - k + j) * cyclicGeneratorMatrix P r ^ j) =
        ∑ j ∈ Finset.range k, infinityCorrectionTerm P r u k j ζ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [infinityCorrectionTerm, A]
    have hexponent :
        k + (r.matrixRank - k + j) = r.matrixRank + j := by omega
    rw [hexponent, infinityCyclicCoefficient_rank_add]
  rw [hwrapped]
  rw [infinityConjugationCorrectionSum_eq_sum_terms,
    infinityConjugationCorrectionSum_eq_sum_terms]
  have hrank : k + (r.matrixRank - k) = r.matrixRank :=
    Nat.add_sub_of_le hk
  have hrange :
      Finset.range r.matrixRank =
        Finset.range (k + (r.matrixRank - k)) :=
    congrArg Finset.range hrank.symm
  have hfull :
      (∑ i ∈ Finset.range r.matrixRank,
          infinityCorrectionTerm P r u k i ζ) =
        (∑ j ∈ Finset.range k, infinityCorrectionTerm P r u k j ζ) +
          ∑ i ∈ Finset.range (r.matrixRank - k),
            infinityCorrectionTerm P r u k (k + i) ζ := by
    rw [hrange, Finset.sum_range_add]
  have hnonwrapped :
      (∑ i ∈ Finset.range (r.matrixRank - k),
          A i * cyclicGeneratorMatrix P r ^ (k + i)) =
        ∑ i ∈ Finset.range (r.matrixRank - k),
          infinityCorrectionTerm P r u k (k + i) ζ := by
    rfl
  rw [hnonwrapped, onePlusY_eq_one_add_splittingY, add_smul, one_smul]
  rw [hfull]
  abel

/-- The wrapped `y`-multiple becomes the finite correction after applying
the outer `y⁻¹`. -/
theorem inv_splittingY_smul_add_splittingY_smul
    (P : BasePrime) (r : Rank)
    (F K : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    (splittingY P r)⁻¹ • (F + (splittingY P r) • K) =
      K + (splittingY P r)⁻¹ • F := by
  rw [smul_add, smul_smul]
  rw [inv_mul_cancel₀ (splittingY_ne_zero P r), one_smul]
  abel

/-- LSV05b equation (9), proved for every cyclic-basis exponent.  The sole
premise is the intrinsic basis bound `k ≤ d`; all displayed coefficients
are computed definitions rather than assumed data. -/
theorem constantConjugatedCartwrightStegerB_conj_monomial
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (hk : k ≤ r.matrixRank) (ζ : ConstantExtension P r) :
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ k)) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityConjugationFormula P r u k ζ := by
  change
    ((constantConjugatedCartwrightStegerB P r u :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        infinityLeadingMonomial P r k ζ) *
        (((constantConjugatedCartwrightStegerB P r u)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) = _
  rw [constantConjugatedCartwrightStegerB_conj_monomial_shifted]
  rw [sum_infinityShiftedCorrectionTerm P r u k hk ζ]
  rw [inv_splittingY_smul_add_splittingY_smul]
  rw [infinityConjugationFormula, infinityLeadingMonomial]
  abel

/-- Equation (9) for every actual class-indexed generator owned by the
Cartwright--Steger matrix group. -/
theorem cartwrightStegerGenerator_conj_monomial
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r)
    (k : Fin r.matrixRank) (ζ : ConstantExtension P r) :
    ((cartwrightStegerGenerator P r x :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ))) *
        (((cartwrightStegerGenerator P r x)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      infinityConjugationFormula P r
        (constantClassRepresentative P r x) (k : ℕ) ζ := by
  rw [cartwrightStegerGenerator_eq_constantConjugatedB]
  exact constantConjugatedCartwrightStegerB_conj_monomial P r
    (constantClassRepresentative P r x) (k : ℕ)
    (Nat.le_of_lt k.isLt) ζ

/-- The intrinsic upper-unipotent condition at infinity: on each cyclic
basis block, conjugation is the identity on that block, plus earlier blocks,
plus a term divisible by the infinity uniformizer `y⁻¹`.  The witnesses are
coefficients in the constructed constant field, not caller-supplied matrix
or conclusion data. -/
def HasUpperUnipotentInfinityConjugation
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) : Prop :=
  ∀ (k : Fin r.matrixRank) (ζ : ConstantExtension P r),
    ∃ lower tail : ℕ → ConstantExtension P r,
      ((g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
          (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ))) *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (SplittingFunctionField P r)) =
        constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ) +
          (∑ i ∈ Finset.range (k : ℕ),
            constantMatrix P r (lower i) * cyclicGeneratorMatrix P r ^ i) +
          (splittingY P r)⁻¹ •
            ∑ i ∈ Finset.range r.matrixRank,
              constantMatrix P r (tail i) * cyclicGeneratorMatrix P r ^ i

/-- Every construction-owned Cartwright--Steger generator satisfies the
upper-unipotent infinity condition, with the coefficients computed by
equation (9). -/
theorem cartwrightStegerGenerator_hasUpperUnipotentInfinityConjugation
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    HasUpperUnipotentInfinityConjugation P r
      (cartwrightStegerGenerator P r x) := by
  intro k ζ
  let coeff : ℕ → ConstantExtension P r := fun i =>
    infinityConjugationCoefficient P r
        (constantClassRepresentative P r x) (k : ℕ) ζ *
      (infinityCyclicCoefficient P r
        (constantClassRepresentative P r x) i : ConstantExtension P r)
  refine ⟨coeff, coeff, ?_⟩
  rw [cartwrightStegerGenerator_conj_monomial]
  rfl

/-- The proved inverse expansion for each internally selected generator
of the construction-owned global matrix group. -/
theorem cartwrightStegerGenerator_inv_val
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    (((cartwrightStegerGenerator P r x)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      constantConjugatedBInverseExpansion P r
        (constantClassRepresentative P r x) := by
  rw [cartwrightStegerGenerator_eq_constantConjugatedB]
  exact constantConjugatedCartwrightStegerB_inv_val P r
    (constantClassRepresentative P r x)

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
