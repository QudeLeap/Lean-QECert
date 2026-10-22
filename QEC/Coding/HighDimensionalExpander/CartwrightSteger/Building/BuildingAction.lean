import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Order.Reduction
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.FrobeniusCharpoly
import QEC.Coding.HighDimensionalExpander.Combinatorics.BuildingAdjacency
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-!
# The local building action of the Cartwright--Steger lattice

This module constructs the local splitting data at the building place.  In
particular, the required `d`th root of `1 + y` in `F_q[[y]]` is obtained from
adic completeness and Hensel's lemma; it is not supplied by a caller.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

/-- The `y`-adic ideal in the building integer ring. -/
noncomputable def buildingRootIdeal (P : BasePrime) :
    Ideal (BuildingIntegerRing P) :=
  Ideal.span {PowerSeries.X}

/-- Polynomial whose Hensel lift is the local splitting scalar. -/
noncomputable def buildingRootPolynomial
    (P : BasePrime) (r : Rank) :
    Polynomial (BuildingIntegerRing P) :=
  Polynomial.X ^ r.matrixRank -
    Polynomial.C (1 + PowerSeries.X)

theorem buildingRootPolynomial_monic
    (P : BasePrime) (r : Rank) :
    (buildingRootPolynomial P r).Monic := by
  exact Polynomial.monic_X_pow_sub_C (1 + PowerSeries.X)
    (by cases r <;> simp [Rank.matrixRank])

theorem buildingRootPolynomial_eval_one_mem
    (P : BasePrime) (r : Rank) :
    (buildingRootPolynomial P r).eval 1 ∈ buildingRootIdeal P := by
  have hx : PowerSeries.X ∈ buildingRootIdeal P :=
    Ideal.subset_span (Set.mem_singleton PowerSeries.X)
  simpa [buildingRootPolynomial] using (buildingRootIdeal P).neg_mem hx

theorem buildingRankCast_ne_zero
    (P : BasePrime) (r : Rank) :
    (r.matrixRank : BaseField P) ≠ 0 := by
  change (r.matrixRank : ZMod P.q) ≠ 0
  intro hzero
  have hdiv : P.q ∣ r.matrixRank :=
    (ZMod.natCast_eq_zero_iff r.matrixRank P.q).mp hzero
  exact (Nat.not_dvd_of_pos_of_lt
    (lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r))
    (lt_of_le_of_lt (by cases r <;> simp [Rank.matrixRank]) P.five_le)) hdiv

theorem buildingRootPolynomial_derivative_eval_one_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit
      ((buildingRootPolynomial P r).derivative.eval 1) := by
  have heq :
      (buildingRootPolynomial P r).derivative.eval 1 =
        (r.matrixRank : BuildingIntegerRing P) := by
    rw [buildingRootPolynomial, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero]
    simp
  rw [heq]
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [isUnit_iff_ne_zero]
  simpa using buildingRankCast_ne_zero P r

theorem buildingRootPolynomial_derivative_quotient_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit
      (Ideal.Quotient.mk (buildingRootIdeal P)
        ((buildingRootPolynomial P r).derivative.eval 1)) :=
  (buildingRootPolynomial_derivative_eval_one_isUnit P r).map _

/-- Hensel lifting produces a root congruent to `1` modulo `y`. -/
theorem exists_buildingOnePlusYRoot
    (P : BasePrime) (r : Rank) :
    ∃ a : BuildingIntegerRing P,
      (buildingRootPolynomial P r).IsRoot a ∧
        a - 1 ∈ buildingRootIdeal P := by
  letI : HenselianRing (BuildingIntegerRing P) (buildingRootIdeal P) := by
    rw [buildingRootIdeal]
    infer_instance
  exact HenselianRing.is_henselian
      (buildingRootPolynomial P r)
      (buildingRootPolynomial_monic P r)
      1
      (buildingRootPolynomial_eval_one_mem P r)
      (buildingRootPolynomial_derivative_quotient_isUnit P r)

/-- The construction-owned local scalar whose `d`th power is `1 + y`. -/
noncomputable def buildingOnePlusYRoot
    (P : BasePrime) (r : Rank) : BuildingIntegerRing P :=
  Classical.choose (exists_buildingOnePlusYRoot P r)

theorem buildingOnePlusYRoot_isRoot
    (P : BasePrime) (r : Rank) :
    (buildingRootPolynomial P r).IsRoot
      (buildingOnePlusYRoot P r) :=
  (Classical.choose_spec (exists_buildingOnePlusYRoot P r)).1

theorem buildingOnePlusYRoot_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingOnePlusYRoot P r ^ r.matrixRank =
      1 + PowerSeries.X := by
  have h := buildingOnePlusYRoot_isRoot P r
  rw [Polynomial.IsRoot, buildingRootPolynomial,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at h
  exact sub_eq_zero.mp h

theorem buildingOnePlusYRoot_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit (buildingOnePlusYRoot P r) := by
  rw [← isUnit_pow_iff
    (by cases r <;> norm_num [Rank.matrixRank] : r.matrixRank ≠ 0)]
  rw [buildingOnePlusYRoot_pow_matrixRank]
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The Hensel root bundled as a unit of the building integer ring. -/
noncomputable def buildingOnePlusYRootUnit
    (P : BasePrime) (r : Rank) : (BuildingIntegerRing P)ˣ :=
  (buildingOnePlusYRoot_isUnit P r).unit

@[simp] theorem buildingOnePlusYRootUnit_coe
    (P : BasePrime) (r : Rank) :
    (buildingOnePlusYRootUnit P r : BuildingIntegerRing P) =
      buildingOnePlusYRoot P r :=
  IsUnit.unit_spec (buildingOnePlusYRoot_isUnit P r)

@[simp]
theorem buildingOnePlusYRoot_constantCoeff
    (P : BasePrime) (r : Rank) :
    PowerSeries.constantCoeff (buildingOnePlusYRoot P r) = 1 := by
  have hmem :=
    (Classical.choose_spec (exists_buildingOnePlusYRoot P r)).2
  change buildingOnePlusYRoot P r - 1 ∈
    Ideal.span ({PowerSeries.X} : Set (BuildingIntegerRing P)) at hmem
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)

/-! ## The local split cyclic-algebra matrices -/

/-- The Hensel root viewed in the building local field. -/
noncomputable def buildingOnePlusYRootField
    (P : BasePrime) (r : Rank) : BuildingLocalField P :=
  (buildingOnePlusYRoot P r : BuildingLocalField P)

/-- The local coordinate `y`. -/
noncomputable def buildingLocalY (P : BasePrime) : BuildingLocalField P :=
  ((PowerSeries.X : BuildingIntegerRing P) : BuildingLocalField P)

theorem buildingOnePlusYRootField_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingOnePlusYRootField P r ^ r.matrixRank =
      1 + buildingLocalY P := by
  rw [buildingOnePlusYRootField, buildingLocalY,
    ← PowerSeries.coe_pow, buildingOnePlusYRoot_pow_matrixRank]
  simp

theorem one_add_buildingLocalY_ne_zero
    (P : BasePrime) : 1 + buildingLocalY P ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun f : BuildingLocalField P => f.coeff 0) hzero
  simp [buildingLocalY] at hcoeff

theorem buildingOnePlusYRootField_ne_zero
    (P : BasePrime) (r : Rank) :
    buildingOnePlusYRootField P r ≠ 0 := by
  intro hzero
  have hpow := buildingOnePlusYRootField_pow_matrixRank P r
  rw [hzero, zero_pow (by cases r <;> simp [Rank.matrixRank])] at hpow
  exact one_add_buildingLocalY_ne_zero P hpow.symm

/-- Frobenius in the fixed constant-field basis, base-changed to the
building local field. -/
noncomputable def buildingFrobeniusMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  (frobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).map
    (algebraMap (BaseField P) (BuildingLocalField P))

noncomputable def buildingFrobeniusGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.GeneralLinearGroup.map
    (algebraMap (BaseField P) (BuildingLocalField P))
    (frobeniusGL P r)

@[simp] theorem buildingFrobeniusGL_coe
    (P : BasePrime) (r : Rank) :
    (buildingFrobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingFrobeniusMatrix P r :=
  rfl

theorem buildingFrobeniusMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingFrobeniusMatrix P r ^ r.matrixRank = 1 := by
  have hbase :
      (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) ^
          r.matrixRank = 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact congrArg Units.val (frobeniusGL_pow_matrixRank P r)
  rw [buildingFrobeniusMatrix, ← Matrix.map_pow, hbase]
  simp

theorem buildingFrobeniusMatrix_charpoly
    (P : BasePrime) (r : Rank) :
    (buildingFrobeniusMatrix P r).charpoly =
      Polynomial.X ^ r.matrixRank - 1 := by
  rw [buildingFrobeniusMatrix, Matrix.charpoly_map,
    frobeniusGL_charpoly]
  simp

/-- The regular matrix of a constant-field element at the building place. -/
noncomputable def buildingConstantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  (constantRegularMatrix P r c).map
    (algebraMap (BaseField P) (BuildingLocalField P))

theorem buildingFrobeniusMatrix_mul_buildingConstantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    buildingFrobeniusMatrix P r * buildingConstantMatrix P r c =
      buildingConstantMatrix P r (constantFrobenius P r c) *
        buildingFrobeniusMatrix P r := by
  change
    (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).map
          (algebraMap (BaseField P) (BuildingLocalField P)) *
      (constantRegularMatrix P r c).map
          (algebraMap (BaseField P) (BuildingLocalField P)) =
    (constantRegularMatrix P r (constantFrobenius P r c)).map
          (algebraMap (BaseField P) (BuildingLocalField P)) *
      (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).map
          (algebraMap (BaseField P) (BuildingLocalField P))
  rw [← Matrix.map_mul, frobeniusGL_mul_constantRegularMatrix,
    Matrix.map_mul]

/-- Local cyclic generator `z = (1+y)^(1/d) Frobenius`. -/
noncomputable def buildingCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  buildingOnePlusYRootField P r • buildingFrobeniusMatrix P r

noncomputable def buildingCyclicGeneratorGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
      (Units.mk0 (buildingOnePlusYRootField P r)
        (buildingOnePlusYRootField_ne_zero P r)) *
    buildingFrobeniusGL P r

/-- The local cyclic generator is already invertible over the building
integer ring.  This is the integral representative used to place it in the
maximal compact subgroup. -/
noncomputable def buildingCyclicGeneratorIntegralGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P) :=
  Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
      (buildingOnePlusYRootUnit P r) *
    SphericalHecke.constantGeneralLinearLift (BaseField P) r.matrixRank
      (frobeniusGL P r)

theorem buildingCyclicGeneratorIntegralGL_toLocal
    (P : BasePrime) (r : Rank) :
    SphericalHecke.powerSeriesGeneralLinearToLocal (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r) =
      buildingCyclicGeneratorGL P r := by
  have hfrob :
      SphericalHecke.powerSeriesGeneralLinearToLocal
          (BaseField P) r.matrixRank
          (SphericalHecke.constantGeneralLinearLift
            (BaseField P) r.matrixRank (frobeniusGL P r)) =
        buildingFrobeniusGL P r := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change HahnSeries.ofPowerSeries Int (BaseField P)
        (PowerSeries.C ((frobeniusGL P r) i j)) =
      algebraMap (BaseField P) (BuildingLocalField P)
        ((frobeniusGL P r) i j)
    rw [HahnSeries.ofPowerSeries_C,
      LaurentSeries.algebraMap_apply]
  rw [buildingCyclicGeneratorIntegralGL,
    SphericalHecke.powerSeriesGeneralLinearToLocal, map_mul]
  change Matrix.GeneralLinearGroup.map _
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingOnePlusYRootUnit P r)) *
      SphericalHecke.powerSeriesGeneralLinearToLocal
        (BaseField P) r.matrixRank
        (SphericalHecke.constantGeneralLinearLift
          (BaseField P) r.matrixRank (frobeniusGL P r)) = _
  rw [hfrob]
  rw [buildingCyclicGeneratorGL]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [SphericalHecke.integerEmbedding, buildingOnePlusYRootField]
  · simp [SphericalHecke.integerEmbedding, hij]

/-- Modulo the building uniformizer, the integral cyclic generator is the
arithmetic Frobenius matrix: the Hensel scalar reduces to one. -/
theorem powerSeriesReductionGL_buildingCyclicGeneratorIntegralGL
    (P : BasePrime) (r : Rank) :
    SphericalHecke.powerSeriesReductionGL (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r) =
      frobeniusGL P r := by
  rw [buildingCyclicGeneratorIntegralGL, map_mul,
    SphericalHecke.powerSeriesReductionGL_constantGeneralLinearLift]
  change Matrix.GeneralLinearGroup.map PowerSeries.constantCoeff
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingOnePlusYRootUnit P r)) * frobeniusGL P r = _
  have hscalar : Matrix.GeneralLinearGroup.map PowerSeries.constantCoeff
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingOnePlusYRootUnit P r)) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [buildingOnePlusYRootUnit_coe]
    · simp [hij]
  rw [hscalar, one_mul]

theorem buildingCyclicGenerator_mem_maximalCompact
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup.mk (buildingCyclicGeneratorGL P r) ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
  rw [← buildingCyclicGeneratorIntegralGL_toLocal P r]
  exact SphericalHecke.mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact _

@[simp] theorem buildingCyclicGeneratorGL_coe
    (P : BasePrime) (r : Rank) :
    (buildingCyclicGeneratorGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) =
      buildingCyclicGeneratorMatrix P r := by
  rw [buildingCyclicGeneratorGL, buildingCyclicGeneratorMatrix,
    Units.val_mul, buildingFrobeniusGL_coe]
  change Matrix.scalar (Fin r.matrixRank)
      (buildingOnePlusYRootField P r) * buildingFrobeniusMatrix P r = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem buildingCyclicGeneratorMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingCyclicGeneratorMatrix P r ^ r.matrixRank =
      (1 + buildingLocalY P) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) := by
  rw [buildingCyclicGeneratorMatrix, smul_pow,
    buildingFrobeniusMatrix_pow_matrixRank,
    buildingOnePlusYRootField_pow_matrixRank]

theorem buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    buildingCyclicGeneratorMatrix P r * buildingConstantMatrix P r c =
      buildingConstantMatrix P r (constantFrobenius P r c) *
        buildingCyclicGeneratorMatrix P r := by
  rw [buildingCyclicGeneratorMatrix, Matrix.smul_mul, Matrix.mul_smul,
    buildingFrobeniusMatrix_mul_buildingConstantMatrix]

theorem buildingLocalY_ne_zero (P : BasePrime) :
    buildingLocalY P ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun f : BuildingLocalField P => f.coeff 1) hzero
  simp [buildingLocalY] at hcoeff

/-- The local Cartwright--Steger matrix `b = 1 - z⁻¹`. -/
noncomputable def buildingBMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  1 - ((buildingCyclicGeneratorGL P r)⁻¹ :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P))

/-- The same matrix before embedding the building integer ring into its
fraction field.  It need not be invertible over the integer ring. -/
noncomputable def buildingBIntegralMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P) :=
  1 - ((buildingCyclicGeneratorIntegralGL P r)⁻¹ :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P))

theorem buildingBIntegralMatrix_toLocal
    (P : BasePrime) (r : Rank) :
    (SphericalHecke.integerEmbedding (BaseField P)).mapMatrix
        (buildingBIntegralMatrix P r) =
      buildingBMatrix P r := by
  rw [buildingBIntegralMatrix, buildingBMatrix, map_sub, map_one]
  change (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) -
      (((SphericalHecke.powerSeriesGeneralLinearToLocal
        (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r))⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) = _
  rw [buildingCyclicGeneratorIntegralGL_toLocal]

/-- The residue matrix of `b` is exactly `1 - Frobenius⁻¹`. -/
theorem buildingBIntegralMatrix_reduction
    (P : BasePrime) (r : Rank) :
    (buildingBIntegralMatrix P r).map PowerSeries.constantCoeff =
      1 - ((frobeniusGL P r)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)) := by
  rw [buildingBIntegralMatrix,
    Matrix.map_sub PowerSeries.constantCoeff (by intros; simp),
    Matrix.map_one PowerSeries.constantCoeff (by simp) (by simp)]
  change (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BaseField P)) -
      (((SphericalHecke.powerSeriesReductionGL
        (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r))⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) = _
  rw [powerSeriesReductionGL_buildingCyclicGeneratorIntegralGL]

theorem buildingBMatrix_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit (buildingBMatrix P r) := by
  apply isUnit_one_sub_inv_of_pow_eq_one_add_smul_one
    (buildingCyclicGeneratorGL P r) r.matrixRank
    (buildingLocalY P) (buildingLocalY_ne_zero P)
  simpa only [buildingCyclicGeneratorGL_coe] using
    buildingCyclicGeneratorMatrix_pow_matrixRank P r

/-- The local `b` as a genuine general-linear element. -/
noncomputable def buildingBGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  (buildingBMatrix_isUnit P r).unit

@[simp] theorem buildingBGL_coe
    (P : BasePrime) (r : Rank) :
    (buildingBGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingBMatrix P r :=
  IsUnit.unit_spec (buildingBMatrix_isUnit P r)

/-- Local form of LSV Proposition `normb`: the building-place determinant
of `b = 1 - z⁻¹` is exactly `y / (1+y)`. -/
theorem buildingBMatrix_det (P : BasePrime) (r : Rank) :
    Matrix.det (buildingBMatrix P r) =
      buildingLocalY P / (1 + buildingLocalY P) := by
  let F : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P) := buildingFrobeniusMatrix P r
  let Fg : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (BuildingLocalField P) := buildingFrobeniusGL P r
  let a : BuildingLocalField P := buildingOnePlusYRootField P r
  let au : (BuildingLocalField P)ˣ :=
    Units.mk0 a (buildingOnePlusYRootField_ne_zero P r)
  let c : BuildingLocalField P := (au⁻¹ : (BuildingLocalField P)ˣ)
  have hchar : F.charpoly = Polynomial.X ^ r.matrixRank - 1 :=
    buildingFrobeniusMatrix_charpoly P r
  have hdetF : Matrix.det F =
      (-1 : BuildingLocalField P) ^ r.matrixRank * (-1) := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hchar]
    cases r <;> norm_num [Rank.matrixRank]
  have hdetFne : Matrix.det F ≠ 0 := by
    dsimp [F]
    exact Units.ne_zero (Matrix.GeneralLinearGroup.det (buildingFrobeniusGL P r))
  have heval := Matrix.eval_charpoly F c
  rw [hchar] at heval
  have hscalar : Matrix.scalar (Fin r.matrixRank) c =
      c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P)) := by
    exact (Matrix.smul_one_eq_diagonal c).symm
  have hdetCsubF : Matrix.det
      (c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P)) - F) = c ^ r.matrixRank - 1 := by
    rw [← hscalar]
    exact heval.symm.trans (by simp)
  have hdetFsubC : Matrix.det
      (F - c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P))) =
      (-1 : BuildingLocalField P) ^ r.matrixRank *
        (c ^ r.matrixRank - 1) := by
    rw [show F - c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) =
        -(c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) - F) by abel]
    rw [Matrix.det_neg, Fintype.card_fin, hdetCsubF]
  have hfactor : buildingBMatrix P r =
      ((Fg⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) *
        (F - c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P))) := by
    have hscalarInv :
        (((Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) au)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) :
              Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (BuildingLocalField P)) =
          c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) := by
      change Matrix.diagonal (fun _ => c) = c • (1 : Matrix
        (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
      exact (Matrix.smul_one_eq_diagonal c).symm
    change 1 - (((Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) au *
      Fg)⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) = _
    rw [mul_inv_rev, Units.val_mul, hscalarInv, Matrix.mul_sub]
    have hFg :
        ((Fg⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (BuildingLocalField P)) * F = 1 := by
      change ((Fg⁻¹ * Fg : Matrix.GeneralLinearGroup
        (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) = 1
      simp
    rw [hFg]
  have hdetFgInv : Matrix.det
      (((Fg⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P))) = (Matrix.det F)⁻¹ := by
    change ((Matrix.GeneralLinearGroup.det Fg⁻¹ :
      (BuildingLocalField P)ˣ) : BuildingLocalField P) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    congr 1
  rw [hfactor, Matrix.det_mul, hdetFgInv, hdetF, hdetFsubC]
  dsimp [c, au, a]
  change ((-1 : BuildingLocalField P) ^ r.matrixRank * (-1))⁻¹ *
      ((-1 : BuildingLocalField P) ^ r.matrixRank *
        (((buildingOnePlusYRootField P r)⁻¹) ^ r.matrixRank - 1)) = _
  rw [inv_pow, buildingOnePlusYRootField_pow_matrixRank]
  cases r <;> norm_num [Rank.matrixRank] <;>
    field_simp [one_add_buildingLocalY_ne_zero P] <;> ring

theorem one_add_buildingLocalY_order
    (P : BasePrime) :
    (1 + buildingLocalY P).order = 0 := by
  have hlt :
      (1 : BuildingLocalField P).orderTop <
        (buildingLocalY P).orderTop := by
    simp [buildingLocalY]
  have htop := HahnSeries.orderTop_add_eq_left hlt
  have hne := one_add_buildingLocalY_ne_zero P
  have hcoe :
      (((1 + buildingLocalY P).order : Int) : WithTop Int) =
        (0 : WithTop Int) := by
    calc
      _ = (1 + buildingLocalY P).orderTop :=
        HahnSeries.order_eq_orderTop_of_ne_zero hne
      _ = (1 : BuildingLocalField P).orderTop := htop
      _ = 0 := by simp
  exact WithTop.coe_eq_coe.mp hcoe

/-- The determinant of the local Cartwright--Steger generator has exactly
one unit of building-place valuation. -/
theorem buildingBGL_det_localUnitOrder
    (P : BasePrime) (r : Rank) :
    SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det (buildingBGL P r)) = 1 := by
  let den : (BuildingLocalField P)ˣ :=
    Units.mk0 (1 + buildingLocalY P) (one_add_buildingLocalY_ne_zero P)
  have hdet : Matrix.GeneralLinearGroup.det (buildingBGL P r) =
      SphericalHecke.uniformizerUnit (BaseField P) * den⁻¹ := by
    apply Units.ext
    change Matrix.det (buildingBMatrix P r) = _
    rw [buildingBMatrix_det]
    simp [den, buildingLocalY, SphericalHecke.coe_uniformizerUnit,
      div_eq_mul_inv]
  rw [hdet, SphericalHecke.localUnitOrder_mul,
    SphericalHecke.localUnitOrder_inv]
  have huniformizer : SphericalHecke.localUnitOrder
      (SphericalHecke.uniformizerUnit (BaseField P)) = 1 := by
    simpa using SphericalHecke.localUnitOrder_uniformizerUnit_pow
      (k := BaseField P) 1
  have hden : SphericalHecke.localUnitOrder den = 0 := by
    exact one_add_buildingLocalY_order P
  rw [huniformizer, hden]
  norm_num

/-- Every entry of `b` is integral at the building place.  This is derived
from the integral lift of `z`, including the integrality of its inverse. -/
theorem buildingBMatrix_orderLowerBound_zero
    (P : BasePrime) (r : Rank) :
    SphericalHecke.MatrixOrderLowerBound 0 (buildingBMatrix P r) := by
  have hzInv :=
    SphericalHecke.integralGeneralLinearToLocal_inv_orderLowerBound
      (SphericalHecke.powerSeriesGeneralLinearToInteger
        (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r))
  rw [SphericalHecke.powerSeries_integer_local_triangle,
    buildingCyclicGeneratorIntegralGL_toLocal] at hzInv
  have hone : SphericalHecke.MatrixOrderLowerBound 0
      (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P)) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.one_apply_ne hij, HahnSeries.orderTop_zero]
      exact le_top
  have hneg : SphericalHecke.MatrixOrderLowerBound 0
      (-((buildingCyclicGeneratorGL P r)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) := by
    intro i j
    change 0 ≤ (-(((buildingCyclicGeneratorGL P r)⁻¹ :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) i j).orderTop
    rw [HahnSeries.orderTop_neg]
    exact hzInv i j
  simpa [buildingBMatrix, sub_eq_add_neg] using hone.add hneg

/-- The constructive Cartan type of `b` is exactly the first fundamental
coweight: integrality makes all Smith exponents nonnegative, while the
determinant computation forces their sum to be one. -/
theorem buildingB_smithDominantCoweight_eq_fundamental
    (P : BasePrime) (r : Rank) :
    SphericalHecke.smithDominantCoweight (buildingBGL P r) =
      SphericalHecke.fundamentalDominantCoweight r.matrixRank 1 := by
  let weight :=
    SphericalHecke.smithDominantCoweight (buildingBGL P r)
  have hsmith :
      (∑ i, (SphericalHecke.smithExponent
        (buildingBGL P r) i : ℤ)) = 1 := by
    rw [SphericalHecke.smithExponent_sum_eq_det_localUnitOrder_of_orderLowerBound_zero
      (buildingBGL P r)]
    · exact buildingBGL_det_localUnitOrder P r
    · simpa only [buildingBGL_coe] using
        buildingBMatrix_orderLowerBound_zero P r
  have hsumInt : (∑ i, (weight.exponent i : ℤ)) = 1 := by
    rw [show weight = SphericalHecke.smithDominantCoweight
      (buildingBGL P r) by rfl,
      SphericalHecke.smithDominantCoweight_exponent_sum]
    exact hsmith
  have hsumNat : ∑ i, weight.exponent i = 1 := by
    exact_mod_cast hsumInt
  change weight =
    SphericalHecke.fundamentalDominantCoweight r.matrixRank 1
  exact SphericalHecke.dominantCoweight_eq_fundamental_one_of_sum_eq_one
    (lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)) weight hsumNat

/-- The basic Cartwright--Steger element is a genuine color-one building
step: its projective class lies in the first fundamental Cartan double
coset. -/
theorem buildingB_mem_fundamentalDoubleCoset
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup.mk (buildingBGL P r) ∈
      SphericalHecke.fundamentalDoubleCoset
        (BaseField P) r.matrixRank 1 := by
  rw [← SphericalHecke.dominantDoubleCoset_fundamental]
  rw [← buildingB_smithDominantCoweight_eq_fundamental P r]
  exact SphericalHecke.mk_mem_dominantDoubleCoset (buildingBGL P r)

/-- Nonzero constants represented over the building local field. -/
noncomputable def buildingConstantIntegralGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P) :=
  SphericalHecke.constantGeneralLinearLift
    (BaseField P) r.matrixRank
    (Units.map (constantRegularMatrix P r).toMonoidHom u)

noncomputable def buildingConstantGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.GeneralLinearGroup.map
      (algebraMap (BaseField P) (BuildingLocalField P))
    (Units.map (constantRegularMatrix P r).toMonoidHom u)

theorem buildingConstantGL_eq_constantLift_toLocal
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    buildingConstantGL P r u =
      SphericalHecke.powerSeriesGeneralLinearToLocal
        (BaseField P) r.matrixRank
        (buildingConstantIntegralGL P r u) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change algebraMap (BaseField P) (BuildingLocalField P)
      ((constantRegularMatrix P r) (u : ConstantExtension P r) i j) =
    HahnSeries.ofPowerSeries Int (BaseField P)
      (PowerSeries.C
        ((constantRegularMatrix P r) (u : ConstantExtension P r) i j))
  rw [HahnSeries.ofPowerSeries_C]
  rw [LaurentSeries.algebraMap_apply]

theorem buildingConstant_mem_maximalCompact
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.ProjGenLinGroup.mk (buildingConstantGL P r u) ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
  rw [buildingConstantGL_eq_constantLift_toLocal]
  exact SphericalHecke.mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact _

@[simp] theorem buildingConstantGL_coe
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    (buildingConstantGL P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingConstantMatrix P r u :=
  rfl

/-- The local Cartwright--Steger conjugate `b_u = u b u⁻¹`. -/
noncomputable def buildingCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  buildingConstantGL P r u * buildingBGL P r *
    (buildingConstantGL P r u)⁻¹

/-- Conjugating by a constant matrix does not change the determinant of the
local Cartwright--Steger generator. -/
theorem buildingCartwrightStegerGeneratorGL_det
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup.det
        (buildingCartwrightStegerGeneratorGL P r u) =
      Matrix.GeneralLinearGroup.det (buildingBGL P r) := by
  simp [buildingCartwrightStegerGeneratorGL, map_mul]

/-- Every constant conjugate has exactly one unit of building-place
determinant valuation. -/
theorem buildingCartwrightStegerGeneratorGL_det_localUnitOrder
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (buildingCartwrightStegerGeneratorGL P r u)) = 1 := by
  rw [buildingCartwrightStegerGeneratorGL_det,
    buildingBGL_det_localUnitOrder]

/-- Integral matrix underlying the local conjugate `b_u`.  Its determinant
has order one, so it is invertible only after passing to the local field. -/
noncomputable def buildingCartwrightStegerGeneratorIntegralMatrix
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P) :=
  (buildingConstantIntegralGL P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P)) *
    buildingBIntegralMatrix P r *
  ((buildingConstantIntegralGL P r u)⁻¹ :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P))

/-- Reduction of the integral generator is constant conjugation of
`1 - Frobenius⁻¹`. -/
theorem buildingCartwrightStegerGeneratorIntegralMatrix_reduction
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    (buildingCartwrightStegerGeneratorIntegralMatrix P r u).map
        PowerSeries.constantCoeff =
      (constantRegularMatrix P r (u : ConstantExtension P r)) *
        (1 - ((frobeniusGL P r)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P))) *
      (constantRegularMatrix P r
        ((u : ConstantExtension P r)⁻¹)) := by
  rw [buildingCartwrightStegerGeneratorIntegralMatrix,
    Matrix.map_mul, Matrix.map_mul,
    buildingBIntegralMatrix_reduction]
  change
    ((SphericalHecke.powerSeriesReductionGL (BaseField P) r.matrixRank)
      (buildingConstantIntegralGL P r u) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) * _ *
    (((SphericalHecke.powerSeriesReductionGL (BaseField P) r.matrixRank)
      (buildingConstantIntegralGL P r u))⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)) = _
  rw [buildingConstantIntegralGL,
    SphericalHecke.powerSeriesReductionGL_constantGeneralLinearLift]
  simp

theorem buildingCartwrightStegerGeneratorIntegralMatrix_toLocal
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    (SphericalHecke.integerEmbedding (BaseField P)).mapMatrix
        (buildingCartwrightStegerGeneratorIntegralMatrix P r u) =
      (buildingCartwrightStegerGeneratorGL P r u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) := by
  rw [buildingCartwrightStegerGeneratorIntegralMatrix,
    map_mul, map_mul, buildingBIntegralMatrix_toLocal]
  change
    (SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank (buildingConstantIntegralGL P r u) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) *
      buildingBMatrix P r *
    ((SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank (buildingConstantIntegralGL P r u))⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) = _
  rw [← buildingConstantGL_eq_constantLift_toLocal]
  simp [buildingCartwrightStegerGeneratorGL]

/-- Equal building right cosets of two local generators force equality of
the image subspaces of their integral reductions.  The determinant-order
calculation removes the projective scalar before reduction. -/
theorem generatorReductionRange_eq_of_vertex_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (hvertex :
      (QuotientGroup.mk
          (Matrix.ProjGenLinGroup.mk
            (buildingCartwrightStegerGeneratorGL P r u)) :
        SphericalHecke.BuildingVertex (BaseField P) r.matrixRank) =
        QuotientGroup.mk
          (Matrix.ProjGenLinGroup.mk
            (buildingCartwrightStegerGeneratorGL P r v))) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          ((buildingCartwrightStegerGeneratorIntegralMatrix P r u).map
            PowerSeries.constantCoeff)) =
      LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          ((buildingCartwrightStegerGeneratorIntegralMatrix P r v).map
            PowerSeries.constantCoeff)) := by
  let Au := buildingCartwrightStegerGeneratorGL P r u
  let Av := buildingCartwrightStegerGeneratorGL P r v
  let R : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (BuildingLocalField P) := Au⁻¹ * Av
  have hcompact : Matrix.ProjGenLinGroup.mk R ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    have hrel := QuotientGroup.eq.mp hvertex
    simpa [R, Au, Av, map_mul, map_inv] using hrel
  have hdetR : SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det R) = 0 := by
    simp [R, Au, Av, map_mul, map_inv,
      SphericalHecke.localUnitOrder_mul,
      SphericalHecke.localUnitOrder_inv,
      buildingCartwrightStegerGeneratorGL_det_localUnitOrder]
  have hd : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hRintegral : R ∈ SphericalHecke.integralGeneralLinearSet
      (BaseField P) r.matrixRank :=
    (SphericalHecke.projective_mk_mem_maximalCompact_iff_integral
      (BaseField P) r.matrixRank hd R hdetR).mp hcompact
  rw [← SphericalHecke.range_integralGeneralLinearToLocal] at hRintegral
  obtain ⟨D, hD⟩ := hRintegral
  let C := SphericalHecke.integerGeneralLinearToPowerSeries
    (BaseField P) r.matrixRank D
  have hC : SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank C = R := by
    rw [← SphericalHecke.powerSeries_integer_local_triangle]
    rw [SphericalHecke.powerSeriesGeneralLinearToInteger_inverse]
    exact hD
  have hmatrix : buildingCartwrightStegerGeneratorIntegralMatrix P r v =
      buildingCartwrightStegerGeneratorIntegralMatrix P r u *
        (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingIntegerRing P)) := by
    apply Matrix.map_injective
      (SphericalHecke.integerEmbedding_injective (BaseField P))
    change
      (buildingCartwrightStegerGeneratorIntegralMatrix P r v).map
          (SphericalHecke.integerEmbedding (BaseField P)) =
        (buildingCartwrightStegerGeneratorIntegralMatrix P r u *
          (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingIntegerRing P))).map
          (SphericalHecke.integerEmbedding (BaseField P))
    rw [Matrix.map_mul]
    have hu :=
      buildingCartwrightStegerGeneratorIntegralMatrix_toLocal P r u
    have hv :=
      buildingCartwrightStegerGeneratorIntegralMatrix_toLocal P r v
    change (buildingCartwrightStegerGeneratorIntegralMatrix P r u).map
      (SphericalHecke.integerEmbedding (BaseField P)) =
        (Au : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) at hu
    change (buildingCartwrightStegerGeneratorIntegralMatrix P r v).map
      (SphericalHecke.integerEmbedding (BaseField P)) =
        (Av : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) at hv
    have hc := congrArg Units.val hC
    change (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingIntegerRing P)).map
        (SphericalHecke.integerEmbedding (BaseField P)) =
      (R : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P)) at hc
    rw [hv, hu, hc]
    simp [R]
  rw [hmatrix, Matrix.map_mul]
  exact (range_toLin_mul_generalLinear P r
    ((buildingCartwrightStegerGeneratorIntegralMatrix P r u).map
      PowerSeries.constantCoeff)
    (SphericalHecke.powerSeriesReductionGL
      (BaseField P) r.matrixRank C)).symm

/-- Projective local generator indexed by the source projective constant
class. -/
noncomputable def buildingCartwrightStegerGenerator
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk
    (buildingCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r u))

/-- Every projectively indexed Cartwright--Steger generator is a color-one
building step.  Conjugation is absorbed by the two maximal-compact factors. -/
theorem buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    buildingCartwrightStegerGenerator P r u ∈
      SphericalHecke.fundamentalDoubleCoset
        (BaseField P) r.matrixRank 1 := by
  let c := Matrix.ProjGenLinGroup.mk
    (buildingConstantGL P r (constantClassRepresentative P r u))
  have hc : c ∈ SphericalHecke.maximalCompact
      (BaseField P) r.matrixRank :=
    buildingConstant_mem_maximalCompact P r
      (constantClassRepresentative P r u)
  rw [← SphericalHecke.dominantDoubleCoset_fundamental]
  have hb : Matrix.ProjGenLinGroup.mk (buildingBGL P r) ∈
      SphericalHecke.dominantDoubleCoset (BaseField P)
        (SphericalHecke.fundamentalDominantCoweight r.matrixRank 1) := by
    rw [SphericalHecke.dominantDoubleCoset_fundamental]
    exact buildingB_mem_fundamentalDoubleCoset P r
  have hleft := SphericalHecke.left_mul_mem_dominantDoubleCoset
    (BaseField P)
    (SphericalHecke.fundamentalDominantCoweight r.matrixRank 1) hc hb
  have hconj := SphericalHecke.right_mul_mem_dominantDoubleCoset
    (BaseField P)
    (SphericalHecke.fundamentalDominantCoweight r.matrixRank 1)
    ((SphericalHecke.maximalCompact (BaseField P) r.matrixRank).inv_mem hc)
    hleft
  simpa [buildingCartwrightStegerGenerator,
    buildingCartwrightStegerGeneratorGL, c, map_mul, map_inv] using hconj

/-- The standard-vertex neighbor selected by a projective constant class. -/
noncomputable def buildingGeneratorNeighbor
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    {q // q ∈ SphericalHecke.fundamentalNeighborCosets
      (BaseField P) r.matrixRank 1} := by
  refine ⟨QuotientGroup.mk (buildingCartwrightStegerGenerator P r u), ?_⟩
  rw [SphericalHecke.mem_fundamentalNeighborCosets]
  exact ⟨buildingCartwrightStegerGenerator P r u,
    buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset P r u, rfl⟩

/-- The source projective classes and the complete color-one neighbor set
have exactly the same cardinality in both construction ranks. -/
theorem natCard_constantProjectiveClass_eq_coloredAdjacencyDegree_one
    (P : BasePrime) (r : Rank) :
    Nat.card (ConstantProjectiveClass P r) =
      SphericalHecke.coloredAdjacencyDegree
        (BaseField P) r.matrixRank 1 := by
  rw [natCard_constantProjectiveClass]
  cases r with
  | three =>
      simp only [Rank.matrixRank]
      rw [SphericalHecke.coloredAdjacencyDegree_rankThree_one]
      simp [Finset.sum_range_succ]
      ring
  | four =>
      simp only [Rank.matrixRank]
      rw [SphericalHecke.coloredAdjacencyDegree_rankFour_one]
      simp [Finset.sum_range_succ]
      ring

theorem card_buildingGeneratorNeighbor_domain_eq_codomain
    (P : BasePrime) (r : Rank) :
    Fintype.card (ConstantProjectiveClass P r) =
      Fintype.card
        {q // q ∈ SphericalHecke.fundamentalNeighborCosets
          (BaseField P) r.matrixRank 1} := by
  rw [← Nat.card_eq_fintype_card,
    natCard_constantProjectiveClass_eq_coloredAdjacencyDegree_one]
  simp [SphericalHecke.coloredAdjacencyDegree]

/-- Distinct projective constant classes select distinct color-one
neighbors.  Thus the local Cartwright--Steger generators have no collisions
at the standard vertex. -/
theorem buildingGeneratorNeighbor_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingGeneratorNeighbor P r) := by
  intro x y hxy
  let u := constantClassRepresentative P r x
  let v := constantClassRepresentative P r y
  have hvertex :
      (QuotientGroup.mk
          (Matrix.ProjGenLinGroup.mk
            (buildingCartwrightStegerGeneratorGL P r u)) :
        SphericalHecke.BuildingVertex (BaseField P) r.matrixRank) =
      QuotientGroup.mk
        (Matrix.ProjGenLinGroup.mk
          (buildingCartwrightStegerGeneratorGL P r v)) := by
    have hval := congrArg Subtype.val hxy
    exact hval
  have hrange := generatorReductionRange_eq_of_vertex_eq P r u v hvertex
  rw [buildingCartwrightStegerGeneratorIntegralMatrix_reduction,
    buildingCartwrightStegerGeneratorIntegralMatrix_reduction,
    range_toLin_constant_conjugate_one_sub_frobeniusGL_inv,
    range_toLin_constant_conjugate_one_sub_frobeniusGL_inv] at hrange
  let a : ConstantExtension P r :=
    (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹
  have hstable : (frobeniusDifferenceRange P r).map
      (constantMultiplicationLinearMap P r a) ≤
      frobeniusDifferenceRange P r := by
    rintro _ ⟨z, hz, rfl⟩
    have huz : (u : ConstantExtension P r) * z ∈
        (frobeniusDifferenceRange P r).map
          (constantMultiplicationLinearMap P r u) := by
      exact Submodule.mem_map_of_mem hz
    rw [hrange] at huz
    obtain ⟨w, hw, huw⟩ := huz
    have haw : a * z = w := by
      change ((u : ConstantExtension P r) *
        (v : ConstantExtension P r)⁻¹) * z = w
      change (v : ConstantExtension P r) * w =
        (u : ConstantExtension P r) * z at huw
      apply (mul_left_cancel₀ (Units.ne_zero v))
      simpa [mul_assoc, mul_left_comm, mul_comm] using huw.symm
    simpa [haw] using hw
  obtain ⟨c, hc⟩ :=
    exists_eq_algebraMap_of_map_frobeniusDifferenceRange_le
      P r a hstable
  have hc_ne : c ≠ 0 := by
    intro hc0
    have ha0 : a = 0 := by simpa [hc0] using hc
    exact (mul_ne_zero (Units.ne_zero u)
      (inv_ne_zero (Units.ne_zero v))) ha0
  let cu : (BaseField P)ˣ := Units.mk0 c hc_ne
  have hquotient :
      (QuotientGroup.mk u : ConstantProjectiveClass P r) =
        QuotientGroup.mk v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change u / v ∈ baseScalarUnits P r
    refine ⟨cu, ?_⟩
    apply Units.ext
    simpa [a, cu, baseScalarUnitHom, div_eq_mul_inv] using hc.symm
  exact (QuotientGroup.out_eq' x).symm.trans
    (hquotient.trans (QuotientGroup.out_eq' y))

/-- The source-indexed generators enumerate every color-one neighbor exactly
once. -/
theorem buildingGeneratorNeighbor_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (buildingGeneratorNeighbor P r) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨buildingGeneratorNeighbor_injective P r,
    card_buildingGeneratorNeighbor_domain_eq_codomain P r⟩

/-- Canonical equivalence between projective constant classes and the full
color-one link of the standard building vertex. -/
noncomputable def buildingGeneratorNeighborEquiv
    (P : BasePrime) (r : Rank) :
    ConstantProjectiveClass P r ≃
      {q // q ∈ SphericalHecke.fundamentalNeighborCosets
        (BaseField P) r.matrixRank 1} :=
  Equiv.ofBijective (buildingGeneratorNeighbor P r)
    (buildingGeneratorNeighbor_bijective P r)

/-- The locally represented Cartwright--Steger lattice. -/
noncomputable def BuildingCartwrightStegerLattice
    (P : BasePrime) (r : Rank) :
    Subgroup
      (Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) :=
  Subgroup.closure
    (Set.range (buildingCartwrightStegerGenerator P r))

/-- A source-indexed generator, bundled as an element of the constructed
local lattice. -/
noncomputable def buildingLatticeGenerator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    BuildingCartwrightStegerLattice P r :=
  ⟨buildingCartwrightStegerGenerator P r u,
    Subgroup.subset_closure (Set.mem_range_self u)⟩

@[simp]
theorem buildingLatticeGenerator_coe
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    (buildingLatticeGenerator P r u :
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingCartwrightStegerGenerator P r u :=
  rfl

/-! ## The genuine building-vertex orbit map -/

/-- Building vertices at the place `y = 0`, in the homogeneous-space model
constructed by the spherical Hecke foundation. -/
abbrev CartwrightStegerBuildingVertex
    (P : BasePrime) (r : Rank) :=
  SphericalHecke.BuildingVertex (BaseField P) r.matrixRank

/-- Orbit map of the locally represented lattice at the standard building
vertex. -/
noncomputable def buildingLatticeVertexMap
    (P : BasePrime) (r : Rank) :
    BuildingCartwrightStegerLattice P r →
      CartwrightStegerBuildingVertex P r :=
  fun g => QuotientGroup.mk
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))

/-- At every vertex already in the lattice orbit, right multiplication by
the source generators enumerates the entire color-one neighbor set exactly
once.  This is the translated local form of simple transitivity. -/
noncomputable def buildingGeneratorNeighborAtEquiv
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r) :
    ConstantProjectiveClass P r ≃
      {q // SphericalHecke.ColoredBuildingAdjacent
        (BaseField P) r.matrixRank 1
        (buildingLatticeVertexMap P r g) q} := by
  let eBase := (buildingGeneratorNeighborEquiv P r).trans
    (SphericalHecke.fundamentalNeighborAdjacentBaseEquiv
      (BaseField P) r.matrixRank 1)
  let gl : Matrix.ProjGenLinGroup (Fin r.matrixRank)
      (BuildingLocalField P) := g
  have hcenter :
      gl •
          (QuotientGroup.mk 1 : CartwrightStegerBuildingVertex P r) =
        buildingLatticeVertexMap P r g := by
    rw [MulAction.Quotient.smul_mk]
    simp [gl, smul_eq_mul, buildingLatticeVertexMap]
  exact {
    toFun := fun u => ⟨gl • (eBase u).1, by
      rw [← hcenter]
      exact (SphericalHecke.coloredBuildingAdjacent_smul_iff
        (BaseField P) r.matrixRank 1 gl _ _).2 (eBase u).2⟩
    invFun := fun q => eBase.symm ⟨gl⁻¹ • q.1, by
      have hq : SphericalHecke.ColoredBuildingAdjacent
          (BaseField P) r.matrixRank 1
          (gl • (QuotientGroup.mk 1 : CartwrightStegerBuildingVertex P r))
          q.1 := by simpa [hcenter] using q.2
      have hback := (SphericalHecke.coloredBuildingAdjacent_smul_iff
        (BaseField P) r.matrixRank 1 gl⁻¹ _ _).2 hq
      simpa using hback⟩
    left_inv := fun u => by
      apply eBase.injective
      apply Subtype.ext
      simp
    right_inv := fun q => by
      apply Subtype.ext
      simp
  }

@[simp]
theorem buildingGeneratorNeighborAtEquiv_apply
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r)
    (u : ConstantProjectiveClass P r) :
    (buildingGeneratorNeighborAtEquiv P r g u).1 =
      buildingLatticeVertexMap P r (g * buildingLatticeGenerator P r u) := by
  rfl

/-- Every color-one neighbor of a lattice-orbit vertex is reached by a
unique source generator. -/
theorem existsUnique_generator_mul_eq_coloredNeighbor
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r)
    (q : CartwrightStegerBuildingVertex P r)
    (hq : SphericalHecke.ColoredBuildingAdjacent
      (BaseField P) r.matrixRank 1
      (buildingLatticeVertexMap P r g) q) :
    ∃! u : ConstantProjectiveClass P r,
      buildingLatticeVertexMap P r
        (g * buildingLatticeGenerator P r u) = q := by
  let q' : {z // SphericalHecke.ColoredBuildingAdjacent
      (BaseField P) r.matrixRank 1
      (buildingLatticeVertexMap P r g) z} := ⟨q, hq⟩
  let u := (buildingGeneratorNeighborAtEquiv P r g).symm q'
  refine ⟨u, ?_, ?_⟩
  · dsimp [u]
    rw [← buildingGeneratorNeighborAtEquiv_apply]
    exact congrArg Subtype.val
      ((buildingGeneratorNeighborAtEquiv P r g).apply_symm_apply q')
  · intro v hv
    apply (buildingGeneratorNeighborAtEquiv P r g).injective
    apply Subtype.ext
    rw [buildingGeneratorNeighborAtEquiv_apply,
      buildingGeneratorNeighborAtEquiv_apply]
    exact hv.trans (by
      rw [← buildingGeneratorNeighborAtEquiv_apply]
      exact (congrArg Subtype.val
        ((buildingGeneratorNeighborAtEquiv P r g).apply_symm_apply q')).symm)

/-- Every vertex reachable from the base by color-one building steps lies in
the constructed lattice orbit. -/
theorem exists_lattice_of_colorOne_reachable
    (P : BasePrime) (r : Rank)
    (q : CartwrightStegerBuildingVertex P r)
    (hreach : Relation.ReflTransGen
      (SphericalHecke.ColoredBuildingAdjacent
        (BaseField P) r.matrixRank 1)
      (QuotientGroup.mk 1) q) :
    ∃ g : BuildingCartwrightStegerLattice P r,
      buildingLatticeVertexMap P r g = q := by
  induction hreach with
  | refl =>
      exact ⟨1, rfl⟩
  | @tail q s _ hqs ih =>
      obtain ⟨g, hg⟩ := ih
      have hgs : SphericalHecke.ColoredBuildingAdjacent
          (BaseField P) r.matrixRank 1
          (buildingLatticeVertexMap P r g) s := by
        simpa [hg] using hqs
      obtain ⟨u, hu, _⟩ :=
        existsUnique_generator_mul_eq_coloredNeighbor P r g s hgs
      exact ⟨g * buildingLatticeGenerator P r u, hu⟩

/-- The locally represented Cartwright--Steger lattice acts transitively on
the vertices of the rank-three or rank-four affine building.  This is the
orbit-surjectivity part of the Cartwright--Steger simple-transitivity
statement; stabilizer triviality is a separate global arithmetic claim. -/
theorem buildingLatticeVertexMap_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (buildingLatticeVertexMap P r) := by
  intro q
  apply exists_lattice_of_colorOne_reachable P r q
  cases r with
  | three =>
      exact SphericalHecke.rankThree_colorOneReachable (BaseField P) q
  | four =>
      exact SphericalHecke.rankFour_colorOneReachable (BaseField P) q

/-- Every constructed lattice generator sends the standard vertex to an
actual color-one adjacent building vertex. -/
theorem buildingLatticeGenerator_adjacent_base
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    SphericalHecke.ColoredBuildingAdjacent
      (BaseField P) r.matrixRank 1
      (QuotientGroup.mk 1)
      (buildingLatticeVertexMap P r (buildingLatticeGenerator P r u)) := by
  change SphericalHecke.ColoredBuildingAdjacent
    (BaseField P) r.matrixRank 1
    (QuotientGroup.mk 1)
    (QuotientGroup.mk (buildingCartwrightStegerGenerator P r u))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa using
    buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset P r u

@[simp] theorem buildingLatticeVertexMap_one
    (P : BasePrime) (r : Rank) :
    buildingLatticeVertexMap P r 1 = QuotientGroup.mk 1 :=
  rfl

theorem buildingLatticeVertexMap_eq_iff
    (P : BasePrime) (r : Rank)
    (g h : BuildingCartwrightStegerLattice P r) :
    buildingLatticeVertexMap P r g = buildingLatticeVertexMap P r h ↔
      ((g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P))⁻¹ *
        (h : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P))) ∈
        SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
  exact QuotientGroup.eq

/-- Injectivity of the orbit map is exactly triviality of the lattice
stabilizer of the standard vertex. -/
theorem buildingLatticeVertexMap_injective_iff
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingLatticeVertexMap P r) ↔
      ∀ g : BuildingCartwrightStegerLattice P r,
        (g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P)) ∈
            SphericalHecke.maximalCompact (BaseField P) r.matrixRank →
          g = 1 := by
  constructor
  · intro hinj g hg
    apply hinj
    rw [buildingLatticeVertexMap_eq_iff]
    simpa using
      (SphericalHecke.maximalCompact (BaseField P) r.matrixRank).inv_mem hg
  · intro htriv g h hgh
    have hrel := (buildingLatticeVertexMap_eq_iff P r g h).mp hgh
    let k : BuildingCartwrightStegerLattice P r := g⁻¹ * h
    have hk :
        (k : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P)) ∈
            SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
      exact hrel
    have hkOne : k = 1 := htriv k hk
    change g⁻¹ * h = 1 at hkOne
    exact inv_mul_eq_one.mp hkOne

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
