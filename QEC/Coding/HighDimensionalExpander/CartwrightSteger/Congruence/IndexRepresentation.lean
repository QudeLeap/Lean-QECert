import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Norm.Norm
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.IndexSplitting

/-!
# The Cartwright--Steger element at the index-controlled place

This file evaluates the explicit formula `b = 1 - z⁻¹` at the
construction-owned `Chooseorder` place.  Its determinant is proved to be the
selected full-order unit, so its projective class together with `PSL` generates
the full finite `PGL`.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

private theorem generalLinear_eq_of_projective_eq_of_diagonal_one
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (i : n) (A B : Matrix.GeneralLinearGroup n K)
    (hprojective : Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk B)
    (hA : (A : Matrix n n K) i i = 1)
    (hB : (B : Matrix n n K) i i = 1) :
    A = B := by
  have hcenter : A⁻¹ * B ∈
      Subgroup.center (Matrix.GeneralLinearGroup n K) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    rw [map_mul, map_inv, hprojective]
    simp
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨a, ha⟩ := hcenter
  have hB_eq : B = A * Matrix.GeneralLinearGroup.scalar n a := by
    calc
      B = A * (A⁻¹ * B) := by group
      _ = A * Matrix.GeneralLinearGroup.scalar n a := by rw [← ha]
  have hmatrix := congrArg Units.val hB_eq
  have hentry := congrFun (congrFun hmatrix i) i
  have haone : (1 : K) = a := by
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.mul_diagonal,
      Matrix.scalar_apply, hA, hB] using hentry
  have haunit : a = 1 := Units.ext haone.symm
  subst a
  simpa using hB_eq.symm

/-- The explicit Cartwright--Steger `b`-matrix at the `Chooseorder` place. -/
noncomputable def indexBMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) :=
  cyclicBMatrix r (indexPlaceY P r level)

/-- The selected `b`-matrix is genuinely `1 - z⁻¹` for the compatible
split cyclic generator, not merely a matrix with the desired determinant. -/
theorem indexBMatrix_eq_one_sub_indexCyclicGenerator_inv
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexBMatrix P r level =
      1 - ((indexCyclicGeneratorGL P r level)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ResidueField P r level)) := by
  cases r <;> rfl

theorem indexBMatrix_det
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.det (indexBMatrix P r level) =
      (indexRatioUnit P r level : ResidueField P r level) := by
  rw [indexBMatrix,
    cyclicBMatrix_det r (indexPlaceY P r level)
      (indexPlaceY_one_add_ne_zero P r level),
    indexPlaceY_div_one_add]

theorem indexBMatrix_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexBMatrix P r level) := by
  rw [Matrix.isUnit_iff_isUnit_det, indexBMatrix_det]
  exact (indexRatioUnit P r level).isUnit

/-- The evaluated `b`-matrix as a genuine general-linear element. -/
noncomputable def indexBGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  (indexBMatrix_isUnit P r level).unit

@[simp] theorem indexBGL_coe
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexBGL P r level :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      indexBMatrix P r level :=
  IsUnit.unit_spec (indexBMatrix_isUnit P r level)

theorem indexBGL_det
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup.det (indexBGL P r level) =
      indexRatioUnit P r level := by
  apply Units.ext
  change Matrix.det (indexBMatrix P r level) =
    (indexRatioUnit P r level : ResidueField P r level)
  exact indexBMatrix_det P r level

/-- Since `b = 1 - z⁻¹`, the compatible cyclic generator commutes with
the actual Cartwright--Steger element. -/
theorem indexCyclicGeneratorGL_commute_indexBGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorGL P r level * indexBGL P r level =
      indexBGL P r level * indexCyclicGeneratorGL P r level := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, indexCyclicGeneratorGL_coe,
    indexBGL_coe, indexBMatrix_eq_one_sub_indexCyclicGenerator_inv,
    mul_sub, sub_mul, mul_one, one_mul]
  have hzRight :
      indexCyclicGeneratorMatrix P r level *
          ((indexCyclicGeneratorGL P r level)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (ResidueField P r level)) = 1 := by
    simpa only [← indexCyclicGeneratorGL_coe,
      Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_one] using congrArg Units.val
        (mul_inv_cancel (indexCyclicGeneratorGL P r level))
  have hzLeft :
      ((indexCyclicGeneratorGL P r level)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ResidueField P r level)) *
        indexCyclicGeneratorMatrix P r level = 1 := by
    simpa only [← indexCyclicGeneratorGL_coe,
      Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_one] using congrArg Units.val
        (inv_mul_cancel (indexCyclicGeneratorGL P r level))
  rw [hzRight, hzLeft]

/-- Projective class of the actual evaluated Cartwright--Steger formula. -/
noncomputable def indexB
    (P : BasePrime) (r : Rank) (level : Nat) : PGL P r level :=
  Matrix.ProjGenLinGroup.mk (indexBGL P r level)

theorem residueProjectiveDetClass_indexB
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueProjectiveDetClass P r level (indexB P r level) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  rw [indexB, residueProjectiveDetClass]
  change QuotientGroup.mk' _
      (Matrix.GeneralLinearGroup.det (indexBGL P r level)) = _
  rw [indexBGL_det]
  rfl

theorem residueProjectiveDetClass_indexB_orderOf
    (P : BasePrime) (r : Rank) (level : Nat) :
    orderOf (residueProjectiveDetClass P r level (indexB P r level)) =
      Nat.card (ResiduePowerClass P r level) := by
  rw [residueProjectiveDetClass_indexB,
    indexRatioUnit_orderOf, IndexSelection.natCard_powerClass]
  simp only [Fintype.card_fin]

/-- `whatisr` at the full-index `Chooseorder` place: the genuine `b` formula
and `PSL` generate the entire finite projective group. -/
theorem PSL_sup_indexB_eq_PGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    PSL P r level ⊔ Subgroup.zpowers (indexB P r level) = ⊤ := by
  exact ProjectiveIndex.generatedProjectiveImage_eq_top
      (Fin r.matrixRank) (ResidueField P r level)
      (indexB P r level)
      (residueProjectiveDetClass_indexB_orderOf P r level)

/-- The evaluated generator `b_u = u b u⁻¹`.  The indexing units and every
matrix are construction-owned; quotienting the constant units by base-field
scalars is handled by the source Cartwright--Steger indexing layer. -/
noncomputable def indexCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  indexConstantGL P r level u * indexBGL P r level *
    (indexConstantGL P r level u)⁻¹

theorem indexCartwrightStegerGeneratorGL_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCartwrightStegerGeneratorGL P r level u =
      indexConstantGL P r level u * indexBGL P r level *
        indexConstantGL P r level u⁻¹ := by
  rw [indexCartwrightStegerGeneratorGL]
  have hinv :
      (indexConstantGL P r level u)⁻¹ =
        indexConstantGL P r level u⁻¹ := by
    change (Units.map
      (indexConstantMatrixEmbedding P r level).toMonoidHom u)⁻¹ =
      Units.map (indexConstantMatrixEmbedding P r level).toMonoidHom u⁻¹
    exact (map_inv (Units.map
      (indexConstantMatrixEmbedding P r level).toMonoidHom) u).symm
  rw [hinv]

/-- Constant conjugation multiplies the source parameter. -/
theorem indexConstantGL_conj_indexCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (a u : (ConstantExtension P r)ˣ) :
    indexConstantGL P r level a *
        indexCartwrightStegerGeneratorGL P r level u *
          (indexConstantGL P r level a)⁻¹ =
      indexCartwrightStegerGeneratorGL P r level (a * u) := by
  rw [indexCartwrightStegerGeneratorGL_eq,
    indexCartwrightStegerGeneratorGL_eq]
  change
    indexConstantGLHom P r level a *
        (indexConstantGLHom P r level u * indexBGL P r level *
          indexConstantGLHom P r level u⁻¹) *
        (indexConstantGLHom P r level a)⁻¹ =
      indexConstantGLHom P r level (a * u) * indexBGL P r level *
        indexConstantGLHom P r level (a * u)⁻¹
  simp only [map_mul, map_inv]
  group

/-- Conjugation by `z` applies Frobenius to the source parameter. -/
theorem indexCyclicGeneratorGL_conj_indexCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCyclicGeneratorGL P r level *
        indexCartwrightStegerGeneratorGL P r level u *
          (indexCyclicGeneratorGL P r level)⁻¹ =
      indexCartwrightStegerGeneratorGL P r level
        (indexConstantFrobeniusUnit P r u) := by
  let z := indexCyclicGeneratorGL P r level
  let C := indexConstantGLHom P r level
  let φ := indexConstantFrobeniusUnit P r
  have hconstant (w : (ConstantExtension P r)ˣ) :
      z * C w * z⁻¹ = C (φ w) := by
    change
      indexCyclicGeneratorGL P r level * indexConstantGL P r level w *
          (indexCyclicGeneratorGL P r level)⁻¹ =
        indexConstantGL P r level (indexConstantFrobeniusUnit P r w)
    rw [indexCyclicGeneratorGL_mul_indexConstantGL]
    group
  have hb : z * indexBGL P r level * z⁻¹ =
      indexBGL P r level := by
    dsimp [z]
    rw [indexCyclicGeneratorGL_commute_indexBGL]
    group
  rw [indexCartwrightStegerGeneratorGL_eq,
    indexCartwrightStegerGeneratorGL_eq]
  change z * (C u * indexBGL P r level * C u⁻¹) * z⁻¹ =
    C (φ u) * indexBGL P r level * C (φ u)⁻¹
  calc
    z * (C u * indexBGL P r level * C u⁻¹) * z⁻¹ =
        (z * C u * z⁻¹) *
          (z * indexBGL P r level * z⁻¹) *
            (z * C u⁻¹ * z⁻¹) := by group
    _ = C (φ u) * indexBGL P r level * C (φ u⁻¹) := by
      rw [hconstant, hb, hconstant]
    _ = C (φ u) * indexBGL P r level * C (φ u)⁻¹ := by
      rw [map_inv, map_inv]

/-- Conjugation by a represented constant preserves the unit diagonal of
`b = 1 - z⁻¹`. -/
theorem indexCartwrightStegerGeneratorGL_apply_self
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) (i : Fin r.matrixRank) :
    (indexCartwrightStegerGeneratorGL P r level u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) i i = 1 := by
  rw [indexCartwrightStegerGeneratorGL_eq,
    Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul,
    indexConstantGL_coe, indexBGL_coe, indexConstantGL_coe,
    indexConstantMatrix, indexConstantMatrix,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases r <;> fin_cases i <;>
    simp [indexBMatrix, cyclicBMatrix]

private def generatorFirstIndex (r : Rank) : Fin r.matrixRank :=
  ⟨0, by cases r <;> decide⟩

private def generatorSecondIndex (r : Rank) : Fin r.matrixRank :=
  ⟨1, by cases r <;> decide⟩

/-- The first superdiagonal entry records the Frobenius ratio of the
constant-class representative. -/
theorem indexCartwrightStegerGeneratorGL_apply_first_second
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    (indexCartwrightStegerGeneratorGL P r level u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))
        (generatorFirstIndex r) (generatorSecondIndex r) =
      -indexConstantEmbedding P r level
        ((u : ConstantExtension P r) *
          ((constantFrobenius P r).symm
            (u : ConstantExtension P r))⁻¹) := by
  rw [indexCartwrightStegerGeneratorGL_eq,
    Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul,
    indexConstantGL_coe, indexBGL_coe, indexConstantGL_coe,
    indexConstantMatrix, indexConstantMatrix,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases r <;>
    simp [generatorFirstIndex, generatorSecondIndex,
      indexBMatrix, cyclicBMatrix]

noncomputable def indexCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) : PGL P r level :=
  Matrix.ProjGenLinGroup.mk
    (indexCartwrightStegerGeneratorGL P r level u)

theorem indexCartwrightStegerGenerator_eq_conj
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCartwrightStegerGenerator P r level u =
      Matrix.ProjGenLinGroup.mk (indexConstantGL P r level u) *
        indexB P r level *
          (Matrix.ProjGenLinGroup.mk
            (indexConstantGL P r level u))⁻¹ := by
  simp [indexCartwrightStegerGenerator,
    indexCartwrightStegerGeneratorGL, indexB, map_mul, map_inv]

/-- The represented constant units, projectivized in the finite residue
matrix algebra. -/
noncomputable def indexConstantPGLHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ConstantExtension P r)ˣ →* PGL P r level :=
  Matrix.ProjGenLinGroup.mk.comp (indexConstantGLHom P r level)

/-- Base-field scalar units vanish after projectivizing the compatible
constant representation. -/
@[simp] theorem indexConstantPGLHom_baseScalar
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : (BaseField P)ˣ) :
    indexConstantPGLHom P r level (baseScalarUnitHom P r a) = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (indexConstantGL P r level (baseScalarUnitHom P r a)) = 1
  rw [indexConstantGL_baseScalar, Matrix.ProjGenLinGroup.mk_scalar]

/-- Constant conjugation permutes the finite Cartwright--Steger generators
by multiplication of their source parameters. -/
theorem indexConstantPGL_conj_indexCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (a u : (ConstantExtension P r)ˣ) :
    indexConstantPGLHom P r level a *
        indexCartwrightStegerGenerator P r level u *
          (indexConstantPGLHom P r level a)⁻¹ =
      indexCartwrightStegerGenerator P r level (a * u) := by
  exact congrArg Matrix.ProjGenLinGroup.mk
      (indexConstantGL_conj_indexCartwrightStegerGeneratorGL
        P r level a u)

/-- Conjugation by the cyclic generator permutes the finite
Cartwright--Steger generators by Frobenius. -/
theorem indexCyclicGeneratorPGL_conj_indexCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.ProjGenLinGroup.mk (indexCyclicGeneratorGL P r level) *
        indexCartwrightStegerGenerator P r level u *
          (Matrix.ProjGenLinGroup.mk
            (indexCyclicGeneratorGL P r level))⁻¹ =
      indexCartwrightStegerGenerator P r level
        (indexConstantFrobeniusUnit P r u) := by
  simpa [indexCartwrightStegerGenerator, map_mul, map_inv] using
    congrArg Matrix.ProjGenLinGroup.mk
      (indexCyclicGeneratorGL_conj_indexCartwrightStegerGeneratorGL
        P r level u)

/-- Equality of two projective generators forces their constant parameters
to differ by a base-field scalar. -/
theorem quotientMk_eq_of_indexCartwrightStegerGenerator_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (ConstantExtension P r)ˣ)
    (hprojective : indexCartwrightStegerGenerator P r level u =
      indexCartwrightStegerGenerator P r level v) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v := by
  have hgl :
      indexCartwrightStegerGeneratorGL P r level u =
        indexCartwrightStegerGeneratorGL P r level v :=
    generalLinear_eq_of_projective_eq_of_diagonal_one
      (generatorFirstIndex r)
      (indexCartwrightStegerGeneratorGL P r level u)
      (indexCartwrightStegerGeneratorGL P r level v)
      hprojective
      (indexCartwrightStegerGeneratorGL_apply_self P r level u _)
      (indexCartwrightStegerGeneratorGL_apply_self P r level v _)
  have hentry := congrArg
    (fun A : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) =>
      (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))
          (generatorFirstIndex r) (generatorSecondIndex r)) hgl
  change
    (indexCartwrightStegerGeneratorGL P r level u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))
        (generatorFirstIndex r) (generatorSecondIndex r) =
      (indexCartwrightStegerGeneratorGL P r level v :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))
        (generatorFirstIndex r) (generatorSecondIndex r) at hentry
  rw [indexCartwrightStegerGeneratorGL_apply_first_second,
    indexCartwrightStegerGeneratorGL_apply_first_second] at hentry
  have hratio :
      (u : ConstantExtension P r) *
          ((constantFrobenius P r).symm
            (u : ConstantExtension P r))⁻¹ =
        (v : ConstantExtension P r) *
          ((constantFrobenius P r).symm
            (v : ConstantExtension P r))⁻¹ := by
    apply (indexConstantEmbedding P r level).injective
    exact neg_injective hentry
  have hsu :
    (constantFrobenius P r).symm
          (u : ConstantExtension P r) ≠ 0 :=
    fun hzero => Units.ne_zero u <|
      (constantFrobenius P r).symm.injective (by
        rw [map_zero]
        exact hzero)
  have hsv :
    (constantFrobenius P r).symm
          (v : ConstantExtension P r) ≠ 0 :=
    fun hzero => Units.ne_zero v <|
      (constantFrobenius P r).symm.injective (by
        rw [map_zero]
        exact hzero)
  have hdiv :
      (u : ConstantExtension P r) /
          (constantFrobenius P r).symm u =
        (v : ConstantExtension P r) /
          (constantFrobenius P r).symm v := by
    simpa [div_eq_mul_inv] using hratio
  have hcross :
      (u : ConstantExtension P r) *
          (constantFrobenius P r).symm v =
        (v : ConstantExtension P r) *
          (constantFrobenius P r).symm u :=
    (div_eq_div_iff hsu hsv).mp hdiv
  have hfixedSymm :
      (constantFrobenius P r).symm
          ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) =
        (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹ := by
    have hdiv2 :
        (constantFrobenius P r).symm (u : ConstantExtension P r) /
            (constantFrobenius P r).symm (v : ConstantExtension P r) =
          (u : ConstantExtension P r) / (v : ConstantExtension P r) := by
      apply (div_eq_div_iff hsv (Units.ne_zero v)).mpr
      simpa [mul_comm] using hcross.symm
    simpa [map_mul, map_inv, div_eq_mul_inv] using hdiv2
  have hfixed :
      constantFrobenius P r
          ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) =
        (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹ := by
    have h := congrArg (constantFrobenius P r) hfixedSymm
    simpa using h.symm
  obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_constantFrobenius_eq
    P r ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) hfixed
  have ha_ne : a ≠ 0 := by
    intro hzero
    have := ha
    rw [hzero, map_zero] at this
    exact (mul_ne_zero (Units.ne_zero u) (inv_ne_zero (Units.ne_zero v))) this.symm
  let au : (BaseField P)ˣ := Units.mk0 a ha_ne
  apply QuotientGroup.eq_iff_div_mem.mpr
  change u / v ∈ baseScalarUnits P r
  refine ⟨au, ?_⟩
  apply Units.ext
  simpa [au, baseScalarUnitHom, div_eq_mul_inv] using ha

/-- Conversely, a source-projective equality is sufficient for equality of
the represented Cartwright--Steger generators. -/
theorem indexCartwrightStegerGenerator_eq_of_quotientMk_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (ConstantExtension P r)ˣ)
    (hquotient :
      (QuotientGroup.mk u : ConstantProjectiveClass P r) =
        QuotientGroup.mk v) :
    indexCartwrightStegerGenerator P r level u =
      indexCartwrightStegerGenerator P r level v := by
  have hdiv : u / v ∈ baseScalarUnits P r :=
    QuotientGroup.eq_iff_div_mem.mp hquotient
  obtain ⟨a, ha⟩ := hdiv
  have hconstantDiv :
      indexConstantPGLHom P r level (u / v) = 1 := by
    rw [← ha, indexConstantPGLHom_baseScalar]
  have hconstant :
      indexConstantPGLHom P r level u =
        indexConstantPGLHom P r level v := by
    apply div_eq_one.mp
    simpa [map_div] using hconstantDiv
  have hconstant' :
      Matrix.ProjGenLinGroup.mk (indexConstantGL P r level u) =
        Matrix.ProjGenLinGroup.mk (indexConstantGL P r level v) := by
    simpa [indexConstantPGLHom, indexConstantGL] using hconstant
  rw [indexCartwrightStegerGenerator_eq_conj,
    indexCartwrightStegerGenerator_eq_conj, hconstant']

/-- All Cartwright--Steger conjugates have the same determinant class. -/
theorem residueProjectiveDetClass_indexCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    residueProjectiveDetClass P r level
        (indexCartwrightStegerGenerator P r level u) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  rw [indexCartwrightStegerGenerator_eq_conj, map_mul, map_mul, map_inv,
    residueProjectiveDetClass_indexB]
  rw [mul_comm _
    (QuotientGroup.mk (indexRatioUnit P r level) :
      ResiduePowerClass P r level),
    mul_assoc, mul_inv_cancel, mul_one]

/-- The evaluated Cartwright--Steger generator indexed by the source
projective constant class `F_(q^d)^× / F_q^×`.  Representatives are selected
internally, exactly as in the global construction. -/
noncomputable def indexCartwrightStegerClassGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) : PGL P r level :=
  indexCartwrightStegerGenerator P r level
    (constantClassRepresentative P r u)

theorem residueProjectiveDetClass_indexCartwrightStegerClassGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    residueProjectiveDetClass P r level
        (indexCartwrightStegerClassGenerator P r level u) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  exact residueProjectiveDetClass_indexCartwrightStegerGenerator
    P r level (constantClassRepresentative P r u)

/-- The source projective constant classes index distinct finite
Cartwright--Steger generators. -/
theorem indexCartwrightStegerClassGenerator_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexCartwrightStegerClassGenerator P r level) := by
  intro u v huv
  have hmk := quotientMk_eq_of_indexCartwrightStegerGenerator_eq
    P r level (constantClassRepresentative P r u)
      (constantClassRepresentative P r v) huv
  simpa [constantClassRepresentative] using hmk

theorem one_lt_natCard_constantProjectiveClass
    (P : BasePrime) (r : Rank) :
    1 < Nat.card (ConstantProjectiveClass P r) := by
  have hcard := natCard_constantProjectiveClass_mul_baseScalar P r
  have hq : 1 ≤ P.q := P.one_le
  have hsub : P.q - 1 + 1 = P.q := Nat.sub_add_cancel hq
  by_contra hnot
  have hc : Nat.card (ConstantProjectiveClass P r) ≤ 1 :=
    Nat.le_of_not_gt hnot
  have hmul :
      Nat.card (ConstantProjectiveClass P r) * (P.q - 1) ≤
        P.q - 1 := by
    simpa using Nat.mul_le_mul_right (P.q - 1) hc
  have hpowSub : P.q ^ r.matrixRank - 1 ≤ P.q - 1 := by
    rw [← hcard]
    exact hmul
  have hpow : P.q ^ r.matrixRank ≤ P.q := by
    calc
      P.q ^ r.matrixRank = P.q ^ r.matrixRank - 1 + 1 :=
        (Nat.sub_add_cancel (one_le_pow₀ hq)).symm
      _ ≤ P.q - 1 + 1 := Nat.add_le_add_right hpowSub 1
      _ = P.q := hsub
  have hlt : P.q < P.q ^ r.matrixRank := by
    simpa using Nat.pow_lt_pow_right
      (lt_of_lt_of_le (by norm_num : 1 < 5) P.five_le)
      (show 1 < r.matrixRank by
        exact lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r))
  exact (Nat.not_lt_of_ge hpow) hlt

/-- No finite Cartwright--Steger generator collapses to the identity.
All source-indexed generators are conjugates of the same element `b`; if
one conjugate were trivial, every conjugate would be trivial, contradicting
the proved injectivity of the source projective indexing. -/
theorem indexCartwrightStegerClassGenerator_ne_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    indexCartwrightStegerClassGenerator P r level u ≠ 1 := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨v, huv⟩ := exists_ne u
  intro hu
  have hb : indexB P r level = 1 := by
    have h := congrArg
      (fun g : PGL P r level =>
        (Matrix.ProjGenLinGroup.mk (indexConstantGL P r level
          (constantClassRepresentative P r u)))⁻¹ * g *
            Matrix.ProjGenLinGroup.mk (indexConstantGL P r level
              (constantClassRepresentative P r u))) hu
    simpa [indexCartwrightStegerClassGenerator,
      indexCartwrightStegerGenerator_eq_conj, mul_assoc] using h
  have hv : indexCartwrightStegerClassGenerator P r level v = 1 := by
    simp [indexCartwrightStegerClassGenerator,
      indexCartwrightStegerGenerator_eq_conj, hb]
  exact huv ((indexCartwrightStegerClassGenerator_injective P r level)
    (hu.trans hv.symm)).symm

/-- The finite subgroup generated by all evaluated Cartwright--Steger
conjugates. -/
noncomputable def IndexCartwrightStegerImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  Subgroup.closure
    (Set.range (indexCartwrightStegerClassGenerator P r level))

/-- The same finite generator family before quotienting its source parameters
by base-field scalars.  Keeping this auxiliary closure makes the stabilizer
action completely explicit; equality with the class-indexed closure is proved
below rather than built into the definition. -/
noncomputable def IndexCartwrightStegerUnitImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  Subgroup.closure
    (Set.range (indexCartwrightStegerGenerator P r level))

theorem indexCartwrightStegerUnitGenerator_mem_unitImage
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCartwrightStegerGenerator P r level u ∈
      IndexCartwrightStegerUnitImage P r level :=
  Subgroup.subset_closure ⟨u, rfl⟩

theorem IndexCartwrightStegerImage_le_unitImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level ≤
      IndexCartwrightStegerUnitImage P r level := by
  rw [IndexCartwrightStegerImage]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨u, rfl⟩
  exact indexCartwrightStegerUnitGenerator_mem_unitImage P r level
    (constantClassRepresentative P r u)

theorem indexCartwrightStegerUnitGenerator_eq_classGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCartwrightStegerGenerator P r level u =
      indexCartwrightStegerClassGenerator P r level
        (QuotientGroup.mk u) := by
  apply indexCartwrightStegerGenerator_eq_of_quotientMk_eq
  exact (QuotientGroup.out_eq'
    (QuotientGroup.mk u : ConstantProjectiveClass P r)).symm

theorem IndexCartwrightStegerUnitImage_le_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerUnitImage P r level ≤
      IndexCartwrightStegerImage P r level := by
  rw [IndexCartwrightStegerUnitImage]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨u, rfl⟩
  rw [indexCartwrightStegerUnitGenerator_eq_classGenerator]
  exact Subgroup.subset_closure ⟨QuotientGroup.mk u, rfl⟩

/-- Quotienting source parameters by base-field scalars neither enlarges nor
shrinks the generated finite Cartwright--Steger subgroup. -/
theorem IndexCartwrightStegerUnitImage_eq_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerUnitImage P r level =
      IndexCartwrightStegerImage P r level :=
  le_antisymm
    (IndexCartwrightStegerUnitImage_le_image P r level)
    (IndexCartwrightStegerImage_le_unitImage P r level)

/-- Every represented constant unit normalizes the unquotiented finite
Cartwright--Steger image. -/
theorem indexConstantPGL_mem_normalizer_unitImage
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : (ConstantExtension P r)ˣ) :
    indexConstantPGLHom P r level a ∈
      Subgroup.normalizer
        (IndexCartwrightStegerUnitImage P r level : Set _) := by
  apply Subgroup.normalizer_le_normalizer_closure
    (Set.range (indexCartwrightStegerGenerator P r level))
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨u, rfl⟩ := hg
  exact ⟨a * u,
    indexConstantPGL_conj_indexCartwrightStegerGenerator
      P r level a u |>.symm⟩

/-- The cyclic generator normalizes the unquotiented finite
Cartwright--Steger image. -/
theorem indexCyclicGeneratorPGL_mem_normalizer_unitImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.ProjGenLinGroup.mk (indexCyclicGeneratorGL P r level) ∈
      Subgroup.normalizer
        (IndexCartwrightStegerUnitImage P r level : Set _) := by
  apply Subgroup.normalizer_le_normalizer_closure
    (Set.range (indexCartwrightStegerGenerator P r level))
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨u, rfl⟩ := hg
  exact ⟨indexConstantFrobeniusUnit P r u,
    indexCyclicGeneratorPGL_conj_indexCartwrightStegerGenerator
      P r level u |>.symm⟩

/-- The finite analogue of the LSV stabilizer: it is generated by all
represented constant units together with the cyclic element `z`. -/
noncomputable def IndexCartwrightStegerStabilizer
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  Subgroup.closure
    (Set.range (indexConstantPGLHom P r level) ∪
      {Matrix.ProjGenLinGroup.mk (indexCyclicGeneratorGL P r level)})

theorem IndexCartwrightStegerStabilizer_le_normalizer_unitImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerStabilizer P r level ≤
      Subgroup.normalizer
        (IndexCartwrightStegerUnitImage P r level : Set _) := by
  rw [IndexCartwrightStegerStabilizer]
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | hg)
  · obtain ⟨a, rfl⟩ := hg
    exact indexConstantPGL_mem_normalizer_unitImage P r level a
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact indexCyclicGeneratorPGL_mem_normalizer_unitImage P r level

theorem IndexCartwrightStegerStabilizer_le_normalizer_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerStabilizer P r level ≤
      Subgroup.normalizer
        (IndexCartwrightStegerImage P r level : Set _) := by
  rw [← IndexCartwrightStegerUnitImage_eq_image]
  exact IndexCartwrightStegerStabilizer_le_normalizer_unitImage P r level

/-- The ambient finite subgroup generated by the Cartwright--Steger image and
its explicit constant/cyclic stabilizer. -/
noncomputable def IndexCartwrightStegerAmbient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  IndexCartwrightStegerStabilizer P r level ⊔
    IndexCartwrightStegerUnitImage P r level

/-- The unquotiented Cartwright--Steger image is normal in the explicitly
generated finite ambient group. -/
instance indexCartwrightStegerUnitImage_normal_in_ambient
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((IndexCartwrightStegerUnitImage P r level).subgroupOf
      (IndexCartwrightStegerAmbient P r level)).Normal := by
  rw [IndexCartwrightStegerAmbient]
  exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
    (IndexCartwrightStegerStabilizer_le_normalizer_unitImage P r level)

/-- The original class-indexed Cartwright--Steger image is therefore normal
in the same explicit finite ambient group. -/
instance indexCartwrightStegerImage_normal_in_ambient
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((IndexCartwrightStegerImage P r level).subgroupOf
      (IndexCartwrightStegerAmbient P r level)).Normal := by
  rw [← IndexCartwrightStegerUnitImage_eq_image]
  infer_instance

theorem indexCartwrightStegerGenerator_mem_image
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    indexCartwrightStegerClassGenerator P r level u ∈
      IndexCartwrightStegerImage P r level :=
  Subgroup.subset_closure ⟨u, rfl⟩

/-- The generated image has a construction-owned nonidentity element in
`PSL`, obtained as the ratio of two distinct Cartwright--Steger generators. -/
theorem exists_nontrivial_mem_image_inter_PSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ g : PGL P r level,
      g ∈ IndexCartwrightStegerImage P r level ∧
      g ∈ PSL P r level ∧ g ≠ 1 := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨u, v, huv⟩ := exists_pair_ne (ConstantProjectiveClass P r)
  let gu := indexCartwrightStegerClassGenerator P r level u
  let gv := indexCartwrightStegerClassGenerator P r level v
  refine ⟨gu * gv⁻¹,
    (IndexCartwrightStegerImage P r level).mul_mem
      (indexCartwrightStegerGenerator_mem_image P r level u)
      ((IndexCartwrightStegerImage P r level).inv_mem
        (indexCartwrightStegerGenerator_mem_image P r level v)), ?_, ?_⟩
  · rw [← ker_residueProjectiveDetClass_eq_PSL P r level,
      MonoidHom.mem_ker, map_mul, map_inv]
    rw [residueProjectiveDetClass_indexCartwrightStegerClassGenerator,
      residueProjectiveDetClass_indexCartwrightStegerClassGenerator,
      mul_inv_cancel]
  · intro hone
    have heq : gu = gv := by
      apply (mul_inv_eq_one.mp hone)
    exact huv ((indexCartwrightStegerClassGenerator_injective P r level) heq)

/-- Exact determinant-class image of the generated finite subgroup.  This is
the image computation in LSV Proposition `whatisr`, before strong
approximation supplies the separate `PSL` containment. -/
theorem map_IndexCartwrightStegerImage_residueProjectiveDetClass
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCartwrightStegerImage P r level).map
        (residueProjectiveDetClass P r level) =
      Subgroup.zpowers
        (QuotientGroup.mk (indexRatioUnit P r level) :
          ResiduePowerClass P r level) := by
  apply le_antisymm
  · rw [IndexCartwrightStegerImage,
      MonoidHom.map_closure]
    apply (Subgroup.closure_le _).2
    rintro q ⟨g, ⟨u, rfl⟩, rfl⟩
    rw [residueProjectiveDetClass_indexCartwrightStegerClassGenerator]
    exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_eq_closure]
    apply (Subgroup.closure_le _).2
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact ⟨indexCartwrightStegerClassGenerator P r level 1,
      indexCartwrightStegerGenerator_mem_image P r level 1,
      residueProjectiveDetClass_indexCartwrightStegerClassGenerator
        P r level 1⟩

/-- The determinant-class image is all of `PGL/PSL`; equivalently, the
Cartwright--Steger finite image meets every projective determinant class. -/
theorem map_IndexCartwrightStegerImage_residueProjectiveDetClass_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCartwrightStegerImage P r level).map
        (residueProjectiveDetClass P r level) = ⊤ := by
  rw [map_IndexCartwrightStegerImage_residueProjectiveDetClass]
  apply (Subgroup.card_eq_iff_eq_top
    (Subgroup.zpowers
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level))).mp
  rw [Nat.card_zpowers, indexRatioUnit_orderOf,
    IndexSelection.natCard_powerClass]
  simp only [Fintype.card_fin]

/-- Determinant color restricted to the actual finite Cartwright--Steger
image. -/
noncomputable def indexImageDetClassHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level →*
      ResiduePowerClass P r level :=
  (residueProjectiveDetClass P r level).comp
    (IndexCartwrightStegerImage P r level).subtype

theorem indexImageDetClassHom_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexImageDetClassHom P r level) := by
  intro q
  have hq : q ∈ (IndexCartwrightStegerImage P r level).map
      (residueProjectiveDetClass P r level) := by
    rw [map_IndexCartwrightStegerImage_residueProjectiveDetClass_eq_top]
    exact Subgroup.mem_top q
  obtain ⟨g, hg, hqg⟩ := hq
  exact ⟨⟨g, hg⟩, hqg⟩

/-- The color-zero part of the constructed image. -/
noncomputable def IndexCartwrightStegerColorZero
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexCartwrightStegerImage P r level) :=
  (indexImageDetClassHom P r level).ker

noncomputable instance indexCartwrightStegerColorZeroNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCartwrightStegerColorZero P r level).Normal := by
  dsimp [IndexCartwrightStegerColorZero]
  infer_instance

theorem mem_IndexCartwrightStegerColorZero_iff_mem_PSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : IndexCartwrightStegerImage P r level) :
    g ∈ IndexCartwrightStegerColorZero P r level ↔
      (g : PGL P r level) ∈ PSL P r level := by
  change (g : PGL P r level) ∈
      (residueProjectiveDetClass P r level).ker ↔
    (g : PGL P r level) ∈ PSL P r level
  rw [ker_residueProjectiveDetClass_eq_PSL]

/-- The color quotient of the constructed image is exactly the selected
projective determinant-class group. -/
noncomputable def indexColorQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level ⧸
        IndexCartwrightStegerColorZero P r level ≃*
      ResiduePowerClass P r level :=
  QuotientGroup.quotientKerEquivOfSurjective
    (indexImageDetClassHom P r level)
    (indexImageDetClassHom_surjective P r level)

/-- Exact controlled index: the color-zero subgroup quotient is the full
projective determinant-class group.  The separate strong-approximation step
is still required to identify this subgroup with the full finite `PSL`. -/
theorem natCard_indexColorQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (IndexCartwrightStegerImage P r level ⧸
          IndexCartwrightStegerColorZero P r level) =
      Nat.card (ResiduePowerClass P r level) :=
  Nat.card_congr (indexColorQuotientEquiv P r level)

/-- Numerical form of the controlled index from LSV Proposition 6.7. -/
theorem natCard_indexColorQuotient_eq_gcd
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (IndexCartwrightStegerImage P r level ⧸
          IndexCartwrightStegerColorZero P r level) =
      (Fintype.card (ResidueField P r level) - 1).gcd
        r.matrixRank := by
  calc
    Nat.card
        (IndexCartwrightStegerImage P r level ⧸
          IndexCartwrightStegerColorZero P r level) =
        Nat.card (ResiduePowerClass P r level) :=
      natCard_indexColorQuotient P r level
    _ = (Fintype.card (ResidueField P r level) - 1).gcd
        r.matrixRank := by
      simpa only [ResiduePowerClass, Fintype.card_fin] using
        (IndexSelection.natCard_powerClass
          (ResidueField P r level) (Fintype.card (Fin r.matrixRank)))

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
