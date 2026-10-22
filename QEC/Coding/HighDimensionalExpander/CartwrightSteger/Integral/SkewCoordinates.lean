import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.ArithmeticCyclicCoordinates
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewRepresentation

/-!
# Integral cyclic coordinates and the skew Laurent representation

This module identifies scalar matrices with coefficients in
`F_q[y, 1/(1+y)]` inside the image of the genuine skew Laurent
representation.  Together with the integral cyclic-coordinate theorem,
this supplies the missing reverse bridge from the Cartwright--Steger order
to `F_(q^d){z,z⁻¹}`.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

noncomputable def functionFieldScalarMatrix
    (P : BasePrime) (r : Rank) :
    FunctionField P →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  (Matrix.scalar (Fin r.matrixRank)).comp (functionFieldEmbedding P r)

/-- Function-field scalars represented by actual skew Laurent elements. -/
noncomputable def globalSkewScalarRange
    (P : BasePrime) (r : Rank) : Subring (FunctionField P) where
  carrier := {x | ∃ f : CartwrightStegerSkewLaurentRing P r,
    skewLaurentToGlobalMatrix P r f = functionFieldScalarMatrix P r x}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro x y ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨f + g, ?_⟩
    simp only [map_add, hf, hg]
  neg_mem' := by
    rintro x ⟨f, hf⟩
    refine ⟨-f, ?_⟩
    simp only [map_neg, hf]
  mul_mem' := by
    rintro x y ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨f * g, ?_⟩
    simp only [map_mul, hf, hg]

theorem baseField_scalar_mem_globalSkewScalarRange
    (P : BasePrime) (r : Rank) (a : BaseField P) :
    algebraMap (BaseField P) (FunctionField P) a ∈
      globalSkewScalarRange P r := by
  refine ⟨SkewMonoidAlgebra.single 1
    (algebraMap (BaseField P) (ConstantExtension P r) a), ?_⟩
  rw [skewLaurentToGlobalMatrix_single]
  simp only [globalCyclicZMatrixHom_apply]
  simp
  ext i j
  by_cases hij : i = j
  · subst j
    simp [constantMatrix, functionFieldScalarMatrix, functionFieldEmbedding_C]
  · simp [constantMatrix, functionFieldScalarMatrix, hij]

theorem ratFuncX_mem_globalSkewScalarRange
    (P : BasePrime) (r : Rank) :
    (RatFunc.X : FunctionField P) ∈ globalSkewScalarRange P r := by
  let zd : CartwrightStegerSkewLaurentRing P r :=
    SkewMonoidAlgebra.single
      (Multiplicative.ofAdd (r.matrixRank : ℤ)) 1
  refine ⟨zd - 1, ?_⟩
  rw [map_sub, map_one]
  dsimp [zd]
  rw [skewLaurentToGlobalMatrix_single]
  simp only [globalCyclicZMatrixHom_apply]
  change constantMatrix P r 1 *
      ((cyclicGenerator P r) ^ (r.matrixRank : ℤ) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) - 1 = _
  rw [zpow_natCast]
  change constantMatrix P r 1 *
      cyclicGeneratorMatrix P r ^ r.matrixRank - 1 = _
  rw [cyclicGenerator_pow_matrixRank]
  rw [show constantMatrix P r 1 = 1 by
    exact map_one (constantMatrixEmbedding P r), one_mul]
  have hscalar :
      (onePlusY P r) •
          (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
        Matrix.scalar (Fin r.matrixRank) (onePlusY P r) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hscalar]
  change Matrix.scalar (Fin r.matrixRank) (onePlusY P r) - 1 =
    Matrix.scalar (Fin r.matrixRank) (functionFieldEmbedding P r RatFunc.X)
  rw [functionFieldEmbedding_X]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.one_apply,
      if_pos]
    simp only [Matrix.diagonal_apply, if_pos]
    dsimp only [onePlusY]
    ring
  · simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.one_apply,
      if_neg hij]
    simp only [Matrix.diagonal_apply, if_neg hij]
    simp only [sub_zero]

theorem polynomial_scalar_mem_globalSkewScalarRange
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    algebraMap (PolynomialRing P) (FunctionField P) f ∈
      globalSkewScalarRange P r := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [map_add]
      exact (globalSkewScalarRange P r).add_mem hf hg
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact (globalSkewScalarRange P r).mul_mem
        (baseField_scalar_mem_globalSkewScalarRange P r a)
        ((globalSkewScalarRange P r).pow_mem
          (ratFuncX_mem_globalSkewScalarRange P r) n)

noncomputable def skewLaurentRankMonomial
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r :=
  SkewMonoidAlgebra.single
    (Multiplicative.ofAdd (r.matrixRank : ℤ)) 1

noncomputable def skewLaurentRankMonomialInv
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r :=
  SkewMonoidAlgebra.single
    (Multiplicative.ofAdd (-(r.matrixRank : ℤ))) 1

theorem skewLaurentToGlobalMatrix_rankMonomial
    (P : BasePrime) (r : Rank) :
    skewLaurentToGlobalMatrix P r (skewLaurentRankMonomial P r) =
      functionFieldScalarMatrix P r (1 + RatFunc.X) := by
  rw [skewLaurentRankMonomial, skewLaurentToGlobalMatrix_single]
  simp only [globalCyclicZMatrixHom_apply]
  change constantMatrix P r 1 *
      ((cyclicGenerator P r) ^ (r.matrixRank : ℤ) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) = _
  rw [zpow_natCast]
  change constantMatrix P r 1 *
      cyclicGeneratorMatrix P r ^ r.matrixRank = _
  rw [cyclicGenerator_pow_matrixRank]
  rw [show constantMatrix P r 1 = 1 by
    exact map_one (constantMatrixEmbedding P r), one_mul]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.one_apply, if_pos,
      functionFieldScalarMatrix, RingHom.comp_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    rw [functionFieldEmbedding_onePlusY]
    simp
  · simp [functionFieldScalarMatrix, hij]

theorem skewLaurentRankMonomialInv_mul_rankMonomial
    (P : BasePrime) (r : Rank) :
    skewLaurentRankMonomialInv P r * skewLaurentRankMonomial P r = 1 := by
  rw [skewLaurentRankMonomialInv, skewLaurentRankMonomial,
    SkewMonoidAlgebra.single_mul_single]
  simp

theorem functionField_onePlusY_ne_zero (P : BasePrime) :
    (1 + RatFunc.X : FunctionField P) ≠ 0 := by
  intro h
  have hm := congrArg (functionFieldEmbedding P (Rank.three)) h
  rw [map_zero, functionFieldEmbedding_onePlusY] at hm
  exact onePlusY_ne_zero P Rank.three hm

theorem skewLaurentToGlobalMatrix_rankMonomialInv
    (P : BasePrime) (r : Rank) :
    skewLaurentToGlobalMatrix P r (skewLaurentRankMonomialInv P r) =
      functionFieldScalarMatrix P r
        ((1 + RatFunc.X : FunctionField P)⁻¹) := by
  let A := skewLaurentToGlobalMatrix P r
    (skewLaurentRankMonomialInv P r)
  let S := functionFieldScalarMatrix P r
    (1 + RatFunc.X : FunctionField P)
  let B := functionFieldScalarMatrix P r
    ((1 + RatFunc.X : FunctionField P)⁻¹)
  have hAS : A * S = 1 := by
    have h := congrArg (skewLaurentToGlobalMatrix P r)
      (skewLaurentRankMonomialInv_mul_rankMonomial P r)
    simpa only [map_mul, map_one, skewLaurentToGlobalMatrix_rankMonomial,
      A, S] using h
  have hSB : S * B = 1 := by
    change functionFieldScalarMatrix P r (1 + RatFunc.X) *
      functionFieldScalarMatrix P r ((1 + RatFunc.X)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ (functionField_onePlusY_ne_zero P), map_one]
  change A = B
  calc
    A = A * (S * B) := by rw [hSB, mul_one]
    _ = (A * S) * B := by rw [mul_assoc]
    _ = B := by rw [hAS, one_mul]

theorem ratFuncOnePlusXInv_mem_globalSkewScalarRange
    (P : BasePrime) (r : Rank) :
    ((1 + RatFunc.X : FunctionField P)⁻¹) ∈
      globalSkewScalarRange P r :=
  ⟨skewLaurentRankMonomialInv P r,
    skewLaurentToGlobalMatrix_rankMonomialInv P r⟩

noncomputable def polynomialToGlobalSkewScalarRange
    (P : BasePrime) (r : Rank) :
    PolynomialRing P →+* globalSkewScalarRange P r where
  toFun f := ⟨algebraMap (PolynomialRing P) (FunctionField P) f,
    polynomial_scalar_mem_globalSkewScalarRange P r f⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' f g := Subtype.ext (map_add _ f g)
  map_mul' f g := Subtype.ext (map_mul _ f g)

@[simp] theorem polynomialToGlobalSkewScalarRange_coe
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    (polynomialToGlobalSkewScalarRange P r f : FunctionField P) =
      algebraMap (PolynomialRing P) (FunctionField P) f := rfl

noncomputable def globalSkewScalarOnePlusXUnit
    (P : BasePrime) (r : Rank) : (globalSkewScalarRange P r)ˣ where
  val := ⟨1 + RatFunc.X,
    (globalSkewScalarRange P r).add_mem
      (globalSkewScalarRange P r).one_mem
      (ratFuncX_mem_globalSkewScalarRange P r)⟩
  inv := ⟨(1 + RatFunc.X : FunctionField P)⁻¹,
    ratFuncOnePlusXInv_mem_globalSkewScalarRange P r⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (functionField_onePlusY_ne_zero P))
  inv_val := Subtype.ext (inv_mul_cancel₀ (functionField_onePlusY_ne_zero P))

noncomputable def integralArithmeticToGlobalSkewScalarRange
    (P : BasePrime) (r : Rank) :
    IntegralArithmeticRing P →+* globalSkewScalarRange P r :=
  IsLocalization.Away.lift
    (1 + Polynomial.X : PolynomialRing P)
    (S := IntegralArithmeticRing P)
    (g := polynomialToGlobalSkewScalarRange P r) (by
      have hu := (globalSkewScalarOnePlusXUnit P r).isUnit
      convert hu using 1
      apply Subtype.ext
      simp [polynomialToGlobalSkewScalarRange,
        globalSkewScalarOnePlusXUnit])

@[simp] theorem integralArithmeticToGlobalSkewScalarRange_algebraMap
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    integralArithmeticToGlobalSkewScalarRange P r
        (algebraMap (PolynomialRing P) (IntegralArithmeticRing P) f) =
      polynomialToGlobalSkewScalarRange P r f := by
  exact IsLocalization.Away.lift_eq _ _ _

theorem integralArithmeticToGlobalSkewScalarRange_coe
    (P : BasePrime) (r : Rank) (a : IntegralArithmeticRing P) :
    (integralArithmeticToGlobalSkewScalarRange P r a : FunctionField P) =
      integralArithmeticToFunctionField P a := by
  have hhom :
      (globalSkewScalarRange P r).subtype.comp
          (integralArithmeticToGlobalSkewScalarRange P r) =
        integralArithmeticToFunctionField P := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (1 + Polynomial.X : PolynomialRing P))
    apply RingHom.ext
    intro f
    simp only [RingHom.comp_apply,
      integralArithmeticToGlobalSkewScalarRange_algebraMap,
      integralArithmeticToFunctionField_algebraMap]
    rfl
  exact RingHom.congr_fun hhom a

theorem exists_skewLaurent_of_integralArithmetic
    (P : BasePrime) (r : Rank) (a : IntegralArithmeticRing P) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f =
        functionFieldScalarMatrix P r
          (integralArithmeticToFunctionField P a) := by
  obtain ⟨f, hf⟩ := (integralArithmeticToGlobalSkewScalarRange P r a).property
  refine ⟨f, ?_⟩
  rw [← integralArithmeticToGlobalSkewScalarRange_coe P r a]
  exact hf

noncomputable def skewLaurentCyclicBasisMonomial
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    CartwrightStegerSkewLaurentRing P r :=
  SkewMonoidAlgebra.single (Multiplicative.ofAdd (p.2 : ℤ))
    (constantBasis P r p.1)

theorem skewLaurentToGlobalMatrix_cyclicBasisMonomial
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentToGlobalMatrix P r
        (skewLaurentCyclicBasisMonomial P r p) =
      (functionFieldCyclicBasisVector P r p :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) := by
  rw [skewLaurentCyclicBasisMonomial, skewLaurentToGlobalMatrix_single]
  simp only [globalCyclicZMatrixHom_apply]
  change constantMatrix P r (constantBasis P r p.1) *
      ((cyclicGenerator P r) ^ (p.2 : ℤ) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) = _
  rw [zpow_natCast]
  rfl

theorem skewLaurentToGlobalMatrix_integralScalar_mul_cyclicBasisMonomial
    (P : BasePrime) (r : Rank) (a : IntegralArithmeticRing P)
    (f : CartwrightStegerSkewLaurentRing P r)
    (hf : skewLaurentToGlobalMatrix P r f =
      functionFieldScalarMatrix P r
        (integralArithmeticToFunctionField P a))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentToGlobalMatrix P r
        (f * skewLaurentCyclicBasisMonomial P r p) =
      (integralArithmeticToFunctionField P a) •
        (functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by
  rw [map_mul, hf, skewLaurentToGlobalMatrix_cyclicBasisMonomial]
  ext i j
  simp [functionFieldScalarMatrix, Matrix.mul_apply,
    Matrix.diagonal_apply, Algebra.smul_def]
  left
  rfl

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
