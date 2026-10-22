import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewResidueCoordinates

/-!
# Faithfulness of the integral skew representation

The coefficients of the global matrix representation are recovered from the
residue-class Laurent coordinates.  In particular, the representation of the
integral skew Laurent ring is injective.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

/-- Reduce an arbitrary integral power of the cyclic generator to its unique
residue exponent, with the quotient recorded by the central scalar `1 + y`. -/
theorem globalCyclicZMatrixHom_decomposition
    (P : BasePrime) (r : Rank) (n : ℤ) :
    globalCyclicZMatrixHom P r (Multiplicative.ofAdd n) =
      (algebraMap (FunctionField P) (SplittingFunctionField P r)
        ((1 + RatFunc.X) ^ skewExponentQuotient r n)) •
        cyclicGeneratorMatrix P r ^ (skewExponentResidue r n : ℕ) := by
  let a : (SplittingFunctionField P r)ˣ :=
    Units.mk0 (onePlusY P r) (onePlusY_ne_zero P r)
  have hgl : cyclicGenerator P r ^ r.matrixRank =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) a := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    rw [cyclicGenerator_val, cyclicGenerator_pow_matrixRank]
    change onePlusY P r • 1 = Matrix.scalar (Fin r.matrixRank) (onePlusY P r)
    rw [Matrix.scalar_apply]
    exact Matrix.smul_one_eq_diagonal _
  rw [globalCyclicZMatrixHom_apply]
  change ((↑((cyclicGenerator P r) ^ n)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) = _
  conv_lhs => rw [skewExponent_decomposition r n]
  rw [zpow_add, zpow_mul, zpow_natCast, hgl, ← map_zpow]
  change ((Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
      (a ^ skewExponentQuotient r n) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _) *
      cyclicGeneratorMatrix P r ^ (skewExponentResidue r n : ℕ) = _
  have ha : ((a ^ skewExponentQuotient r n :
      (SplittingFunctionField P r)ˣ) : SplittingFunctionField P r) =
      algebraMap (FunctionField P) (SplittingFunctionField P r)
        ((1 + RatFunc.X) ^ skewExponentQuotient r n) := by
    calc
      ((a ^ skewExponentQuotient r n :
          (SplittingFunctionField P r)ˣ) : SplittingFunctionField P r) =
          (onePlusY P r) ^ skewExponentQuotient r n := by
            exact Units.val_zpow_eq_zpow_val a _
      _ = (functionFieldEmbedding P r (1 + RatFunc.X)) ^
          skewExponentQuotient r n := by
            congr 1
            simp [onePlusY, functionFieldEmbedding_X]
      _ = functionFieldEmbedding P r
          ((1 + RatFunc.X) ^ skewExponentQuotient r n) :=
        (map_zpow₀ (functionFieldEmbedding P r)
          (1 + RatFunc.X) (skewExponentQuotient r n)).symm
  have hscalar :
      ((↑(Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
          (a ^ skewExponentQuotient r n))) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) =
        ((a ^ skewExponentQuotient r n :
          (SplittingFunctionField P r)ˣ) : SplittingFunctionField P r) • 1 := by
    change Matrix.scalar (Fin r.matrixRank)
        (((a ^ skewExponentQuotient r n :
          (SplittingFunctionField P r)ˣ) : SplittingFunctionField P r)) = _
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hscalar, smul_mul_assoc, one_mul, ha]

/-- On a single skew monomial, each matrix-basis coordinate is the evaluation
at `1 + y` of the corresponding residue-class Laurent coordinate. -/
theorem splittingCyclicBasis_repr_skewLaurentToGlobalMatrix_single
    (P : BasePrime) (r : Rank) (m : Multiplicative ℤ)
    (c : ConstantExtension P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (splittingCyclicBasis P r).repr
        (skewLaurentToGlobalMatrix P r
          (SkewMonoidAlgebra.single m c)) p =
      algebraMap (FunctionField P) (SplittingFunctionField P r)
        (functionFieldOnePlusYLaurentEvaluation P
          (skewLaurentCyclicLaurentCoordinate P r
            (SkewMonoidAlgebra.single m c) p)) := by
  rcases p with ⟨i, k⟩
  rw [skewLaurentToGlobalMatrix_single]
  have hm : m = Multiplicative.ofAdd m.toAdd := rfl
  conv_lhs => rw [hm, globalCyclicZMatrixHom_decomposition]
  rw [mul_smul_comm, LinearEquiv.map_smul]
  change (algebraMap (FunctionField P) (SplittingFunctionField P r)
      ((1 + RatFunc.X) ^ skewExponentQuotient r m.toAdd)) *
      ((splittingCyclicBasis P r).repr
        (constantMatrix P r c * cyclicGeneratorMatrix P r ^
          (skewExponentResidue r m.toAdd : ℕ))) (i, k) = _
  rw [
    splittingCyclicBasis_repr_cyclicMonomial]
  rw [skewLaurentCyclicLaurentCoordinate_single]
  by_cases h : skewExponentResidue r m.toAdd = k
  · subst k
    simp only [if_true]
    rw [functionFieldOnePlusYLaurentEvaluation,
      LaurentPolynomial.eval₂_C_mul_T, map_mul,
      Units.val_zpow_eq_zpow_val]
    have hc : algebraMap (FunctionField P) (SplittingFunctionField P r)
        (algebraMap (BaseField P) (FunctionField P)
          ((constantBasis P r).repr c i)) =
        algebraMap (BaseField P) (SplittingFunctionField P r)
          ((constantBasis P r).repr c i) := by
      change functionFieldEmbedding P r
          (RatFunc.C ((constantBasis P r).repr c i)) = _
      exact functionFieldEmbedding_C P r _
    rw [hc]
    have hu : ((functionFieldOnePlusYUnit P : (FunctionField P)ˣ) :
        FunctionField P) ^ skewExponentQuotient r m.toAdd =
        (1 + RatFunc.X) ^ skewExponentQuotient r m.toAdd := rfl
    rw [hu, map_zpow₀, map_add, map_one]
    have hx : algebraMap (FunctionField P) (SplittingFunctionField P r)
        (RatFunc.X : FunctionField P) =
        (RatFunc.X : SplittingFunctionField P r) :=
      functionFieldEmbedding_X P r
    rw [hx]
    ac_rfl
  · have h' : k ≠ skewExponentResidue r m.toAdd := by
      intro hk
      exact h hk.symm
    have hzRight :
        (if skewExponentResidue r m.toAdd = k then
          LaurentPolynomial.C ((constantBasis P r).repr c i) *
            LaurentPolynomial.T (skewExponentQuotient r m.toAdd)
        else 0 : LaurentPolynomial (BaseField P)) = 0 := if_neg h
    have hzLeft :
        (if k = skewExponentResidue r m.toAdd then
          algebraMap (BaseField P) (SplittingFunctionField P r)
            ((constantBasis P r).repr c i)
        else 0 : SplittingFunctionField P r) = 0 := if_neg h'
    rw [hzRight, hzLeft, mul_zero, map_zero, map_zero]

/-- The residue-class Laurent coordinate formula for an arbitrary skew
Laurent polynomial. -/
theorem splittingCyclicBasis_repr_skewLaurentToGlobalMatrix
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (splittingCyclicBasis P r).repr
        (skewLaurentToGlobalMatrix P r f) p =
      algebraMap (FunctionField P) (SplittingFunctionField P r)
        (functionFieldOnePlusYLaurentEvaluation P
          (skewLaurentCyclicLaurentCoordinate P r f p)) := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, LinearEquiv.map_add]
      change ((splittingCyclicBasis P r).repr
          (skewLaurentToGlobalMatrix P r f)) p +
          ((splittingCyclicBasis P r).repr
            (skewLaurentToGlobalMatrix P r g)) p = _
      rw [hf, hg, skewLaurentCyclicLaurentCoordinate_add, map_add, map_add]
  | single m c =>
      exact splittingCyclicBasis_repr_skewLaurentToGlobalMatrix_single
        P r m c p

/-- The explicit global matrix representation of the integral skew Laurent
ring is faithful. -/
theorem skewLaurentToGlobalMatrix_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (skewLaurentToGlobalMatrix P r) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply skewLaurent_eq_zero_of_cyclicLaurentCoordinates_eq_zero P r
  intro p
  apply functionFieldOnePlusYLaurentEvaluation_injective P
  apply functionFieldEmbedding_injective P r
  have hzero : skewLaurentToGlobalMatrix P r (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  calc
    _ = (splittingCyclicBasis P r).repr
        (skewLaurentToGlobalMatrix P r (f - g)) p :=
      (splittingCyclicBasis_repr_skewLaurentToGlobalMatrix
        P r (f - g) p).symm
    _ = 0 := by rw [hzero, map_zero]; exact Finsupp.zero_apply
    _ = _ := by simp

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
