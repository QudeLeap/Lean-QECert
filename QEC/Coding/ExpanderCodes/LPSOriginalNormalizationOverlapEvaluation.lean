import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationChartEvaluation
/-!
# Original normalization complex points

Derived internal mathematics on the original modular-equation fields and
filled analytic curve. The source graph route is PK22 `ex:Xpq` (main.tex,
lines 484–486). This constructs actual local evaluations and complex points;
it does not prove GAGA, good reduction, Weil bounds, or the qLDPC main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance : TopologicalSpace (LPSOriginalFilledCurve N) := lpsOriginalFilledTopology N
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "ICL" => lpsOriginalComplexNormalLaurentChart N hpos
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq' rfl

omit [NeZero N] in
lemma lpsOriginalLaurentBase_constant (c : ℂ) :
    lpsOriginalComplexLaurentBaseToGeneratedField N hpos (LaurentPolynomial.C c) =
      algebraMap ℂ K c := by
  change algebraMap J K (lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.C c)) = _
  rw [← Polynomial.toLaurent_C, lpsOriginalComplexLaurentBaseFractionMap_polynomial]
  change algebraMap J K (algebraMap P J (Polynomial.C c)) = _
  rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ P J]
  rfl

omit [NeZero N] in
lemma lpsOriginalLaurentBase_T_one :
    lpsOriginalComplexLaurentBaseToGeneratedField N hpos (LaurentPolynomial.T 1) =
      algebraMap P K Polynomial.X := by
  change algebraMap J K (lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.T 1)) = _
  rw [lpsOriginalComplexLaurentBaseFractionMap_T_one]
  rfl

omit [NeZero N] in
lemma lpsOriginalLaurentBase_T_neg_one :
    lpsOriginalComplexLaurentBaseToGeneratedField N hpos (LaurentPolynomial.T (-1)) =
      (algebraMap P K Polynomial.X)⁻¹ := by
  change algebraMap J K
    (lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.T (-1))) = _
  rw [lpsOriginalComplexLaurentBaseFractionMap_T_neg_one, map_inv₀]
  rfl

lemma lpsOriginalLaurentBase_order_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (p : LaurentPolynomial ℂ) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (lpsOriginalComplexLaurentBaseToGeneratedField N hpos p) := by
  apply nonnegative_laurent_map (lpsOriginalFieldLocalOrder N hN hpos x)
    (lpsOriginalComplexLaurentBaseToGeneratedField N hpos)
  · intro c
    rw [lpsOriginalLaurentBase_constant]
    exact lpsOriginalFieldLocalOrder_constant_nonnegative N hN hpos x c
  · rw [lpsOriginalLaurentBase_T_one]; exact hj
  · rw [lpsOriginalLaurentBase_T_neg_one]; exact hi

lemma lpsOriginalLaurentIntegral_order_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (a : ICL) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val := by
  have ha : (lpsOriginalComplexLaurentBaseToGeneratedField N hpos).IsIntegralElem a.val :=
    a.property
  exact nonnegative_of_integral_map (lpsOriginalFieldLocalOrder N hN hpos x)
    (lpsOriginalComplexLaurentBaseToGeneratedField N hpos)
    (lpsOriginalLaurentBase_order_nonnegative N hpos hN x hj hi) ha

def lpsOriginalLaurentNormalChartToMeromorphicInteger
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    ICL →+* (AddValuation.toValuation
      (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x))).integer := by
  letI : Algebra (LaurentPolynomial ℂ) K :=
    (lpsOriginalComplexLaurentBaseToGeneratedField N hpos).toAlgebra
  let φ := (lpsOriginalFieldToLocal N hN hpos x).comp
    (integralClosure (LaurentPolynomial ℂ) K).val.toRingHom
  refine φ.codRestrict _ ?_
  intro a
  change 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val
  exact lpsOriginalLaurentIntegral_order_nonnegative N hpos hN x hj hi a

def lpsOriginalLaurentNormalChartEvaluation
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) : ICL →+* ℂ :=
  (meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN x)).comp
    (lpsOriginalLaurentNormalChartToMeromorphicInteger N hpos hN x hj hi)

lemma lpsOriginalLaurentNormalChartEvaluation_zeroDiagram
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    (lpsOriginalLaurentNormalChartEvaluation N hpos hN x hj hi).comp
      (lpsOriginalComplexNormalZeroToLaurent N hpos) =
        lpsOriginalZeroNormalChartEvaluation N hpos hN x hj := by
  apply RingHom.ext
  intro a
  rfl

lemma lpsOriginalLaurentNormalChartEvaluation_infinityDiagram
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    (lpsOriginalLaurentNormalChartEvaluation N hpos hN x hj hi).comp
      (lpsOriginalComplexNormalInfinityToLaurent N hpos) =
        lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi := by
  apply RingHom.ext
  intro a
  rfl

end
end QEC.Coding.TannerLiftedProduct
