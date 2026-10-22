import QEC.Coding.ExpanderCodes.LPSOriginalLocalMeromorphicOrder
import QEC.Coding.AlgebraicGeometry.Places.AnalyticGermEvaluation
import QEC.Coding.ExpanderCodes.LPSOriginalComplexNormalCharts

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
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra
local instance : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq' rfl

def lpsOriginalZeroNormalChartToMeromorphicInteger
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    IC0 →+* (AddValuation.toValuation
      (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x))).integer := by
  let φ := (lpsOriginalFieldToLocal N hN hpos x).comp (integralClosure P K).val.toRingHom
  refine φ.codRestrict _ ?_
  intro a
  change 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val
  exact lpsOriginalFieldLocalOrder_integral_nonnegative N hN hpos x hj a

def lpsOriginalZeroNormalChartEvaluation
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    IC0 →+* ℂ :=
  (meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN x)).comp
    (lpsOriginalZeroNormalChartToMeromorphicInteger N hpos hN x hj)

lemma lpsOriginalZeroNormalChartEvaluation_rep
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (a : IC0) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x))
    (he : F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g) :
    lpsOriginalZeroNormalChartEvaluation N hpos hN x hj a = g (lpsOriginalLocalChartCenter N hN x) := by
  apply meromorphicNoPoleEvaluation_rep _ _ g hg
  change (lpsOriginalFieldToLocal N hN hpos x a.val).val = (g : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  rw [lpsOriginalFieldToLocal_representative N hN hpos x a.val F hF]
  change (F.val ∘ (lpsOriginalLocalChart N hN x).symm : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ) = (g : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  exact Filter.Germ.coe_eq.mpr he

lemma lpsOriginalZeroNormalChartEvaluation_analytic_representative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (a : IC0) :
    ∃ F : LPSOriginalFilledMeromorphicFunctionRing N hN,
      lpsOriginalCompactMeromorphicGermAlgHom N hN F =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x) ∧
        F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g ∧
        lpsOriginalZeroNormalChartEvaluation N hpos hN x hj a = g (lpsOriginalLocalChartCenter N hN x) := by
  obtain ⟨F,hF,g,hg,he⟩ := lpsOriginalZeroIntegral_analytic_extension N hN hpos x hj a
  exact ⟨F,hF,g,hg,he,lpsOriginalZeroNormalChartEvaluation_rep N hpos hN x hj a F hF g hg he⟩

omit [NeZero N] in
lemma lpsOriginalReciprocalFieldPolynomialMap_eval (p : P) :
    lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p =
      p.eval₂ (algebraMap ℂ K) (algebraMap P K Polynomial.X)⁻¹ := by
  let φ : J →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ J K
  change algebraMap J K
    (QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction.fractionInverse ℂ
      (algebraMap P J p)) = _
  rw [QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction.fractionInverse_polynomial]
  change φ (p.eval₂ (algebraMap ℂ J) (algebraMap P J Polynomial.X)⁻¹) = _
  rw [Polynomial.algHom_eval₂_algebraMap, map_inv₀]
  rfl

lemma lpsOriginalReciprocalFieldPolynomialMap_order_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (p : P) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p) := by
  rw [lpsOriginalReciprocalFieldPolynomialMap_eval]
  exact nonnegative_polynomial_eval (lpsOriginalFieldLocalOrder N hN hpos x)
    (algebraMap ℂ K) (lpsOriginalFieldLocalOrder_constant_nonnegative N hN hpos x) _ hj p

lemma lpsOriginalInfinityIntegral_order_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (a : lpsOriginalComplexNormalInfinityChart N hpos) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val := by
  have hi : (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem a.val :=
    a.property
  exact nonnegative_of_integral_map (lpsOriginalFieldLocalOrder N hN hpos x)
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos)
    (lpsOriginalReciprocalFieldPolynomialMap_order_nonnegative N hpos hN x hj) hi

lemma lpsOriginalNormalizationChart_order_cover (x : LPSOriginalFilledCurve N) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X) ∨
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹ :=
  additiveValuation_nonnegative_or_inverse (lpsOriginalFieldLocalOrder N hN hpos x) _

def lpsOriginalInfinityNormalChartToMeromorphicInteger
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalComplexNormalInfinityChart N hpos →+*
      (AddValuation.toValuation (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x))).integer := by
  letI : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
  let φ := (lpsOriginalFieldToLocal N hN hpos x).comp (integralClosure P K).val.toRingHom
  refine φ.codRestrict _ ?_
  intro a
  change 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val
  exact lpsOriginalInfinityIntegral_order_nonnegative N hpos hN x hj a

def lpsOriginalInfinityNormalChartEvaluation
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalComplexNormalInfinityChart N hpos →+* ℂ :=
  (meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN x)).comp
    (lpsOriginalInfinityNormalChartToMeromorphicInteger N hpos hN x hj)

lemma lpsOriginalInfinityNormalChartEvaluation_rep
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (a : lpsOriginalComplexNormalInfinityChart N hpos)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x))
    (he : F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g) :
    lpsOriginalInfinityNormalChartEvaluation N hpos hN x hj a = g (lpsOriginalLocalChartCenter N hN x) := by
  apply meromorphicNoPoleEvaluation_rep _ _ g hg
  change (lpsOriginalFieldToLocal N hN hpos x a.val).val =
    (g : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  rw [lpsOriginalFieldToLocal_representative N hN hpos x a.val F hF]
  change (F.val ∘ (lpsOriginalLocalChart N hN x).symm : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ) =
    (g : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  exact Filter.Germ.coe_eq.mpr he

lemma lpsOriginalInfinityNormalChartEvaluation_analytic_representative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (a : lpsOriginalComplexNormalInfinityChart N hpos) :
    ∃ F : LPSOriginalFilledMeromorphicFunctionRing N hN,
      lpsOriginalCompactMeromorphicGermAlgHom N hN F =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x) ∧
        F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g ∧
        lpsOriginalInfinityNormalChartEvaluation N hpos hN x hj a = g (lpsOriginalLocalChartCenter N hN x) := by
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val)
  have hv := lpsOriginalInfinityIntegral_order_nonnegative N hpos hN x hj a
  rw [lpsOriginalFieldLocalOrder_value,
    lpsOriginalFieldToLocal_representative N hN hpos x a.val F hF] at hv
  change 0 ≤ meromorphicOrderAt (F.val ∘ (lpsOriginalLocalChart N hN x).symm)
    (lpsOriginalLocalChartCenter N hN x) at hv
  obtain ⟨g,hg,he⟩ := (F.property x _ ((lpsOriginalLocalChart N hN x).map_source
    (lpsOriginalLocalChart_mem_source N hN x))).meromorphicOrderAt_nonneg_iff.mp hv
  exact ⟨F,hF,g,hg,he,lpsOriginalInfinityNormalChartEvaluation_rep N hpos hN x hj a F hF g hg he⟩

lemma lpsOriginalZeroConstantChart_value (c : ℂ) :
    (lpsOriginalComplexZeroConstantRingHom N hpos c).val = algebraMap ℂ K c := by
  rw [lpsOriginalComplexZeroConstantChartRingHom_apply]
  have h := lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue N hpos c 1
  have h1 : (1 : lpsOriginalIntegerNormalZeroChart N hpos).val = 1 := rfl
  rw [h1, map_one, mul_one] at h
  exact h

lemma lpsOriginalInfinityConstantChart_value (c : ℂ) :
    (lpsOriginalComplexInfinityConstantRingHom N hpos c).val = algebraMap ℂ K c := by
  rw [lpsOriginalComplexInfinityConstantChartRingHom_apply]
  have h := lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue N hpos c 1
  have h1 : (1 : lpsOriginalIntegerNormalInfinityChart N hpos).val = 1 := rfl
  rw [h1, map_one, mul_one] at h
  exact h

lemma lpsOriginalZeroNormalChartEvaluation_constant
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) (c : ℂ) :
    lpsOriginalZeroNormalChartEvaluation N hpos hN x hj
      (lpsOriginalComplexZeroConstantRingHom N hpos c) = c := by
  apply meromorphicNoPoleEvaluation_rep _ _ (fun _ => c) analyticAt_const
  change (lpsOriginalFieldToLocal N hN hpos x
    (lpsOriginalComplexZeroConstantRingHom N hpos c).val).val =
      ((fun _ : ℂ => c) : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  rw [lpsOriginalZeroConstantChart_value, lpsOriginalFieldToLocal_constant]
  rfl

lemma lpsOriginalInfinityNormalChartEvaluation_constant
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) (c : ℂ) :
    lpsOriginalInfinityNormalChartEvaluation N hpos hN x hj
      (lpsOriginalComplexInfinityConstantRingHom N hpos c) = c := by
  apply meromorphicNoPoleEvaluation_rep _ _ (fun _ => c) analyticAt_const
  change (lpsOriginalFieldToLocal N hN hpos x
    (lpsOriginalComplexInfinityConstantRingHom N hpos c).val).val =
      ((fun _ : ℂ => c) : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  rw [lpsOriginalInfinityConstantChart_value, lpsOriginalFieldToLocal_constant]
  rfl

lemma lpsOriginalZeroNormalChartEvaluation_surjective
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    Function.Surjective (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj) :=
  fun c => ⟨lpsOriginalComplexZeroConstantRingHom N hpos c,
    lpsOriginalZeroNormalChartEvaluation_constant N hpos hN x hj c⟩

lemma lpsOriginalInfinityNormalChartEvaluation_surjective
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    Function.Surjective (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hj) :=
  fun c => ⟨lpsOriginalComplexInfinityConstantRingHom N hpos c,
    lpsOriginalInfinityNormalChartEvaluation_constant N hpos hN x hj c⟩

end
end QEC.Coding.TannerLiftedProduct
