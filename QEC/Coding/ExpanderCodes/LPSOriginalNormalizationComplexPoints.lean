import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationOverlapEvaluation
import QEC.Coding.ExpanderCodes.LPSOriginalGlobalNormalizationComparison

/-!
# Original normalization complex points

Derived internal mathematics on the original modular-equation fields and
filled analytic curve. The source graph route is PK22 `ex:Xpq` (main.tex,
lines 484–486). This constructs actual local evaluations and complex points;
it does not prove GAGA, good reduction, Weil bounds, or the qLDPC main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance : TopologicalSpace (LPSOriginalFilledCurve N) := lpsOriginalFilledTopology N
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq' rfl

def lpsOriginalZeroNormalizationSpecPoint (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    Spec (.of ℂ) ⟶ lpsOriginalComplexNormalSchemeChart N hpos false :=
  Spec.map (CommRingCat.ofHom (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj))

def lpsOriginalInfinityNormalizationSpecPoint (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    Spec (.of ℂ) ⟶ lpsOriginalComplexNormalSchemeChart N hpos true :=
  Spec.map (CommRingCat.ofHom (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi))

def lpsOriginalLaurentNormalizationSpecPoint (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    Spec (.of ℂ) ⟶ Spec (.of (lpsOriginalComplexNormalLaurentChart N hpos)) :=
  Spec.map (CommRingCat.ofHom (lpsOriginalLaurentNormalChartEvaluation N hpos hN x hj hi))

lemma lpsOriginalLaurentNormalizationSpecPoint_zeroDiagram (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalLaurentNormalizationSpecPoint N hpos hN x hj hi ≫
      lpsOriginalComplexNormalSchemeOverlapMap N hpos false =
        lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (lpsOriginalLaurentNormalChartEvaluation_zeroDiagram N hpos hN x hj hi)

lemma lpsOriginalLaurentNormalizationSpecPoint_infinityDiagram (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalLaurentNormalizationSpecPoint N hpos hN x hj hi ≫
      lpsOriginalComplexNormalSchemeOverlapMap N hpos true =
        lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (lpsOriginalLaurentNormalChartEvaluation_infinityDiagram N hpos hN x hj hi)

lemma lpsOriginalNormalizationSpecPoint_gluedAgreement (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj ≫
      lpsOriginalComplexNormalGluedChartMap N hpos false =
    lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi ≫
      lpsOriginalComplexNormalGluedChartMap N hpos true := by
  rw [← lpsOriginalLaurentNormalizationSpecPoint_zeroDiagram N hpos hN x hj hi,
    ← lpsOriginalLaurentNormalizationSpecPoint_infinityDiagram N hpos hN x hj hi]
  simp only [Category.assoc]
  rw [lpsOriginalComplexNormalGluedOverlap_agreement]

lemma lpsOriginalZeroNormalizationSpecPoint_overC (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj ≫
      lpsOriginalComplexChartToSpecC N hpos false = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp]
  have hc : (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj).comp
      (lpsOriginalComplexZeroConstantRingHom N hpos) = RingHom.id ℂ := by
    apply RingHom.ext
    intro c
    exact lpsOriginalZeroNormalChartEvaluation_constant N hpos hN x hj c
  change Spec.map (CommRingCat.ofHom ((lpsOriginalZeroNormalChartEvaluation N hpos hN x hj).comp
    (lpsOriginalComplexZeroConstantRingHom N hpos))) = 𝟙 _
  rw [hc]
  simp

lemma lpsOriginalInfinityNormalizationSpecPoint_overC (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi ≫
      lpsOriginalComplexChartToSpecC N hpos true = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp]
  have hc : (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi).comp
      (lpsOriginalComplexInfinityConstantRingHom N hpos) = RingHom.id ℂ := by
    apply RingHom.ext
    intro c
    exact lpsOriginalInfinityNormalChartEvaluation_constant N hpos hN x hi c
  change Spec.map (CommRingCat.ofHom ((lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi).comp
    (lpsOriginalComplexInfinityConstantRingHom N hpos))) = 𝟙 _
  rw [hc]
  simp

def lpsOriginalNormalizationCurveSpecPoint (x : LPSOriginalFilledCurve N) :
    Spec (.of ℂ) ⟶ lpsOriginalComplexNormalGluedScheme N hpos := by
  classical
  exact if hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X) then
    lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj ≫
      lpsOriginalComplexNormalGluedChartMap N hpos false
  else
    lpsOriginalInfinityNormalizationSpecPoint N hpos hN x
      ((lpsOriginalNormalizationChart_order_cover N hpos hN x).resolve_left hj) ≫
        lpsOriginalComplexNormalGluedChartMap N hpos true

lemma lpsOriginalNormalizationCurveSpecPoint_overC (x : LPSOriginalFilledCurve N) :
    lpsOriginalNormalizationCurveSpecPoint N hpos hN x ≫
      lpsOriginalComplexNormalGluedToSpecC N hpos = 𝟙 _ := by
  classical
  unfold lpsOriginalNormalizationCurveSpecPoint
  split_ifs with hj
  · rw [Category.assoc, lpsOriginalComplexNormalGluedToSpecC_chart]
    exact lpsOriginalZeroNormalizationSpecPoint_overC N hpos hN x hj
  · rw [Category.assoc, lpsOriginalComplexNormalGluedToSpecC_chart]
    exact lpsOriginalInfinityNormalizationSpecPoint_overC N hpos hN x _

lemma lpsOriginalNormalizationCurveSpecPoint_zero (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    lpsOriginalNormalizationCurveSpecPoint N hpos hN x =
      lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj ≫
        lpsOriginalComplexNormalGluedChartMap N hpos false := by
  classical
  simp only [lpsOriginalNormalizationCurveSpecPoint, dif_pos hj]

lemma lpsOriginalNormalizationCurveSpecPoint_infinity (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalNormalizationCurveSpecPoint N hpos hN x =
      lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi ≫
        lpsOriginalComplexNormalGluedChartMap N hpos true := by
  classical
  unfold lpsOriginalNormalizationCurveSpecPoint
  split_ifs with hj
  · exact lpsOriginalNormalizationSpecPoint_gluedAgreement N hpos hN x hj hi
  · rfl

def lpsOriginalNormalizationIntegerBaseChangeSpecPoint (x : LPSOriginalFilledCurve N) :
    Spec (.of ℂ) ⟶ lpsOriginalIntegerNormalComplexBaseChange N hpos :=
  lpsOriginalNormalizationCurveSpecPoint N hpos hN x ≫
    (lpsOriginalComplexNormalGluedIntegerBaseChangeIso N hpos).hom

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalNormalizationIntegerBaseChangeSpecPoint_complexProjection
    (x : LPSOriginalFilledCurve N) :
    lpsOriginalNormalizationIntegerBaseChangeSpecPoint N hpos hN x ≫ pullback.fst _ _ = 𝟙 _ := by
  change (lpsOriginalNormalizationCurveSpecPoint N hpos hN x ≫
    lpsOriginalComplexNormalToIntegerBaseChange N hpos) ≫ _ = _
  rw [Category.assoc, lpsOriginalComplexNormalToIntegerBaseChange_complexProjection]
  exact lpsOriginalNormalizationCurveSpecPoint_overC N hpos hN x

end
end QEC.Coding.TannerLiftedProduct
