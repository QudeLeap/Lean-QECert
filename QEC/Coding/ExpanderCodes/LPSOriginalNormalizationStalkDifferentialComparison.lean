import QEC.Coding.AlgebraicGeometry.Schemes.StalkScalars
import QEC.Coding.AlgebraicGeometry.Differentials.KaehlerMapImage
import QEC.Coding.ExpanderCodes.LPSOriginalNativeLocalDifferentialComparison
import QEC.Coding.ExpanderCodes.LPSOriginalLocalRegularDifferentialComparison

/-!
# Actual original normalization stalk differentials and native regularity

At each constructed filled point of the original Gamma0(N) curve, evaluate
the structural scalar germs of the actual glued normalization on both charts.
The genuine stalk ring equivalence preserves these scalars, hence is a complex
algebra equivalence with the actual meromorphic-order DVR. The real stalk
Kähler image in the SAME C(j,jN) consists exactly of universal differentials
whose actual native chart coefficient has no pole.

Derived internal closure for parent #449 and PK22 ex:Xpq (pinned main.tex
484–486). No global point coverage/GAGA, original good reduction, Frobenius/Weil
bound, or arbitrary-finite-field explicit quantum family is established here.
The public main-theorem claim and its verified TeX remain unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped TensorProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
local notation "ICI" => lpsOriginalComplexNormalInfinityChart N hpos
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl

/-- Actual zero-chart constants embed as the unchanged complex constants in the original field. -/
lemma lpsOriginalZeroConstant_value (c : ℂ) :
    (lpsOriginalComplexZeroConstantRingHom N hpos c).val = algebraMap ℂ K c := by
  rw [lpsOriginalComplexZeroConstantChartRingHom_apply]
  change (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hpos (c ⊗ₜ[ℤ] 1)).val = _
  simpa only [OneMemClass.coe_one,map_one,mul_one] using
    lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue N hpos c 1

/-- Actual infinity-chart constants embed as the unchanged complex constants in the original field. -/
lemma lpsOriginalInfinityConstant_value (c : ℂ) :
    (lpsOriginalComplexInfinityConstantRingHom N hpos c).val = algebraMap ℂ K c := by
  rw [lpsOriginalComplexInfinityConstantChartRingHom_apply]
  change (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hpos (c ⊗ₜ[ℤ] 1)).val = _
  simpa only [OneMemClass.coe_one,map_one,mul_one] using
    lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue N hpos c 1

/-- The actual zero-chart stalk equivalence preserves each structural complex constant. -/
lemma lpsOriginalZeroPointStalk_constant (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) (c : ℂ) :
    ((lpsOriginalZeroNormalizationPointLocalRingEquiv N hpos hN x hj)
      (StructureSheaf.toStalk IC0
        ((lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj).base
          (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ))
        (lpsOriginalComplexZeroConstantRingHom N hpos c))).val = algebraMap ℂ K c := by
  change ((lpsOriginalZeroStalkMeromorphicValuationRingEquiv N hpos hN x hj)
    (algebraMap IC0 _ (lpsOriginalComplexZeroConstantRingHom N hpos c))).val = _
  rw [lpsOriginalZeroStalkMeromorphicValuationRingEquiv_algebraMap]
  exact lpsOriginalZeroConstant_value N hpos c

/-- The actual infinity-chart stalk equivalence preserves each structural complex constant. -/
lemma lpsOriginalInfinityPointStalk_constant (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹)
    (c : ℂ) :
    ((lpsOriginalInfinityNormalizationPointLocalRingEquiv N hpos hN x hi)
      (StructureSheaf.toStalk ICI
        ((lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi).base
          (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ))
        (lpsOriginalComplexInfinityConstantRingHom N hpos c))).val = algebraMap ℂ K c := by
  change ((lpsOriginalInfinityStalkMeromorphicValuationRingEquiv N hpos hN x hi)
    (algebraMap ICI _ (lpsOriginalComplexInfinityConstantRingHom N hpos c))).val = _
  rw [lpsOriginalInfinityStalkMeromorphicValuationRingEquiv_algebraMap]
  exact lpsOriginalInfinityConstant_value N hpos c


/-- Literal scalar germ along the actual normalization structural morphism to Spec C. -/
def lpsOriginalNormalizationStalkStructuralScalar (x : LPSOriginalFilledCurve N) :
    ℂ →+* (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)) :=
  schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
    (lpsOriginalComplexNormalGluedToSpecC N hpos)
    ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
      (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ))

/-- The actual glued zero-chart stalk transport preserves structural scalar germs. -/
lemma lpsOriginalNormalizationStalkStructuralScalar_zero (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) (c : ℂ) :
    ((lpsOriginalNormalizationCurveLocalRingEquiv_zero N hpos hN x hj)
      (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x c)).val = algebraMap ℂ K c := by
  let y := (lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj).base
    (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)
  let : IsOpenImmersion (lpsOriginalComplexNormalGluedChartMap N hpos false) :=
    lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos false
  let e := (CategoryTheory.asIso
    ((lpsOriginalComplexNormalGluedChartMap N hpos false).stalkMap y)).commRingCatIsoToRingEquiv.trans
    (lpsOriginalZeroNormalizationPointLocalRingEquiv N hpos hN x hj)
  have ht := scalarRingEquiv_transport (.of ℂ)
    (.of ((AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring))
    (Spec (.of ℂ) ⟶ lpsOriginalComplexNormalGluedScheme N hpos)
    (fun q => (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      (q.base (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))
    (fun q => schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
      (lpsOriginalComplexNormalGluedToSpecC N hpos)
      (q.base (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))
    (lpsOriginalNormalizationCurveSpecPoint_zero N hpos hN x hj) e c
  refine (congrArg (fun v => v.val) ht).trans ?_
  change ((lpsOriginalZeroNormalizationPointLocalRingEquiv N hpos hN x hj)
    ((lpsOriginalComplexNormalGluedChartMap N hpos false).stalkMap y
      (schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
        (lpsOriginalComplexNormalGluedToSpecC N hpos)
        ((lpsOriginalComplexNormalGluedChartMap N hpos false) y) c))).val = _
  have hc := schemeStalkScalar_chart (.of ℂ) (.of IC0)
    (lpsOriginalComplexNormalGluedScheme N hpos)
    (lpsOriginalComplexNormalGluedChartMap N hpos false)
    (lpsOriginalComplexNormalGluedToSpecC N hpos)
    (CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hpos))
    (lpsOriginalComplexNormalGluedToSpecC_chart N hpos false) y c
  exact (congrArg (fun z => ((lpsOriginalZeroNormalizationPointLocalRingEquiv
    N hpos hN x hj) z).val) hc).trans
      (lpsOriginalZeroPointStalk_constant N hpos hN x hj c)

/-- The actual glued infinity-chart stalk transport preserves structural scalar germs. -/
lemma lpsOriginalNormalizationStalkStructuralScalar_infinity (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹)
    (c : ℂ) :
    ((lpsOriginalNormalizationCurveLocalRingEquiv_infinity N hpos hN x hi)
      (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x c)).val = algebraMap ℂ K c := by
  let y := (lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi).base
    (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)
  let : IsOpenImmersion (lpsOriginalComplexNormalGluedChartMap N hpos true) :=
    lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos true
  let e := (CategoryTheory.asIso
    ((lpsOriginalComplexNormalGluedChartMap N hpos true).stalkMap y)).commRingCatIsoToRingEquiv.trans
    (lpsOriginalInfinityNormalizationPointLocalRingEquiv N hpos hN x hi)
  have ht := scalarRingEquiv_transport (.of ℂ)
    (.of ((AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring))
    (Spec (.of ℂ) ⟶ lpsOriginalComplexNormalGluedScheme N hpos)
    (fun q => (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      (q.base (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))
    (fun q => schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
      (lpsOriginalComplexNormalGluedToSpecC N hpos)
      (q.base (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))
    (lpsOriginalNormalizationCurveSpecPoint_infinity N hpos hN x hi) e c
  refine (congrArg (fun v => v.val) ht).trans ?_
  change ((lpsOriginalInfinityNormalizationPointLocalRingEquiv N hpos hN x hi)
    ((lpsOriginalComplexNormalGluedChartMap N hpos true).stalkMap y
      (schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
        (lpsOriginalComplexNormalGluedToSpecC N hpos)
        ((lpsOriginalComplexNormalGluedChartMap N hpos true) y) c))).val = _
  have hc := schemeStalkScalar_chart (.of ℂ) (.of ICI)
    (lpsOriginalComplexNormalGluedScheme N hpos)
    (lpsOriginalComplexNormalGluedChartMap N hpos true)
    (lpsOriginalComplexNormalGluedToSpecC N hpos)
    (CommRingCat.ofHom (lpsOriginalComplexInfinityConstantRingHom N hpos))
    (lpsOriginalComplexNormalGluedToSpecC_chart N hpos true) y c
  exact (congrArg (fun z => ((lpsOriginalInfinityNormalizationPointLocalRingEquiv
    N hpos hN x hi) z).val) hc).trans
      (lpsOriginalInfinityPointStalk_constant N hpos hN x hi c)

/-- The previously constructed whole original stalk ring equivalence preserves actual structural scalars. -/
lemma lpsOriginalNormalizationStalkStructuralScalar_value (x : LPSOriginalFilledCurve N) (c : ℂ) :
    ((lpsOriginalNormalizationCurveLocalRingEquiv N hpos hN x)
      (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x c)).val = algebraMap ℂ K c := by
  by_cases hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)
  · simp only [lpsOriginalNormalizationCurveLocalRingEquiv,dif_pos hj]
    exact lpsOriginalNormalizationStalkStructuralScalar_zero N hpos hN x hj c
  · simp only [lpsOriginalNormalizationCurveLocalRingEquiv,dif_neg hj]
    exact lpsOriginalNormalizationStalkStructuralScalar_infinity N hpos hN x
      ((lpsOriginalNormalizationChart_order_cover N hpos hN x).resolve_left hj) c

/-- The actual original glued normalization stalk at the constructed complex point. -/
abbrev lpsOriginalNormalizationPointStalk (x : LPSOriginalFilledCurve N) : CommRingCat :=
  (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
    ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
      (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ))
variable (x : LPSOriginalFilledCurve N)
local notation "St" => lpsOriginalNormalizationPointStalk N hpos hN x
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance : Algebra ℂ St := (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x).toAlgebra
local instance : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra

/-- Genuine C-algebra equivalence for the actual original glued stalk and meromorphic-order DVR. -/
def lpsOriginalNormalizationStalkValuationComplexAlgEquiv : St ≃ₐ[ℂ] V where
  toRingEquiv := lpsOriginalNormalizationCurveLocalRingEquiv N hpos hN x
  commutes' c := by
    apply Subtype.ext
    change ((lpsOriginalNormalizationCurveLocalRingEquiv N hpos hN x)
      (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x c)).val = algebraMap ℂ K c
    exact lpsOriginalNormalizationStalkStructuralScalar_value N hpos hN x c


/-- Actual embedding of the original normalization stalk into the SAME original function field. -/
def lpsOriginalNormalizationStalkToFieldComplexAlgHom : St →ₐ[ℂ] K where
  toRingHom := (ValuationSubring.subtype V).comp
    (lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).toRingHom
  commutes' c := by
    exact congrArg (fun v : V => v.val)
      ((lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).commutes c)

local instance : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance : Algebra St V :=
  (lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).toRingHom.toAlgebra
local instance : Algebra St K := (lpsOriginalNormalizationStalkToFieldComplexAlgHom N hpos hN x).toAlgebra
local instance : IsScalarTower ℂ St V := .of_algebraMap_eq fun c =>
  ((lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).commutes c).symm
local instance : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
local instance : IsScalarTower ℂ St K := .of_algebraMap_eq fun c =>
  ((lpsOriginalNormalizationStalkToFieldComplexAlgHom N hpos hN x).commutes c).symm
local instance : IsScalarTower St V K := .of_algebraMap_eq fun v => by rfl

local instance : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance : SMulCommClass ℂ St K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (algebraMap St K f * g) =
      algebraMap St K f * (algebraMap ℂ K c * g)
    ring
local instance : SMulCommClass ℂ St V where
  smul_comm c f g := by
    change algebraMap ℂ V c * (algebraMap St V f * g) =
      algebraMap St V f * (algebraMap ℂ V c * g)
    ring
local instance : SMulCommClass ℂ K K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f * g) = f * (algebraMap ℂ K c * g)
    ring
local instance : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance : SMul V (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Module V (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance : SMul St (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Module St (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance : SMul St (KaehlerDifferential ℂ V) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ V
local instance : Module St (KaehlerDifferential ℂ V) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ V

/-- The real original stalk Kähler image equals the real meromorphic-order DVR Kähler image. -/
lemma lpsOriginalNormalizationStalkKaehlerRange_iff_valuation
    (differentialForm : KaehlerDifferential ℂ K) :
    differentialForm ∈ (KaehlerDifferential.map ℂ ℂ St K).range ↔
      differentialForm ∈ (KaehlerDifferential.map ℂ ℂ V K).range := by
  apply kaehler_field_map_range_iff ℂ St V K
  exact (lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).surjective

/-- Actual original normalization-stalk Kähler regularity is equivalent to the native analytic no-pole coefficient. -/
lemma lpsOriginalNormalizationStalkKaehlerRange_iff_nativeNoPole
    (differentialForm : KaehlerDifferential ℂ K) :
    differentialForm ∈ (KaehlerDifferential.map ℂ ℂ St K).range ↔
      0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
        (lpsOriginalNativeCovectorToLocal N hN x
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm)) := by
  rw [lpsOriginalNormalizationStalkKaehlerRange_iff_valuation]
  change differentialForm ∈
    ((KaehlerDifferential.D ℂ K).compAlgebraMap V).liftKaehlerDifferential.range ↔ _
  exact lpsOriginalLocalKaehlerRange_iff_nativeNoPole
    (N := N) (hN := hN) (x := x) (hpos := hpos) differentialForm

end
end QEC.Coding.TannerLiftedProduct
