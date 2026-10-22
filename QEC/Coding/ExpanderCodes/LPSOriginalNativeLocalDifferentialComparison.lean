import QEC.Coding.ExpanderCodes.LPSOriginalLocalRegularDifferentialComparison
import QEC.Coding.ExpanderCodes.LPSOriginalGenericCompactDifferentialComparison

/-!
# Actual native covectors and original local differential coefficients

Descend the literal chart coefficient of a native covector through its actual
codiscrete-zero quotient. Prove all-df compatibility and whole universal
differential agreement in the SAME original C(j,jN), including pointwise
function multiplication. Identify native no-pole coefficients with the actual
regular differential lattice and meromorphic-order DVR differential image.

Derived internal closure on the PK22 ex:Xpq route (pinned main.tex 484–486),
for parent #449. This is a comparison at constructed filled analytic points;
global algebraic point coverage and GAGA remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "Cov" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
local instance : Algebra ℂ G := (germComplexConstants a).toAlgebra

local instance : AddCommGroup Cov := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup

/-- The actual representative chart coefficient as a complex-linear map to local germs. -/
def lpsOriginalCovectorRepresentativeToLocal : Cov →ₗ[ℂ] G := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := lpsOriginalLocalChart N hN x
  have ha : a ∈ e.target := e.map_source (lpsOriginalLocalChart_mem_source N hN x)
  exact
    { toFun := fun σ => ⟨(lpsOriginalFilledCovectorChartCoefficient N hN σ.val x : Germ (𝓝[≠] a) ℂ),
        lpsOriginalFilledCovectorChartCoefficient N hN σ.val x,σ.property x a ha,rfl⟩
      map_add' := by
        intro σ τ
        apply Subtype.ext
        change ((lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x) (σ.val+τ.val) :
          Germ (𝓝[≠] a) ℂ) = _
        rw [map_add]
        rfl
      map_smul' := by
        intro c σ
        apply Subtype.ext
        change ((lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x) (c • σ.val) :
          Germ (𝓝[≠] a) ℂ) = _
        rw [map_smul]
        rfl }

/-- Actual codiscrete-zero native covectors have zero coefficient germ at each filled point. -/
lemma lpsOriginalCovectorGlobalZero_le_localKernel :
    lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN ≤
      (lpsOriginalCovectorRepresentativeToLocal N hN x).ker := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro σ hσ
  change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), σ.val y = 0 at hσ
  let e := lpsOriginalLocalChart N hN x
  have hx : x ∈ e.source := lpsOriginalLocalChart_mem_source N hN x
  have ha : e x ∈ e.target := e.map_source hx
  have hp : ∀ᶠ y in 𝓝[≠] x, σ.val y = 0 := by
    have h := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hσ x (Set.mem_univ x)
    change {y | σ.val y = 0} ∈ 𝓝[≠] x
    simpa only [Set.compl_univ,Set.union_empty] using h
  have ht : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
    have h : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] (e.symm (e x))) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(e.symm.continuousAt ha).tendsto.mono_left nhdsWithin_le_nhds,
          e.symm.eventually_ne_nhdsWithin ha⟩
    simpa only [e.left_inv hx] using h
  change lpsOriginalCovectorRepresentativeToLocal N hN x σ = 0
  apply Subtype.ext
  change (lpsOriginalFilledCovectorChartCoefficient N hN σ.val x : Germ (𝓝[≠] a) ℂ) = 0
  apply Germ.coe_eq.mpr
  filter_upwards [ht.eventually hp] with z hz
  change σ.val ((chartAt ℂ x).symm z) = 0 at hz
  simp only [lpsOriginalFilledCovectorChartCoefficient,ContinuousLinearMap.inCoordinates]
  rw [hz]
  simp

/-- Descend literal native chart coefficients through the actual compact covector quotient. -/
def lpsOriginalNativeCovectorToLocal :
    LPSOriginalCompactMeromorphicCovectorGerms N hN →ₗ[ℂ] G :=
  (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN).liftQ
    (lpsOriginalCovectorRepresentativeToLocal N hN x)
    (lpsOriginalCovectorGlobalZero_le_localKernel N hN x)

/-- The descended coefficient map evaluates each genuine representative by its actual chart coefficient. -/
lemma lpsOriginalNativeCovectorToLocal_class (σ : Cov) :
    lpsOriginalNativeCovectorToLocal N hN x (lpsOriginalCompactMeromorphicCovectorClass N hN σ) =
      lpsOriginalCovectorRepresentativeToLocal N hN x σ := rfl


/-- Actual df agrees with differentiation of its actual local function representative. -/
lemma lpsOriginalCovectorRepresentativeToLocal_D
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) :
    lpsOriginalCovectorRepresentativeToLocal N hN x
      ⟨lpsOriginalFilledFunctionCovector N hN F.val,
        lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩ =
      germDerivative a (lpsOriginalRepresentativeToLocal N hN x F) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := lpsOriginalLocalChart N hN x
  have ha : a ∈ e.target := e.map_source (lpsOriginalLocalChart_mem_source N hN x)
  apply Subtype.ext
  change (lpsOriginalFilledCovectorChartCoefficient N hN
    (lpsOriginalFilledFunctionCovector N hN F.val) x : Germ (𝓝[≠] a) ℂ) = _
  rw [germDerivative_value a (lpsOriginalRepresentativeToLocal N hN x F)
    (F.val ∘ e.symm) (F.property x a ha) rfl]
  apply Germ.coe_eq.mpr
  filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds ha)] with z hz
  exact lpsOriginalFilledFunctionCovector_chart N hN F.val x z hz

/-- Pointwise multiplication becomes actual multiplication of local coefficient germs. -/
lemma lpsOriginalCovectorRepresentativeToLocal_functionTimes
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) (σ : Cov) :
    lpsOriginalCovectorRepresentativeToLocal N hN x
      (lpsOriginalFilledMeromorphicFunctionTimesCovector N hN F σ) =
      lpsOriginalRepresentativeToLocal N hN x F *
        lpsOriginalCovectorRepresentativeToLocal N hN x σ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards with z
  exact lpsOriginalFilledFunctionTimesCovector_chart N hN F.val σ.val x z


section GenericComparison
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance : SMulCommClass ℂ K K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f * g) = f * (algebraMap ℂ K c * g)
    ring
local instance : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra
local instance : Algebra K G := (lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).toAlgebra
local instance : SMul K G := Algebra.toSMul (R := K) (A := G)
local instance : Module K G := Algebra.toModule (R := K) (A := G)

/-- Whole native universal df compatibility, independent of the chosen actual representative. -/
lemma lpsOriginalNativeCovectorToLocal_D (f : K)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalNativeCovectorToLocal N hN x
      (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
        (KaehlerDifferential.D ℂ K f)) =
      lpsOriginalFieldLocalDifferentialMap N hpos hN x (KaehlerDifferential.D ℂ K f) := by
  rw [lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D N hpos hN f F hF,
    lpsOriginalNativeCovectorToLocal_class,lpsOriginalCovectorRepresentativeToLocal_D,
    lpsOriginalFieldLocalDifferentialMap_D,
    lpsOriginalFieldToLocal_representative N hN hpos x f F hF]

/-- Every universal differential has the same actual native and universal local coefficient. -/
lemma lpsOriginalNativeCovectorToLocal_agrees (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalNativeCovectorToLocal N hN x
      (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm) =
      lpsOriginalFieldLocalDifferentialMap N hpos hN x differentialForm := by
  let c : K := lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm
  let dj : KaehlerDifferential ℂ K := KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X)
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN c)
  have hFc : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN c := hF
  let σ : Cov := ⟨lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N),
    lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
      (lpsOriginalFilledChartMeromorphic_j N hN)⟩
  have hσ : lpsOriginalCompactMeromorphicCovectorClass N hN σ =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN dj :=
    (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D_j N hpos hN).symm
  have hσlocal : lpsOriginalCovectorRepresentativeToLocal N hN x σ =
      germDerivative a (lpsOriginalRepresentativeToLocal N hN x
        ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩) :=
    lpsOriginalCovectorRepresentativeToLocal_D N hN x
      ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩
  have hdifferentialForm : differentialForm = c • dj := lpsOriginalGenericKaehler_expand N hpos differentialForm
  rw [hdifferentialForm,lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_functionTimes
    N hpos hN c dj F σ hFc hσ,lpsOriginalNativeCovectorToLocal_class,
    lpsOriginalCovectorRepresentativeToLocal_functionTimes,
    ← lpsOriginalFieldToLocal_representative N hN hpos x c F hFc]
  change lpsOriginalFieldToLocal N hN hpos x c *
    lpsOriginalCovectorRepresentativeToLocal N hN x σ = _
  rw [hσlocal,← lpsOriginalFieldToLocal_j N hN hpos x]
  change lpsOriginalFieldToLocal N hN hpos x c *
    germDerivative a (lpsOriginalFieldToLocal N hN hpos x (algebraMap P K Polynomial.X)) =
      lpsOriginalFieldLocalDifferentialMap N hpos hN x
        (c • KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X))
  rw [map_smul,lpsOriginalFieldLocalDifferentialMap_D]
  rfl


section Regularity
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance : SMul V K := Algebra.toSMul (R := V) (A := K)
local instance : Module V K := Algebra.toModule (R := V) (A := K)
local instance : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance : SMul V (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Module V (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- Actual native covectors are no-pole exactly on the original regular-function differential lattice. -/
lemma lpsOriginalLocalDifferentialLattice_iff_nativeNoPole
    (differentialForm : KaehlerDifferential ℂ K) :
    differentialForm ∈ lpsOriginalLocalDifferentialLattice N hpos hN x ↔
      0 ≤ meromorphicOrderValuation a
        (lpsOriginalNativeCovectorToLocal N hN x
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm)) := by
  rw [lpsOriginalNativeCovectorToLocal_agrees]
  exact lpsOriginalLocalDifferentialLattice_iff_noPole N hpos hN x differentialForm

/-- The real original Ω(V/C) image is exactly the no-pole actual native covector condition. -/
lemma lpsOriginalLocalKaehlerRange_iff_nativeNoPole
    (differentialForm : KaehlerDifferential ℂ K) :
    differentialForm ∈ ((KaehlerDifferential.D ℂ K).compAlgebraMap V).liftKaehlerDifferential.range ↔
      0 ≤ meromorphicOrderValuation a
        (lpsOriginalNativeCovectorToLocal N hN x
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm)) := by
  rw [lpsOriginalNativeCovectorToLocal_agrees]
  exact lpsOriginalLocalKaehlerRange_iff_noPole N hpos hN x differentialForm

end Regularity

end GenericComparison

end
end QEC.Coding.TannerLiftedProduct
