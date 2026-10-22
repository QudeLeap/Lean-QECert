import QEC.Coding.ExpanderCodes.LPSOriginalCompactMeromorphicFunctionField
import QEC.Coding.AlgebraicGeometry.Places.MeromorphicGerms
import QEC.Coding.ExpanderCodes.LPSOriginalGenericCompactDifferentialComparison

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
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
local instance lpsOriginalLocalChartGermTopology : TopologicalSpace (LPSOriginalFilledCurve N) :=
  lpsOriginalFilledTopology N

abbrev lpsOriginalLocalChart (x : LPSOriginalFilledCurve N) :
    OpenPartialHomeomorph (LPSOriginalFilledCurve N) ℂ := by
  letI := lpsOriginalFilledChartedSpace N hN
  exact chartAt ℂ x

lemma lpsOriginalLocalChart_mem_source (x : LPSOriginalFilledCurve N) :
    x ∈ (lpsOriginalLocalChart N hN x).source := by
  let := lpsOriginalFilledChartedSpace N hN
  exact mem_chart_source ℂ x

abbrev lpsOriginalLocalChartCenter (x : LPSOriginalFilledCurve N) : ℂ := (lpsOriginalLocalChart N hN x) x

def lpsOriginalRepresentativeToLocal (x : LPSOriginalFilledCurve N) :
    LPSOriginalFilledMeromorphicFunctionRing N hN →+*
      MeromorphicGermRing (lpsOriginalLocalChartCenter N hN x) where
  toFun F := ⟨(F.val ∘ (lpsOriginalLocalChart N hN x).symm : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ),
    F.val ∘ (lpsOriginalLocalChart N hN x).symm,
    F.property x _ ((lpsOriginalLocalChart N hN x).map_source (lpsOriginalLocalChart_mem_source N hN x)), rfl⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

lemma lpsOriginalGlobalKernel_le_localKernel (x : LPSOriginalFilledCurve N) :
    RingHom.ker (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict ≤
      RingHom.ker (lpsOriginalRepresentativeToLocal N hN x) := by
  intro F hF
  change (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F = 0 at hF
  have hzero := congrArg Subtype.val hF
  have hg : F.val =ᶠ[Filter.codiscrete (LPSOriginalFilledCurve N)] 0 :=
    Filter.Germ.coe_eq.mp hzero
  let e := lpsOriginalLocalChart N hN x
  have hx : x ∈ e.source := lpsOriginalLocalChart_mem_source N hN x
  have ha : e x ∈ e.target := e.map_source hx
  have hp : F.val =ᶠ[𝓝[≠] x] 0 := by
    have hh := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hg x (Set.mem_univ x)
    have hh' : {y | F.val y = (0 : ℂ)} ∈ 𝓝[≠] x := by
      simpa only [Set.compl_univ, Set.union_empty, Pi.zero_apply] using hh
    exact hh'
  have ht : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
    have h : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] (e.symm (e x))) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(e.symm.continuousAt ha).tendsto.mono_left nhdsWithin_le_nhds,
          e.symm.eventually_ne_nhdsWithin ha⟩
    simpa only [e.left_inv hx] using h
  change lpsOriginalRepresentativeToLocal N hN x F = 0
  apply Subtype.ext
  change (F.val ∘ (lpsOriginalLocalChart N hN x).symm : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ) =
    (0 : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  apply Filter.Germ.coe_eq.mpr
  exact ht.eventually hp

def lpsOriginalCompactToLocal (x : LPSOriginalFilledCurve N) :
    LPSOriginalCompactMeromorphicGermRing N hN →+*
      MeromorphicGermRing (lpsOriginalLocalChartCenter N hN x) :=
  ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.liftOfSurjective
    (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective)
    ⟨lpsOriginalRepresentativeToLocal N hN x, lpsOriginalGlobalKernel_le_localKernel N hN x⟩

lemma compactToLocal_representative (x : LPSOriginalFilledCurve N)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) :
    lpsOriginalCompactToLocal N hN x ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F) =
      lpsOriginalRepresentativeToLocal N hN x F :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

def lpsOriginalFieldToLocal (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    lpsOriginalGeneratedFunctionField N hpos →+* MeromorphicGermRing (lpsOriginalLocalChartCenter N hN x) :=
  (lpsOriginalCompactToLocal N hN x).comp
    (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN).toRingHom

/-- Pull actual analytic orders back to the independently defined original field. -/
def lpsOriginalFieldLocalOrder (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    AddValuation (lpsOriginalGeneratedFunctionField N hpos) (WithTop ℤ) := by
  letI := lpsOriginalJFractionEmbedding.toAlgebra
  exact (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)).comap
    (lpsOriginalFieldToLocal N hN hpos x)

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalFieldLocalOrder_value (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ f : lpsOriginalGeneratedFunctionField N hpos,
      lpsOriginalFieldLocalOrder N hN hpos x f =
        meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x) (lpsOriginalFieldToLocal N hN hpos x f) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  intro f
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalFieldLocalOrder_ne_top (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ f : lpsOriginalGeneratedFunctionField N hpos, f ≠ 0 →
      lpsOriginalFieldLocalOrder N hN hpos x f ≠ ⊤ := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  intro f hf htop
  have hlocal : lpsOriginalFieldToLocal N hN hpos x f = 0 :=
    (meromorphicOrderValuation_eq_top_iff _ _).mp htop
  apply hf
  exact (lpsOriginalFieldToLocal N hN hpos x).injective
    (hlocal.trans (map_zero _).symm)

section ActualScalarAndCoordinate
variable (hpos : 0 < N)
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra
local instance : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq' rfl

lemma lpsOriginalFieldToLocal_constant (x : LPSOriginalFilledCurve N) (c : ℂ) :
    lpsOriginalFieldToLocal N hN hpos x (algebraMap ℂ K c) =
      lpsOriginalRepresentativeToLocal N hN x (lpsOriginalFilledMeromorphicComplexConstants N hN c) := by
  change lpsOriginalCompactToLocal N hN x
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN (algebraMap ℂ K c)) = _
  rw [(lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN).commutes]
  exact compactToLocal_representative N hN x _

lemma lpsOriginalFieldToLocal_j (x : LPSOriginalFilledCurve N) :
    lpsOriginalFieldToLocal N hN hpos x (algebraMap P K Polynomial.X) =
      lpsOriginalRepresentativeToLocal N hN x
        ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩ := by
  change lpsOriginalCompactToLocal N hN x
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
      (algebraMap P K Polynomial.X)) = _
  rw [lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j]
  exact compactToLocal_representative N hN x _

lemma lpsOriginalFieldLocalOrder_constant_nonnegative
    (x : LPSOriginalFilledCurve N) (c : ℂ) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap ℂ K c) := by
  rw [lpsOriginalFieldLocalOrder_value, lpsOriginalFieldToLocal_constant]
  change 0 ≤ meromorphicOrderAt (fun _ : ℂ => c) (lpsOriginalLocalChartCenter N hN x)
  exact (MeromorphicAt.const c _).meromorphicOrderAt_nonneg_iff.mpr
    ⟨fun _ => c, analyticAt_const, Filter.EventuallyEq.rfl⟩

/-- At an actual filled-curve point where j has no pole, all C[j] coefficients have no pole. -/
lemma lpsOriginalFieldLocalOrder_polynomial_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (p : P) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K p) := by
  let φ : P →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ P K
  have he : p.eval₂ (algebraMap ℂ K) (algebraMap P K Polynomial.X) =
      algebraMap P K p := Polynomial.eval₂_algebraMap_X p φ
  rw [← he]
  exact nonnegative_polynomial_eval (lpsOriginalFieldLocalOrder N hN hpos x)
    (algebraMap ℂ K) (lpsOriginalFieldLocalOrder_constant_nonnegative N hN hpos x)
    _ hj p

/-- Every actual integral element of the original zero normalization chart has no local pole. -/
lemma lpsOriginalFieldLocalOrder_integral_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (a : integralClosure P K) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val :=
  nonnegative_of_integral_map (lpsOriginalFieldLocalOrder N hN hpos x) (algebraMap P K)
    (lpsOriginalFieldLocalOrder_polynomial_nonnegative N hN hpos x hj) a.property

lemma lpsOriginalFieldToLocal_representative (x : LPSOriginalFilledCurve N)
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalFieldToLocal N hN hpos x f = lpsOriginalRepresentativeToLocal N hN x F := by
  change lpsOriginalCompactToLocal N hN x
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) = _
  rw [← hF]
  exact compactToLocal_representative N hN x F

lemma lpsOriginalZeroIntegral_analytic_extension
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (a : integralClosure P K) :
    ∃ F : LPSOriginalFilledMeromorphicFunctionRing N hN,
      lpsOriginalCompactMeromorphicGermAlgHom N hN F =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x) ∧
        F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g := by
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val)
  refine ⟨F,hF,?_⟩
  have hv := lpsOriginalFieldLocalOrder_integral_nonnegative N hN hpos x hj a
  rw [lpsOriginalFieldLocalOrder_value,
    lpsOriginalFieldToLocal_representative N hN hpos x a.val F hF] at hv
  change 0 ≤ meromorphicOrderAt (F.val ∘ (lpsOriginalLocalChart N hN x).symm)
    (lpsOriginalLocalChartCenter N hN x) at hv
  exact (F.property x _ ((lpsOriginalLocalChart N hN x).map_source
    (lpsOriginalLocalChart_mem_source N hN x))).meromorphicOrderAt_nonneg_iff.mp hv

end ActualScalarAndCoordinate
end
end QEC.Coding.TannerLiftedProduct
