import QEC.Coding.ExpanderCodes.LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# LPSOriginalFilledDifferential

Construct actual analytic sections of Hom(Tangent,trivial complex line). Prove faithful complex-linear original cusp-form transport and the original p+1 Hecke tangent pullback. Algebraic correspondence and spectral magnitude remain subsequent mathematics.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

/-- The intrinsic covector at each point of the original filled complex curve. -/
def lpsOriginalFilledDifferential (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∀x : LPSOriginalFilledCurve N, TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  exact fun x => ContinuousLinearMap.mul ℂ ℂ
    (lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x x))

/-- The genuine Hom-bundle coordinates equal the explicit coefficient in any chart. -/
lemma lpsOriginalFilledDifferential_inCoordinates (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x y : LPSOriginalFilledCurve N)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y∈(chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y
      (lpsOriginalFilledDifferential N hN f y)=
        ContinuousLinearMap.mul ℂ ℂ
          (lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x y)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  have hz : chartAt ℂ x y∈((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
    change chartAt ℂ x y∈(chartAt ℂ x).target ∧
      (chartAt ℂ x).symm (chartAt ℂ x y)∈(chartAt ℂ y).source
    exact ⟨(chartAt ℂ x).map_source hy,by rw [(chartAt ℂ x).left_inv hy];exact mem_chart_source ℂ y⟩
  have hk := lpsOriginalFilledCoordinateCoefficient_cocycle N hN f x y
    (chartAt ℂ x y) hz
  have he : ((chartAt ℂ x).symm.trans (chartAt ℂ y)) (chartAt ℂ x y)=chartAt ℂ y y := by
    rw [OpenPartialHomeomorph.trans_apply,(chartAt ℂ x).left_inv hy]
  dsimp only at hk
  rw [he] at hk
  have ht : (trivializationAt ℂ (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x).continuousLinearMapAt ℂ y=
      ContinuousLinearMap.id ℂ ℂ := Bundle.Trivial.continuousLinearMapAt_trivialization ℂ _ ℂ y
  rw [ContinuousLinearMap.inCoordinates,ht,ContinuousLinearMap.id_comp,
    TangentBundle.symmL_trivializationAt_eq_core hy,tangentBundleCore_coordChange_achart]
  have heq : extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) x).symm=
      (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ→ℂ) := rfl
  rw [heq]
  simp only [modelWithCornersSelf_coe,Set.range_id,fderivWithin_univ]
  change (ContinuousLinearMap.mul ℂ ℂ
    (lpsOriginalFilledCoordinateCoefficient N f y (chartAt ℂ y y))).comp
      (fderiv ℂ (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ→ℂ) (chartAt ℂ x y))=
      ContinuousLinearMap.mul ℂ ℂ (lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x y))
  apply ContinuousLinearMap.ext
  intro v
  change lpsOriginalFilledCoordinateCoefficient N f y (chartAt ℂ y y) *
    (fderiv ℂ (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ→ℂ) (chartAt ℂ x y)) v=
      lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x y) * v
  rw [fderiv_eq_deriv_mul]
  rw [←mul_assoc,hk]


/-- The intrinsic covector is an analytic section of the actual tangent Hom bundle. -/
lemma lpsOriginalFilledDifferential_contMDiff (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ,ℂ→L[ℂ]ℂ)) ω
      (fun x : LPSOriginalFilledCurve N => Bundle.TotalSpace.mk' (ℂ→L[ℂ]ℂ)
        (E:=fun y : LPSOriginalFilledCurve N =>
          TangentSpace 𝓘(ℂ) y →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ y)
        x (lpsOriginalFilledDifferential N hN f x)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id,?_⟩
  have ha := lpsOriginalFilledCoordinateCoefficient_analytic N hN f x
    (chartAt ℂ x x) ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x) x :=
    contMDiffAt_extChartAt (I:=𝓘(ℂ))
  have hK : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y => lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x y)) x :=
    ha.contDiffAt.contMDiffAt.comp x hc
  have hm := (ContinuousLinearMap.mul ℂ ℂ).contMDiffAt (n:=ω) |>.comp x hK
  apply hm.congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, y∈(chartAt ℂ x).source :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  filter_upwards [hn] with y hy
  exact lpsOriginalFilledDifferential_inCoordinates N hN f x y hy

/-- The original interior chart pulls its coefficient back to the original cusp form. -/
lemma lpsOriginalFilledInteriorChart_projection_differential (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (τ : ℍ) (hs : letI := lpsOriginalFilledTopology N
      Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ)∈
        (lpsOriginalFilledInteriorChart N hN x).source) :
    letI := lpsOriginalFilledTopology N
    let Φ : ℂ→ℂ := fun z => lpsOriginalFilledInteriorChart N hN x
      (Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
        (UpperHalfPlane.ofComplex z)))
    f (UpperHalfPlane.ofComplex (Φ τ)) * deriv Φ τ = f τ := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective proj := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  change Sum.inl (proj τ)∈Sum.inl ''(chartAt ℂ x).source at hs
  obtain ⟨a,ha,he⟩ := hs
  have hm : proj τ∈(chartAt ℂ x).source := by
    have he' := Sum.inl.inj he
    rwa [he'] at ha
  change proj τ∈((hf.localInverseAt (r x)).trans UpperHalfPlane.ofComplex.symm).source at hm
  have hd := lpsGamma0_localInverse_differential_pullback N hN f (r x) τ hm.1
  have heq : (fun z : ℂ => lpsOriginalFilledInteriorChart N hN x
      (Sum.inl (proj (UpperHalfPlane.ofComplex z))))=
      (fun z : ℂ => ((hf.localInverseAt (r x)) (proj (UpperHalfPlane.ofComplex z)) : ℂ)) := by
    funext z
    change ((chartAt ℂ x).lift_openEmbedding (lpsOriginalFilledTopology_interior_openEmbedding N))
      (Sum.inl (proj (UpperHalfPlane.ofComplex z)))=_
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  dsimp only
  rw [heq]
  have he0 : lpsOriginalFilledInteriorChart N hN x (Sum.inl (proj τ))=
      ((hf.localInverseAt (r x)) (proj τ) : ℂ) := by
    simpa only [UpperHalfPlane.ofComplex_apply] using congrFun heq (τ:ℂ)
  simp only [UpperHalfPlane.ofComplex_apply]
  change f (UpperHalfPlane.ofComplex (lpsOriginalFilledInteriorChart N hN x (Sum.inl (proj τ)))) *
    deriv (fun z : ℂ => ((hf.localInverseAt (r x)) (proj (UpperHalfPlane.ofComplex z)) : ℂ)) τ = f τ
  rw [he0,UpperHalfPlane.ofComplex_apply]
  exact hd

/-- The actual orbit-projection tangent map pulls the global covector back to the original differential. -/
lemma lpsOriginalFilledDifferential_projection_pullback (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    let proj : ℍ→LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
    lpsOriginalFilledDifferential N hN f (proj τ)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) proj τ v) = lpsCuspDifferential N f τ v := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let proj : ℍ→LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
  have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) proj τ :=
    (lpsOriginalFilled_projection_contMDiff N hN τ).mdifferentiableAt (by decide)
  have hd := lpsOriginalFilledInteriorChart_projection_differential N hN f
    (Quotient.mk _ τ) τ (lpsOriginalFilledInteriorChart_mem N hN (Quotient.mk _ τ))
  let D : ℂ→L[ℂ]ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) proj τ
  dsimp only
  change f (UpperHalfPlane.ofComplex (lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ) (proj τ))) *
    D v = f τ*v
  have hder : D=
      fderivWithin ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) τ proj)
        (Set.range 𝓘(ℂ)) (extChartAt 𝓘(ℂ) τ τ) := by
    exact if_pos hm
  rw [hder]
  simp only [modelWithCornersSelf_coe,Set.range_id,fderivWithin_univ]
  change f (UpperHalfPlane.ofComplex (lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ) (proj τ))) *
    (fderiv ℂ (fun z : ℂ => lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ)
      (proj (UpperHalfPlane.ofComplex z))) (τ:ℂ)) v = f τ*v
  rw [fderiv_eq_deriv_mul,←mul_assoc]
  simpa only [proj,UpperHalfPlane.ofComplex_apply] using congrArg (fun z : ℂ => z*v) hd

/-- The intrinsic global differential faithfully determines the original cusp form. -/
lemma lpsOriginalFilledDifferential_injective (N : ℕ) [NeZero N] (hN : 4∣N) :
    Function.Injective (lpsOriginalFilledDifferential N hN) := by
  intro f g he
  apply DFunLike.ext
  intro τ
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let proj : ℍ→LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
  have h := congrArg (fun D => D (proj τ) (mfderiv 𝓘(ℂ) 𝓘(ℂ) proj τ (1:ℂ))) he
  rw [lpsOriginalFilledDifferential_projection_pullback,
    lpsOriginalFilledDifferential_projection_pullback] at h
  simpa only [lpsCuspDifferential_apply,mul_one] using h

/-- The actual analytic covector section attached to an original weight-two cusp form. -/
def lpsOriginalFilledHolomorphicDifferential (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContMDiffSection 𝓘(ℂ) (ℂ→L[ℂ]ℂ) ω
      (fun x : LPSOriginalFilledCurve N =>
        TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ x) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact ⟨lpsOriginalFilledDifferential N hN f,
    lpsOriginalFilledDifferential_contMDiff N hN f⟩

/-- The intrinsic global differential is additive. -/
lemma lpsOriginalFilledDifferential_add (N : ℕ) [NeZero N] (hN : 4∣N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsOriginalFilledDifferential N hN (f+g)=
      lpsOriginalFilledDifferential N hN f+lpsOriginalFilledDifferential N hN g := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  funext x
  cases x with
  | inl y =>
    change ContinuousLinearMap.mul ℂ ℂ ((f+g) (UpperHalfPlane.ofComplex
      (lpsOriginalFilledInteriorChart N hN y (Sum.inl y))))=_
    simp only [FunLike.coe_add,Pi.add_apply]
    exact map_add (ContinuousLinearMap.mul ℂ ℂ) _ _
  | inr c =>
    change ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N (f+g)
      (lpsOriginalCuspRepresentative N c) (lpsOriginalFilledCuspChart N c (Sum.inr c)))=_
    rw [lpsOriginalFilledCuspChart_cusp,lpsOriginalCuspQCoefficient_zero_add]
    rw [map_add]
    change ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) 0)+
      ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N g (lpsOriginalCuspRepresentative N c) 0)=
      ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c)
        (lpsOriginalFilledCuspChart N c (Sum.inr c)))+
      ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N g (lpsOriginalCuspRepresentative N c)
        (lpsOriginalFilledCuspChart N c (Sum.inr c)))
    rw [lpsOriginalFilledCuspChart_cusp]

/-- The intrinsic global differential respects complex scalar multiplication. -/
lemma lpsOriginalFilledDifferential_smul (N : ℕ) [NeZero N] (hN : 4∣N)
    (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsOriginalFilledDifferential N hN (c • f)=
      c • lpsOriginalFilledDifferential N hN f := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  funext x
  cases x with
  | inl y =>
    change ContinuousLinearMap.mul ℂ ℂ ((c • f) (UpperHalfPlane.ofComplex
      (lpsOriginalFilledInteriorChart N hN y (Sum.inl y))))=_
    simp only [FunLike.coe_smul,Pi.smul_apply]
    exact map_smul (ContinuousLinearMap.mul ℂ ℂ) c _
  | inr d =>
    change ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N (c • f)
      (lpsOriginalCuspRepresentative N d) (lpsOriginalFilledCuspChart N d (Sum.inr d)))=_
    rw [lpsOriginalFilledCuspChart_cusp,lpsOriginalCuspQCoefficient_zero_smul]
    change ContinuousLinearMap.mul ℂ ℂ (c • lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d) 0)=_
    rw [map_smul]
    change c • ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d) 0)=
      c • ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d)
        (lpsOriginalFilledCuspChart N d (Sum.inr d)))
    rw [lpsOriginalFilledCuspChart_cusp]

/-- The concrete complex-linear map from original cusp forms to actual analytic covector sections. -/
def lpsOriginalFilledDifferentialLinearMap (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℂ]
      ContMDiffSection 𝓘(ℂ) (ℂ→L[ℂ]ℂ) ω
        (fun x : LPSOriginalFilledCurve N =>
          TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ x) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  refine { toFun:=lpsOriginalFilledHolomorphicDifferential N hN
           map_add':=?_
           map_smul':=?_ }
  · intro f g
    apply ContMDiffSection.ext
    intro x
    exact congrFun (lpsOriginalFilledDifferential_add N hN f g) x
  · intro c f
    apply ContMDiffSection.ext
    intro x
    exact congrFun (lpsOriginalFilledDifferential_smul N hN c f) x

/-- The original cusp-form map into analytic covector sections is injective. -/
lemma lpsOriginalFilledDifferentialLinearMap_injective (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    Function.Injective (lpsOriginalFilledDifferentialLinearMap N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro f g he
  apply lpsOriginalFilledDifferential_injective N hN
  exact congrArg (fun s => s.toFun) he

/-- The original p+1 Hecke sum is preserved through the genuine orbit-projection tangent pullback. -/
lemma lpsOriginalFilledDifferential_Hecke_pullback (N p : ℕ) [NeZero N]
    (hN : 4∣N) [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    let proj : ℍ→LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
    lpsOriginalFilledDifferentialLinearMap N hN (lpsCuspHeckeLinearMap N p hNp f) (proj τ)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) proj τ v) =
      ∑i : Option (Fin p),lpsOriginalFilledDifferentialLinearMap N hN f
        (proj (lpsHeckeUpperGL ℝ p i • τ))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) proj (lpsHeckeUpperGL ℝ p i • τ)
          (deriv (fun z : ℂ => (lpsHeckeUpperGL ℝ p i • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ*v)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  dsimp only
  simp_rw [show ∀g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2,
    ∀σ : ℍ, ∀w : ℂ,
    lpsOriginalFilledDifferentialLinearMap N hN g
      (Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)) σ w)=
      lpsCuspDifferential N g σ w from fun g σ w =>
      lpsOriginalFilledDifferential_projection_pullback N hN g σ w]
  exact lpsCuspHecke_differential_sum N p hNp f τ v

end
end QEC.Coding.TannerLiftedProduct
