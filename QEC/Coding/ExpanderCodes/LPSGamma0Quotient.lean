import QEC.Coding.ExpanderCodes.LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient

/-!
# LPSGamma0Quotient

The natural projective image has the SAME original Gamma0 orbits. Derived freeness, continuity and proper discontinuity give the original quotient projection a genuine covering and a complex-analytic atlas. Local injectivity forces local lifts to differ by one original Mobius representative, proving analytic transition charts and projection.
This is the noncompact analytic quotient. Cusp compactification, algebraic modular curves,
arithmetic Hecke/Frobenius correspondence and the PK22 magnitude bound remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

/-- Natural projective image of the ORIGINAL real Gamma0 subgroup. -/
def lpsGamma0Projective (N : ℕ) : Subgroup PGL(2,ℝ) :=
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).map Matrix.ProjGenLinGroup.mk

/-- Projectivization leaves precisely the original orbits unchanged. -/
lemma lpsGamma0_projective_orbit_iff (N : ℕ) (τ σ : ℍ) :
    τ∈MulAction.orbit (lpsGamma0Projective N) σ ↔
      τ∈MulAction.orbit (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) σ := by
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨γ,hγ,he⟩ := g.property
    refine ⟨⟨γ,hγ⟩,?_⟩
    change γ • σ=τ
    change g.val • σ=τ at hg
    simpa only [←he,UpperHalfPlane.pglMk_smul] using hg
  · rintro ⟨g,hg⟩
    refine ⟨⟨Matrix.ProjGenLinGroup.mk g.val,⟨g.val,g.property,rfl⟩⟩,?_⟩
    change Matrix.ProjGenLinGroup.mk g.val • σ=τ
    change g.val • σ=τ at hg
    simpa only [UpperHalfPlane.pglMk_smul] using hg

/-- The natural projective image acts freely; the original GL action still contains minus identity. -/
lemma lpsGamma0Projective_isCancelSMul (N : ℕ) (hN : 4∣N) :
    IsCancelSMul (lpsGamma0Projective N) ℍ := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g τ hfix
  obtain ⟨γ,hγ,he⟩ := g.property
  obtain ⟨δ,hδ,hd⟩ := hγ
  change g.val • τ=τ at hfix
  rw [←he,UpperHalfPlane.pglMk_smul,←hd] at hfix
  apply Subtype.ext
  change g.val=1
  rcases lpsGamma0_fixed_mapGL N hN δ hδ τ hfix with hp|hm
  · rw [←he,←hd,hp,Matrix.ProjGenLinGroup.mk_one]
  · rw [←he,←hd,hm]
    apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
    apply UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp
    intro z
    simp only [UpperHalfPlane.neg_smul,one_smul]

/-- Continuity is inherited from the actual Mobius representatives. -/
instance lpsGamma0Projective_continuous (N : ℕ) :
    ContinuousConstSMul (lpsGamma0Projective N) ℍ where
  continuous_const_smul g := by
    obtain ⟨γ,hγ,he⟩ := g.property
    change Continuous (fun τ : ℍ => g.val • τ)
    rw [←he]
    simpa only [UpperHalfPlane.pglMk_smul] using
      (continuous_const_smul γ : Continuous (fun τ : ℍ => γ • τ))

/-- The natural image inherits actual compact-set finiteness from the original arithmetic action. -/
instance lpsGamma0Projective_proper (N : ℕ) [NeZero N] :
    ProperlyDiscontinuousSMul (lpsGamma0Projective N) ℍ := by
  rw [Subgroup.properlyDiscontinuousSMul_iff]
  intro K L hK hL
  have hp : ProperlyDiscontinuousSMul
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ := inferInstance
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hp
  refine ((hp hK hL).image Matrix.ProjGenLinGroup.mk).subset ?_
  rintro g ⟨hg,hgKL⟩
  obtain ⟨γ,hγ,he⟩ := hg
  refine ⟨γ,⟨hγ,?_⟩,he⟩
  rw [←he] at hgKL
  change (((fun τ : ℍ => Matrix.ProjGenLinGroup.mk γ • τ) '' K)∩L).Nonempty at hgKL
  change (((fun τ : ℍ => γ • τ) '' K)∩L).Nonempty
  simpa only [UpperHalfPlane.pglMk_smul] using hgKL

/-- The projection to the ORIGINAL Gamma0 orbit quotient is a genuine projective covering. -/
lemma lpsGamma0_quotientCover (N : ℕ) [NeZero N] (hN : 4∣N) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ))
      (lpsGamma0Projective N) := by
  let := lpsGamma0Projective_isCancelSMul N hN
  exact isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_properlyDiscontinuousSMul
    (fun {τ σ} => Quotient.eq''.trans (lpsGamma0_projective_orbit_iff N τ σ).symm)

/-- The actual original orbit projection is locally a homeomorphism. -/
lemma lpsGamma0_quotient_localHomeomorph (N : ℕ) [NeZero N] (hN : 4∣N) :
    IsLocalHomeomorph
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) :=
  (lpsGamma0_quotientCover N hN).isCoveringMap.isLocalHomeomorph

/-- The actual local-inverse complex-chart atlas on the original quotient, proved analytic below. -/
@[instance_reducible]
def lpsGamma0QuotientChartedSpace (N : ℕ) [NeZero N] (hN : 4∣N) :
    ChartedSpace ℂ (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :=
  (lpsGamma0_quotient_localHomeomorph N hN).chartedSpace Quotient.mk_surjective

/-- Genuine continuous local lifts differ near a point by ONE original Mobius representative. -/
lemma lpsGamma0_lifts_eventually_smul (N : ℕ) [NeZero N] (hN : 4∣N)
    {X : Type*} [TopologicalSpace X] (u v : X→ℍ) (x : X)
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (he : (fun z => Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (v z)) =ᶠ[𝓝 x]
      (fun z => Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (u z))) :
    ∃ γ : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      v =ᶠ[𝓝 x] (fun z => γ.val • u z) := by
  have h0 := Quotient.eq''.mp he.eq_of_nhds
  obtain ⟨γ,hγ⟩ := h0
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  let e := hf.localInverseAt (v x)
  have he0 : v x∈e.target := hf.self_mem_localInverseAt_target
  have hvo : ∀ᶠ z in 𝓝 x, v z∈e.target := hv (e.open_target.mem_nhds he0)
  have hgo : ∀ᶠ z in 𝓝 x, γ.val • u z∈e.target := by
    apply ((continuous_const_smul γ.val).continuousAt.comp hu)
    change e.target∈𝓝 (γ.val • u x)
    change γ.val • u x=v x at hγ
    rw [hγ]
    exact e.open_target.mem_nhds he0
  refine ⟨γ,?_⟩
  filter_upwards [hvo,hgo,he] with z hvz hgz hez
  apply hf.injOn_localInverseAt_target hvz hgz
  calc
    Quotient.mk _ (v z)=Quotient.mk _ (u z) := hez
    _=Quotient.mk _ (γ.val • u z) := by
      apply Quotient.sound
      exact ⟨γ⁻¹,by
        change γ⁻¹ • (γ • u z)=u z
        exact inv_smul_smul γ (u z)⟩

/-- This covering applies at every actual theta level, including the original residue-prime family. -/
lemma lpsOriginalThetaLevel_quotientCover (q : ℕ) (hq : q≠0) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) ℍ))
      (lpsGamma0Projective ((4*q)^2)) := by
  have : NeZero ((4*q)^2) := ⟨by positivity⟩
  apply lpsGamma0_quotientCover
  exact dvd_pow (dvd_mul_right 4 q) (by decide)

/-- The chosen local inverse has genuine analytic Mobius transitions on every sheet overlap. -/
lemma lpsGamma0_localInverse_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (σ τ : ℍ)
    (hs : Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ∈
      ((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ).source) :
    AnalyticAt ℂ (fun z : ℂ =>
      (((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ)
        (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)) : ℂ)) τ := by
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  let e := hf.localInverseAt σ
  let π := Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let u : ℂ→ℍ := UpperHalfPlane.ofComplex
  let v : ℂ→ℍ := fun z => e (π (u z))
  have hu : ContinuousAt u (τ:ℂ) :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) τ.im_pos).continuousAt
  have hπ : Continuous π := continuous_quot_mk
  have ht : π (u τ)=π τ := by simp [u]
  have hv : ContinuousAt v (τ:ℂ) := by
    apply (e.continuousAt (by simpa only [ht] using hs)).comp
    exact hπ.continuousAt.comp hu
  have he : (fun z => π (v z)) =ᶠ[𝓝 (τ:ℂ)] (fun z => π (u z)) := by
    have hsrc : ∀ᶠ z in 𝓝 (τ:ℂ), π (u z)∈e.source := by
      apply hπ.continuousAt.comp hu
      change e.source∈𝓝 (π (u τ))
      exact e.open_source.mem_nhds (by simpa only [ht] using hs)
    filter_upwards [hsrc] with z hz
    exact hf.apply_localInverseAt_of_mem hz
  obtain ⟨γ,hγ⟩ := lpsGamma0_lifts_eventually_smul N hN u v τ hu hv he
  have hd : γ.val.val.det=1 := by
    obtain ⟨δ,hδ,hg⟩ := γ.property
    rw [←hg]
    simp only [← Matrix.GeneralLinearGroup.val_det_apply,Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have ha := UpperHalfPlane.analyticAt_smul (g:=γ.val) (by rw [hd];norm_num) τ
  apply ha.congr
  filter_upwards [hγ] with z hz
  exact congrArg UpperHalfPlane.coe hz.symm

/-- The original noncompact Gamma0 orbit quotient has genuine complex-analytic transition charts. -/
lemma lpsGamma0Quotient_isManifold (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsGamma0QuotientChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by
  let Q := MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
  let π : ℍ→Q := Quotient.mk _
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective π := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  let := lpsGamma0QuotientChartedSpace N hN
  apply isManifold_of_contDiffOn 𝓘(ℂ) ω Q
  intro a b ha hb
  change ∃ q, (hf.localInverseAt (r q)).trans (chartAt ℂ (r q))=a at ha
  change ∃ q, (hf.localInverseAt (r q)).trans (chartAt ℂ (r q))=b at hb
  obtain ⟨q,rfl⟩ := ha
  obtain ⟨q',rfl⟩ := hb
  have hc (τ : ℍ) : chartAt ℂ τ=UpperHalfPlane.ofComplex.symm := rfl
  simp only [hc]
  intro z hz
  have hpos : 0<z.im := by
    have hm := hz.1.1
    change z∈((hf.localInverseAt (r q)).trans UpperHalfPlane.ofComplex.symm).target at hm
    simpa [UpperHalfPlane.ofComplex] using hm.1
  let τ : ℍ := ⟨z,hpos⟩
  have hs : π τ∈(hf.localInverseAt (r q')).source := by
    have hm := hz.1.2
    change ((hf.localInverseAt (r q)).trans UpperHalfPlane.ofComplex.symm).symm z∈
      ((hf.localInverseAt (r q')).trans UpperHalfPlane.ofComplex.symm).source at hm
    simpa only [OpenPartialHomeomorph.trans_apply,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm,hf.localInverseAt_symm,
      UpperHalfPlane.ofComplex_apply_of_im_pos hpos,
      OpenPartialHomeomorph.symm_target] using hm.1
  have ht := lpsGamma0_localInverse_analytic N hN (r q') τ hs
  apply ContDiffAt.contDiffWithinAt
  simpa [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    OpenPartialHomeomorph.coe_trans,OpenPartialHomeomorph.coe_trans_symm,
    hf.localInverseAt_symm,UpperHalfPlane.ofComplex,Function.comp_def,τ,hf] using
    ht.contDiffAt (n:=ω)

/-- The ORIGINAL orbit projection is complex-analytic in the proved quotient atlas. -/
lemma lpsGamma0Quotient_projection_contMDiff (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsGamma0QuotientChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) := by
  let Q := MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
  let π : ℍ→Q := Quotient.mk _
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective π := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  let := lpsGamma0QuotientChartedSpace N hN
  intro τ
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_quot_mk.continuousAt,?_⟩
  have hs : π τ∈(hf.localInverseAt (r (π τ))).source := by
    have hc := ChartedSpace.mem_chart_source (H:=ℂ) (π τ)
    change π τ∈((hf.localInverseAt (r (π τ))).trans (chartAt ℂ (r (π τ)))).source at hc
    exact hc.1
  have ha := lpsGamma0_localInverse_analytic N hN (r (π τ)) τ hs
  have hc (z : ℍ) : chartAt ℂ z=UpperHalfPlane.ofComplex.symm := rfl
  have hchart : chartAt ℂ (π τ)=
      (hf.localInverseAt (r (π τ))).trans (chartAt ℂ (r (π τ))) := rfl
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,hc,Function.comp_id,Function.id_comp]
  simp [UpperHalfPlane.ofComplex]
  change ContDiffWithinAt ℂ ω
    (fun z : ℂ => chartAt ℂ (π τ) (π (UpperHalfPlane.ofComplex z))) Set.univ (τ:ℂ)
  rw [hchart]
  simpa [OpenPartialHomeomorph.trans_apply,UpperHalfPlane.ofComplex,Function.comp_def] using
    ha.contDiffAt (n:=ω) |>.contDiffWithinAt

end
end QEC.Coding.TannerLiftedProduct
