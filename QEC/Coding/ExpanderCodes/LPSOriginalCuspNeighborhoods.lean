import QEC.Coding.ExpanderCodes.LPSOriginalCuspWidths
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Maps.Strict.Basic

/-!
# LPSOriginalCuspNeighborhoods

Actual minimal widths and original cusp-neighborhood geometry for the same Gamma0 group.
No width, stabilizer, descent, analytic coefficient or quotient topology law is assumed.
These are punctured neighborhoods; cusp filling, analytic gluing, compactness, algebraic
modular curves, arithmetic Hecke/Frobenius correspondence and the PK22 magnitude bound
remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

/-- The actual upper-right matrix acts by the genuine real translation. -/
lemma lpsUpperRight_smul_coe (x : ℝ) (τ : ℍ) :
    ((Matrix.GeneralLinearGroup.upperRightHom x • τ : ℍ):ℂ)=(τ:ℂ)+(x:ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.GeneralLinearGroup.upperRightHom]
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [Matrix.GeneralLinearGroup.upperRightHom,Matrix.det_fin_two]

/-- The genuine exponential coordinate has exactly integer-width translation fibers. -/
lemma lpsQParam_fiber (h : ℝ) (hh : h≠0) (z w : ℂ) :
    Function.Periodic.qParam h z=Function.Periodic.qParam h w ↔
      ∃ m : ℤ, z=w+(m:ℂ)*(h:ℂ) := by
  constructor
  · intro he
    obtain ⟨m,hm⟩ := Function.Periodic.qParam_left_inv_mod_period hh z
    obtain ⟨n,hn⟩ := Function.Periodic.qParam_left_inv_mod_period hh w
    rw [he] at hm
    have hx := hm.symm.trans hn
    refine ⟨n-m,?_⟩
    push_cast
    linear_combination hx
  · rintro ⟨m,rfl⟩
    unfold Function.Periodic.qParam
    have he : ((2:ℂ)*Real.pi*I)*(w+(m:ℂ)*(h:ℂ))/(h:ℂ)=
        ((2:ℂ)*Real.pi*I)*w/(h:ℂ)+(m:ℂ)*((2:ℂ)*Real.pi*I) := by
      field_simp [Complex.ofReal_ne_zero.mpr hh]
    rw [he]
    exact Complex.exp_periodic.int_mul m _

/-- A genuine integral matrix relating two points above height one must fix infinity. -/
lemma lpsIntegralHoroball_lowerLeft_zero (g : GL (Fin 2) ℝ)
    (hg : g∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range)
    (τ : ℍ) (ht : 1<τ.im) (hgt : 1<(g • τ).im) : g 1 0=0 := by
  rcases hg with ⟨γ,rfl⟩
  by_contra hc
  have he : (Matrix.SpecialLinearGroup.mapGL ℝ γ) 1 0=(γ 1 0:ℝ) := by
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have hcZ : γ 1 0≠0 := by
    intro hz
    apply hc
    rw [he,hz];simp
  have hZ : (1:ℤ)≤(γ 1 0)^2 := by
    have hp := sq_pos_of_ne_zero hcZ
    omega
  have hR : (1:ℝ)≤((Matrix.SpecialLinearGroup.mapGL ℝ γ) 1 0)^2 := by
    rw [he]
    exact_mod_cast hZ
  have hd := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
  have hi := UpperHalfPlane.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
  simp only [Matrix.SpecialLinearGroup.det_mapGL,Units.val_one,abs_one,one_mul] at hi
  rw [hi] at hgt
  have hn := UpperHalfPlane.normSq_denom_pos (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ.im_ne_zero
  have hsmall := (lt_div_iff₀ hn).mp hgt
  nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sq_nonneg τ.im)]

/-- Actual minimal-width exponential fibers equal the true cusp-group orbit fibers. -/
lemma lpsOriginalCuspGroup_horoball_fiber (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ σ : ℍ) (ht : 1<τ.im) (hs : 1<σ.im) :
    Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ=
      Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty σ ↔
      ∃ g∈lpsOriginalCuspGroup N ρ, g • σ=τ := by
  constructor
  · intro he
    obtain ⟨m,hm⟩ := (lpsQParam_fiber _
      (lpsOriginalCuspGroup_width_positive N ρ).ne' τ σ).mp he
    refine ⟨Matrix.GeneralLinearGroup.upperRightHom
      (m • (lpsOriginalCuspGroup N ρ).strictWidthInfty),?_,?_⟩
    · apply Subgroup.mem_strictPeriods_iff.mp
      rw [lpsOriginalCuspGroup_periods_generated]
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m,rfl⟩
    · apply UpperHalfPlane.ext
      rw [lpsUpperRight_smul_coe]
      simpa only [zsmul_eq_mul,Complex.ofReal_mul,Complex.ofReal_intCast] using hm.symm
  · rintro ⟨g,hg,he⟩
    have hc := lpsIntegralHoroball_lowerLeft_zero g
      (lpsOriginalCuspGroup_le_SLRange N ρ hg) σ hs (he ▸ ht)
    have hf := OnePoint.smul_infty_eq_self_iff.mpr hc
    obtain ⟨m,hm⟩ := lpsOriginalCuspGroup_stabilizer_generated N ρ g hg hf
    have hh : ((τ:ℍ):ℂ)=(σ:ℂ)+(m:ℂ)*((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ) := by
      rw [←he]
      rcases hm with hm|hm
      · rw [hm,lpsUpperRight_smul_coe]
        simp only [zsmul_eq_mul,Complex.ofReal_mul,Complex.ofReal_intCast]
      · rw [hm,UpperHalfPlane.neg_smul,lpsUpperRight_smul_coe]
        simp only [zsmul_eq_mul,Complex.ofReal_mul,Complex.ofReal_intCast]
    exact (lpsQParam_fiber _ (lpsOriginalCuspGroup_width_positive N ρ).ne' τ σ).mpr ⟨m,hh⟩

/-- Integral conjugation preserves exactly the original Gamma0 orbit relation. -/
lemma lpsOriginalCuspGroup_orbit_iff (N : ℕ) (ρ : SL(2,ℤ)) (τ σ : ℍ) :
    (∃ g∈lpsOriginalCuspGroup N ρ, g • σ=τ) ↔
      ∃ g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
        g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ • σ)=
          Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ := by
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  constructor
  · rintro ⟨g,hg,he⟩
    refine ⟨r*g*r⁻¹,?_,?_⟩
    · rwa [lpsOriginalCuspGroup,ConjAct.toConjAct_inv,
        Subgroup.mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul] at hg
    · change (r*g*r⁻¹) • (r • σ)=r • τ
      simp only [mul_smul,inv_smul_smul]
      rw [he]
  · rintro ⟨g,hg,he⟩
    refine ⟨r⁻¹*g*r,?_,?_⟩
    · rw [lpsOriginalCuspGroup,ConjAct.toConjAct_inv,
        Subgroup.mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul]
      change r*(r⁻¹*g*r)*r⁻¹∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
      have hc : r*(r⁻¹*g*r)*r⁻¹=g := by group
      rw [hc]
      exact hg
    · simp only [mul_smul]
      rw [he]
      exact inv_smul_smul r τ

/-- The coordinate fibers are precisely the ORIGINAL quotient fibers near the cusp. -/
lemma lpsOriginalCusp_horoball_originalQuotient_fiber (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ σ : ℍ) (ht : 1<τ.im) (hs : 1<σ.im) :
    Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ=
      Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty σ ↔
      ∃ g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
        g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ • σ)=
          Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ :=
  (lpsOriginalCuspGroup_horoball_fiber N ρ τ σ ht hs).trans
    (lpsOriginalCuspGroup_orbit_iff N ρ τ σ)

/-- The actual high-horoball coordinate image is exactly its punctured disc. -/
lemma lpsOriginalCusp_horoball_coordinate_range (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) (q : ℂ) :
    q∈(fun τ : ℍ => Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) ''
      {τ : ℍ | 1<τ.im} ↔
      q≠0 ∧ ‖q‖<Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty) := by
  let w := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  have hw : 0<w := lpsOriginalCuspGroup_width_positive N ρ
  constructor
  · rintro ⟨τ,hτ,rfl⟩
    exact ⟨Function.Periodic.qParam_ne_zero _,
      by simpa only [mul_one] using (Function.Periodic.norm_qParam_lt_iff hw 1 (τ:ℂ)).mpr hτ⟩
  · rintro ⟨hq,hn⟩
    let z := Function.Periodic.invQParam w q
    have hz : 1<z.im := by
      apply (Function.Periodic.norm_qParam_lt_iff hw 1 z).mp
      rw [Function.Periodic.qParam_right_inv hw.ne' hq]
      simpa only [mul_one] using hn
    have hp : 0<z.im := by linarith
    refine ⟨⟨z,hp⟩,hz,?_⟩
    exact Function.Periodic.qParam_right_inv hw.ne' hq

/-- A nonzero-width exponential coordinate is open by its nonzero strict derivative. -/
lemma lpsQParam_isOpenMap (h : ℝ) (hh : h≠0) : IsOpenMap (Function.Periodic.qParam h) := by
  apply isOpenMap_of_hasStrictDerivAt
    (f':=fun z : ℂ => (((2:ℂ)*Real.pi*I)/(h:ℂ))*Function.Periodic.qParam h z)
  · intro z
    unfold Function.Periodic.qParam
    have hd := (((hasStrictDerivAt_id z).const_mul ((2:ℂ)*Real.pi*I)).div_const (h:ℂ)).cexp
    simpa only [id_eq,one_mul,mul_comm] using hd
  · intro z
    exact mul_ne_zero (div_ne_zero Complex.two_pi_I_ne_zero (Complex.ofReal_ne_zero.mpr hh))
      (Function.Periodic.qParam_ne_zero z)

/-- The restriction of the ORIGINAL Gamma0 orbit relation to the actual cusp horoball. -/
def lpsOriginalCuspHoroballRel (N : ℕ) (ρ : SL(2,ℤ)) :
    Setoid {τ : ℍ // 1<τ.im} :=
  (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ).comap
    (fun τ => Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ.val)

/-- The genuine punctured-disc image at the actual minimal width. -/
def lpsOriginalCuspDisk (N : ℕ) (ρ : SL(2,ℤ)) : Set ℂ :=
  {q | q≠0 ∧ ‖q‖<Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty)}

/-- The true minimal-width exponential coordinate on the actual high horoball. -/
def lpsOriginalCuspCoordinate (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    {τ : ℍ // 1<τ.im} → lpsOriginalCuspDisk N ρ := fun τ =>
  ⟨Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ.val,
    (lpsOriginalCusp_horoball_coordinate_range N ρ _).mp ⟨τ.val,τ.property,rfl⟩⟩

/-- The genuine coordinate is an open continuous surjection and hence a quotient map. -/
lemma lpsOriginalCuspCoordinate_quotientMap (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Topology.IsQuotientMap (lpsOriginalCuspCoordinate N ρ) := by
  have hd : IsOpen (lpsOriginalCuspDisk N ρ) :=
    (isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_lt continuous_norm continuous_const)
  have hh : IsOpen {τ : ℍ | 1<τ.im} := isOpen_lt continuous_const UpperHalfPlane.continuous_im
  have ho : IsOpenMap (lpsOriginalCuspCoordinate N ρ) := by
    apply hd.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    exact (lpsQParam_isOpenMap _ (lpsOriginalCuspGroup_width_positive N ρ).ne').comp
      (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.comp hh.isOpenMap_subtype_val)
  have hc : Continuous (lpsOriginalCuspCoordinate N ρ) := by
    apply Continuous.subtype_mk
    exact Function.Periodic.continuous_qParam.comp
      (UpperHalfPlane.continuous_coe.comp continuous_subtype_val)
  apply ho.isQuotientMap hc
  intro q
  obtain ⟨τ,ht,he⟩ := (lpsOriginalCusp_horoball_coordinate_range N ρ q.val).mpr q.property
  exact ⟨⟨τ,ht⟩,Subtype.ext he⟩

/-- The actual coordinate kernel is precisely the restricted original orbit relation. -/
lemma lpsOriginalCuspCoordinate_kernel (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ σ : {τ : ℍ // 1<τ.im}) :
    lpsOriginalCuspHoroballRel N ρ τ σ ↔
      (Setoid.ker (lpsOriginalCuspCoordinate N ρ)) τ σ := by
  change MulAction.orbitRel _ _ (Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ.val)
    (Matrix.SpecialLinearGroup.mapGL ℝ ρ • σ.val) ↔ _
  rw [MulAction.orbitRel_apply]
  change _ ↔ lpsOriginalCuspCoordinate N ρ τ=lpsOriginalCuspCoordinate N ρ σ
  rw [Subtype.ext_iff]
  have hf := lpsOriginalCusp_horoball_originalQuotient_fiber N ρ τ.val σ.val τ.property σ.property
  simpa only [MulAction.mem_orbit_iff,Subtype.exists,MulAction.subgroup_smul_def,
    Subtype.coe_mk,lpsOriginalCuspCoordinate,exists_prop] using hf.symm

/-- The actual restricted original orbit quotient is homeomorphic to its punctured disc. -/
noncomputable def lpsOriginalCuspHoroball_homeomorph (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Quotient (lpsOriginalCuspHoroballRel N ρ) ≃ₜ lpsOriginalCuspDisk N ρ := by
  let f : C({τ : ℍ // 1<τ.im},lpsOriginalCuspDisk N ρ) :=
    ⟨lpsOriginalCuspCoordinate N ρ,(lpsOriginalCuspCoordinate_quotientMap N ρ).continuous⟩
  exact (Homeomorph.Quotient.congrRight (lpsOriginalCuspCoordinate_kernel N ρ)).trans
    (Topology.IsQuotientMap.homeomorph (f:=f) (lpsOriginalCuspCoordinate_quotientMap N ρ))

/-- The true projection of the integral cusp horoball into the ORIGINAL Gamma0 quotient. -/
def lpsOriginalCuspProjection (N : ℕ) (ρ : SL(2,ℤ)) :
    {τ : ℍ // 1<τ.im} →
      MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
  fun τ => ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ.val⟧

/-- The actual original cusp projection is open, without a supplied quotient topology law. -/
lemma lpsOriginalCuspProjection_open (N : ℕ) (ρ : SL(2,ℤ)) :
    IsOpenMap (lpsOriginalCuspProjection N ρ) := by
  let : ContinuousConstSMul
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
    ⟨fun g => continuous_const_smul g.val⟩
  have hh : IsOpen {τ : ℍ | 1<τ.im} := isOpen_lt continuous_const UpperHalfPlane.continuous_im
  exact isOpenMap_quotient_mk'_mul.comp
    ((isOpenMap_smul (Matrix.SpecialLinearGroup.mapGL ℝ ρ)).comp hh.isOpenMap_subtype_val)

/-- The actual original cusp projection is continuous. -/
lemma lpsOriginalCuspProjection_continuous (N : ℕ) (ρ : SL(2,ℤ)) :
    Continuous (lpsOriginalCuspProjection N ρ) :=
  continuous_quotient_mk'.comp ((continuous_const_smul _).comp continuous_subtype_val)

/-- The actual projection kernel is the same restricted original orbit relation. -/
lemma lpsOriginalCuspProjection_kernel (N : ℕ) (ρ : SL(2,ℤ))
    (τ σ : {τ : ℍ // 1<τ.im}) :
    lpsOriginalCuspHoroballRel N ρ τ σ ↔
      (Setoid.ker (lpsOriginalCuspProjection N ρ)) τ σ := by
  change MulAction.orbitRel _ _ (Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ.val)
    (Matrix.SpecialLinearGroup.mapGL ℝ ρ • σ.val) ↔
      (⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ.val⟧ :
        MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)=
          ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • σ.val⟧
  exact Quotient.eq.symm

/-- The actual cusp neighborhood is an OPEN subspace of the original quotient. -/
lemma lpsOriginalCuspProjection_openRange (N : ℕ) (ρ : SL(2,ℤ)) :
    IsOpen (Set.range (lpsOriginalCuspProjection N ρ)) := by
  simpa only [Set.image_univ] using lpsOriginalCuspProjection_open N ρ Set.univ isOpen_univ

/-- A genuine homeomorphism from the actual OPEN original cusp neighborhood to its punctured disc. -/
noncomputable def lpsOriginalCuspNeighborhoodChart (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Set.range (lpsOriginalCuspProjection N ρ) ≃ₜ lpsOriginalCuspDisk N ρ :=
  ((Homeomorph.Quotient.congrRight (lpsOriginalCuspProjection_kernel N ρ)).trans
    (Homeomorph.quotientKerEquivRange ((lpsOriginalCuspProjection_open N ρ).isStrictMap
      (lpsOriginalCuspProjection_continuous N ρ)))).symm.trans
        (lpsOriginalCuspHoroball_homeomorph N ρ)

/-- The actual original-neighborhood homeomorphism sends projections to the genuine q coordinate. -/
lemma lpsOriginalCuspNeighborhoodChart_projection (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ : {τ : ℍ // 1<τ.im}) :
    lpsOriginalCuspNeighborhoodChart N ρ ⟨lpsOriginalCuspProjection N ρ τ,⟨τ,rfl⟩⟩=
      lpsOriginalCuspCoordinate N ρ τ := by
  let e := (Homeomorph.Quotient.congrRight (lpsOriginalCuspProjection_kernel N ρ)).trans
    (Homeomorph.quotientKerEquivRange ((lpsOriginalCuspProjection_open N ρ).isStrictMap
      (lpsOriginalCuspProjection_continuous N ρ)))
  have he : e ⟦τ⟧=⟨lpsOriginalCuspProjection N ρ τ,⟨τ,rfl⟩⟩ := rfl
  change lpsOriginalCuspHoroball_homeomorph N ρ
    (e.symm ⟨lpsOriginalCuspProjection N ρ τ,⟨τ,rfl⟩⟩)=_
  rw [←he,e.symm_apply_apply]
  rfl

end
end QEC.Coding.TannerLiftedProduct
