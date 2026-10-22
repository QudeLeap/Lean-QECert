import QEC.Coding.ExpanderCodes.LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous

/-!
# LPSOriginalCompactCore

True finite original coset cover, compact truncated core and actual integral imaginary-height bounds.
This internal topological geometry supplies no complex analytic filled atlas, arithmetic
modular model, good reduction, Hecke/Frobenius/Jacobian/Rosati magnitude or PK22 theorem.
The original group, source and public theorem scope remain unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

/-- The inverse of a fixed genuine original left-coset representative. -/
def lpsOriginalGamma0CosetRepresentative (N : ℕ)
    (x : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : SL(2,ℤ) := x.out⁻¹

/-- The actual original quotient projection after the integral matrix action. -/
def lpsOriginalGamma0Projected (N : ℕ) (ρ : SL(2,ℤ)) (τ : ℍ) :
    MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
  ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧

/-- The genuine original integral projection is continuous. -/
lemma lpsOriginalGamma0Projected_continuous (N : ℕ) (ρ : SL(2,ℤ)) :
    Continuous (lpsOriginalGamma0Projected N ρ) :=
  continuous_quotient_mk'.comp (continuous_const_smul _)

/-- The finite original coset images of the actual truncated fundamental domain. -/
def lpsOriginalGamma0CompactCore (N : ℕ) (Y : ℝ) :
    Set (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :=
  ⋃ x : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    lpsOriginalGamma0Projected N (lpsOriginalGamma0CosetRepresentative N x) ''
      ModularGroup.truncatedFundamentalDomain Y

/-- The genuine truncated core is compact by finite index and continuous images. -/
lemma lpsOriginalGamma0CompactCore_isCompact (N : ℕ) [NeZero N] (Y : ℝ) :
    IsCompact (lpsOriginalGamma0CompactCore N Y) := by
  apply isCompact_iUnion
  intro x
  exact (ModularGroup.isCompact_truncatedFundamentalDomain Y).image
    (lpsOriginalGamma0Projected_continuous N _)

/-- Fixed original coset representatives really cover the quotient by fundamental-domain images. -/
lemma lpsOriginalGamma0Projected_fundamentalDomain_cover (N : ℕ) (τ : ℍ) :
    ∃ (x : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (z : ℍ),
      z ∈ ModularGroup.fd ∧
        lpsOriginalGamma0Projected N (lpsOriginalGamma0CosetRepresentative N x) z=
          (⟦τ⟧ : MulAction.orbitRel.Quotient
            (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  obtain ⟨h,hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) g
  refine ⟨⟦g⟧,g • τ,hg,?_⟩
  change (⟦Matrix.SpecialLinearGroup.mapGL ℝ ((QuotientGroup.mk g :
    SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out⁻¹) • (g • τ)⟧ :
      MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)=⟦τ⟧
  rw [hh,mul_inv_rev,map_mul,map_inv]
  have he : Matrix.SpecialLinearGroup.mapGL ℝ g • τ=g • τ := rfl
  rw [←he,mul_smul,map_inv,inv_smul_smul]
  apply Quotient.eq.mpr
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  refine ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ (h.val⁻¹),?_⟩,?_⟩
  · exact ⟨h.val⁻¹,(CongruenceSubgroup.Gamma0 N).inv_mem h.property,rfl⟩
  · change Matrix.SpecialLinearGroup.mapGL ℝ (h.val⁻¹) • τ=_
    rw [map_inv]

/-- Every original quotient point lies in the truncated core or an actual cusp tail. -/
lemma lpsOriginalGamma0_core_or_tail (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1≤Y)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    x∈lpsOriginalGamma0CompactCore N Y ∨
      ∃ c : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        x∈Set.range (lpsOriginalCuspProjection N (lpsOriginalGamma0CosetRepresentative N c)) := by
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep x
  obtain ⟨c,z,hz,he⟩ := lpsOriginalGamma0Projected_fundamentalDomain_cover N τ
  by_cases h : z.im≤Y
  · left
    rw [←he]
    apply Set.mem_iUnion.mpr
    exact ⟨c,z,⟨hz,h⟩,rfl⟩
  · right
    refine ⟨c,⟨⟨z,lt_of_le_of_lt hY (lt_of_not_ge h)⟩,?_⟩⟩
    exact he

/-- The actual original quotient is Hausdorff by its genuine arithmetic properly discontinuous action. -/
lemma lpsOriginalGamma0Quotient_t2 (N : ℕ) [NeZero N] :
    T2Space (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by
  let : ContinuousConstSMul (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
    ⟨fun g => continuous_const_smul g.val⟩
  infer_instance

/-- Every actual integral matrix bounds transformed height by max(y,1/y). -/
lemma lpsIntegral_im_bound (g : GL (Fin 2) ℝ)
    (hg : g∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range) (τ : ℍ) :
    (g • τ).im≤ max τ.im (1/τ.im) := by
  by_cases hc : g 1 0=0
  · obtain ⟨x,hx⟩ := lpsIntegralFixInfinity_translation g hg hc
    rw [lpsSignedTranslation_im g x hx]
    exact le_max_left _ _
  · rcases hg with ⟨γ,rfl⟩
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
    rw [hi]
    have hb : τ.im^2≤Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sq_nonneg τ.im)]
    calc
      _≤τ.im/τ.im^2 := div_le_div_of_nonneg_left τ.im_pos.le (sq_pos_of_pos τ.im_pos) hb
      _=1/τ.im := by field_simp
      _≤ max τ.im (1/τ.im) := le_max_right _ _

/-- The original quotient equality implies the genuine integral upper bound on cusp height. -/
lemma lpsOriginalGamma0_projected_im_bound (N : ℕ) (ρ : SL(2,ℤ)) (τ σ : ℍ)
    (h : lpsOriginalGamma0Projected N ρ τ=
      (⟦σ⟧ : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) :
    τ.im≤ max σ.im (1/σ.im) := by
  have ho := Quotient.eq.mp h
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at ho
  obtain ⟨g,hg⟩ := ho
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let d := r⁻¹*g.val
  have hd : d∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range := by
    obtain ⟨γ,hγ,hγg⟩ := g.property
    refine ⟨ρ⁻¹*γ,?_⟩
    simp only [map_mul,map_inv]
    rw [hγg]
  have hs : d • σ=τ := by
    simp only [d,mul_smul]
    change r⁻¹ • (g • σ)=τ
    rw [hg]
    exact inv_smul_smul r τ
  simpa only [hs] using lpsIntegral_im_bound d hd σ

/-- The genuine original orbit projection is open. -/
lemma lpsOriginalGamma0_quotientProjection_open (N : ℕ) :
    IsOpenMap (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) : ℍ → MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by
  let : ContinuousConstSMul (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
    ⟨fun g => continuous_const_smul g.val⟩
  exact isOpenMap_quotient_mk'_mul

/-- The ORIGINAL quotient is second countable as a genuine open quotient of the upper half-plane. -/
lemma lpsOriginalGamma0Quotient_secondCountable (N : ℕ) :
    SecondCountableTopology (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :=
  TopologicalSpace.Quotient.secondCountableTopology (lpsOriginalGamma0_quotientProjection_open N)

end
end QEC.Coding.TannerLiftedProduct
