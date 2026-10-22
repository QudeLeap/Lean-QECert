import QEC.Coding.ExpanderCodes.LPSModularFundamentalDomain

/-!
# Actual coset-section integration domains

Genuine section laws prove subgroup coverage and almost-disjointness. Finite index gives exact volume and integrable inverse-cover formulas; no domain or integral conclusion is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

/-- The inverse-section union of the actual modular fundamental domain. -/
def lpsCosetSectionDomain (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup) : Set ℍ :=
  ⋃ c : lpsEffectiveModularGroup ⧸ H, (r c)⁻¹ • ModularGroup.fd

/-- Every inverse-section union is null measurable for actual hyperbolic volume. -/
lemma lpsCosetSectionDomain_nullMeasurable (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup) :
    NullMeasurableSet (lpsCosetSectionDomain H r) volume := by
  apply NullMeasurableSet.iUnion
  intro c
  exact lpsEffectiveFundamentalDomain.nullMeasurableSet_smul (r c)⁻¹

/-- A genuine coset section gives actual subgroup orbit coverage, including infinite index. -/
lemma lpsCosetSectionDomain_covers (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup) (hr : ∀c, QuotientGroup.mk (r c) = c) (τ : ℍ) :
    ∃h : H,h • τ ∈ lpsCosetSectionDomain H r := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  let g' : lpsEffectiveModularGroup := (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict g
  let c : lpsEffectiveModularGroup ⧸ H := QuotientGroup.mk g'
  have hc : QuotientGroup.mk (r c) = QuotientGroup.mk g' := hr c
  have hk : (r c)⁻¹*g' ∈ H := QuotientGroup.eq.mp hc
  let h : H := ⟨(r c)⁻¹*g',hk⟩
  refine ⟨h,Set.mem_iUnion.mpr ⟨c,?_⟩⟩
  rw [mem_smul_set_iff_inv_smul_mem]
  change (r c) • (((r c)⁻¹*g') • τ) ∈ ModularGroup.fd
  rw [←mul_smul,mul_inv_cancel_left]
  change g • τ ∈ ModularGroup.fd
  exact hg

/-- Distinct subgroup translates of a genuine inverse-section union are almost disjoint. -/
lemma lpsCosetSectionDomain_aedisjoint (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (h : H) (hh : h ≠ 1) :
    AEDisjoint volume (h • lpsCosetSectionDomain H r) (lpsCosetSectionDomain H r) := by
  simp only [lpsCosetSectionDomain,smul_set_iUnion,AEDisjoint.iUnion_left_iff,AEDisjoint.iUnion_right_iff]
  intro d c
  change AEDisjoint volume ((h : lpsEffectiveModularGroup) •
    ((r c)⁻¹ • ModularGroup.fd)) ((r d)⁻¹ • ModularGroup.fd)
  rw [←mul_smul]
  apply lpsEffectiveFundamentalDomain.aedisjoint
  intro he
  have hm : (r d)⁻¹ * r c = (h : lpsEffectiveModularGroup) := by
    have := congrArg (fun x : lpsEffectiveModularGroup => x * r c) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using this.symm
  have hc : d = c := by
    rw [←hr d,←hr c,QuotientGroup.eq,hm]
    exact h.property
  subst c
  have hh' : (h : lpsEffectiveModularGroup) = 1 := by
    rw [hm.symm,inv_mul_cancel]
  exact hh (Subtype.ext hh')

/-- Every genuine coset section constructs an actual subgroup fundamental domain. -/
lemma lpsCosetSectionDomain_fundamental (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    IsFundamentalDomain H (lpsCosetSectionDomain H r) volume := by
  apply IsFundamentalDomain.mk'' (lpsCosetSectionDomain_nullMeasurable H r)
  · exact Eventually.of_forall (lpsCosetSectionDomain_covers H r hr)
  · exact lpsCosetSectionDomain_aedisjoint H r hr
  · intro h
    exact (lpsEffectiveMeasurePreserving (h : lpsEffectiveModularGroup)).quasiMeasurePreserving

/-- Distinct genuine inverse-coset components are almost disjoint. -/
lemma lpsCosetSectionDomain_components (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    Pairwise (fun c d => AEDisjoint volume ((r c)⁻¹ • ModularGroup.fd)
      ((r d)⁻¹ • ModularGroup.fd)) := by
  intro c d hcd
  apply lpsEffectiveFundamentalDomain.aedisjoint
  intro he
  apply hcd
  have he' : r c = r d := inv_injective he
  exact (hr c).symm.trans ((congrArg (QuotientGroup.mk : lpsEffectiveModularGroup →
    lpsEffectiveModularGroup ⧸ H) he').trans (hr d))

/-- Integrable components give the true finite-cover integral, with inverse action orientation. -/
lemma lpsCosetSectionDomain_integral (H : Subgroup lpsEffectiveModularGroup)
    [H.FiniteIndex] (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (F : ℍ → ℂ)
    (hF : ∀c, IntegrableOn F ((r c)⁻¹ • ModularGroup.fd) volume) :
    (∫τ in lpsCosetSectionDomain H r, F τ) =
      ∑' c, ∫τ in ModularGroup.fd, F ((r c)⁻¹ • τ) := by
  let : Fintype (lpsEffectiveModularGroup ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  unfold lpsCosetSectionDomain
  rw [integral_iUnion_ae
    (fun c => lpsEffectiveFundamentalDomain.nullMeasurableSet_smul (r c)⁻¹)
    (lpsCosetSectionDomain_components H r hr) (integrableOn_finite_iUnion.mpr hF)]
  apply tsum_congr
  intro c
  exact (lpsEffectiveMeasurePreserving (r c)⁻¹).setIntegral_image_emb
    (lpsEffectiveMeasurableEmbedding (r c)⁻¹) F ModularGroup.fd

/-- The true finite-cover volume is exact subgroup index times modular-domain volume. -/
lemma lpsCosetSectionDomain_volume (H : Subgroup lpsEffectiveModularGroup)
    [H.FiniteIndex] (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    (volume : Measure ℍ) (lpsCosetSectionDomain H r) =
      (H.index : ℝ≥0∞) * volume ModularGroup.fd := by
  let : Fintype (lpsEffectiveModularGroup ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  unfold lpsCosetSectionDomain
  rw [measure_iUnion₀ (lpsCosetSectionDomain_components H r hr)
    (fun c => lpsEffectiveFundamentalDomain.nullMeasurableSet_smul (r c)⁻¹)]
  simp only [measure_smul,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Subgroup.index, Nat.card_eq_fintype_card]

end
end QEC.Coding.TannerLiftedProduct
