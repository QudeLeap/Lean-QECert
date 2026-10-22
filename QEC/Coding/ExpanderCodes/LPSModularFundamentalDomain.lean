import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic

/-!
# LPSModularFundamentalDomain

Actual hyperbolic boundary nullness, the effective integral modular action, exact congruence cosets, and proved subgroup integration domains. The ineffective full SL action is not assigned a fundamental domain.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

/-- Ambient complex null sets pull back to null sets for the actual weighted hyperbolic volume. -/
lemma lpsHyperbolicNull {s : Set ℍ}
    (hs : (volume : Measure ℂ) (UpperHalfPlane.coe '' s) = 0) :
    (volume : Measure ℍ) s = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ hs

/-- Every real-coordinate level set in the complex plane has Lebesgue measure zero. -/
lemma lpsComplexVerticalNull (x : ℝ) :
    (volume : Measure ℂ) {z : ℂ | z.re = x} = 0 := by
  have h := Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) (0 : Fin 2) x
  have hm : MeasurableSet {f : Fin 2 → ℝ | f 0 = x} :=
    measurableSet_eq_fun (measurable_pi_apply (0 : Fin 2)) measurable_const
  have he := Complex.volume_preserving_equiv_pi.measure_preimage hm.nullMeasurableSet
  change (volume : Measure ℂ) (Complex.measurableEquivPi ⁻¹' {f : Fin 2 → ℝ | f 0 = x}) = 0
  exact he.trans h

/-- The circle and vertical-line boundary of the actual closed modular domain is hyperbolically null. -/
lemma lpsBoundaryNull : (volume : Measure ℍ) (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  apply lpsHyperbolicNull
  have hcircle : (volume : Measure ℂ) (Metric.sphere 0 1) = 0 := Measure.addHaar_sphere volume 0 1
  have hnull : (volume : Measure ℂ)
      (Metric.sphere 0 1 ∪ {z : ℂ | z.re = (1:ℝ)/2} ∪ {z : ℂ | z.re = -(1:ℝ)/2}) = 0 := by
    apply measure_union_null (measure_union_null hcircle (lpsComplexVerticalNull _))
    exact lpsComplexVerticalNull _
  apply measure_mono_null _ hnull
  rintro z ⟨τ, hτ, rfl⟩
  rcases hτ with ⟨⟨hn,hr⟩,ho⟩
  by_cases h : 1 < Complex.normSq (τ : ℂ)
  · have hre : |τ.re| = (1:ℝ)/2 := le_antisymm hr (not_lt.mp fun hh => ho ⟨h,hh⟩)
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)).mp hre with hp | hm
    · exact Or.inl (Or.inr hp)
    · apply Or.inr
      change τ.re = -(1:ℝ)/2
      linarith [hm]
  · have hn' : Complex.normSq (τ : ℂ) = 1 := le_antisymm (not_lt.mp h) hn
    apply Or.inl ∘ Or.inl
    rw [Metric.mem_sphere, dist_zero_right]
    have hp : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
    rw [Complex.normSq_eq_norm_sq] at hn'
    nlinarith

/-- The actual closed and open modular domains agree almost everywhere. -/
lemma lpsFdAeFdo : ModularGroup.fd =ᵐ[volume] ModularGroup.fdo := by
  apply ae_eq_set.mpr
  exact ⟨lpsBoundaryNull, by simp [sdiff_eq_empty.mpr ModularGroup.fdo_subset_fd]⟩

/-- The actual effective image of the integral modular action. -/
def lpsEffectiveModularGroup : Subgroup (Equiv.Perm ℍ) :=
  (MulAction.toPermHom SL(2,ℤ) ℍ).range

/-- The true permutation image of the countable integral modular group is countable. -/
@[instance] lemma lpsEffectiveModularGroup_countable : Countable lpsEffectiveModularGroup := by
  let : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let : Countable SL(2,ℤ) := (show Function.Injective (fun g : SL(2,ℤ) => g.val) from
    fun g h he => Subtype.ext he).countable
  exact (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict_surjective.countable

/-- Every effective modular permutation comes from an actual integral determinant-one matrix. -/
lemma lpsEffectiveRepresentative (g : lpsEffectiveModularGroup) :
    ∃ h : SL(2,ℤ), (g : Equiv.Perm ℍ) = MulAction.toPerm h := by
  rcases g.property with ⟨h,hh⟩
  exact ⟨h,hh.symm⟩

/-- Every effective modular permutation preserves the actual hyperbolic measure. -/
lemma lpsEffectiveMeasurePreserving (g : lpsEffectiveModularGroup) :
    MeasurePreserving (fun τ : ℍ => g • τ) volume volume := by
  obtain ⟨h,hh⟩ := lpsEffectiveRepresentative g
  have he : (fun τ : ℍ => g • τ) = (fun τ => (h : GL (Fin 2) ℝ) • τ) := by
    funext τ
    change (g : Equiv.Perm ℍ) τ = _
    rw [hh]
    exact ModularGroup.sl_moeb h τ
  rw [he]
  exact measurePreserving_smul _ _

/-- Every effective modular permutation is a measurable embedding. -/
lemma lpsEffectiveMeasurableEmbedding (g : lpsEffectiveModularGroup) :
    MeasurableEmbedding (fun τ : ℍ => g • τ) := by
  obtain ⟨h,hh⟩ := lpsEffectiveRepresentative g
  have he : (fun τ : ℍ => g • τ) = (fun τ => (h : GL (Fin 2) ℝ) • τ) := by
    funext τ
    change (g : Equiv.Perm ℍ) τ = _
    rw [hh]
    exact ModularGroup.sl_moeb h τ
  rw [he]
  exact measurableEmbedding_const_smul _

/-- A nonidentity effective permutation cannot overlap the open modular domain. -/
lemma lpsEffectiveDisjoint (g : lpsEffectiveModularGroup) (hg : g ≠ 1) :
    Disjoint (g • ModularGroup.fdo) ModularGroup.fdo := by
  obtain ⟨h,hh⟩ := lpsEffectiveRepresentative g
  apply Set.disjoint_left.mpr
  rintro τ ⟨z,hz,rfl⟩ hτ
  have hτ' : h • z ∈ ModularGroup.fdo := by
    change (g : Equiv.Perm ℍ) z ∈ ModularGroup.fdo at hτ
    simpa only [hh, MulAction.toPerm_apply] using hτ
  have he : (g : Equiv.Perm ℍ) = 1 := by
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hτ' with rfl | rfl
    · rw [hh]
      ext z
      simp
    · rw [hh]
      ext z
      simp [-ModularGroup.sl_moeb]
  exact hg (Subtype.ext he)

/-- Orbit coverage and proved null boundary give a genuine fundamental domain for the effective action. -/
lemma lpsEffectiveFundamentalDomain :
    IsFundamentalDomain lpsEffectiveModularGroup ModularGroup.fd volume := by
  apply IsFundamentalDomain.mk'' ModularGroup.isClosed_fd.measurableSet.nullMeasurableSet
  · apply Eventually.of_forall
    intro τ
    obtain ⟨h,hh⟩ := ModularGroup.exists_smul_mem_fd τ
    exact ⟨(MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict h,hh⟩
  · intro g hg
    have ha : g • ModularGroup.fd =ᵐ[volume] g • ModularGroup.fdo := by
      have := (lpsEffectiveMeasurePreserving g⁻¹).quasiMeasurePreserving.ae_eq lpsFdAeFdo
      change (fun x => x ∈ g • ModularGroup.fd) =ᵐ[volume] (fun x => x ∈ g • ModularGroup.fdo)
      filter_upwards [this] with x hx
      simp only [mem_smul_set_iff_inv_smul_mem]
      change ModularGroup.fd (g⁻¹ • x) = ModularGroup.fdo (g⁻¹ • x)
      exact hx
    exact (lpsEffectiveDisjoint g hg).aedisjoint.congr ha lpsFdAeFdo
  · intro g
    exact (lpsEffectiveMeasurePreserving g).quasiMeasurePreserving


/-- The effective modular action is measurable for each group element. -/
@[instance] lemma lpsEffectiveMeasurableConstSMul : MeasurableConstSMul lpsEffectiveModularGroup ℍ where
  measurable_const_smul g := (lpsEffectiveMeasurePreserving g).measurable

/-- The actual hyperbolic measure is invariant under the effective modular action. -/
@[instance] lemma lpsEffectiveSMulInvariantMeasure :
    SMulInvariantMeasure lpsEffectiveModularGroup ℍ volume where
  measure_preimage_smul g _ hs := (lpsEffectiveMeasurePreserving g).measure_preimage hs.nullMeasurableSet

/-- The ineffective integral modular matrices are precisely identity and negative identity. -/
lemma lpsEffectiveKernel (h : SL(2,ℤ)) :
    (MulAction.toPermHom SL(2,ℤ) ℍ) h = 1 ↔ h = 1 ∨ h = -1 := by
  constructor
  · intro hh
    let z : ℍ := ⟨⟨0,2⟩,by norm_num⟩
    have hz : z ∈ ModularGroup.fdo := by norm_num [z,ModularGroup.fdo,Complex.normSq_apply]
    have he : h • z = z := by
      have := congrArg (fun e : Equiv.Perm ℍ => e z) hh
      exact this
    exact ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz (by simpa only [he] using hz)
  · rintro (rfl | rfl) <;> ext z <;> simp [-ModularGroup.sl_moeb]

/-- The ineffective center belongs to every original Gamma0 subgroup, including level zero. -/
lemma lpsEffectiveKernel_le_Gamma0 (N : ℕ) :
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤ CongruenceSubgroup.Gamma0 N := by
  intro h hh
  have he : (MulAction.toPermHom SL(2,ℤ) ℍ) h = 1 :=
    congrArg (fun e : lpsEffectiveModularGroup => (e : Equiv.Perm ℍ)) hh
  rcases (lpsEffectiveKernel h).mp he with rfl | rfl <;> simp

/-- The congruence subgroup in the actual effective modular image. -/
def lpsEffectiveGamma0 (N : ℕ) : Subgroup lpsEffectiveModularGroup :=
  (CongruenceSubgroup.Gamma0 N).map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict

/-- Pulling back the actual effective Gamma0 image recovers the original subgroup exactly. -/
lemma lpsEffectiveGamma0_comap (N : ℕ) :
    (lpsEffectiveGamma0 N).comap (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict =
      CongruenceSubgroup.Gamma0 N :=
  Subgroup.comap_map_eq_self (lpsEffectiveKernel_le_Gamma0 N)

/-- Removing the ineffective center preserves the actual congruence coset space. -/
def lpsEffectiveGamma0CosetEquiv (N : ℕ) :
    SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N ≃ lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N := by
  let φ : SL(2,ℤ) →* lpsEffectiveModularGroup :=
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
  let f : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N →
      lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N :=
    Quotient.map' φ (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      have hm := Subgroup.mem_map_of_mem φ hxy
      rw [map_mul,map_inv] at hm
      exact hm)
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H x =>
      induction y using QuotientGroup.induction_on with | H y =>
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        have hh : x⁻¹*y ∈ (lpsEffectiveGamma0 N).comap φ := by
          simpa only [f,Quotient.map'_mk'',QuotientGroup.eq,map_mul,map_inv,
            Subgroup.mem_comap] using hxy
        change x⁻¹*y ∈ (lpsEffectiveGamma0 N).comap
          (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict at hh
        rw [lpsEffectiveGamma0_comap] at hh
        exact hh
  · intro y
    induction y using QuotientGroup.induction_on with | H y =>
      obtain ⟨x,rfl⟩ := (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict_surjective y
      exact ⟨QuotientGroup.mk x,rfl⟩

/-- Removing the ineffective center preserves the exact congruence index. -/
lemma lpsEffectiveGamma0_index (N : ℕ) :
    (lpsEffectiveGamma0 N).index = (CongruenceSubgroup.Gamma0 N).index :=
  Nat.card_congr (lpsEffectiveGamma0CosetEquiv N).symm

/-- Every coset space of the actual effective modular group is countable. -/
@[instance] lemma lpsEffectiveCosets_countable (H : Subgroup lpsEffectiveModularGroup) :
    Countable (lpsEffectiveModularGroup ⧸ H) :=
  inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel H)))

/-- A genuine coset-union domain for any subgroup of the effective modular group. -/
def lpsCongruenceDomain (H : Subgroup lpsEffectiveModularGroup) : Set ℍ :=
  ⋃ c : lpsEffectiveModularGroup ⧸ H, (Quotient.out c)⁻¹ • ModularGroup.fd

/-- The actual inverse-coset union is null measurable for hyperbolic volume. -/
lemma lpsCongruenceDomain_nullMeasurable (H : Subgroup lpsEffectiveModularGroup) :
    NullMeasurableSet (lpsCongruenceDomain H) volume := by
  apply NullMeasurableSet.iUnion
  intro c
  exact lpsEffectiveFundamentalDomain.nullMeasurableSet_smul (Quotient.out c)⁻¹

/-- Every point has an actual subgroup translate in the inverse-coset union domain. -/
lemma lpsCongruenceDomain_covers (H : Subgroup lpsEffectiveModularGroup) (τ : ℍ) :
    ∃h : H,h • τ ∈ lpsCongruenceDomain H := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  let g' : lpsEffectiveModularGroup := (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict g
  let c : lpsEffectiveModularGroup ⧸ H := QuotientGroup.mk g'
  let r := Quotient.out c
  have hc : QuotientGroup.mk r = QuotientGroup.mk g' := Quotient.out_eq' c
  have hk : r⁻¹*g' ∈ H := QuotientGroup.eq.mp hc
  let h : H := ⟨r⁻¹*g',hk⟩
  refine ⟨h,Set.mem_iUnion.mpr ⟨c,?_⟩⟩
  rw [mem_smul_set_iff_inv_smul_mem]
  change r • ((r⁻¹*g') • τ) ∈ ModularGroup.fd
  rw [←mul_smul,mul_inv_cancel_left]
  change g • τ ∈ ModularGroup.fd
  exact hg

/-- Nonidentity subgroup translates of the actual inverse-coset domain are almost disjoint. -/
lemma lpsCongruenceDomain_aedisjoint (H : Subgroup lpsEffectiveModularGroup)
    (h : H) (hh : h ≠ 1) :
    AEDisjoint volume (h • lpsCongruenceDomain H) (lpsCongruenceDomain H) := by
  simp only [lpsCongruenceDomain,smul_set_iUnion,AEDisjoint.iUnion_left_iff,AEDisjoint.iUnion_right_iff]
  intro d c
  change AEDisjoint volume ((h : lpsEffectiveModularGroup) •
    ((Quotient.out c)⁻¹ • ModularGroup.fd)) ((Quotient.out d)⁻¹ • ModularGroup.fd)
  rw [←mul_smul]
  apply lpsEffectiveFundamentalDomain.aedisjoint
  intro he
  have hm : (Quotient.out d)⁻¹ * Quotient.out c = (h : lpsEffectiveModularGroup) := by
    have := congrArg (fun x : lpsEffectiveModularGroup => x * Quotient.out c) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using this.symm
  have hc : d = c := by
    rw [←Quotient.out_eq' d,←Quotient.out_eq' c,QuotientGroup.eq,hm]
    exact h.property
  subst c
  have hh' : (h : lpsEffectiveModularGroup) = 1 := by
    rw [hm.symm,inv_mul_cancel]
  exact hh (Subtype.ext hh')

/-- The actual inverse-coset union is a genuine subgroup fundamental domain. -/
lemma lpsCongruenceDomain_fundamental (H : Subgroup lpsEffectiveModularGroup) :
    IsFundamentalDomain H (lpsCongruenceDomain H) volume := by
  apply IsFundamentalDomain.mk'' (lpsCongruenceDomain_nullMeasurable H)
  · exact Eventually.of_forall (lpsCongruenceDomain_covers H)
  · exact lpsCongruenceDomain_aedisjoint H
  · intro h
    exact (lpsEffectiveMeasurePreserving (h : lpsEffectiveModularGroup)).quasiMeasurePreserving

/-- The actual effective Gamma0 subgroup has its proved inverse-coset fundamental domain. -/
lemma lpsGamma0Domain_fundamental (N : ℕ) :
    IsFundamentalDomain (lpsEffectiveGamma0 N)
      (lpsCongruenceDomain (lpsEffectiveGamma0 N)) volume :=
  lpsCongruenceDomain_fundamental (lpsEffectiveGamma0 N)

/-- Every positive original Gamma0 level has finite index in the effective modular group. -/
lemma lpsGamma0Domain_finiteIndex (N : ℕ) [NeZero N] :
    (lpsEffectiveGamma0 N).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff,lpsEffectiveGamma0_index]
  exact Subgroup.FiniteIndex.index_ne_zero


end
end QEC.Coding.TannerLiftedProduct
