import QEC.Coding.ExpanderCodes.LPSCosetSectionDomain
import QEC.Coding.ExpanderCodes.LPSCuspPeterssonPositive

/-!
# The original pairing on actual Gamma0 integration domains

Project original congruence representatives through the proved effective quotient. The resulting genuine section domain identifies the original finite-coset trace pairing with the untraced Petersson integral. Convergence, domain independence, positive definiteness and the exact original index are retained.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

/-- The original/effective Gamma0 quotient equivalence sends actual representatives to their projection. -/
lemma lpsEffectiveGamma0CosetEquiv_mk (N : ℕ) (h : SL(2,ℤ)) :
    lpsEffectiveGamma0CosetEquiv N (QuotientGroup.mk h) =
      QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict h) := rfl

/-- The effective coset section obtained from the original integral Gamma0 representatives. -/
def lpsGamma0CosetSection (N : ℕ) :
    lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N → lpsEffectiveModularGroup :=
  fun c => (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
    (Quotient.out ((lpsEffectiveGamma0CosetEquiv N).symm c))

/-- The original projected representatives satisfy the actual effective coset section law. -/
lemma lpsGamma0CosetSection_mk (N : ℕ) (c : lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) :
    QuotientGroup.mk (lpsGamma0CosetSection N c) = c := by
  have he := lpsEffectiveGamma0CosetEquiv_mk N (Quotient.out ((lpsEffectiveGamma0CosetEquiv N).symm c))
  have hh := congrArg (lpsEffectiveGamma0CosetEquiv N)
    (Quotient.out_eq' ((lpsEffectiveGamma0CosetEquiv N).symm c))
  exact he.symm.trans (hh.trans ((lpsEffectiveGamma0CosetEquiv N).apply_symm_apply c))

/-- A projected inverse-section integrand is the original Gamma0 coset Petersson component. -/
lemma lpsGamma0SectionPetersson (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) (τ : ℍ) :
    petersson 2 f g ((lpsGamma0CosetSection N c)⁻¹ • τ) =
      lpsCuspCosetPetersson N f g τ ((lpsEffectiveGamma0CosetEquiv N).symm c) := by
  rw [←Quotient.out_eq' ((lpsEffectiveGamma0CosetEquiv N).symm c),
    lpsCuspCosetPetersson_apply]
  rfl

/-- The genuine cusp bound gives absolute convergence on every actual modular translate. -/
lemma lpsGamma0Petersson_translate_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) :
    IntegrableOn (petersson 2 f g) (h • ModularGroup.fd) volume := by
  obtain ⟨C,hC⟩ := CuspFormClass.petersson_bounded_left 2 _ f g
  have hi : IntegrableOn (fun _ : ℍ => C) (h • ModularGroup.fd) := by
    have ht : (volume : Measure ℍ) (h • ModularGroup.fd) ≠ ∞ := by
      rw [measure_smul]
      exact ne_of_lt lpsPetersson_fundamentalDomain_volume_finite
    exact integrableOn_const ht
  exact hi.mono' (petersson_continuous 2 (by fun_prop) (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall hC)

/-- The actual original Petersson trace reindexes over effective Gamma0 cosets, without a center factor. -/
lemma lpsCuspPeterssonTrace_sectionSum (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) :
    lpsCuspPeterssonTrace N f g τ =
      ∑' c, petersson 2 f g ((lpsGamma0CosetSection N c)⁻¹ • τ) := by
  let : (lpsEffectiveGamma0 N).FiniteIndex := lpsGamma0Domain_finiteIndex N
  let : Fintype (lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Subgroup.fintypeQuotientOfFiniteIndex
  simp_rw [lpsGamma0SectionPetersson,tsum_fintype]
  unfold lpsCuspPeterssonTrace
  apply Fintype.sum_equiv (lpsEffectiveGamma0CosetEquiv N)
  intro c
  rw [Equiv.symm_apply_apply]

/-- The original convergent trace pairing is exactly the untraced integral on its genuine section domain. -/
lemma lpsCuspPeterssonPairing_sectionDomain (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f g =
      ∫τ in lpsCosetSectionDomain (lpsEffectiveGamma0 N) (lpsGamma0CosetSection N), petersson 2 f g τ := by
  let : (lpsEffectiveGamma0 N).FiniteIndex := lpsGamma0Domain_finiteIndex N
  let : Fintype (lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  rw [lpsCosetSectionDomain_integral _ _ (lpsGamma0CosetSection_mk N) _
    (fun c => lpsGamma0Petersson_translate_integrable N f g _)]
  unfold lpsCuspPeterssonPairing
  simp_rw [lpsCuspPeterssonTrace_sectionSum,tsum_fintype]
  apply integral_finsetSum
  intro c _
  exact ((lpsEffectiveMeasurePreserving (lpsGamma0CosetSection N c)⁻¹).integrableOn_image
    (lpsEffectiveMeasurableEmbedding (lpsGamma0CosetSection N c)⁻¹)).mp
      (lpsGamma0Petersson_translate_integrable N f g _)

/-- The genuine Gamma0 integration domain matching the original integral representatives. -/
def lpsGamma0PeterssonDomain (N : ℕ) : Set ℍ :=
  lpsCosetSectionDomain (lpsEffectiveGamma0 N) (lpsGamma0CosetSection N)

/-- The original-representative domain is fundamental for actual effective Gamma0, including level zero. -/
lemma lpsGamma0PeterssonDomain_fundamental (N : ℕ) :
    IsFundamentalDomain (lpsEffectiveGamma0 N) (lpsGamma0PeterssonDomain N) volume :=
  lpsCosetSectionDomain_fundamental _ _ (lpsGamma0CosetSection_mk N)

/-- The genuine Petersson integrand is invariant under the actual effective Gamma0 action. -/
lemma lpsGamma0Petersson_effectiveInvariant (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveGamma0 N) (τ : ℍ) :
    petersson 2 f g (h • τ) = petersson 2 f g τ := by
  rcases Subgroup.mem_map.mp h.property with ⟨γ,hγ,he⟩
  change petersson 2 f g (((h : lpsEffectiveModularGroup) : Equiv.Perm ℍ) τ) = _
  rw [←he]
  exact lpsCuspPetersson_smul N f g γ hγ τ

/-- The original finite-cover Gamma0 Petersson integral is absolutely convergent. -/
lemma lpsGamma0PeterssonDomain_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (petersson 2 f g) (lpsGamma0PeterssonDomain N) volume := by
  let : (lpsEffectiveGamma0 N).FiniteIndex := lpsGamma0Domain_finiteIndex N
  let : Fintype (lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact integrableOn_finite_iUnion.mpr (fun c => lpsGamma0Petersson_translate_integrable N f g _)

/-- Every actual effective Gamma0 fundamental domain computes the original untraced pairing. -/
lemma lpsCuspPeterssonPairing_gamma0Domain (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    lpsCuspPeterssonPairing N f g = ∫τ in s,petersson 2 f g τ := by
  rw [lpsCuspPeterssonPairing_sectionDomain]
  exact (lpsGamma0PeterssonDomain_fundamental N).setIntegral_eq hs (lpsGamma0Petersson_effectiveInvariant N f g)

/-- The genuine untraced Petersson integral converges on every actual Gamma0 fundamental domain. -/
lemma lpsGamma0Petersson_domain_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IntegrableOn (petersson 2 f g) s volume :=
  ((lpsGamma0PeterssonDomain_fundamental N).integrableOn_iff hs
    (lpsGamma0Petersson_effectiveInvariant N f g)).mp (lpsGamma0PeterssonDomain_integrable N f g)

/-- The original positive-definite pairing detects zero cusp forms on every genuine Gamma0 domain. -/
lemma lpsGamma0Petersson_domain_self_zero_iff (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    (∫τ in s,petersson 2 f f τ) = 0 ↔ f = 0 := by
  rw [←lpsCuspPeterssonPairing_gamma0Domain N f f hs]
  exact lpsCuspPeterssonPairing_self_eq_zero_iff N f

/-- The original Gamma0 domain volume uses the exact original integral congruence index. -/
lemma lpsGamma0PeterssonDomain_volume (N : ℕ) [NeZero N] :
    (volume : Measure ℍ) (lpsGamma0PeterssonDomain N) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * volume ModularGroup.fd := by
  let : (lpsEffectiveGamma0 N).FiniteIndex := lpsGamma0Domain_finiteIndex N
  rw [lpsGamma0PeterssonDomain,lpsCosetSectionDomain_volume _ _ (lpsGamma0CosetSection_mk N),lpsEffectiveGamma0_index]

/-- Every positive-level original Gamma0 integration domain has finite actual hyperbolic volume. -/
lemma lpsGamma0PeterssonDomain_volume_finite (N : ℕ) [NeZero N] :
    (volume : Measure ℍ) (lpsGamma0PeterssonDomain N) < ∞ := by
  rw [lpsGamma0PeterssonDomain_volume]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) lpsPetersson_fundamentalDomain_volume_finite

end
end QEC.Coding.TannerLiftedProduct
