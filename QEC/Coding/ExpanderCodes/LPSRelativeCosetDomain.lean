import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Genuine relative coset domains

Actual inverse sections prove coverage, almost disjointness, finite integration and exact index volume for measure-preserving group actions.
-/

namespace QEC.Coding.TannerLiftedProduct
open MeasureTheory Set Filter
open scoped Pointwise ENNReal
noncomputable section

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quotient of a countable group is countable; used locally for actual coset unions. -/
local instance lpsRelativeDomain_countableQuotient (H : Subgroup G) : Countable (G ⧸ H) :=
  inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel H)))
/-- Actual inverse-section union for a subgroup of a measure-preserving group. -/
def lpsRelativeDomain (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G) : Set α :=
  ⋃ c : G ⧸ H, (r c)⁻¹ • s

/-- Countable inverse translates of a true fundamental domain are null measurable. -/
lemma lpsRelativeDomain_nullMeasurable (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G) (hs : IsFundamentalDomain G s μ) :
    NullMeasurableSet (lpsRelativeDomain H s r) μ := by
  apply NullMeasurableSet.iUnion
  intro c
  exact hs.nullMeasurableSet_smul (r c)⁻¹

omit [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] in
/-- The actual section law gives almost-everywhere subgroup orbit coverage. -/
lemma lpsRelativeDomain_covers (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G) (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    ∀ᵐ τ ∂μ,∃h : H,h • τ ∈ lpsRelativeDomain H s r := by
  filter_upwards [hs.ae_covers] with τ hτ
  obtain ⟨g,hg⟩ := hτ
  let g' : G := g
  let c : G ⧸ H := QuotientGroup.mk g'
  have hc : QuotientGroup.mk (r c) = QuotientGroup.mk g' := hr c
  have hk : (r c)⁻¹*g' ∈ H := QuotientGroup.eq.mp hc
  let h : H := ⟨(r c)⁻¹*g',hk⟩
  refine ⟨h,Set.mem_iUnion.mpr ⟨c,?_⟩⟩
  rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
  change (r c) • (((r c)⁻¹*g') • τ) ∈ s
  rw [←mul_smul,mul_inv_cancel_left]
  exact hg

omit [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] in
/-- True section laws give almost-disjoint subgroup translates of the union. -/
lemma lpsRelativeDomain_aedisjoint (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) (h : H) (hh : h ≠ 1) :
    AEDisjoint μ (h • lpsRelativeDomain H s r) (lpsRelativeDomain H s r) := by
  simp only [lpsRelativeDomain,smul_set_iUnion,AEDisjoint.iUnion_left_iff,AEDisjoint.iUnion_right_iff]
  intro d c
  change AEDisjoint μ ((h : G) •
    ((r c)⁻¹ • s)) ((r d)⁻¹ • s)
  rw [←mul_smul]
  apply hs.aedisjoint
  intro he
  have hm : (r d)⁻¹ * r c = (h : G) := by
    have := congrArg (fun x : G => x * r c) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using this.symm
  have hc : d = c := by
    rw [←hr d,←hr c,QuotientGroup.eq,hm]
    exact h.property
  subst c
  have hh' : (h : G) = 1 := by
    rw [hm.symm,inv_mul_cancel]
  exact hh (Subtype.ext hh')

/-- The genuine inverse-section union is a subgroup fundamental domain. -/
lemma lpsRelativeDomain_fundamental (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    IsFundamentalDomain H (lpsRelativeDomain H s r) μ := by
  apply IsFundamentalDomain.mk'' (lpsRelativeDomain_nullMeasurable H s r hs)
  · exact lpsRelativeDomain_covers H s r hr hs
  · exact lpsRelativeDomain_aedisjoint H s r hr hs
  · intro h
    exact (MeasureTheory.measurePreserving_smul (h : G) μ).quasiMeasurePreserving

omit [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] in
/-- Distinct coset components are almost disjoint in the original measure. -/
lemma lpsRelativeDomain_components (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    Pairwise (fun c d => AEDisjoint μ ((r c)⁻¹ • s)
      ((r d)⁻¹ • s)) := by
  intro c d hcd
  apply hs.aedisjoint
  intro he
  apply hcd
  have he' : r c = r d := inv_injective he
  exact (hr c).symm.trans ((congrArg (QuotientGroup.mk : G →
    G ⧸ H) he').trans (hr d))

/-- Integrate the true finite-index cover as inverse-actor component integrals. -/
lemma lpsRelativeDomain_integral (H : Subgroup G) (s : Set α)
    [H.FiniteIndex] (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) (F : α → E)
    (hF : ∀c, IntegrableOn F ((r c)⁻¹ • s) μ) :
    (∫τ in lpsRelativeDomain H s r, F τ ∂μ) =
      ∑' c, ∫τ in s, F ((r c)⁻¹ • τ) ∂μ := by
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  unfold lpsRelativeDomain
  rw [integral_iUnion_ae
    (fun c => hs.nullMeasurableSet_smul (r c)⁻¹)
    (lpsRelativeDomain_components H s r hr hs) (integrableOn_finite_iUnion.mpr hF)]
  apply tsum_congr
  intro c
  exact (MeasureTheory.measurePreserving_smul (r c)⁻¹ μ).setIntegral_image_emb
    (measurableEmbedding_const_smul (r c)⁻¹) F s

/-- The actual finite-index cover has exact index times original domain measure. -/
lemma lpsRelativeDomain_measure (H : Subgroup G) (s : Set α)
    [H.FiniteIndex] (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    (μ : Measure α) (lpsRelativeDomain H s r) =
      (H.index : ℝ≥0∞) * μ s := by
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  unfold lpsRelativeDomain
  rw [measure_iUnion₀ (lpsRelativeDomain_components H s r hr hs)
    (fun c => hs.nullMeasurableSet_smul (r c)⁻¹)]
  simp only [measure_smul,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Subgroup.index, Nat.card_eq_fintype_card]

section IndexedRelative
variable {G α I : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  [Fintype I] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype I] in
/-- A genuine indexed coset section constructs a subgroup fundamental domain. -/
lemma lpsIndexedRelativeDomain_fundamental (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) :
    IsFundamentalDomain H (⋃i,(r i)⁻¹ • s) μ := by
  have heq : (⋃i,(r i)⁻¹ • s)=lpsRelativeDomain H s (fun c => r (e.symm c)) := by
    ext x
    simp only [lpsRelativeDomain,Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨e i,by simpa using hi⟩
    · rintro ⟨c,hc⟩
      exact ⟨e.symm c,hc⟩
  rw [heq]
  exact lpsRelativeDomain_fundamental H s _ (by intro c;simpa using hr (e.symm c)) hs

omit [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] [Fintype I] in
/-- Distinct true indexed section components are almost disjoint. -/
lemma lpsIndexedRelativeDomain_components (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) :
    Pairwise (fun i j => AEDisjoint μ ((r i)⁻¹ • s) ((r j)⁻¹ • s)) := by
  intro i j hij
  apply hs.aedisjoint
  intro he
  apply hij
  apply e.injective
  rw [←hr i,←hr j,inv_injective he]

omit [Countable G] in
/-- The integrable indexed cover equals its true finite inverse-actor integral sum. -/
lemma lpsIndexedRelativeDomain_integral (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) (F : α → E)
    (hF : ∀i,IntegrableOn F ((r i)⁻¹ • s) μ) :
    (∫x in ⋃i,(r i)⁻¹ • s,F x ∂μ)=∑i,∫x in s,F ((r i)⁻¹ • x) ∂μ := by
  rw [integral_iUnion_ae (fun i => hs.nullMeasurableSet_smul (r i)⁻¹)
    (lpsIndexedRelativeDomain_components H s hs e r hr) (integrableOn_finite_iUnion.mpr hF),
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _hi
  exact (MeasureTheory.measurePreserving_smul (r i)⁻¹ μ).setIntegral_image_emb
    (measurableEmbedding_const_smul (r i)⁻¹) F s
end IndexedRelative

/-- Transport a true relative-subgroup domain back to its actual original subgroup. -/
lemma lpsRelativeFundamental_subgroupOf {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] (H K : Subgroup G) (h : H ≤ K) {μ : Measure α}
    {s : Set α} (hs : IsFundamentalDomain (H.subgroupOf K) s μ) :
    IsFundamentalDomain H s μ :=
  hs.preimage_of_equiv (Measure.QuasiMeasurePreserving.id μ)
    (Subgroup.subgroupOfEquivOfLe h).bijective (fun _ _ => rfl)

end
end QEC.Coding.TannerLiftedProduct
