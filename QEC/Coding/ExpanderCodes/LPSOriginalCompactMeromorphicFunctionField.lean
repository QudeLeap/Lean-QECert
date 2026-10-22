import QEC.Coding.ExpanderCodes.LPSOriginalFullMeromorphicFunctionField

/-!
# The entire original compact meromorphic function field

This module belongs to the source-grounded original LPS analytic proof closure.
Milne, *Modular Functions and Modular Forms*, Theorem 6.1 (PDF85 / printed82)
and Propositions 1.16–1.18 motivate the genuine function-field degree argument.
The filled original Gamma0(N) manifold statements retain their proved scope
4 divides N, including the actual theta levels 16*q_graph^2.

The all-meromorphic objects use actual chartwise-meromorphic representatives
and genuine germ equality. They are never defined as the generated C(j,j_N).
The public arbitrary-field/all-rate PK22 theorem, arithmetic normalization,
uniform good reduction and geometric Weil estimate remain further proof work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- An actual local homeomorphism sends genuine punctured neighborhoods to punctured neighborhoods. -/
lemma lpsOriginalLocalHomeomorph_tendsto_punctured
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) (x : X) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] (f x)) := by
  obtain ⟨e,hx,he⟩ := hf x
  rw [he]
  exact tendsto_nhdsWithin_iff.mpr
    ⟨(e.continuousAt hx).tendsto.mono_left nhdsWithin_le_nhds,
      e.eventually_ne_nhdsWithin hx⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Zero actual global compact-curve germs pull back to zero upstairs through the original local quotient. -/
lemma lpsOriginalFilled_global_germ_zero_pullback
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) :
    letI := lpsOriginalFilledTopology N
    (F : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) = 0 →
      (lpsOriginalFilledMeromorphicPullback N F :
        Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ) = 0 := by
  let := lpsOriginalFilledTopology N
  intro hF
  have he : {y : LPSOriginalFilledCurve N | F y = 0} ∈
      Filter.codiscrete (LPSOriginalFilledCurve N) := by
    exact Filter.Germ.coe_eq.mp hF
  apply Filter.Germ.coe_eq.mpr
  change {z : ℂ | lpsOriginalFilledMeromorphicPullback N F z = 0} ∈
    Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  let π : ℍ → LPSOriginalFilledCurve N := fun τ => Sum.inl ⟦τ⟧
  have hπ : IsLocalHomeomorph π :=
    (lpsOriginalFilledTopology_interior_openEmbedding N).isLocalHomeomorph.comp
      (lpsGamma0_quotient_localHomeomorph N hN)
  have hsource : z ∈ UpperHalfPlane.ofComplex.source := by
    change z ∈ (UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph
      (UpperHalfPlane.coe : ℍ → ℂ)).target
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨z,hz⟩,rfl⟩
  have ho : Tendsto UpperHalfPlane.ofComplex (𝓝[≠] z)
      (𝓝[≠] (UpperHalfPlane.ofComplex z)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(UpperHalfPlane.ofComplex.continuousAt hsource).tendsto.mono_left nhdsWithin_le_nhds,
        UpperHalfPlane.ofComplex.eventually_ne_nhdsWithin hsource⟩
  have ht := (lpsOriginalLocalHomeomorph_tendsto_punctured hπ
    (UpperHalfPlane.ofComplex z)).comp ho
  have hf : ∀ᶠ y in 𝓝[≠] (π (UpperHalfPlane.ofComplex z)), F y = 0 := by
    have hh := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp he
      (π (UpperHalfPlane.ofComplex z)) (Set.mem_univ _)
    simp only [Set.compl_univ,Set.union_empty] at hh
    exact hh
  filter_upwards [ht.eventually hf] with w hw
  exact Or.inl hw

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Zero upstairs germs force zero actual values at every regular interior point. -/
lemma lpsOriginalFilledMeromorphic_zero_at_regular_interior
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hzero : (lpsOriginalFilledMeromorphicPullback N F :
      Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ) = 0)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F (Sum.inl x) → F (Sum.inl x) = 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro hreg
  let e := lpsOriginalFilledInteriorChart N hN x
  let a := e (Sum.inl x)
  have hs : Sum.inl x ∈ e.source := lpsOriginalFilledInteriorChart_mem N hN x
  have ha : a ∈ e.target := e.map_source hs
  have hpos : 0 < a.im := lpsOriginalFilledInteriorChart_target_pos N hN x a ha
  have hc : ContinuousAt (F ∘ e.symm) a := by
    have hFc : ContinuousAt F (e.symm a) := by
      rw [show e.symm a = Sum.inl x from e.left_inv hs]
      exact hreg.continuousAt
    exact hFc.comp (e.symm.continuousAt ha)
  have hh := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp
    (Filter.Germ.coe_eq.mp hzero) a hpos
  have hH : ∀ᶠ z : ℂ in 𝓝[≠] a, z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    nhdsWithin_le_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hpos)
  have hf : (F ∘ e.symm) =ᶠ[𝓝[≠] a] (0 : ℂ → ℂ) := by
    filter_upwards [hh,hH] with z hz hzin
    have hz0 := hz.resolve_right (by simpa using hzin)
    change F (e.symm z) = 0
    change lpsOriginalFilledMeromorphicPullback N F z = 0 at hz0
    dsimp only [e]
    rw [lpsOriginalFilledInteriorChart_symm]
    exact hz0
  have h := tendsto_nhds_unique
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
    ((tendsto_const_nhds : Tendsto (0 : ℂ → ℂ) (𝓝[≠] a) (𝓝 (0 : ℂ))).congr' hf.symm)
  change F (e.symm a) = 0 at h
  rw [show e.symm a = Sum.inl x from e.left_inv hs] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compactness and the true finite cusp set recover zero global germs from zero upstairs germs. -/
lemma lpsOriginalFilledMeromorphic_pullback_zero_global_germ
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hzero : (lpsOriginalFilledMeromorphicPullback N F :
      Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ) = 0) :
    letI := lpsOriginalFilledTopology N
    (F : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) = 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let : T1Space (LPSOriginalFilledCurve N) := @T2Space.t1Space _
    (lpsOriginalFilledTopology N) (lpsOriginalFilledTopology_t2Space N)
  let B := {x : LPSOriginalFilledCurve N | ¬ ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x}
  have hB : B.Finite := lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN F hF
  have hC : (Set.range (Sum.inr : CuspOrbits
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) → LPSOriginalFilledCurve N)).Finite :=
    Set.finite_range _
  have he := (hB.union hC).compl_mem_codiscrete
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [he] with x hx
  rcases x with x | c
  · apply lpsOriginalFilledMeromorphic_zero_at_regular_interior N hN F hzero x
    by_contra hn
    exact hx (Or.inl hn)
  · exact False.elim (hx (Or.inr ⟨c,rfl⟩))

/-- Actual global compact-curve germ equality to zero is equivalent to upstairs restriction equality to zero. -/
lemma lpsOriginalFilledMeromorphic_germ_zero_iff
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    (F : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) = 0 ↔
      (lpsOriginalFilledMeromorphicPullback N F :
        Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ) = 0 :=
  ⟨lpsOriginalFilled_global_germ_zero_pullback N hN F,
    lpsOriginalFilledMeromorphic_pullback_zero_global_germ N hN F hF⟩

/-- Genuine global compact-curve germ equality is exactly genuine upstairs restriction equality. -/
lemma lpsOriginalFilledMeromorphic_germ_eq_iff
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F G : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hG : lpsOriginalFilledChartMeromorphic N hN G) :
    letI := lpsOriginalFilledTopology N
    (F : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) = G ↔
      (lpsOriginalFilledMeromorphicPullback N F :
        Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ) =
      lpsOriginalFilledMeromorphicPullback N G := by
  let := lpsOriginalFilledTopology N
  have hsub : lpsOriginalFilledChartMeromorphic N hN (F-G) :=
    lpsOriginalFilledChartMeromorphic_add N hN hF
      (lpsOriginalFilledChartMeromorphic_neg N hN hG)
  have h := lpsOriginalFilledMeromorphic_germ_zero_iff N hN (F-G) hsub
  have he : lpsOriginalFilledMeromorphicPullback N (F-G) =
      lpsOriginalFilledMeromorphicPullback N F - lpsOriginalFilledMeromorphicPullback N G := rfl
  rw [he,Filter.Germ.coe_sub,Filter.Germ.coe_sub,sub_eq_zero,sub_eq_zero] at h
  exact h

/-- The pointwise ring of ALL actual functions meromorphic in every original filled chart. -/
def lpsOriginalFilledMeromorphicFunctionSubring
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) : Subring (LPSOriginalFilledCurve N → ℂ) where
  carrier := {F | lpsOriginalFilledChartMeromorphic N hN F}
  zero_mem' := lpsOriginalFilledChartMeromorphic_const N hN 0
  one_mem' := lpsOriginalFilledChartMeromorphic_const N hN 1
  add_mem' := lpsOriginalFilledChartMeromorphic_add N hN
  mul_mem' := lpsOriginalFilledChartMeromorphic_mul N hN
  neg_mem' := lpsOriginalFilledChartMeromorphic_neg N hN

/-- The underlying ring of ALL actual original filled-curve meromorphic representatives. -/
abbrev LPSOriginalFilledMeromorphicFunctionRing
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  ↥(lpsOriginalFilledMeromorphicFunctionSubring N hN)

/-- Send ALL actual original chartwise-meromorphic functions to genuine global codiscrete germs. -/
def lpsOriginalCompactMeromorphicGermMap
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    LPSOriginalFilledMeromorphicFunctionRing N hN →+*
      Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ := by
  let := lpsOriginalFilledTopology N
  exact (Filter.Germ.coeRingHom (Filter.codiscrete (LPSOriginalFilledCurve N))).comp
    (lpsOriginalFilledMeromorphicFunctionSubring N hN).subtype

/-- The actual global germ image of ALL chartwise-meromorphic representatives, without a generation definition. -/
abbrev LPSOriginalCompactMeromorphicGermRing
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  ↥(lpsOriginalCompactMeromorphicGermMap N hN).range

/-- The concrete original upstairs restriction map for every actual meromorphic representative. -/
def lpsOriginalFilledFunctionToRestrictedMeromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    LPSOriginalFilledMeromorphicFunctionRing N hN →+*
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN where
  toFun F := lpsOriginalFilledMeromorphicRestriction N hN F.val F.property
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)

/-- Actual global germ equality makes upstairs restriction well-defined on the genuine quotient. -/
lemma lpsOriginalCompactMeromorphicGermMap_kernel_le
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    RingHom.ker (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict ≤
      RingHom.ker (lpsOriginalFilledFunctionToRestrictedMeromorphic N hN) := by
  intro F hF
  change (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F = 0 at hF
  have he := congrArg Subtype.val hF
  have h := lpsOriginalFilled_global_germ_zero_pullback N hN F.val he
  change lpsOriginalFilledFunctionToRestrictedMeromorphic N hN F = 0
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- Descend the actual restriction map through genuine global compact-curve germs. -/
def lpsOriginalCompactToRestrictedMeromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    LPSOriginalCompactMeromorphicGermRing N hN →+*
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN :=
  ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.liftOfSurjective
    (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective)
    ⟨lpsOriginalFilledFunctionToRestrictedMeromorphic N hN,
      lpsOriginalCompactMeromorphicGermMap_kernel_le N hN⟩

/-- The descended map literally recovers restriction of every actual representative. -/
lemma lpsOriginalCompactToRestrictedMeromorphic_apply
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) :
    lpsOriginalCompactToRestrictedMeromorphic N hN
      ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F) =
        lpsOriginalFilledMeromorphicRestriction N hN F.val F.property :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

/-- The genuine global/upstairs germ comparison makes compact-curve restriction faithful. -/
lemma lpsOriginalCompactToRestrictedMeromorphic_injective
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Function.Injective (lpsOriginalCompactToRestrictedMeromorphic N hN) := by
  intro x y he
  obtain ⟨F,rfl⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective x
  obtain ⟨G,rfl⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective y
  rw [lpsOriginalCompactToRestrictedMeromorphic_apply,
    lpsOriginalCompactToRestrictedMeromorphic_apply] at he
  have hH := congrArg (fun z : lpsOriginalFilledMeromorphicRestrictionSubfield N hN =>
    z.val.val) he
  have hg := (lpsOriginalFilledMeromorphic_germ_eq_iff N hN F.val G.val F.property G.property).mpr hH
  exact Subtype.ext hg

/-- Every actual meromorphic restriction comes from its genuine compact-curve representative. -/
lemma lpsOriginalCompactToRestrictedMeromorphic_surjective
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Function.Surjective (lpsOriginalCompactToRestrictedMeromorphic N hN) := by
  intro x
  obtain ⟨F,hF,hx⟩ := x.property
  refine ⟨(lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict ⟨F,hF⟩,?_⟩
  rw [lpsOriginalCompactToRestrictedMeromorphic_apply]
  apply Subtype.ext
  apply Subtype.ext
  exact hx.symm

/-- The concrete equivalence between ALL original global meromorphic germs and ALL actual restrictions. -/
def lpsOriginalCompactRestrictedMeromorphicEquiv
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    LPSOriginalCompactMeromorphicGermRing N hN ≃+*
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN :=
  RingEquiv.ofBijective (lpsOriginalCompactToRestrictedMeromorphic N hN)
    ⟨lpsOriginalCompactToRestrictedMeromorphic_injective N hN,
      lpsOriginalCompactToRestrictedMeromorphic_surjective N hN⟩

/-- Faithful actual restriction proves the genuine compact meromorphic ring nontrivial. -/
instance lpsOriginalCompactMeromorphicGerm_nontrivial
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Nontrivial (LPSOriginalCompactMeromorphicGermRing N hN) := by
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  have hh := congrArg (lpsOriginalCompactToRestrictedMeromorphic N hN) h
  rw [map_zero,map_one] at hh
  exact zero_ne_one hh

/-- Construct actual field inverses on the entire compact-curve meromorphic germ ring. -/
@[instance_reducible]
def lpsOriginalCompactMeromorphicGermField
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Field (LPSOriginalCompactMeromorphicGermRing N hN) :=
  Field.ofIsUnitOrEqZero (fun A => by
    by_cases hA : A=0
    · exact Or.inr hA
    · apply Or.inl
      let f := lpsOriginalCompactToRestrictedMeromorphic N hN
      have hfa : f A ≠ 0 := by
        intro hz
        apply hA
        apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
        simpa only [map_zero] using hz
      obtain ⟨b,hb⟩ := isUnit_iff_exists_inv.mp (isUnit_iff_ne_zero.mpr hfa)
      obtain ⟨B,hB⟩ := lpsOriginalCompactToRestrictedMeromorphic_surjective N hN b
      apply isUnit_iff_exists_inv.mpr
      refine ⟨B,?_⟩
      apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
      rw [map_mul,hB,hb,map_one])

/-- The SAME independently generated C(j,j_N) is equivalent to ALL actual original compact meromorphic germs. -/
def lpsOriginalGeneratedCompactMeromorphicEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    lpsOriginalGeneratedFunctionField N hpos ≃+* LPSOriginalCompactMeromorphicGermRing N hN := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact (lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN).trans
    (lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm

/-- The genuine field instance on ALL actual original compact-curve meromorphic germs. -/
instance lpsOriginalCompactMeromorphicField
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Field (LPSOriginalCompactMeromorphicGermRing N hN) :=
  lpsOriginalCompactMeromorphicGermField N hN

/-- The faithful SAME C(j) map into the actual original compact meromorphic field. -/
def lpsOriginalCompactMeromorphicJFractionEmbedding
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    FractionRing (Polynomial ℂ) →+* LPSOriginalCompactMeromorphicGermRing N hN :=
  (lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm.toRingHom.comp
    (lpsOriginalFullMeromorphicJFractionEmbedding N hN)

/-- The full original compact meromorphic-field equivalence preserves the SAME faithful C(j) base. -/
def lpsOriginalGeneratedCompactMeromorphicAlgEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    lpsOriginalGeneratedFunctionField N hpos ≃ₐ[FractionRing (Polynomial ℂ)]
      LPSOriginalCompactMeromorphicGermRing N hN := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  let e := lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN
  refine { e with commutes' := ?_ }
  intro r
  apply (lpsOriginalCompactRestrictedMeromorphicEquiv N hN).injective
  change (lpsOriginalCompactRestrictedMeromorphicEquiv N hN)
    ((lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm
      (lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN
        (algebraMap (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hpos) r))) =
    (lpsOriginalCompactRestrictedMeromorphicEquiv N hN)
      ((lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm
        (lpsOriginalFullMeromorphicJFractionEmbedding N hN r))
  rw [RingEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  apply Subtype.ext
  rfl

/-- The ENTIRE actual compact meromorphic field is finite dimensional over SAME C(j). -/
lemma lpsOriginalCompactMeromorphicField_finiteDimensional
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    FiniteDimensional (FractionRing (Polynomial ℂ))
      (LPSOriginalCompactMeromorphicGermRing N hN) := by
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
  let e := lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

/-- The ENTIRE actual compact meromorphic field has the genuine original Gamma0 coset degree. -/
lemma lpsOriginalCompactMeromorphicField_finrank_eq
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ))
      (LPSOriginalCompactMeromorphicGermRing N hN) =
        Nat.card (LPSOriginalMeromorphicCosets N) := by
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [←(lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN).toLinearEquiv.finrank_eq]
  exact lpsOriginalGeneratedFunctionField_finrank_eq N hpos

/-- Every actual original compact meromorphic function has a SAME C(j,j_N) representation in genuine global germs. -/
lemma lpsOriginalCompactMeromorphic_generated_representation
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∃ x : lpsOriginalGeneratedFunctionField N hpos,
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN x).val =
        (F : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let y := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict
    (⟨F,hF⟩ : LPSOriginalFilledMeromorphicFunctionRing N hN)
  refine ⟨(lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN).symm y,?_⟩
  rw [RingEquiv.apply_symm_apply]
  rfl

end
end QEC.Coding.TannerLiftedProduct
