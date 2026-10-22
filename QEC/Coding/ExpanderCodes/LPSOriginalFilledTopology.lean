import QEC.Coding.ExpanderCodes.LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order

/-!
# LPSOriginalFilledTopology

The actual final cusp-gluing topology: original/cusp open embeddings, compactness, Hausdorffness and second countability.
This internal topological geometry supplies no complex analytic filled atlas, arithmetic
modular model, good reduction, Hecke/Frobenius/Jacobian/Rosati magnitude or PK22 theorem.
The original group, source and public theorem scope remain unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

/-- The FINAL gluing topology of the actual original interior and genuine filled-disc parametrizations. -/
@[instance_reducible]
def lpsOriginalFilledTopology (N : ℕ) [NeZero N] : TopologicalSpace (LPSOriginalFilledCurve N) :=
  TopologicalSpace.coinduced
    (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N)
    inferInstance ⊔
    ⨆ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      TopologicalSpace.coinduced (lpsOriginalFilledCuspParam N c) inferInstance

/-- Openness in the actual gluing topology is tested on the true interior and true filled discs. -/
lemma lpsOriginalFilledTopology_isOpen_iff (N : ℕ) [NeZero N]
    (s : Set (LPSOriginalFilledCurve N)) :
    IsOpen[lpsOriginalFilledTopology N] s ↔
      IsOpen ((Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) ⁻¹' s) ∧
        ∀ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
          IsOpen (lpsOriginalFilledCuspParam N c ⁻¹' s) := by
  change (IsOpen ((Sum.inl : MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) ⁻¹' s) ∧
    IsOpen[⨆ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      TopologicalSpace.coinduced (lpsOriginalFilledCuspParam N c) inferInstance] s) ↔ _
  exact and_congr_right (fun _ => isOpen_iSup_iff)

/-- The original interior injection is continuous for the specified genuine gluing topology. -/
lemma lpsOriginalFilledTopology_interior_continuous (N : ℕ) [NeZero N] :
    @Continuous _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  apply continuous_iff_coinduced_le.mpr
  exact le_sup_left

/-- The genuine filled-disc parametrization is continuous for the specified gluing topology. -/
lemma lpsOriginalFilledTopology_param_continuous (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @Continuous _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspParam N c) := by
  apply continuous_iff_coinduced_le.mpr
  exact (le_iSup (fun c => TopologicalSpace.coinduced (lpsOriginalFilledCuspParam N c)
    inferInstance) c).trans le_sup_right

/-- Each actual closed cusp patch is compact in the true filled topology. -/
lemma lpsOriginalFilledTopology_closedPatch_isCompact (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @IsCompact (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspClosedPatch N c) := by
  let := lpsOriginalFilledTopology N
  have hc : ContinuousOn
      (lpsOriginalFilledCuspInvFun N (lpsOriginalCuspRepresentative N c))
      (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target :=
    continuousOn_iff_continuous_domRestrict.mpr (lpsOriginalFilledTopology_param_continuous N c)
  exact (isCompact_closedBall (0:ℂ) _).image_of_continuousOn
    (hc.mono (lpsOriginalFilledCuspClosedPatch_disc_inside N c))

/-- The whole actual filled topology is compact by the genuine finite compact cover. -/
lemma lpsOriginalFilledTopology_compactSpace (N : ℕ) [NeZero N] :
    @CompactSpace (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by
  let := lpsOriginalFilledTopology N
  constructor
  rw [←lpsOriginalFilledCurve_finite_cover N]
  exact ((lpsOriginalGamma0CompactCore_isCompact N 2).image
    (lpsOriginalFilledTopology_interior_continuous N)).union
      (isCompact_iUnion (lpsOriginalFilledTopology_closedPatch_isCompact N))

/-- The actual filled-disc parametrization is PROVED open in the genuine gluing topology. -/
lemma lpsOriginalFilledTopology_param_open (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @IsOpenMap _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspParam N c) := by
  intro s hs
  apply (lpsOriginalFilledTopology_isOpen_iff N _).mpr
  constructor
  · rw [lpsOriginalFilledCuspParam_original_preimage]
    exact lpsOriginalCuspPunctInverse_open N _ _
      ((lpsOriginalCuspPunctToFull_continuous N _).isOpen_preimage s hs)
  · intro d
    by_cases hd : d=c
    · subst d
      rw [Set.preimage_image_eq _ (lpsOriginalFilledCuspParam_injective N c)]
      exact hs
    · rw [lpsOriginalFilledCuspParam_other_preimage N c d hd]
      exact isOpen_empty

/-- The true full cusp disc is an OPEN EMBEDDING in the actual filled topology. -/
lemma lpsOriginalFilledTopology_param_openEmbedding (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @Topology.IsOpenEmbedding _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspParam N c) := by
  let := lpsOriginalFilledTopology N
  exact .of_continuous_injective_isOpenMap (lpsOriginalFilledTopology_param_continuous N c)
    (lpsOriginalFilledCuspParam_injective N c) (lpsOriginalFilledTopology_param_open N c)

/-- The original interior injection is PROVED open in the genuine filled topology. -/
lemma lpsOriginalFilledTopology_interior_open (N : ℕ) [NeZero N] :
    @IsOpenMap _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  intro s hs
  apply (lpsOriginalFilledTopology_isOpen_iff N _).mpr
  constructor
  · rw [Set.preimage_image_eq _ Sum.inl_injective]
    exact hs
  · intro c
    rw [lpsOriginalFilledCuspParam_interior_preimage]
    exact lpsOriginalCuspPunctToFull_open N _ _
      ((lpsOriginalCuspPunctInverse_continuous N _).isOpen_preimage s hs)

/-- The ORIGINAL quotient is an OPEN EMBEDDING retaining its topology inside the true filling. -/
lemma lpsOriginalFilledTopology_interior_openEmbedding (N : ℕ) [NeZero N] :
    @Topology.IsOpenEmbedding _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  exact .of_continuous_injective_isOpenMap (lpsOriginalFilledTopology_interior_continuous N)
    Sum.inl_injective (lpsOriginalFilledTopology_interior_open N)

/-- Actual height bounds give disjoint OPEN neighborhoods of every interior point and genuine cusp. -/
lemma lpsOriginalFilledTopology_interior_cusp_separation (N : ℕ) [NeZero N]
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    ∃ u v : Set (LPSOriginalFilledCurve N),
      IsOpen[lpsOriginalFilledTopology N] u ∧ IsOpen[lpsOriginalFilledTopology N] v ∧
        Sum.inl y∈u ∧ Sum.inr c∈v ∧ Disjoint u v := by
  let := lpsOriginalFilledTopology N
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep y
  let A : Set ℍ := {σ | τ.im/2<σ.im ∧ σ.im<τ.im+1}
  let Y : ℝ := τ.im+1+2/τ.im+2
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  let B : Set ((lpsOriginalFilledCuspPartialEquiv N r).target) :=
    {q | ‖q.val‖<Real.exp (-2*Real.pi*Y/w)}
  let π : ℍ → MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
      Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  have hA : IsOpen A := (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
  have hB : IsOpen B := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  refine ⟨Sum.inl '' (π '' A),lpsOriginalFilledCuspParam N c '' B,
    lpsOriginalFilledTopology_interior_open N _ (lpsOriginalGamma0_quotientProjection_open N _ hA),
    lpsOriginalFilledTopology_param_open N c _ hB,?_,?_,?_⟩
  · refine ⟨⟦τ⟧,⟨τ,?_,rfl⟩,rfl⟩
    change τ.im/2<τ.im ∧ τ.im<τ.im+1
    constructor <;> linarith [τ.im_pos]
  · let q : (lpsOriginalFilledCuspPartialEquiv N r).target :=
      ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N r⟩
    refine ⟨q,?_,lpsOriginalFilledCuspParam_zero N c q rfl⟩
    change ‖(0:ℂ)‖<_
    simpa only [norm_zero] using Real.exp_pos (-2*Real.pi*Y/w)
  · apply Set.disjoint_left.mpr
    rintro x ⟨a,⟨σ,hσ,heσ⟩,hex⟩ ⟨q,hq,heq⟩
    have hx : lpsOriginalFilledCuspParam N c q=Sum.inl (π σ) := by
      rw [heσ,hex]
      exact heq
    by_cases hz : q.val=0
    · rw [lpsOriginalFilledCuspParam_zero N c q hz] at hx
      cases hx
    obtain ⟨σ',heq',hq'⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c q hz
    have hp : lpsOriginalGamma0Projected N r σ'.val=π σ :=
      Sum.inl.inj (heq'.symm.trans hx)
    have hb := lpsOriginalGamma0_projected_im_bound N r σ'.val σ hp
    have hw : 0<w := lpsOriginalCuspGroup_width_positive N r
    have hhigh : Y<σ'.val.im := by
      have hn : ‖Function.Periodic.qParam w σ'.val‖<Real.exp (-2*Real.pi*Y/w) := by
        rw [←hq']
        exact hq
      simpa only [UpperHalfPlane.coe_im] using
        (Function.Periodic.norm_qParam_lt_iff hw Y (σ'.val:ℂ)).mp hn
    change τ.im/2<σ.im ∧ σ.im<τ.im+1 at hσ
    have hi : 1/σ.im<2/τ.im := by
      apply (div_lt_div_iff₀ σ.im_pos τ.im_pos).mpr
      nlinarith [hσ.1]
    have hYb : τ.im+1<Y := by
      dsimp [Y]
      have hd : 0<2/τ.im := div_pos (by norm_num) τ.im_pos
      linarith
    have hYi : 2/τ.im<Y := by dsimp [Y];linarith [τ.im_pos]
    have hmax : max σ.im (1/σ.im)<Y := max_lt (hσ.2.trans hYb) (hi.trans hYi)
    linarith

/-- The actual filled topology is Hausdorff, including interior-cusp and cusp-cusp separation. -/
lemma lpsOriginalFilledTopology_t2Space (N : ℕ) [NeZero N] :
    @T2Space (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by
  let := lpsOriginalFilledTopology N
  let : T2Space (MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := lpsOriginalGamma0Quotient_t2 N
  constructor
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have hab : a≠b := fun h => hxy (congrArg Sum.inl h)
      obtain ⟨u,v,hu,hv,ha,hb,hd⟩ := t2_separation hab
      refine ⟨Sum.inl '' u,Sum.inl '' v,lpsOriginalFilledTopology_interior_open N u hu,
        lpsOriginalFilledTopology_interior_open N v hv,⟨a,ha,rfl⟩,⟨b,hb,rfl⟩,?_⟩
      apply Set.disjoint_left.mpr
      rintro z ⟨a',ha',rfl⟩ ⟨b',hb',he⟩
      have he' := Sum.inl.inj he
      subst b'
      exact Set.disjoint_left.mp hd ha' hb'
    | inr c => exact lpsOriginalFilledTopology_interior_cusp_separation N a c
  | inr c =>
    cases y with
    | inl a =>
      obtain ⟨u,v,hu,hv,ha,hc,hd⟩ := lpsOriginalFilledTopology_interior_cusp_separation N a c
      exact ⟨v,u,hv,hu,hc,ha,hd.symm⟩
    | inr d =>
      have hcd : c≠d := fun h => hxy (congrArg Sum.inr h)
      have hc := lpsOriginalFilledTopology_param_openEmbedding N c
      have hd := lpsOriginalFilledTopology_param_openEmbedding N d
      refine ⟨Set.range (lpsOriginalFilledCuspParam N c),Set.range (lpsOriginalFilledCuspParam N d),
        hc.isOpen_range,hd.isOpen_range,?_,?_,?_⟩
      · let q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target :=
          ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N _⟩
        exact ⟨q,lpsOriginalFilledCuspParam_zero N c q rfl⟩
      · let q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N d)).target :=
          ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N _⟩
        exact ⟨q,lpsOriginalFilledCuspParam_zero N d q rfl⟩
      · rw [lpsOriginalFilledCuspParam_range,lpsOriginalFilledCuspParam_range]
        exact lpsOriginalFilledCuspPartialEquiv_sources_disjoint N _ _ (by
          simpa only [lpsOriginalCuspRepresentative_orbit] using hcd)

/-- The actual filled topology is second countable via its genuine open surjective finite-disc cover. -/
lemma lpsOriginalFilledTopology_secondCountable (N : ℕ) [NeZero N] :
    @SecondCountableTopology (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by
  let := lpsOriginalFilledTopology N
  let : SecondCountableTopology (MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :=
    lpsOriginalGamma0Quotient_secondCountable N
  let C := CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let D := MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ ⊕
      (Σ c : C, (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
  let f : D → LPSOriginalFilledCurve N :=
    Sum.elim Sum.inl (fun cq => lpsOriginalFilledCuspParam N cq.1 cq.2)
  have hc : Continuous f := continuous_sumElim.mpr
    ⟨lpsOriginalFilledTopology_interior_continuous N,
      continuous_sigma (fun c => lpsOriginalFilledTopology_param_continuous N c)⟩
  have ho : IsOpenMap f := isOpenMap_sumElim.mpr
    ⟨lpsOriginalFilledTopology_interior_open N,
      isOpenMap_sigma.mpr (fun c => lpsOriginalFilledTopology_param_open N c)⟩
  have hs : Function.Surjective f := by
    intro x
    cases x with
    | inl y => exact ⟨Sum.inl y,rfl⟩
    | inr c =>
      let q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target :=
        ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N _⟩
      exact ⟨Sum.inr ⟨c,q⟩,lpsOriginalFilledCuspParam_zero N c q rfl⟩
  exact (ho.isQuotientMap hc hs).secondCountableTopology ho

end
end QEC.Coding.TannerLiftedProduct
