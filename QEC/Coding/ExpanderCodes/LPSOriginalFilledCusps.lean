import QEC.Coding.ExpanderCodes.LPSOriginalCompactCore

/-!
# LPSOriginalFilledCusps

One point per ACTUAL original cusp orbit, proved full-disc inverse laws and genuine finite cover.
This internal topological geometry supplies no complex analytic filled atlas, arithmetic
modular model, good reduction, Hecke/Frobenius/Jacobian/Rosati magnitude or PK22 theorem.
The original group, source and public theorem scope remain unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

/-- The original orbit quotient plus one point for each ACTUAL cusp orbit; this abbreviation supplies no topology. -/
abbrev LPSOriginalFilledCurve (N : ℕ) : Type :=
  MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ ⊕
    CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

/-- The actual punctured original neighborhood together with its single genuine added cusp. -/
def lpsOriginalFilledCuspSource (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Set (LPSOriginalFilledCurve N) := fun x =>
  match x with
  | Sum.inl y => y∈Set.range (lpsOriginalCuspProjection N ρ)
  | Sum.inr c => c=lpsOriginalCuspOrbit N ρ

/-- Extend the genuine minimal-width original coordinate by zero at the added cusp. -/
def lpsOriginalFilledCuspToFun (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    LPSOriginalFilledCurve N → ℂ := fun x =>
  match x with
  | Sum.inl y => if hy : y∈Set.range (lpsOriginalCuspProjection N ρ) then
      (lpsOriginalCuspNeighborhoodChart N ρ ⟨y,hy⟩).val else 0
  | Sum.inr _ => 0

/-- The actual inverse coordinate, sending zero to the genuine added cusp. -/
def lpsOriginalFilledCuspInvFun (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) (q : ℂ) :
    LPSOriginalFilledCurve N :=
  if hq : q=0 then Sum.inr (lpsOriginalCuspOrbit N ρ)
  else if hn : ‖q‖<Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty) then
    Sum.inl ((lpsOriginalCuspNeighborhoodChart N ρ).symm ⟨q,hq,hn⟩).val
  else Sum.inr (lpsOriginalCuspOrbit N ρ)

/-- A proved filled-disc partial equivalence on the actual original quotient with its true cusps. -/
def lpsOriginalFilledCuspPartialEquiv (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    PartialEquiv (LPSOriginalFilledCurve N) ℂ where
  toFun := lpsOriginalFilledCuspToFun N ρ
  invFun := lpsOriginalFilledCuspInvFun N ρ
  source := lpsOriginalFilledCuspSource N ρ
  target := {q | ‖q‖<Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty)}
  map_source' := by
    intro x hx
    cases x with
    | inl y =>
      change y∈Set.range (lpsOriginalCuspProjection N ρ) at hx
      change ‖lpsOriginalFilledCuspToFun N ρ (Sum.inl y)‖<_
      rw [lpsOriginalFilledCuspToFun,dif_pos hx]
      exact (lpsOriginalCuspNeighborhoodChart N ρ ⟨y,hx⟩).property.2
    | inr c =>
      change ‖(0:ℂ)‖<_
      simpa only [norm_zero] using Real.exp_pos
        (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty)
  map_target' := by
    intro q hq
    change ‖q‖<_ at hq
    by_cases hz : q=0
    · rw [lpsOriginalFilledCuspInvFun,dif_pos hz]
      rfl
    · rw [lpsOriginalFilledCuspInvFun,dif_neg hz,dif_pos hq]
      exact ((lpsOriginalCuspNeighborhoodChart N ρ).symm ⟨q,hz,hq⟩).property
  left_inv' := by
    intro x hx
    cases x with
    | inl y =>
      change y∈Set.range (lpsOriginalCuspProjection N ρ) at hx
      let q := lpsOriginalCuspNeighborhoodChart N ρ ⟨y,hx⟩
      have hz : q.val≠0 := q.property.1
      have hn := q.property.2
      rw [lpsOriginalFilledCuspToFun,dif_pos hx]
      change lpsOriginalFilledCuspInvFun N ρ q.val=Sum.inl y
      rw [lpsOriginalFilledCuspInvFun,dif_neg hz,dif_pos hn]
      exact congrArg (fun z => Sum.inl z.val)
        ((lpsOriginalCuspNeighborhoodChart N ρ).symm_apply_apply ⟨y,hx⟩)
    | inr c =>
      change c=lpsOriginalCuspOrbit N ρ at hx
      subst c
      simp [lpsOriginalFilledCuspToFun,lpsOriginalFilledCuspInvFun]
  right_inv' := by
    intro q hq
    change ‖q‖<_ at hq
    by_cases hz : q=0
    · subst q
      simp [lpsOriginalFilledCuspInvFun,lpsOriginalFilledCuspToFun]
    · let y := (lpsOriginalCuspNeighborhoodChart N ρ).symm ⟨q,hz,hq⟩
      rw [lpsOriginalFilledCuspInvFun,dif_neg hz,dif_pos hq]
      change lpsOriginalFilledCuspToFun N ρ (Sum.inl y.val)=q
      rw [lpsOriginalFilledCuspToFun,dif_pos y.property]
      exact congrArg Subtype.val
        ((lpsOriginalCuspNeighborhoodChart N ρ).apply_symm_apply ⟨q,hz,hq⟩)

/-- The genuine added cusp maps to zero. -/
lemma lpsOriginalFilledCuspPartialEquiv_cusp (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    lpsOriginalFilledCuspPartialEquiv N ρ (Sum.inr (lpsOriginalCuspOrbit N ρ))=0 := rfl

/-- The genuine added cusp belongs to its true filled chart source. -/
lemma lpsOriginalFilledCuspPartialEquiv_cusp_mem (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Sum.inr (lpsOriginalCuspOrbit N ρ)∈(lpsOriginalFilledCuspPartialEquiv N ρ).source := rfl

/-- The actual filled coordinate target is an open full disc. -/
lemma lpsOriginalFilledCuspPartialEquiv_target_open (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    IsOpen (lpsOriginalFilledCuspPartialEquiv N ρ).target :=
  isOpen_lt continuous_norm continuous_const

/-- The actual filled disc contains zero. -/
lemma lpsOriginalFilledCuspPartialEquiv_target_zero (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    (0:ℂ)∈(lpsOriginalFilledCuspPartialEquiv N ρ).target := by
  change ‖(0:ℂ)‖<_
  simpa only [norm_zero] using Real.exp_pos
    (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty)

/-- The filled coordinate still computes the SAME actual original minimal-width q parameter. -/
lemma lpsOriginalFilledCuspPartialEquiv_projection (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (τ : {τ : ℍ // 1<τ.im}) :
    lpsOriginalFilledCuspPartialEquiv N ρ (Sum.inl (lpsOriginalCuspProjection N ρ τ))=
      Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ.val := by
  have h : lpsOriginalCuspProjection N ρ τ∈Set.range (lpsOriginalCuspProjection N ρ) :=
    ⟨τ,rfl⟩
  change lpsOriginalFilledCuspToFun N ρ (Sum.inl (lpsOriginalCuspProjection N ρ τ))=_
  rw [lpsOriginalFilledCuspToFun,dif_pos h]
  exact congrArg Subtype.val (lpsOriginalCuspNeighborhoodChart_projection N ρ τ)

/-- On the actual source, zero is precisely the correct genuine cusp point. -/
lemma lpsOriginalFilledCuspPartialEquiv_zero_iff (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (x : LPSOriginalFilledCurve N) (hx : x∈(lpsOriginalFilledCuspPartialEquiv N ρ).source) :
    lpsOriginalFilledCuspPartialEquiv N ρ x=0 ↔ x=Sum.inr (lpsOriginalCuspOrbit N ρ) := by
  constructor
  · intro h
    have hi := (lpsOriginalFilledCuspPartialEquiv N ρ).left_inv hx
    rw [h] at hi
    simpa [lpsOriginalFilledCuspPartialEquiv,lpsOriginalFilledCuspInvFun] using hi.symm
  · rintro rfl
    rfl

/-- Every actual cusp point has a true filled-disc partial equivalence. -/
lemma lpsOriginalFilledCuspPartialEquiv_cover_cusps (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    ∃ ρ : SL(2,ℤ), Sum.inr c∈(lpsOriginalFilledCuspPartialEquiv N ρ).source := by
  obtain ⟨ρ,rfl⟩ := lpsOriginalCuspOrbit_surjective N c
  exact ⟨ρ,rfl⟩

/-- Different true cusp labels have disjoint filled chart sources. -/
lemma lpsOriginalFilledCuspPartialEquiv_sources_disjoint (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (h : lpsOriginalCuspOrbit N ρ≠lpsOriginalCuspOrbit N ρ') :
    Disjoint (lpsOriginalFilledCuspPartialEquiv N ρ).source
      (lpsOriginalFilledCuspPartialEquiv N ρ').source := by
  apply Set.disjoint_left.mpr
  intro x hρ hρ'
  cases x with
  | inl y =>
    exact Set.disjoint_left.mp (lpsOriginalCuspNeighborhood_disjoint N ρ ρ' h) hρ hρ'
  | inr c =>
    exact h (hρ.symm.trans hρ')

/-- The selected genuine cusp-chart image of its actual height-two closed disc. -/
def lpsOriginalFilledCuspClosedPatch (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Set (LPSOriginalFilledCurve N) :=
  lpsOriginalFilledCuspInvFun N (lpsOriginalCuspRepresentative N c) ''
    Metric.closedBall (0:ℂ) (Real.exp
      (-2*Real.pi*2/(lpsOriginalCuspGroup N (lpsOriginalCuspRepresentative N c)).strictWidthInfty))

/-- The genuine closed disc is strictly inside the actual filled chart target. -/
lemma lpsOriginalFilledCuspClosedPatch_disc_inside (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Metric.closedBall (0:ℂ) (Real.exp
      (-2*Real.pi*2/(lpsOriginalCuspGroup N (lpsOriginalCuspRepresentative N c)).strictWidthInfty))⊆
        (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target := by
  intro q hq
  rw [mem_closedBall_zero_iff] at hq
  change ‖q‖<_
  apply hq.trans_lt
  apply Real.exp_lt_exp.mpr
  have hw := lpsOriginalCuspGroup_width_positive N (lpsOriginalCuspRepresentative N c)
  apply (div_lt_div_iff_of_pos_right hw).mpr
  nlinarith [Real.pi_pos]

/-- Each closed patch contains its correct genuine added cusp. -/
lemma lpsOriginalFilledCuspClosedPatch_cusp (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Sum.inr c∈lpsOriginalFilledCuspClosedPatch N c := by
  refine ⟨0,?_,?_⟩
  · rw [mem_closedBall_zero_iff,norm_zero]
    exact (Real.exp_pos _).le
  · simp [lpsOriginalFilledCuspInvFun,lpsOriginalCuspRepresentative_orbit]

/-- Every original height-two tail point lies in the selected true closed cusp patch. -/
lemma lpsOriginalFilledCuspClosedPatch_high_projection (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (σ : {τ : ℍ // 1<τ.im}) (hs : 2≤σ.val.im) :
    Sum.inl (lpsOriginalCuspProjection N ρ σ)∈
      lpsOriginalFilledCuspClosedPatch N (lpsOriginalCuspOrbit N ρ) := by
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  obtain ⟨τ,ht,he⟩ := lpsOriginalCuspNeighborhood_change_point N r ρ
    (lpsOriginalCuspRepresentative_orbit N c) σ
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  let q := Function.Periodic.qParam w τ.val
  have hw : 0<w := lpsOriginalCuspGroup_width_positive N r
  have hq : q∈Metric.closedBall (0:ℂ) (Real.exp (-2*Real.pi*2/w)) := by
    rw [mem_closedBall_zero_iff]
    change ‖Function.Periodic.qParam w τ.val‖≤_
    rw [Function.Periodic.norm_qParam,UpperHalfPlane.coe_im,ht]
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right hw).mpr
    nlinarith [Real.pi_pos]
  refine ⟨q,hq,?_⟩
  have hp : Sum.inl (lpsOriginalCuspProjection N r τ)∈
      (lpsOriginalFilledCuspPartialEquiv N r).source := ⟨τ,rfl⟩
  have hi := (lpsOriginalFilledCuspPartialEquiv N r).left_inv hp
  rw [lpsOriginalFilledCuspPartialEquiv_projection,he] at hi
  exact hi

/-- The actual compact core and finitely many true closed cusp patches cover the ENTIRE filled set. -/
lemma lpsOriginalFilledCurve_finite_cover (N : ℕ) [NeZero N] :
    (Sum.inl '' lpsOriginalGamma0CompactCore N 2) ∪
      (⋃ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
        lpsOriginalFilledCuspClosedPatch N c)=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  cases x with
  | inl y =>
    obtain ⟨τ,rfl⟩ := Quotient.exists_rep y
    obtain ⟨c,z,hz,he⟩ := lpsOriginalGamma0Projected_fundamentalDomain_cover N τ
    by_cases h : z.im≤2
    · left
      refine ⟨⟦τ⟧,?_,rfl⟩
      rw [←he]
      exact Set.mem_iUnion.mpr ⟨c,z,⟨hz,h⟩,rfl⟩
    · right
      have hh : 1<z.im := by linarith
      have hi := lpsOriginalFilledCuspClosedPatch_high_projection N
        (lpsOriginalGamma0CosetRepresentative N c) ⟨z,hh⟩ (le_of_lt (lt_of_not_ge h))
      change Sum.inl (lpsOriginalGamma0Projected N
        (lpsOriginalGamma0CosetRepresentative N c) z)∈_ at hi
      rw [he] at hi
      exact Set.mem_iUnion.mpr ⟨_,hi⟩
  | inr c =>
    exact Or.inr (Set.mem_iUnion.mpr ⟨c,lpsOriginalFilledCuspClosedPatch_cusp N c⟩)

/-- Parametrize a true original filled cusp neighborhood by its actual full disc. -/
def lpsOriginalFilledCuspParam (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target →
      LPSOriginalFilledCurve N :=
  fun q => lpsOriginalFilledCuspInvFun N (lpsOriginalCuspRepresentative N c) q.val

/-- The actual inclusion of the genuine punctured coordinate disc into its full disc. -/
def lpsOriginalCuspPunctToFull (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    lpsOriginalCuspDisk N ρ → (lpsOriginalFilledCuspPartialEquiv N ρ).target :=
  fun q => ⟨q.val,q.property.2⟩

/-- The actual punctured-to-full disc inclusion is continuous. -/
lemma lpsOriginalCuspPunctToFull_continuous (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Continuous (lpsOriginalCuspPunctToFull N ρ) :=
  continuous_subtype_val.subtype_mk _

/-- The actual punctured-to-full disc inclusion is open. -/
lemma lpsOriginalCuspPunctToFull_open (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    IsOpenMap (lpsOriginalCuspPunctToFull N ρ) := by
  have hd := lpsOriginalFilledCuspPartialEquiv_target_open N ρ
  have hp : IsOpen (lpsOriginalCuspDisk N ρ) :=
    (isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_lt continuous_norm continuous_const)
  exact hd.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr hp.isOpenMap_subtype_val

/-- The genuine inverse punctured coordinate with values in the ORIGINAL quotient. -/
def lpsOriginalCuspPunctInverse (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    lpsOriginalCuspDisk N ρ → MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
  fun q => ((lpsOriginalCuspNeighborhoodChart N ρ).symm q).val

/-- The true inverse punctured coordinate is continuous in the ORIGINAL quotient. -/
lemma lpsOriginalCuspPunctInverse_continuous (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Continuous (lpsOriginalCuspPunctInverse N ρ) :=
  continuous_subtype_val.comp (lpsOriginalCuspNeighborhoodChart N ρ).symm.continuous

/-- The true inverse punctured coordinate is open in the ORIGINAL quotient. -/
lemma lpsOriginalCuspPunctInverse_open (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    IsOpenMap (lpsOriginalCuspPunctInverse N ρ) :=
  (lpsOriginalCuspProjection_openRange N ρ).isOpenMap_subtype_val.comp
    (lpsOriginalCuspNeighborhoodChart N ρ).symm.isOpenMap

/-- Away from zero the filled parametrization is the actual original inverse punctured coordinate. -/
lemma lpsOriginalFilledCuspParam_punct (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : lpsOriginalCuspDisk N (lpsOriginalCuspRepresentative N c)) :
    lpsOriginalFilledCuspParam N c
      (lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) q)=
        Sum.inl (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q) := by
  change lpsOriginalFilledCuspInvFun N (lpsOriginalCuspRepresentative N c) q.val=_
  rw [lpsOriginalFilledCuspInvFun,dif_neg q.property.1,dif_pos q.property.2]
  rfl

/-- Zero parametrizes exactly the corresponding genuine cusp orbit. -/
lemma lpsOriginalFilledCuspParam_zero (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq : q.val=0) : lpsOriginalFilledCuspParam N c q=Sum.inr c := by
  simp [lpsOriginalFilledCuspParam,lpsOriginalFilledCuspInvFun,hq,lpsOriginalCuspRepresentative_orbit]

/-- The genuine filled-disc parametrization is injective by the proved inverse laws. -/
lemma lpsOriginalFilledCuspParam_injective (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Function.Injective (lpsOriginalFilledCuspParam N c) := by
  intro q q' he
  apply Subtype.ext
  exact (lpsOriginalFilledCuspPartialEquiv N
    (lpsOriginalCuspRepresentative N c)).symm.injOn q.property q'.property he

/-- The genuine parametrization takes values in its actual original filled chart source. -/
lemma lpsOriginalFilledCuspParam_mem_source (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target) :
    lpsOriginalFilledCuspParam N c q∈
      (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).source :=
  (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).mapsTo_symm q.property

/-- Original preimages of a genuine filled-disc image are computed by the true punctured inverse. -/
lemma lpsOriginalFilledCuspParam_original_preimage (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (s : Set ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)) :
    (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) ⁻¹'
      (lpsOriginalFilledCuspParam N c '' s)=
        lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) ''
          (lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) ⁻¹' s) := by
  ext x
  constructor
  · rintro ⟨q,hq,he⟩
    by_cases hz : q.val=0
    · rw [lpsOriginalFilledCuspParam_zero N c q hz] at he
      cases he
    · let q' : lpsOriginalCuspDisk N (lpsOriginalCuspRepresentative N c) := ⟨q.val,hz,q.property⟩
      have hp : lpsOriginalFilledCuspParam N c q=
          Sum.inl (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q') :=
        lpsOriginalFilledCuspParam_punct N c q'
      rw [hp] at he
      exact ⟨q',hq,Sum.inl.inj he⟩
  · rintro ⟨q,hq,he⟩
    refine ⟨lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) q,hq,?_⟩
    rw [lpsOriginalFilledCuspParam_punct,he]

/-- The filled parametrization of a different actual cusp misses the given cusp-chart image. -/
lemma lpsOriginalFilledCuspParam_other_preimage (N : ℕ) [NeZero N]
    (c d : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (hd : d≠c)
    (s : Set ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)) :
    lpsOriginalFilledCuspParam N d ⁻¹' (lpsOriginalFilledCuspParam N c '' s)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro q ⟨q',hq',he⟩
  have hs := lpsOriginalFilledCuspPartialEquiv_sources_disjoint N
    (lpsOriginalCuspRepresentative N d) (lpsOriginalCuspRepresentative N c) (by
      simpa only [lpsOriginalCuspRepresentative_orbit] using hd)
  have hc := lpsOriginalFilledCuspParam_mem_source N c q'
  rw [he] at hc
  exact Set.disjoint_left.mp hs (lpsOriginalFilledCuspParam_mem_source N d q) hc

/-- True disc preimages of original interior images are exactly the punctured inverse preimages. -/
lemma lpsOriginalFilledCuspParam_interior_preimage (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (s : Set (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) :
    lpsOriginalFilledCuspParam N c ⁻¹' (Sum.inl '' s)=
      lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) ''
        (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) ⁻¹' s) := by
  ext q
  constructor
  · rintro ⟨x,hx,he⟩
    by_cases hz : q.val=0
    · rw [lpsOriginalFilledCuspParam_zero N c q hz] at he
      cases he
    · let q' : lpsOriginalCuspDisk N (lpsOriginalCuspRepresentative N c) := ⟨q.val,hz,q.property⟩
      have hp : lpsOriginalFilledCuspParam N c q=
          Sum.inl (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q') :=
        lpsOriginalFilledCuspParam_punct N c q'
      rw [hp] at he
      refine ⟨q',?_,Subtype.ext rfl⟩
      change lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q'∈s
      rw [←Sum.inl.inj he]
      exact hx
  · rintro ⟨q',hq',rfl⟩
    exact ⟨lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q',hq',
      (lpsOriginalFilledCuspParam_punct N c q').symm⟩

/-- The actual filled-disc parametrization has exactly the true filled chart source as its range. -/
lemma lpsOriginalFilledCuspParam_range (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Set.range (lpsOriginalFilledCuspParam N c)=
      (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).source := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    exact lpsOriginalFilledCuspParam_mem_source N c q
  · intro hx
    let e := lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)
    refine ⟨⟨e x,e.map_source hx⟩,?_⟩
    exact e.left_inv hx

/-- Every nonzero true filled coordinate lifts to an actual high original projection with its q formula. -/
lemma lpsOriginalFilledCuspParam_nonzero_lift (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz : q.val≠0) :
    ∃ τ : {τ : ℍ // 1<τ.im},
      lpsOriginalFilledCuspParam N c q=
        Sum.inl (lpsOriginalCuspProjection N (lpsOriginalCuspRepresentative N c) τ) ∧
      q.val=Function.Periodic.qParam
        (lpsOriginalCuspGroup N (lpsOriginalCuspRepresentative N c)).strictWidthInfty τ.val := by
  let r := lpsOriginalCuspRepresentative N c
  let q' : lpsOriginalCuspDisk N r := ⟨q.val,hz,q.property⟩
  obtain ⟨τ,he⟩ := ((lpsOriginalCuspNeighborhoodChart N r).symm q').property
  have hf : lpsOriginalCuspCoordinate N r τ=q' := by
    rw [←lpsOriginalCuspNeighborhoodChart_projection]
    have hsub : (⟨lpsOriginalCuspProjection N r τ,⟨τ,rfl⟩⟩ :
        Set.range (lpsOriginalCuspProjection N r))=(lpsOriginalCuspNeighborhoodChart N r).symm q' :=
      Subtype.ext he
    rw [hsub]
    exact (lpsOriginalCuspNeighborhoodChart N r).apply_symm_apply q'
  refine ⟨τ,?_,(congrArg Subtype.val hf).symm⟩
  have hp := lpsOriginalFilledCuspParam_punct N c q'
  change lpsOriginalFilledCuspParam N c q=Sum.inl
    (((lpsOriginalCuspNeighborhoodChart N r).symm q').val) at hp
  rw [←he] at hp
  exact hp

end
end QEC.Coding.TannerLiftedProduct
