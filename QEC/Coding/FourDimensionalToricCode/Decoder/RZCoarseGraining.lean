import QEC.Coding.FourDimensionalToricCode.Decoder.Multiscale

/-!
# The `R_Z` coarse-graining step

This module is the source-backed M12 slice for an even input level.  The
finite graph and support records are deliberately only the local ingredients
of the construction.  The correction is a canonical (classical-choice)
function of the input syndrome; the coboundary relation, locality, and weight
bound below are proved from those ingredients rather than stored as fields.
-/

namespace QEC
namespace Coding
namespace MultiscaleDecoder
namespace RZCoarseGraining

open scoped BigOperators

universe u v

abbrev Field := BDL26Field

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]

/-- The fixed middle-cochain projection supplied by the audited RZ induced
map contract (F09).  This is an input API for the induced map, not an
arbitrary correction oracle. -/
structure RZInducedMaps
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) where
  correctionProjection :
    D.family.Cochain1 i.succ →ₗ[Field] D.family.Cochain1 i.castSucc

/-! A finite region record for one RZ replacement. -/
structure RZCoarseGrainingData
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    (V : Type v) [Fintype V] [DecidableEq V] where
  levelGraph : LevelGraph V
  center : C2 i.castSucc → V
  topCenter : C2 i.succ → V
  /-- Optional owner of a correction coordinate.  `none` marks a connector
  coordinate used by the induced map but not owned by any local region. -/
  correctionOwner : C1 i.succ → Option V
  coarseRegion : C2 i.castSucc → Finset (C2 i.succ)
  correctionInputRegion : C2 i.castSucc → Finset (C2 i.succ)
  correctionRegion : C2 i.castSucc → Finset (C1 i.succ)
  lift : C2 i.castSucc → Field → D.family.Cochain2 i.succ
  induced : RZInducedMaps D i
  coarseRegion_cover : ∀ p : C2 i.succ, ∃ z, p ∈ coarseRegion z
  coarseRegion_disjoint :
    ∀ z z', z ≠ z' → Disjoint (coarseRegion z) (coarseRegion z')
  correctionInputRegion_subset :
    ∀ z, coarseRegion z ⊆ correctionInputRegion z
  correctionRegion_disjoint :
    ∀ z z', z ≠ z' → Disjoint (correctionRegion z) (correctionRegion z')
  correctionRegion_coherence :
    ∀ z, correctionRegion z =
      Finset.univ.filter (fun q => correctionOwner q = some (center z))
  lift_supported :
    ∀ z b p, p ∉ coarseRegion z → lift z b p = 0
  lift_parity :
    ∀ z b, (∑ p ∈ coarseRegion z, lift z b p) = b
  induced_syndrome_decomposition :
    ∀ sigma : D.family.Cochain2 i.castSucc,
      (D.rzMap i).map2 sigma =
        ∑ z, lift z (sigma z)
  local_boundary_supported :
    ∀ z (f : D.family.Cochain1 i.succ),
      (∀ q, q ∉ correctionRegion z → f q = 0) →
        ∀ p, p ∉ coarseRegion z →
          D.family.coboundary1 i.succ f p = 0
  topRegion_radius_two :
    ∀ z p, p ∈ coarseRegion z →
      DirectedGraph.distance levelGraph.graph (topCenter p) (center z) ≤ 2
  correctionInput_radius_one :
    ∀ z p, p ∈ correctionInputRegion z →
      DirectedGraph.distance levelGraph.graph (topCenter p) (center z) ≤ 1

namespace RZCoarseGrainingData

variable (A : RZCoarseGrainingData D i V)

/-- The local parity projection from input top cochains to coarse syndrome
coordinates. -/
noncomputable def topParity
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.castSucc :=
  fun z => ∑ p ∈ A.coarseRegion z, sigma p

@[simp]
theorem topParity_apply
    (sigma : D.family.Cochain2 i.succ) (z : C2 i.castSucc) :
    A.topParity sigma z = ∑ p ∈ A.coarseRegion z, sigma p :=
  rfl

/-- Words supported on a finite coordinate region. -/
noncomputable def supportedSubmodule
    {α : Type u} [Fintype α] [DecidableEq α] (S : Finset α) :
    Submodule Field (Word Field α) where
  carrier := {f | ∀ a, a ∉ S → f a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a ha
    simp [hf a ha, hg a ha]
  smul_mem' := by
    intro c f hf a ha
    simp [hf a ha]

noncomputable def localCorrectionSpace
    (z : C2 i.castSucc) :
    Submodule Field (D.family.Cochain1 i.succ) :=
  supportedSubmodule (A.correctionRegion z)

noncomputable def localTopSpace
    (z : C2 i.castSucc) :
    Submodule Field (D.family.Cochain2 i.succ) :=
  supportedSubmodule (A.coarseRegion z)

noncomputable def localBoundaryMap
    (z : C2 i.castSucc) :
    localCorrectionSpace A z →ₗ[Field] localTopSpace A z where
  toFun f :=
    ⟨D.family.coboundary1 i.succ f.1,
      A.local_boundary_supported z f.1 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' c f := by
    apply Subtype.ext
    simp

noncomputable def localBoundaryRange
    (z : C2 i.castSucc) :
    Submodule Field (localTopSpace A z) :=
  LinearMap.range (localBoundaryMap A z)

abbrev localTopQuotient
    (A : RZCoarseGrainingData D i V) (z : C2 i.castSucc) :=
    (localTopSpace A z) ⧸ localBoundaryRange A z

end RZCoarseGrainingData

open RZCoarseGrainingData

/-- Disjoint supported lifts recover their input by taking each region's parity. -/
theorem topParity_rzMap_map2
    (A : RZCoarseGrainingData D i V) (w : D.family.Cochain2 i.castSucc) :
    topParity A ((D.rzMap i).map2 w) = w := by
  classical
  funext z
  rw [A.induced_syndrome_decomposition]
  simp only [topParity, Finset.sum_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single z]
  · exact A.lift_parity z (w z)
  · intro other _ hne
    apply Finset.sum_eq_zero
    intro p hp
    apply A.lift_supported other (w other) p
    intro ho
    exact Finset.disjoint_left.mp (A.coarseRegion_disjoint other z hne) ho hp
  · simp

/-- Degree-two injectivity is derived from the parity left inverse. -/
theorem rzMap_map2_injective (A : RZCoarseGrainingData D i V) :
    Function.Injective (D.rzMap i).map2 := by
  intro a b h
  have hp := congrArg (topParity A) h
  simpa only [topParity_rzMap_map2] using hp

/-! The two named local contract slices from the audited construction. -/

/-- F07: the top local cohomology quotient has one parity coordinate.  The
quotient is taken only after restricting top words to the coarse region. -/
def LocalTopCohomologyIdentification
    (A : RZCoarseGrainingData D i V) : Prop :=
  ∀ z, ∃ e : localTopQuotient A z ≃ₗ[Field] Field,
    ∀ r, e ((localBoundaryRange A z).mkQ r) =
      (∑ p ∈ A.coarseRegion z, (r : D.family.Cochain2 i.succ) p)

/-- Construct the local top-cohomology identification from a parity map.

The equality of the local boundary range with the parity kernel is the only
quotient bookkeeping obligation left to a concrete RZ fixture.  Once that
equality and surjectivity are proved, Mathlib's first-isomorphism theorem
provides the required quotient equivalence.  The final hypothesis records the
coordinate formula for the parity map and keeps the source-facing statement
explicit rather than relying on reducibility of a fixture definition.
-/
theorem localTopCohomologyIdentification_of_parity
    (A : RZCoarseGrainingData D i V)
    (parity : ∀ z : C2 i.castSucc, localTopSpace A z →ₗ[Field] Field)
    (hker : ∀ z, localBoundaryRange A z = LinearMap.ker (parity z))
    (hsurj : ∀ z, Function.Surjective (parity z))
    (hformula : ∀ z r,
      parity z r =
        (∑ p ∈ A.coarseRegion z,
          (r : D.family.Cochain2 i.succ) p)) :
    LocalTopCohomologyIdentification A := by
  intro z
  let e : localTopQuotient A z ≃ₗ[Field] Field :=
    (Submodule.quotEquivOfEq _ _ (hker z)).trans
      ((parity z).quotKerEquivOfSurjective (hsurj z))
  refine ⟨e, ?_⟩
  intro r
  simpa [e] using hformula z r

/-- F09: the fixed induced middle map carries the upper coboundary to the
coarse parity coboundary. -/
def InducedCoboundaryCompatibility
    (A : RZCoarseGrainingData D i V) : Prop :=
  ∀ e : D.family.Cochain1 i.succ,
    topParity A (D.family.coboundary1 i.succ e) =
      D.family.coboundary1 i.castSucc (A.induced.correctionProjection e)

theorem selectedMap_eq_rz_of_even_input
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    (hEven : i.succ.val % 2 = 0) :
    D.selectedMap i = D.rzMap i := by
  change (i.val + 1) % 2 = 0 at hEven
  have hi : i.val % 2 = 1 := by omega
  simp [BDL26DecoderData.selectedMap, replacementKind, hi]

/-- The actual selected degree-two map is injective at an even RZ input. -/
theorem selectedMap_map2_injective (A : RZCoarseGrainingData D i V)
    (hEven : i.succ.val % 2 = 0) : Function.Injective (D.selectedMap i).map2 := by
  rw [selectedMap_eq_rz_of_even_input D i hEven]
  exact rzMap_map2_injective A

theorem localCorrection_exists
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (r : D.family.Cochain2 i.succ)
    (hsupport : ∀ p, p ∉ A.coarseRegion z → r p = 0)
    (hparity : ∑ p ∈ A.coarseRegion z, r p = 0) :
    ∃ f : D.family.Cochain1 i.succ,
      (∀ q, q ∉ A.correctionRegion z → f q = 0) ∧
        (∀ p, D.family.coboundary1 i.succ f p = r p) := by
  classical
  let rLocal : localTopSpace A z := ⟨r, hsupport⟩
  obtain ⟨e, he⟩ := hcoh z
  have hq : (localBoundaryRange A z).mkQ rLocal = 0 := by
    apply e.injective
    rw [he]
    simpa [rLocal, hparity]
  have hmem : rLocal ∈ localBoundaryRange A z := by
    exact (Submodule.Quotient.mk_eq_zero (p := localBoundaryRange A z)
      (x := rLocal)).mp hq
  rcases hmem with ⟨fLocal, hfLocal⟩
  refine ⟨fLocal.1, fLocal.2, ?_⟩
  have hEq : (localBoundaryMap A z fLocal).1 = r := by
    exact congrArg Subtype.val hfLocal
  exact fun p => congrFun hEq p

noncomputable def localResidual
    (A : RZCoarseGrainingData D i V)
  (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.succ :=
  maskWord (A.coarseRegion z) sigma + A.lift z (topParity A sigma z)

theorem localResidual_supported
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) :
    ∀ p, p ∉ A.coarseRegion z → localResidual A z sigma p = 0 := by
  intro p hp
  change (if p ∈ A.coarseRegion z then sigma p else 0) +
      A.lift z (topParity A sigma z) p = 0
  rw [if_neg hp, A.lift_supported z (topParity A sigma z) p hp, add_zero]

theorem localResidual_parity_zero
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) :
    ∑ p ∈ A.coarseRegion z, localResidual A z sigma p = 0 := by
  classical
  simp_rw [localResidual, Pi.add_apply]
  rw [Finset.sum_add_distrib]
  have hmask :
      (∑ p ∈ A.coarseRegion z, maskWord (A.coarseRegion z) sigma p) =
        topParity A sigma z := by
    simp [topParity, maskWord]
  rw [hmask, A.lift_parity]
  exact CharTwo.add_self_eq_zero _

theorem localCorrection_exists_of_syndrome
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) :
    ∃ f : D.family.Cochain1 i.succ,
      (∀ q, q ∉ A.correctionRegion z → f q = 0) ∧
        (∀ p, D.family.coboundary1 i.succ f p = localResidual A z sigma p) := by
  exact localCorrection_exists A hcoh z (localResidual A z sigma)
    (localResidual_supported A z sigma) (localResidual_parity_zero A z sigma)

noncomputable def localCorrectionSelector
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc)
    (r : D.family.Cochain2 i.succ) : D.family.Cochain1 i.succ :=
  if h : ∃ f : D.family.Cochain1 i.succ,
      (∀ q, q ∉ A.correctionRegion z → f q = 0) ∧
        (∀ p, D.family.coboundary1 i.succ f p = r p) then
    Classical.choose h
  else 0

noncomputable def localCorrectionComponent
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain1 i.succ :=
  localCorrectionSelector A z (localResidual A z sigma)

theorem localCorrectionComponent_supported
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) :
    ∀ q, q ∉ A.correctionRegion z → localCorrectionComponent A hcoh z sigma q = 0 := by
  have hex := localCorrection_exists_of_syndrome A hcoh z sigma
  unfold localCorrectionComponent localCorrectionSelector
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1

theorem localCorrectionComponent_boundary
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) :
    ∀ p, D.family.coboundary1 i.succ (localCorrectionComponent A hcoh z sigma) p =
      localResidual A z sigma p := by
  have hex := localCorrection_exists_of_syndrome A hcoh z sigma
  unfold localCorrectionComponent localCorrectionSelector
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

noncomputable def correctionFromSyndrome
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain1 i.succ :=
  ∑ z, localCorrectionComponent A hcoh z sigma

abbrev UpperSyndrome (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :=
  D.family.Syndrome i.succ

abbrev CoarseSyndrome (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :=
  D.family.Syndrome i.castSucc

theorem topParity_mem_range
    (A : RZCoarseGrainingData D i V)
    (hcompat : InducedCoboundaryCompatibility A)
    (sigma : UpperSyndrome D i) :
    topParity A sigma.1 ∈ LinearMap.range (D.family.coboundary1 i.castSucc) := by
  rcases sigma.property with ⟨e, he⟩
  refine ⟨A.induced.correctionProjection e, ?_⟩
  have hc := hcompat e
  rw [he] at hc
  exact hc.symm

noncomputable def coarseSyndrome
    (A : RZCoarseGrainingData D i V)
    (hcompat : InducedCoboundaryCompatibility A)
    (sigma : UpperSyndrome D i) : CoarseSyndrome D i :=
  ⟨topParity A sigma.1, topParity_mem_range A hcompat sigma⟩

@[simp]
theorem coarseSyndrome_coe
    (A : RZCoarseGrainingData D i V)
    (hcompat : InducedCoboundaryCompatibility A)
    (sigma : UpperSyndrome D i) :
    (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) =
      topParity A sigma.1 :=
  rfl

theorem sum_mask_regions
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ) :
    (∑ z, maskWord (A.coarseRegion z) sigma) = sigma := by
  classical
  funext p
  simp only [Finset.sum_apply]
  change (∑ z : C2 i.castSucc, maskWord (A.coarseRegion z) sigma p) = sigma p
  obtain ⟨z, hz⟩ := A.coarseRegion_cover p
  rw [Finset.sum_eq_single z]
  · simp [maskWord, hz]
  · intro z' hz' hne
    have hdisj := Finset.disjoint_left.1 (A.coarseRegion_disjoint z' z hne)
    have hpnot : p ∉ A.coarseRegion z' := by
      intro hp'
      exact hdisj hp' hz
    simp [maskWord, hpnot]
  · simp

theorem sum_localResidual
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ) :
    (∑ z, localResidual A z sigma) =
      sigma + (D.rzMap i).map2 (topParity A sigma) := by
  classical
  calc
    (∑ z, localResidual A z sigma) =
        (∑ z, maskWord (A.coarseRegion z) sigma) +
          (∑ z, A.lift z (topParity A sigma z)) := by
      simp_rw [localResidual]
      rw [Finset.sum_add_distrib]
    _ = sigma + (D.rzMap i).map2 (topParity A sigma) := by
      rw [sum_mask_regions A sigma]
      rw [← A.induced_syndrome_decomposition (topParity A sigma)]

theorem correction_boundary_eq_sumResidual
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (sigma : D.family.Cochain2 i.succ) :
    D.family.coboundary1 i.succ (correctionFromSyndrome A hcoh sigma) =
      ∑ z, localResidual A z sigma := by
  classical
  change D.family.coboundary1 i.succ
      (∑ z, localCorrectionComponent A hcoh z sigma) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  funext p
  exact localCorrectionComponent_boundary A hcoh z sigma p

theorem rz_exact_relation
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : UpperSyndrome D i) :
    (sigma : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ (correctionFromSyndrome A hcoh sigma.1) +
        (D.selectedMap i).map2 (coarseSyndrome A hcompat sigma) := by
  have hselected := selectedMap_eq_rz_of_even_input D i hEven
  have hboundary := correction_boundary_eq_sumResidual A hcoh sigma.1
  have hsum := sum_localResidual A sigma.1
  rw [hselected, coarseSyndrome_coe]
  rw [hboundary, hsum]
  ext p
  simp only [LinearMap.add_apply, Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero]
  simp

noncomputable def activeRegion
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) : Finset (C2 i.succ) :=
  (A.coarseRegion z).filter (fun p => sigma p ≠ 0)

theorem activeRegion_pairwiseDisjoint
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (C2 i.castSucc)))
      (activeRegion A sigma) := by
  intro z hz z' hz' hne
  change Disjoint (activeRegion A sigma z) (activeRegion A sigma z')
  rw [Finset.disjoint_left]
  intro p hp hp'
  exact Finset.disjoint_left.1 (A.coarseRegion_disjoint z z' hne)
    (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp').1

theorem activeRegion_biUnion_eq_support
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ) :
    (Finset.univ : Finset (C2 i.castSucc)).biUnion (activeRegion A sigma) =
      hammingSupport sigma := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_biUnion.1 hp with ⟨z, hz, hpz⟩
    simpa [hammingSupport] using (Finset.mem_filter.1 hpz).2
  · intro hp
    obtain ⟨z, hz⟩ := A.coarseRegion_cover p
    exact Finset.mem_biUnion.2 ⟨z, Finset.mem_univ _,
      Finset.mem_filter.2 ⟨hz, by simpa [hammingSupport] using hp⟩⟩

theorem coarse_weight_le_input
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ) :
    HammingWeight (topParity A sigma) ≤ HammingWeight sigma := by
  classical
  let supportCoarse := hammingSupport (topParity A sigma)
  let active := activeRegion A sigma
  have hpair : (supportCoarse : Set (C2 i.castSucc)).PairwiseDisjoint active := by
    intro z hz z' hz' hne
    exact (activeRegion_pairwiseDisjoint A sigma)
      (Finset.mem_univ z) (Finset.mem_univ z') hne
  have hnonempty : ∀ z ∈ supportCoarse, (active z).Nonempty := by
    intro z hz
    by_contra hne
    have hempty : active z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero : ∀ p ∈ A.coarseRegion z, sigma p = 0 := by
      intro p hp
      by_contra hp0
      have hpa : p ∈ active z := Finset.mem_filter.2 ⟨hp, hp0⟩
      rw [hempty] at hpa
      simpa using hpa
    have hz0 : topParity A sigma z = 0 := by
      simp only [topParity]
      apply Finset.sum_eq_zero
      intro p hp
      exact hzero p hp
    have hznot : z ∉ hammingSupport (topParity A sigma) := by
      have hnezero : ¬(topParity A sigma z ≠ 0) := fun h => h hz0
      simpa only [hammingSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] using hnezero
    exact hznot hz
  have hcoarse :
      supportCoarse.card ≤ (supportCoarse.biUnion active).card := by
    exact Finset.card_le_card_biUnion hpair hnonempty
  have hsubset : supportCoarse.biUnion active ⊆
      (Finset.univ : Finset (C2 i.castSucc)).biUnion active := by
    exact Finset.biUnion_subset_biUnion_of_subset_left active
      (Finset.subset_univ _)
  calc
    HammingWeight (topParity A sigma) = supportCoarse.card := by
      rfl
    _ ≤ (supportCoarse.biUnion active).card := hcoarse
    _ ≤ ((Finset.univ : Finset (C2 i.castSucc)).biUnion active).card :=
      Finset.card_le_card hsubset
    _ = HammingWeight sigma := by
      rw [activeRegion_biUnion_eq_support A sigma]
      rfl

/-- Agreement of two input syndromes on the source-local radius around a
coarse coordinate.  The radius is measured in the directed Tanner graph
derived from the existing level skeleton. -/
def SignalAgreementWithin
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc) (radius : Nat)
    (sigma tau : D.family.Cochain2 i.succ) : Prop :=
  ∀ p, DirectedGraph.distance A.levelGraph.graph (A.topCenter p) (A.center z) ≤ radius →
    sigma p = tau p

/-- The #811 local-complex adapter for the RZ input and correction
coordinates.  Syndrome fibres are indexed by their exact top-centre label;
the correction fibres are the audited F11 correction regions. -/
noncomputable def xiLocalComplex
    (A : RZCoarseGrainingData D i V) :
    LocalComplexData V (C2 i.succ) (C1 i.succ) where
  syndromeRegion := fun v =>
    Finset.univ.filter (fun p => A.topCenter p = v)
  correctionRegion := fun v =>
    Finset.univ.filter (fun q => A.correctionOwner q = some v)

noncomputable def xiSignal
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) (radius : Nat) : D.family.Cochain2 i.succ :=
  xiAggregate A.levelGraph.graph (xiLocalComplex A) sigma (A.center z) radius

theorem xiSignal_apply
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) (radius : Nat) (p : C2 i.succ) :
    xiSignal A sigma z radius p =
      if DirectedGraph.distance A.levelGraph.graph (A.topCenter p) (A.center z) ≤ radius
      then sigma p else 0 := by
  classical
  simp [xiSignal, xiAggregate, xiIndexSet, LocalRegion.directedNeighborhood,
    xiLocalComplex, maskWord]

theorem sigma_agrees_xi_radius_one
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    SignalAgreementWithin A z 1 sigma (xiSignal A sigma z 1) := by
  intro p hp
  rw [xiSignal_apply]
  rw [if_pos hp]

theorem sigma_agrees_xi_radius_two
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    SignalAgreementWithin A z 2 sigma (xiSignal A sigma z 2) := by
  intro p hp
  rw [xiSignal_apply]
  rw [if_pos hp]

theorem coarseParity_invariant_radius_two
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc)
    (sigma tau : D.family.Cochain2 i.succ)
    (hAgree : SignalAgreementWithin A z 2 sigma tau) :
    topParity A sigma z = topParity A tau z := by
  simp only [topParity]
  apply Finset.sum_congr rfl
  intro p hp
  exact hAgree p (A.topRegion_radius_two z p hp)

theorem localResidual_invariant_radius_one
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc)
    (sigma tau : D.family.Cochain2 i.succ)
    (hAgree : SignalAgreementWithin A z 1 sigma tau) :
    localResidual A z sigma = localResidual A z tau := by
  have hTop : topParity A sigma z = topParity A tau z := by
    simp only [topParity]
    apply Finset.sum_congr rfl
    intro p hp
    exact hAgree p (A.correctionInput_radius_one z p
      (A.correctionInputRegion_subset z hp))
  funext p
  by_cases hp : p ∈ A.coarseRegion z
  · simp only [localResidual, maskWord, if_pos hp, Pi.add_apply]
    rw [hAgree p (A.correctionInput_radius_one z p
      (A.correctionInputRegion_subset z hp)), hTop]
  · simp only [localResidual, maskWord, if_neg hp, Pi.add_apply,
      A.lift_supported z (topParity A sigma z) p hp,
      A.lift_supported z (topParity A tau z) p hp, add_zero]

theorem localCorrectionComponent_invariant_radius_one
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (sigma tau : D.family.Cochain2 i.succ)
    (hAgree : SignalAgreementWithin A z 1 sigma tau) :
    localCorrectionComponent A hcoh z sigma =
      localCorrectionComponent A hcoh z tau := by
  have hResidual := localResidual_invariant_radius_one A z sigma tau hAgree
  unfold localCorrectionComponent
  rw [hResidual]

theorem correction_masked_eq_component
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) :
    maskWord (A.correctionRegion z) (correctionFromSyndrome A hcoh sigma) =
      localCorrectionComponent A hcoh z sigma := by
  classical
  funext q
  by_cases hq : q ∈ A.correctionRegion z
  · simp only [maskWord, if_pos hq, correctionFromSyndrome, Finset.sum_apply]
    change (∑ z', localCorrectionComponent A hcoh z' sigma q) =
      localCorrectionComponent A hcoh z sigma q
    rw [Finset.sum_eq_single z]
    · intro z' _ hne
      have hdisj := Finset.disjoint_left.1
        (A.correctionRegion_disjoint z' z hne)
      have hnot : q ∉ A.correctionRegion z' := by
        intro hq'
        exact hdisj hq' hq
      exact localCorrectionComponent_supported A hcoh z' sigma q hnot
    · simp
  · simp [maskWord, hq,
      localCorrectionComponent_supported A hcoh z sigma q hq]

theorem localCorrectionComponent_eq_xi_one
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    localCorrectionComponent A hcoh z sigma =
      localCorrectionComponent A hcoh z (xiSignal A sigma z 1) := by
  exact localCorrectionComponent_invariant_radius_one A hcoh z sigma
    (xiSignal A sigma z 1) (sigma_agrees_xi_radius_one A sigma z)

theorem topParity_eq_xi_two
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    topParity A sigma z = topParity A (xiSignal A sigma z 2) z := by
  exact coarseParity_invariant_radius_two A z sigma
    (xiSignal A sigma z 2) (sigma_agrees_xi_radius_two A sigma z)

/-! A proved terminal bundle for the five source-exact local-computability
claims exposed by the #811 interface.  The fields are conclusions, not
caller-supplied decoder obligations. -/
structure RZLocalComputabilityCertificate
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A) where
  totalCorrectionDecomposition :
    ∀ sigma, correctionFromSyndrome A hcoh sigma =
      ∑ z, localCorrectionComponent A hcoh z sigma
  componentSupported :
    ∀ z sigma q, q ∉ A.correctionRegion z →
      localCorrectionComponent A hcoh z sigma q = 0
  maskedTotalCorrectionEqComponent :
    ∀ z sigma,
      maskWord (A.correctionRegion z) (correctionFromSyndrome A hcoh sigma) =
        localCorrectionComponent A hcoh z sigma
  componentInvariantAtXiOne :
    ∀ sigma z,
      localCorrectionComponent A hcoh z sigma =
        localCorrectionComponent A hcoh z (xiSignal A sigma z 1)
  coarseCoordinateInvariantAtXiTwo :
    ∀ (sigma : UpperSyndrome D i) z,
      (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
        topParity A (xiSignal A sigma.1 z 2) z

theorem localComputabilityCertificate
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A) :
    RZLocalComputabilityCertificate A hcoh hcompat := by
  refine
    { totalCorrectionDecomposition := ?_
      componentSupported := ?_
      maskedTotalCorrectionEqComponent := ?_
      componentInvariantAtXiOne := ?_
      coarseCoordinateInvariantAtXiTwo := ?_ }
  · intro sigma
    rfl
  · intro z sigma q hq
    exact localCorrectionComponent_supported A hcoh z sigma q hq
  · intro z sigma
    exact correction_masked_eq_component A hcoh z sigma
  · intro sigma z
    exact localCorrectionComponent_eq_xi_one A hcoh sigma z
  · intro sigma z
    change topParity A sigma.1 z = topParity A (xiSignal A sigma.1 z 2) z
    exact topParity_eq_xi_two A sigma.1 z

theorem coarseSyndrome_invariant_radius_two
    (A : RZCoarseGrainingData D i V)
    (hcompat : InducedCoboundaryCompatibility A)
    (z : C2 i.castSucc)
    (sigma tau : UpperSyndrome D i)
    (hAgree : SignalAgreementWithin A z 2 sigma.1 tau.1) :
    (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
      (coarseSyndrome A hcompat tau : D.family.Cochain2 i.castSucc) z := by
  exact coarseParity_invariant_radius_two A z sigma.1 tau.1 hAgree

theorem rz_coarse_graining_even
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : UpperSyndrome D i) :
    ∃ sigma' : CoarseSyndrome D i,
      ∃ correction : D.family.Cochain1 i.succ,
        correction = correctionFromSyndrome A hcoh sigma.1 ∧
        (sigma : D.family.Cochain2 i.succ) =
          D.family.coboundary1 i.succ correction +
            (D.selectedMap i).map2 sigma' ∧
        HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) ∧
        (∀ (tau : UpperSyndrome D i) z,
          SignalAgreementWithin A z 2 sigma.1 tau.1 →
          (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
            (coarseSyndrome A hcompat tau : D.family.Cochain2 i.castSucc) z) ∧
        (∀ (tau : UpperSyndrome D i) z,
          SignalAgreementWithin A z 1 sigma.1 tau.1 →
          localCorrectionComponent A hcoh z sigma.1 =
            localCorrectionComponent A hcoh z tau.1) := by
  let sigma' := coarseSyndrome A hcompat sigma
  let correction := correctionFromSyndrome A hcoh sigma.1
  refine ⟨sigma', correction, rfl, ?_, ?_, ?_, ?_⟩
  · exact rz_exact_relation A hcoh hcompat hEven sigma
  · exact coarse_weight_le_input A sigma.1
  · intro tau z hAgree
    exact coarseSyndrome_invariant_radius_two A hcompat z sigma tau hAgree
  · intro tau z hAgree
    exact localCorrectionComponent_invariant_radius_one A hcoh z sigma.1 tau.1 hAgree

end RZCoarseGraining
end MultiscaleDecoder
end Coding
end QEC


/-! ## Canonical RZ reduction independent of the global parity label -/
namespace QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]

/-- The actual canonical correction relation from a proved map equality,
without changing the original global parity convention or correction rule. -/
theorem rz_exact_relation_selected
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A)
    (hselected : D.selectedMap i = D.rzMap i)
    (sigma : UpperSyndrome D i) :
    (sigma : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ (correctionFromSyndrome A hcoh sigma.1) +
        (D.selectedMap i).map2 (coarseSyndrome A hcompat sigma) := by
  have hboundary := correction_boundary_eq_sumResidual A hcoh sigma.1
  have hsum := sum_localResidual A sigma.1
  rw [hselected, coarseSyndrome_coe]
  rw [hboundary, hsum]
  ext p
  simp only [LinearMap.add_apply, Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero]
  simp

/-- The same full canonical RZ reduction on a literal local replacement edge.
No syndrome relation, local exactness or target conclusion is assumed here. -/
theorem rz_coarse_graining_selected
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A)
    (hselected : D.selectedMap i = D.rzMap i)
    (sigma : UpperSyndrome D i) :
    ∃ sigma' : CoarseSyndrome D i,
      ∃ correction : D.family.Cochain1 i.succ,
        correction = correctionFromSyndrome A hcoh sigma.1 ∧
        (sigma : D.family.Cochain2 i.succ) =
          D.family.coboundary1 i.succ correction +
            (D.selectedMap i).map2 sigma' ∧
        HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) ∧
        (∀ (tau : UpperSyndrome D i) z,
          SignalAgreementWithin A z 2 sigma.1 tau.1 →
          (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
            (coarseSyndrome A hcompat tau : D.family.Cochain2 i.castSucc) z) ∧
        (∀ (tau : UpperSyndrome D i) z,
          SignalAgreementWithin A z 1 sigma.1 tau.1 →
          localCorrectionComponent A hcoh z sigma.1 =
            localCorrectionComponent A hcoh z tau.1) := by
  let sigma' := coarseSyndrome A hcompat sigma
  let correction := correctionFromSyndrome A hcoh sigma.1
  refine ⟨sigma', correction, rfl, ?_, ?_, ?_, ?_⟩
  · exact rz_exact_relation_selected A hcoh hcompat hselected sigma
  · exact coarse_weight_le_input A sigma.1
  · intro tau z hAgree
    exact coarseSyndrome_invariant_radius_two A hcompat z sigma tau hAgree
  · intro tau z hAgree
    exact localCorrectionComponent_invariant_radius_one A hcoh z sigma.1 tau.1 hAgree

end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
