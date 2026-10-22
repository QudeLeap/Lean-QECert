import QEC.Coding.FourDimensionalToricCode.Decoder.RXLocalCleaning

/-!
# The `R_X` coarse-graining interface

This file starts the source-facing M12 slice for an odd-input `R_X` step.
The first record below contains only the finite coordinate maps used by the
audited F08 induced-map calculation.  In particular, it does not contain an
inverse-map assertion, a weight conclusion, or a locality conclusion.  Those
are derived by the coarse-graining lemmas added below this raw interface.
-/

namespace QEC
namespace Coding
namespace MultiscaleDecoder
namespace RXCoarseGraining

open scoped BigOperators

universe u v

abbrev Field := BDL26Field

/-- The decoding-graph vertex type for one `R_X` replacement: `X → Q → Z`.
The nested sum keeps the three source node kinds disjoint while exposing the
canonical injections used by the locality contract. -/
abbrev RXVertex (X Q Z : Type v) := X ⊕ (Q ⊕ Z)

variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}

/-! ## F08: raw induced coordinate maps -/

/-- The diagonal word map appearing on the doubled `Z` coordinates. -/
noncomputable def diagonalMap
    {Z : Type v} [Fintype Z] :
    Word Field Z →ₗ[Field] Word Field (Z × Fin 2) where
  toFun signal := fun p => signal p.1
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

/--
Raw F08 data for an `R_X` replacement.  `zPairEquiv` is the finite coordinate
identification for the doubled `Z` sector; the two `map2` laws state the
diagonal value and the zero auxiliary components.  The first and second
connecting maps are recorded as explicit linear maps and equations, rather
than as an asserted cohomology endpoint.
-/
structure RXInducedMaps
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    {X Q : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] where
  adjacencyMap : Word Field X →ₗ[Field] Word Field Q
  gXQ0 : Word Field X →ₗ[Field] Word Field Q
  gXQ0_eq_adjacency : gXQ0 = adjacencyMap
  qzAdjacency : Word Field Q →ₗ[Field] Word Field (C2 i.castSucc)
  gQZ1 : Word Field Q →ₗ[Field]
    Word Field (C2 i.castSucc × Fin 2)
  gQZ1_eq_diagonal_comp :
    gQZ1 = (diagonalMap (Z := C2 i.castSucc)).comp qzAdjacency
  /-- The subset of upper syndrome coordinates belonging to the doubled Z sector. -/
  zSector : Finset (C2 i.succ)
  zPairEquiv : (C2 i.castSucc × Fin 2) ≃
    LocalRegionIndex zSector
  map2_diagonal : ∀ (s : D.family.Cochain2 i.castSucc)
    (z : C2 i.castSucc) (b : Fin 2),
    (D.rxMap i).map2 s (zPairEquiv (z, b)).1 = s z
  map2_auxiliary_zero : ∀ (s : D.family.Cochain2 i.castSucc)
    (p : C2 i.succ), p ∉ zSector → (D.rxMap i).map2 s p = 0

/-! ## F10/F11 raw support data -/

noncomputable def correctionRegionUnion
    {V : Type v} {S C : Type u} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (L : LocalComplexData V S C) : Finset C :=
  Finset.biUnion Finset.univ (fun v => L.correctionRegion v)

def SupportedOn
    {α : Type u} [Fintype α] [DecidableEq α]
    (Y : Finset α) (f : Word Field α) : Prop :=
  ∀ a, a ∉ Y → f a = 0

/--
The remaining F10/F11 information consumed by the RX RG proof.  The sector
equalities are raw coordinate/support identities: they say which finite
coordinates are owned by the local X, Q, and doubled-Z blocks.  The two
coordinate formulas for `map1` identify the Q-local cohomology representative
with the lower correction word; no inverse or decoder conclusion is stored.
-/
structure RXCoarseGrainingData
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    {X Q : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q]
    (Lx : LocalComplexData X (C2 i.succ) (C1 i.succ))
    (Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ))
    {Z : Type v} [Fintype Z] [DecidableEq Z]
    (Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ))
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)] where
  induced : RXInducedMaps (X := X) (Q := Q) D i
  contract : RXConstructionContractSlice (X0 := X0) (Q0 := Q0)
      (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz
  xSector : Finset (C2 i.succ)
  qSector : Finset (C2 i.succ)
  zSector : Finset (C2 i.succ)
  zSector_eq_induced : zSector = induced.zSector
  xSector_eq_regions : xSector = rxRegionUnion Lx
  qSector_eq_regions : qSector = rxRegionUnion Lq
  sectors_pairwise_disjoint :
    Disjoint xSector qSector ∧ Disjoint xSector zSector ∧ Disjoint qSector zSector
  sectors_cover : xSector ∪ qSector ∪ zSector = Finset.univ
  /-- The full Q correction coordinates, i.e. the union of the Q local fibres. -/
  qCorrectionSector : Finset (C1 i.succ)
  qCorrectionSector_eq_regions : qCorrectionSector = correctionRegionUnion Lq
  correction_sectors_cover :
    correctionRegionUnion Lx ∪ qCorrectionSector = Finset.univ
  correction_sectors_disjoint :
    Disjoint (correctionRegionUnion Lx) qCorrectionSector
  /-- The support sector reserved for the chosen local cohomology section. -/
  qRepresentativeSector : Finset (C1 i.succ)
  qRepresentativeSector_subset_qCorrectionSector :
    qRepresentativeSector ⊆ qCorrectionSector
  /-- A selected cocycle representative for every local cohomology class. -/
  cqRepresentative : ∀ q,
    (contract.rx_local_complexes.cq q).middleCohomology →ₗ[Field]
      (contract.rx_local_complexes.cq q).middleCocycleCode.carrier
  /-- The selected representative projects back to its quotient class. -/
  cqRepresentative_mkQ : ∀ q h,
    (contract.rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
        (cqRepresentative q h) = h
  /-- Only the selected section output, not arbitrary cocycles, is supported
      on the representative sector. -/
  cqRepresentative_supported : ∀ q h p,
    p.1 ∉ qRepresentativeSector → (cqRepresentative q h).1 p = 0
  /-- The local cohomology classes identify with the lower one-cochain space. -/
  qCohomologyEquiv :
    (∀ q, (contract.rx_local_complexes.cq q).middleCohomology) ≃ₗ[Field]
      D.family.Cochain1 i.castSucc
  /-- Structural formula for the induced `map1`: it extends the selected
      local quotient representatives and sums them. -/
  rxMap1_eq_cqRepresentative : ∀ lower,
    (D.rxMap i).map1 lower =
      ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        ((cqRepresentative q ((qCohomologyEquiv.symm lower) q)).1)
  /--
  Global bookkeeping for the local `δ⁰` stabilizer adjustment.  This is a
  structural decomposition of the lifted local coboundaries, not a decoder
  conclusion.
  -/
  cqDelta0_sum_decomposition : ∀ (s : ∀ q, Word Field (Q0 q)),
    D.family.coboundary0 i.succ
        (∑ q : Q, contract.support_decomposition.cqLift0 q (s q)) =
      ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        (contract.rx_local_complexes.cqDelta0 q (s q))
  /-- F11 cross-sector non-interference of the Q-to-Z connecting boundary. -/
  cqFlow_outside_xSector : ∀ q f p, p ∈ xSector →
    contract.support_decomposition.cqFlow q f p = 0
  /-- The source decoding graph, with its canonical `X → Q → Z` labels. -/
  levelGraph : LevelGraph (RXVertex X Q Z)
  levelGraph_kind_x : ∀ x, levelGraph.kind (Sum.inl x) = .x
  levelGraph_kind_q : ∀ q, levelGraph.kind (Sum.inr (Sum.inl q)) = .q
  levelGraph_kind_z : ∀ z, levelGraph.kind (Sum.inr (Sum.inr z)) = .z
  /-- The top coordinate owner used by the source-local restrictions. -/
  topCenter : C2 i.succ → RXVertex X Q Z
  /-- Coarse coordinates are given their own `Z`-side graph centre. -/
  coarseCenter : C2 i.castSucc → RXVertex X Q Z
  coarseCenter_is_z : ∀ z, ∃ z0 : Z,
    coarseCenter z = Sum.inr (Sum.inr z0)
  topCenter_coarse_pair : ∀ z (b : Fin 2),
    topCenter (induced.zPairEquiv (z, b)).1 = coarseCenter z
  topCenter_x_iff : ∀ x p,
    p ∈ Lx.syndromeRegion x ↔ topCenter p = Sum.inl x
  topCenter_q_iff : ∀ q p,
    p ∈ Lq.syndromeRegion q ↔ topCenter p = Sum.inr (Sum.inl q)
  topCenter_z_iff : ∀ z p,
    p ∈ Lz.syndromeRegion z ↔ topCenter p = Sum.inr (Sum.inr z)
  zSector_eq_regions : zSector = rxRegionUnion Lz
  lz_regions_pairwise_disjoint :
    ∀ z z', z ≠ z' → Disjoint (Lz.syndromeRegion z) (Lz.syndromeRegion z')
  cx_correction_regions_pairwise_disjoint :
    ∀ x x', x ≠ x' →
      Disjoint (Lx.correctionRegion x) (Lx.correctionRegion x')
  cq_correction_regions_pairwise_disjoint :
    ∀ q q', q ≠ q' →
      Disjoint (Lq.correctionRegion q) (Lq.correctionRegion q')
  /-- F11 flow support is confined to the directed source radius one. -/
  cxFlow_radius_one : ∀ x f p,
    contract.support_decomposition.cxFlow x f p ≠ 0 →
      DirectedGraph.distance levelGraph.graph (Sum.inl x) (topCenter p) ≤ 1
  cqFlow_radius_one : ∀ q f p,
    contract.support_decomposition.cqFlow q f p ≠ 0 →
      DirectedGraph.distance levelGraph.graph (Sum.inr (Sum.inl q)) (topCenter p) ≤ 1
  /-- The two-step source path law used when an X flow feeds a Q flow. -/
  distance_one_comp : ∀ u v w : RXVertex X Q Z,
    DirectedGraph.distance levelGraph.graph u v ≤ 1 →
      DirectedGraph.distance levelGraph.graph v w ≤ 1 →
        DirectedGraph.distance levelGraph.graph u w ≤ 2

namespace RXCoarseGrainingData

variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}

variable (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
  (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)

theorem xSector_mem_of_region
    {p : C2 i.succ} (hp : p ∈ rxRegionUnion Lx) : p ∈ A.xSector := by
  rw [A.xSector_eq_regions]
  exact hp

theorem qSector_mem_of_region
    {p : C2 i.succ} (hp : p ∈ rxRegionUnion Lq) : p ∈ A.qSector := by
  rw [A.qSector_eq_regions]
  exact hp

theorem zero_outside_sector_of_zero_x_zero_q
    {f : D.family.Cochain2 i.succ}
    (hx : ∀ p ∈ A.xSector, f p = 0)
    (hq : ∀ p ∈ A.qSector, f p = 0) :
    SupportedOn A.zSector f := by
  intro p hp
  have hcover : p ∈ (A.xSector ∪ A.qSector) ∪ A.zSector := by
    rw [A.sectors_cover]
    exact Finset.mem_univ p
  have hcover' : (p ∈ A.xSector ∨ p ∈ A.qSector) ∨ p ∈ A.zSector := by
    simpa only [Finset.mem_union] using hcover
  rcases hcover' with hpx | hpz
  · rcases hpx with hpx | hpz
    · exact hx p hpx
    · exact hq p hpz
  · exact (hp hpz).elim

/-! ## The Q-sector cohomology section and the doubled-Z weight identity -/

noncomputable def qCohomologyClass
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    (∀ q, (A.contract.rx_local_complexes.cq q).middleCohomology) :=
  fun q => (A.contract.rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
    ⟨restrictWordLinear (Lq.correctionRegion q) error, by
      change A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0
      exact hCocycle q⟩

theorem qCohomologyClass_mkQ
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0)
    (q : Q) :
    (A.contract.rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
      ⟨restrictWordLinear (Lq.correctionRegion q) error, by
        change A.contract.rx_local_complexes.cqDelta1 q
          (restrictWordLinear (Lq.correctionRegion q) error) = 0
        exact hCocycle q⟩ = qCohomologyClass A error hCocycle q := by
  rfl

theorem cqRepresentative_difference_exists
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0)
    (q : Q) :
    ∃ s : Word Field (Q0 q),
      A.contract.rx_local_complexes.cqDelta0 q s =
        (A.cqRepresentative q (qCohomologyClass A error hCocycle q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error := by
  let r : (A.contract.rx_local_complexes.cq q).middleCocycleCode.carrier :=
    ⟨restrictWordLinear (Lq.correctionRegion q) error, by
      change A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0
      exact hCocycle q⟩
  let h := qCohomologyClass A error hCocycle q
  have hclass :
      (A.contract.rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
          (A.cqRepresentative q h) =
        (A.contract.rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ r := by
    rw [A.cqRepresentative_mkQ]
    rfl
  have hmem :
      (A.cqRepresentative q h - r) ∈
        (A.contract.rx_local_complexes.cq q).middleCoboundaryInCocycles :=
    (Submodule.Quotient.eq
      (A.contract.rx_local_complexes.cq q).middleCoboundaryInCocycles).mp hclass
  have hfirst :
      (A.cqRepresentative q h).1 - r.1 ∈
        (A.contract.rx_local_complexes.cq q).firstCoboundaryCheckCode.carrier := by
    exact hmem
  rcases (ChainComplexData.mem_firstCoboundaryCheckCode_iff
    (A.contract.rx_local_complexes.cq q) ((A.cqRepresentative q h).1 - r.1)).1
      hfirst with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  change wordLinearMapTranspose (A.contract.rx_local_complexes.cq q).boundary1 s = _
  simpa [RXLocalComplexData.cqDelta0, r] using hs

noncomputable def zPairImage
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (z : C2 i.castSucc) : Finset (C2 i.succ) :=
  (Finset.univ : Finset (Fin 2)).image
    (fun b => (A.induced.zPairEquiv (z, b)).1)

theorem zPairImage_card
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (z : C2 i.castSucc) : (zPairImage A z).card = 2 := by
  classical
  rw [zPairImage, Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have hpair := A.induced.zPairEquiv.injective (Subtype.ext hab)
    exact congrArg Prod.snd hpair

theorem zPairImage_pairwise_disjoint
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    Set.PairwiseDisjoint (Set.univ : Set (C2 i.castSucc)) (zPairImage A) := by
  intro z _ z' _ hne
  refine Finset.disjoint_left.2 ?_
  intro p hp hp'
  rcases Finset.mem_image.mp hp with ⟨b, -, hb⟩
  rcases Finset.mem_image.mp hp' with ⟨b', -, hb'⟩
  have hpair : (z, b) = (z', b') :=
    A.induced.zPairEquiv.injective (Subtype.ext (hb.trans hb'.symm))
  have hz : z = z' := congrArg Prod.fst hpair
  exact hne hz

theorem map2_support_eq_biUnion
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (s : D.family.Cochain2 i.castSucc) :
    hammingSupport ((D.rxMap i).map2 s) =
      (hammingSupport s).biUnion (zPairImage A) := by
  classical
  ext p
  by_cases hpz : p ∈ A.induced.zSector
  · obtain ⟨⟨z, b⟩, hpair⟩ := A.induced.zPairEquiv.surjective ⟨p, by
      simpa [A.zSector_eq_induced] using hpz⟩
    have hpb : (A.induced.zPairEquiv (z, b)).1 = p := congrArg Subtype.val hpair
    constructor
    · intro hp
      have hs : s z ≠ 0 := by
        have hp' : (D.rxMap i).map2 s p ≠ 0 := by
          simpa [hammingSupport] using hp
        rw [← hpb, A.induced.map2_diagonal] at hp'
        exact hp'
      refine Finset.mem_biUnion.2 ⟨z, by simpa [hammingSupport] using hs, ?_⟩
      exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, hpb⟩
    · intro hp
      rcases Finset.mem_biUnion.1 hp with ⟨z', hz', hp'⟩
      rcases Finset.mem_image.1 hp' with ⟨b', -, hpb'⟩
      have hp'' : (D.rxMap i).map2 s p ≠ 0 := by
        rw [← hpb', A.induced.map2_diagonal]
        simpa [hammingSupport] using hz'
      simpa [hammingSupport] using hp''
  · have hz : (D.rxMap i).map2 s p = 0 :=
      A.induced.map2_auxiliary_zero s p (by simpa [A.zSector_eq_induced] using hpz)
    constructor
    · intro hp
      simpa [hammingSupport, hz] using hp
    · intro hp
      rcases Finset.mem_biUnion.1 hp with ⟨z, hz', hp'⟩
      rcases Finset.mem_image.1 hp' with ⟨b, -, hpb⟩
      have hpz' : p ∈ A.induced.zSector := by
        rw [← hpb]
        exact (A.induced.zPairEquiv (z, b)).property
      exact (hpz (by simpa [A.zSector_eq_induced] using hpz')).elim

theorem hammingWeight_map2_eq_double
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (s : D.family.Cochain2 i.castSucc) :
    HammingWeight ((D.rxMap i).map2 s) = 2 * HammingWeight s := by
  classical
  rw [HammingWeight_eq_card_hammingSupport, map2_support_eq_biUnion A s,
    Finset.card_biUnion]
  · simp_rw [zPairImage_card]
    rw [HammingWeight_eq_card_hammingSupport]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  · have hpair : (↑(hammingSupport s) : Set (C2 i.castSucc)).PairwiseDisjoint
        (zPairImage A) := by
      intro z hz z' hz' hne
      exact (zPairImage_pairwise_disjoint A)
        (Set.mem_univ z) (Set.mem_univ z') hne
    exact hpair

/-! ## Explicit local cleaning selectors -/

private noncomputable def cxWitnessRG
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)) :
    ∀ x, Word Field (LocalRegionIndex (Lx.correctionRegion x)) :=
  fun x => Classical.choose (A.contract.local_boundary_weight_budgets.cx x
    (restrictWordLinear (Lx.syndromeRegion x) sigma) (hlocal x))

private theorem cxWitnessRG_spec
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)) :
    ∀ x,
      A.contract.rx_local_complexes.cxDelta1 x (cxWitnessRG A sigma hlocal x) =
        restrictWordLinear (Lx.syndromeRegion x) sigma ∧
      HammingWeight (A.contract.support_decomposition.cxFlow x
        (cxWitnessRG A sigma hlocal x)) ≤
        HammingWeight (restrictWordLinear (Lx.syndromeRegion x) sigma) := by
  intro x
  exact Classical.choose_spec (A.contract.local_boundary_weight_budgets.cx x
    (restrictWordLinear (Lx.syndromeRegion x) sigma) (hlocal x))

private noncomputable def cqWitnessRG
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)) :
    ∀ q, Word Field (LocalRegionIndex (Lq.correctionRegion q)) :=
  fun q => Classical.choose (A.contract.local_boundary_weight_budgets.cq q
    (restrictWordLinear (Lq.syndromeRegion q) sigma) (hlocal q))

private theorem cqWitnessRG_spec
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)) :
    ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q (cqWitnessRG A sigma hlocal q) =
        restrictWordLinear (Lq.syndromeRegion q) sigma ∧
      HammingWeight (A.contract.support_decomposition.cqFlow q
        (cqWitnessRG A sigma hlocal q)) ≤
        HammingWeight (restrictWordLinear (Lq.syndromeRegion q) sigma) := by
  intro q
  exact Classical.choose_spec (A.contract.local_boundary_weight_budgets.cq q
    (restrictWordLinear (Lq.syndromeRegion q) sigma) (hlocal q))

noncomputable def cxCorrectionRG
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)) :
    D.family.Correction i.succ :=
  ∑ x : X, extendWordLinear (Lx.correctionRegion x)
    (cxWitnessRG A sigma hlocal x)

noncomputable def cqCorrectionRG
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)) :
    D.family.Correction i.succ :=
  ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
    (cqWitnessRG A sigma hlocal q)

theorem cx_cleaning_explicit
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Syndrome i.succ) :
    HammingWeight (sigma.1 + D.family.coboundary1 i.succ
        (cxCorrectionRG A sigma.1 (A.contract.cx_local_ranges_of_syndrome sigma))) ≤
      HammingWeight sigma.1 ∧
    (∀ p ∈ A.xSector,
      (sigma.1 + D.family.coboundary1 i.succ
        (cxCorrectionRG A sigma.1 (A.contract.cx_local_ranges_of_syndrome sigma))) p = 0) := by
  let hlocal := A.contract.cx_local_ranges_of_syndrome sigma
  let f := cxWitnessRG A sigma.1 hlocal
  let correction := cxCorrectionRG A sigma.1 hlocal
  let flow : D.family.Cochain2 i.succ :=
    ∑ x : X, A.contract.support_decomposition.cxFlow x (f x)
  have hdelta : D.family.coboundary1 i.succ correction =
      rxLocalPart Lx sigma.1 + flow := by
    dsimp [correction, cxCorrectionRG, flow, f]
    calc
      D.family.coboundary1 i.succ
          (∑ x : X, extendWordLinear (Lx.correctionRegion x)
            (cxWitnessRG A sigma.1 hlocal x)) =
          ∑ x : X, D.family.coboundary1 i.succ
            (extendWordLinear (Lx.correctionRegion x)
              (cxWitnessRG A sigma.1 hlocal x)) := by rw [map_sum]
      _ = ∑ x : X,
          (extendWordLinear (Lx.syndromeRegion x)
              (A.contract.rx_local_complexes.cxDelta1 x
                (cxWitnessRG A sigma.1 hlocal x)) +
            A.contract.support_decomposition.cxFlow x
              (cxWitnessRG A sigma.1 hlocal x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact A.contract.support_decomposition.cxDelta1_decomposition x
            (cxWitnessRG A sigma.1 hlocal x)
      _ = rxLocalPart Lx sigma.1 + flow := by
          rw [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          rw [(cxWitnessRG_spec A sigma.1 hlocal x).1]
  have hclean : sigma.1 + D.family.coboundary1 i.succ correction =
      rxResidual Lx sigma.1 + flow := by
    calc
      sigma.1 + D.family.coboundary1 i.succ correction =
          sigma.1 + (rxLocalPart Lx sigma.1 + flow) := by rw [hdelta]
      _ = (rxResidual Lx sigma.1 + rxLocalPart Lx sigma.1) +
            (rxLocalPart Lx sigma.1 + flow) := by
              exact congrArg (fun t => t + (rxLocalPart Lx sigma.1 + flow))
                (RXSupportDecomposition.cx_partition
                  A.contract.support_decomposition sigma.1)
      _ = rxResidual Lx sigma.1 + flow := by
        have htwo : rxLocalPart Lx sigma.1 + rxLocalPart Lx sigma.1 =
            (0 : D.family.Cochain2 i.succ) := by
          ext j
          exact ZModModule.add_self _
        calc
          (rxResidual Lx sigma.1 + rxLocalPart Lx sigma.1) +
              (rxLocalPart Lx sigma.1 + flow) =
              rxResidual Lx sigma.1 +
                (rxLocalPart Lx sigma.1 + rxLocalPart Lx sigma.1) + flow := by
                abel
          _ = rxResidual Lx sigma.1 + 0 + flow := by rw [htwo]
          _ = rxResidual Lx sigma.1 + flow := by simp
  have hflow : HammingWeight flow ≤ HammingWeight (rxLocalPart Lx sigma.1) := by
    calc
      HammingWeight flow ≤ ∑ x : X,
          HammingWeight (A.contract.support_decomposition.cxFlow x (f x)) :=
            HammingWeight_univ_sum_le _
      _ ≤ ∑ x : X, HammingWeight
          (restrictWordLinear (Lx.syndromeRegion x) sigma.1) := by
            apply Finset.sum_le_sum
            intro x hx
            exact (cxWitnessRG_spec A sigma.1 hlocal x).2
      _ = HammingWeight (rxLocalPart Lx sigma.1) :=
        (RXSupportDecomposition.cx_local_part_weight
          A.contract.support_decomposition sigma.1).symm
  constructor
  · calc
      HammingWeight (sigma.1 + D.family.coboundary1 i.succ correction) =
          HammingWeight (rxResidual Lx sigma.1 + flow) := by rw [hclean]
      _ ≤ HammingWeight (rxResidual Lx sigma.1) + HammingWeight flow :=
        HammingWeight_add_le _ _
      _ ≤ HammingWeight (rxResidual Lx sigma.1) +
          HammingWeight (rxLocalPart Lx sigma.1) := Nat.add_le_add_left hflow _
      _ = HammingWeight sigma.1 :=
        RXSupportDecomposition.cx_residual_local_weight
          A.contract.support_decomposition sigma.1
  · intro p hp
    rw [hclean]
    have hpxreg : p ∈ rxRegionUnion Lx := by
      simpa [A.xSector_eq_regions] using hp
    have hres : rxResidual Lx sigma.1 p = 0 := by
      simp [rxResidual, outsideMaskWord, maskWord, hpxreg]
    have hflow : flow p = 0 := by
      dsimp [flow]
      simp only [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro x hx
      exact A.contract.support_decomposition.cxFlow_outside_x_sector
        x (f x) p (by simpa [A.xSector_eq_regions] using hp)
    change rxResidual Lx sigma.1 p + flow p = 0
    rw [hres, hflow, add_zero]

theorem cq_cleaning_explicit
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q))
    (hX : ∀ p ∈ A.xSector, sigma p = 0) :
    HammingWeight (sigma + D.family.coboundary1 i.succ
        (cqCorrectionRG A sigma hlocal)) ≤ HammingWeight sigma ∧
    (∀ p ∈ A.qSector,
      (sigma + D.family.coboundary1 i.succ
        (cqCorrectionRG A sigma hlocal)) p = 0) ∧
    (∀ p ∈ A.xSector,
      (sigma + D.family.coboundary1 i.succ
        (cqCorrectionRG A sigma hlocal)) p = 0) := by
  let f := cqWitnessRG A sigma hlocal
  let correction := cqCorrectionRG A sigma hlocal
  let flow : D.family.Cochain2 i.succ :=
    ∑ q : Q, A.contract.support_decomposition.cqFlow q (f q)
  have hdelta : D.family.coboundary1 i.succ correction =
      rxLocalPart Lq sigma + flow := by
    dsimp [correction, cqCorrectionRG, flow, f]
    calc
      D.family.coboundary1 i.succ
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (cqWitnessRG A sigma hlocal q)) =
          ∑ q : Q, D.family.coboundary1 i.succ
            (extendWordLinear (Lq.correctionRegion q)
              (cqWitnessRG A sigma hlocal q)) := by rw [map_sum]
      _ = ∑ q : Q,
          (extendWordLinear (Lq.syndromeRegion q)
              (A.contract.rx_local_complexes.cqDelta1 q
                (cqWitnessRG A sigma hlocal q)) +
            A.contract.support_decomposition.cqFlow q
              (cqWitnessRG A sigma hlocal q)) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact A.contract.support_decomposition.cqDelta1_decomposition q
            (cqWitnessRG A sigma hlocal q)
      _ = rxLocalPart Lq sigma + flow := by
          rw [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro q hq
          rw [(cqWitnessRG_spec A sigma hlocal q).1]
  have hclean : sigma + D.family.coboundary1 i.succ correction =
      rxResidual Lq sigma + flow := by
    calc
      sigma + D.family.coboundary1 i.succ correction =
          sigma + (rxLocalPart Lq sigma + flow) := by rw [hdelta]
      _ = (rxResidual Lq sigma + rxLocalPart Lq sigma) +
            (rxLocalPart Lq sigma + flow) := by
              exact congrArg (fun t => t + (rxLocalPart Lq sigma + flow))
                (RXSupportDecomposition.cq_partition
                  A.contract.support_decomposition sigma)
      _ = rxResidual Lq sigma + flow := by
        have htwo : rxLocalPart Lq sigma + rxLocalPart Lq sigma =
            (0 : D.family.Cochain2 i.succ) := by
          ext j
          exact ZModModule.add_self _
        calc
          (rxResidual Lq sigma + rxLocalPart Lq sigma) +
              (rxLocalPart Lq sigma + flow) =
              rxResidual Lq sigma +
                (rxLocalPart Lq sigma + rxLocalPart Lq sigma) + flow := by
                abel
          _ = rxResidual Lq sigma + 0 + flow := by rw [htwo]
          _ = rxResidual Lq sigma + flow := by simp
  have hflow : HammingWeight flow ≤ HammingWeight (rxLocalPart Lq sigma) := by
    calc
      HammingWeight flow ≤ ∑ q : Q,
          HammingWeight (A.contract.support_decomposition.cqFlow q (f q)) :=
            HammingWeight_univ_sum_le _
      _ ≤ ∑ q : Q, HammingWeight
          (restrictWordLinear (Lq.syndromeRegion q) sigma) := by
            apply Finset.sum_le_sum
            intro q hq
            exact (cqWitnessRG_spec A sigma hlocal q).2
      _ = HammingWeight (rxLocalPart Lq sigma) :=
        (RXSupportDecomposition.cq_local_part_weight
          A.contract.support_decomposition sigma).symm
  have hweight : HammingWeight (sigma + D.family.coboundary1 i.succ correction) ≤
      HammingWeight sigma := by
    calc
      HammingWeight (sigma + D.family.coboundary1 i.succ correction) =
          HammingWeight (rxResidual Lq sigma + flow) := by rw [hclean]
      _ ≤ HammingWeight (rxResidual Lq sigma) + HammingWeight flow :=
        HammingWeight_add_le _ _
      _ ≤ HammingWeight (rxResidual Lq sigma) +
          HammingWeight (rxLocalPart Lq sigma) := Nat.add_le_add_left hflow _
      _ = HammingWeight sigma :=
        RXSupportDecomposition.cq_residual_local_weight
          A.contract.support_decomposition sigma
  refine ⟨hweight, ?_, ?_⟩
  · intro p hp
    rw [hclean]
    have hpreg : p ∈ rxRegionUnion Lq := by
      simpa [A.qSector_eq_regions] using hp
    have hres : rxResidual Lq sigma p = 0 := by
      simp [rxResidual, outsideMaskWord, maskWord, hpreg]
    have hflow' : flow p = 0 := by
      dsimp [flow]
      simp only [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro q hq
      exact A.contract.support_decomposition.cqFlow_outside_q_sector
        q (f q) p (by simpa [A.qSector_eq_regions] using hp)
    change rxResidual Lq sigma p + flow p = 0
    rw [hres, hflow', add_zero]
  · intro p hp
    rw [hclean]
    have hres : rxResidual Lq sigma p = sigma p := by
      simp [rxResidual, outsideMaskWord, maskWord,
        show p ∉ rxRegionUnion Lq by
          intro hpreg
          have hdis := A.sectors_pairwise_disjoint.1
          exact (Finset.disjoint_left.1 hdis
            (by simpa [A.xSector_eq_regions] using hp)
            (by simpa [A.qSector_eq_regions] using hpreg))]
    have hflow' : flow p = 0 := by
      dsimp [flow]
      simp only [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro q hq
      exact A.cqFlow_outside_xSector q (f q) p hp
    change rxResidual Lq sigma p + flow p = 0
    rw [hres, hflow', add_zero, hX p hp]

theorem cqCorrectionRG_supported
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)) :
    SupportedOn A.qCorrectionSector (cqCorrectionRG A sigma hlocal) := by
  intro p hp
  dsimp [cqCorrectionRG]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  have hpq : p ∉ Lq.correctionRegion q := by
    intro hpq
    apply hp
    rw [A.qCorrectionSector_eq_regions]
    exact Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, hpq⟩
  simp [extendWordLinear, extendLocalSignal, hpq]

theorem selectedMap_eq_rx_of_odd_input
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    (hOdd : i.succ.val % 2 = 1) :
    D.selectedMap i = D.rxMap i := by
  change (i.val + 1) % 2 = 1 at hOdd
  have hi : i.val % 2 = 0 := by omega
  simp [BDL26DecoderData.selectedMap, replacementKind, hi]

/-! ## Source-local graph adapter

The graph adapter below is deliberately structural.  Its vertices are the
three canonical source node kinds, and its local coordinate fibres are the
audited `Y_x`, `Y_q`, and `Y_z` regions.  The five locality statements are
proved later from this adapter and the raw flow-support fields above; they are
not stored in `RXCoarseGrainingData`. -/

noncomputable def rxXiLocalComplex
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    LocalComplexData (RXVertex X Q Z) (C2 i.succ) (C1 i.succ) where
  syndromeRegion := fun v =>
    match v with
    | Sum.inl x => Lx.syndromeRegion x
    | Sum.inr (Sum.inl q) => Lq.syndromeRegion q
    | Sum.inr (Sum.inr z) => Lz.syndromeRegion z
  correctionRegion := fun v =>
    match v with
    | Sum.inl x => Lx.correctionRegion x
    | Sum.inr (Sum.inl q) => Lq.correctionRegion q
    | Sum.inr (Sum.inr _z) => ∅

theorem rxXiLocalComplex_syndromeRegion_eq
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (v : RXVertex X Q Z) :
    (rxXiLocalComplex A).syndromeRegion v =
      match v with
      | Sum.inl x => Lx.syndromeRegion x
      | Sum.inr (Sum.inl q) => Lq.syndromeRegion q
      | Sum.inr (Sum.inr z) => Lz.syndromeRegion z := by
  cases v <;> rfl

theorem rxXiLocalComplex_region_mem_iff
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (v : RXVertex X Q Z) (p : C2 i.succ) :
    p ∈ (rxXiLocalComplex A).syndromeRegion v ↔ A.topCenter p = v := by
  cases v with
  | inl x => exact A.topCenter_x_iff x p
  | inr v =>
      cases v with
      | inl q => exact A.topCenter_q_iff q p
      | inr z => exact A.topCenter_z_iff z p

theorem rxXiLocalComplex_regions_pairwise_disjoint
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    ∀ v w, v ≠ w →
      Disjoint ((rxXiLocalComplex A).syndromeRegion v)
        ((rxXiLocalComplex A).syndromeRegion w) := by
  intro v w hvw
  rw [Finset.disjoint_left]
  intro p hpv hpw
  have htv := (rxXiLocalComplex_region_mem_iff A v p).1 hpv
  have htw := (rxXiLocalComplex_region_mem_iff A w p).1 hpw
  exact hvw (htv.symm.trans htw)

noncomputable def rxXiSignal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (center : RXVertex X Q Z) (radius : Nat) :
    D.family.Cochain2 i.succ :=
  xiAggregate A.levelGraph.graph (rxXiLocalComplex A) sigma center radius

theorem rxXiSignal_apply
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (center : RXVertex X Q Z) (radius : Nat) (p : C2 i.succ) :
    rxXiSignal A sigma center radius p =
      if DirectedGraph.distance A.levelGraph.graph (A.topCenter p) center ≤ radius
      then sigma p else 0 := by
  classical
  let v₀ := A.topCenter p
  have hp₀ : p ∈ (rxXiLocalComplex A).syndromeRegion v₀ :=
    (rxXiLocalComplex_region_mem_iff A v₀ p).2 rfl
  by_cases hdist : DirectedGraph.distance A.levelGraph.graph v₀ center ≤ radius
  · rw [rxXiSignal, xiAggregate, xiIndexSet,
      LocalRegion.directedNeighborhood]
    rw [if_pos hdist]
    change Finset.sum ((Finset.univ : Finset (RXVertex X Q Z)).filter
      (fun u => DirectedGraph.distance A.levelGraph.graph u center ≤ radius))
      (fun u => maskWord ((rxXiLocalComplex A).syndromeRegion u) sigma p) = sigma p
    have hsum := Finset.sum_eq_single
      (s := (Finset.univ : Finset (RXVertex X Q Z)).filter
        (fun u => DirectedGraph.distance A.levelGraph.graph u center ≤ radius))
      (f := fun u => maskWord ((rxXiLocalComplex A).syndromeRegion u) sigma p)
      v₀ (by
        intro v hv hne
        have hpv : p ∉ (rxXiLocalComplex A).syndromeRegion v := by
          intro hpv
          have hEq : v = v₀ := by
            exact ((rxXiLocalComplex_region_mem_iff A v p).1 hpv).symm.trans
              ((rxXiLocalComplex_region_mem_iff A v₀ p).1 hp₀)
          exact hne hEq
        simp [maskWord, hpv]) (by simp [hdist])
    rw [hsum]
    simp [maskWord, hp₀]
  · rw [rxXiSignal, xiAggregate, xiIndexSet,
      LocalRegion.directedNeighborhood]
    rw [if_neg hdist]
    change Finset.sum ((Finset.univ : Finset (RXVertex X Q Z)).filter
      (fun u => DirectedGraph.distance A.levelGraph.graph u center ≤ radius))
      (fun u => maskWord ((rxXiLocalComplex A).syndromeRegion u) sigma p) = 0
    apply Finset.sum_eq_zero
    intro v hv
    by_cases hpv : p ∈ (rxXiLocalComplex A).syndromeRegion v
    · have hv₀ : v = v₀ := by
        exact ((rxXiLocalComplex_region_mem_iff A v p).1 hpv).symm.trans
          ((rxXiLocalComplex_region_mem_iff A v₀ p).1 hp₀)
      exact (hdist (by simpa [hv₀] using hv)).elim
    · simp [maskWord, hpv]

theorem rx_distance_self
    (G : DirectedGraph (RXVertex X Q Z)) (v : RXVertex X Q Z) :
    DirectedGraph.distance G v v = 0 := by
  have hreach : ∀ n,
      DirectedGraph.reachableWithin G n v v = true := by
    intro n
    induction n with
    | zero => simp [DirectedGraph.reachableWithin]
    | succ n ih => simp [DirectedGraph.reachableWithin, ih]
  have haux : ∀ n, DirectedGraph.distanceAux G v v n = some 0 := by
    intro n
    induction n with
    | zero => simp [DirectedGraph.distanceAux, hreach]
    | succ n ih => simp [DirectedGraph.distanceAux, ih, hreach]
  simp [DirectedGraph.distance, haux]

/-- Agreement of two upper words on the directed source ball around a graph
centre.  This is the executable form used by the five #811 locality Props. -/
def rxSignalAgreementWithin
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (center : RXVertex X Q Z) (radius : Nat)
    (sigma tau : D.family.Cochain2 i.succ) : Prop :=
  ∀ p, DirectedGraph.distance A.levelGraph.graph (A.topCenter p) center ≤ radius →
    sigma p = tau p

theorem rxXiSignal_agrees
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (center : RXVertex X Q Z) (radius : Nat) :
    rxSignalAgreementWithin A center radius sigma
      (rxXiSignal A sigma center radius) := by
  intro p hp
  rw [rxXiSignal_apply]
  simp [hp]

theorem rx_restrict_eq_of_agreement
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ)
    (center : RXVertex X Q Z) (radius : Nat)
    (hAgree : rxSignalAgreementWithin A center radius sigma tau)
    (v : RXVertex X Q Z)
    (hRadius : DirectedGraph.distance A.levelGraph.graph v center ≤ radius) :
    restrictWordLinear ((rxXiLocalComplex A).syndromeRegion v) sigma =
      restrictWordLinear ((rxXiLocalComplex A).syndromeRegion v) tau := by
  funext u
  change sigma u.1 = tau u.1
  apply hAgree u.1
  rw [(rxXiLocalComplex_region_mem_iff A v u.1).1 u.property]
  exact hRadius

/-! The public coarse coordinate is the explicit doubled-Z pullback.  The
internal Q-sector representative below is used only to prove that this word
is a lower-level coboundary. -/

noncomputable def coarseProjection
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.castSucc :=
  fun z => sigma (A.induced.zPairEquiv (z, 0)).1

theorem coarseProjection_eq_of_map2
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (s : D.family.Cochain2 i.castSucc)
    (hMap : (D.rxMap i).map2 s = sigma) :
    coarseProjection A sigma = s := by
  funext z
  dsimp [coarseProjection]
  rw [← hMap, A.induced.map2_diagonal]

/-! ## Total selectors and source-local components

The public decoder is defined on every finite upper word.  A local boundary
budget is used when its restriction lies in the corresponding local range;
outside that domain the selector is the zero word.  Thus the functions below
are total functions, as required by the generic #811 local-component surface,
while the preceding coarse-graining theorem recovers the nonzero branch for
an actual syndrome. -/

def CxLocalRange
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : Prop :=
  ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma ∈
    LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)

def CxLocalRangeAt
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) : Prop :=
  restrictWordLinear (Lx.syndromeRegion x) sigma ∈
  LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)

private noncomputable def cxWitnessAt
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X)
    (h : CxLocalRangeAt A sigma x) :
    Word Field (LocalRegionIndex (Lx.correctionRegion x)) :=
  Classical.choose (A.contract.local_boundary_weight_budgets.cx x
    (restrictWordLinear (Lx.syndromeRegion x) sigma) h)

private theorem cxWitnessAt_eq_of_restrict_eq
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (x : X)
    (h : CxLocalRangeAt A sigma x) (h' : CxLocalRangeAt A tau x)
    (hRestr : restrictWordLinear (Lx.syndromeRegion x) sigma =
      restrictWordLinear (Lx.syndromeRegion x) tau) :
    cxWitnessAt A sigma x h = cxWitnessAt A tau x h' := by
  let Pσ : Word Field (LocalRegionIndex (Lx.correctionRegion x)) → Prop :=
    fun f => A.contract.rx_local_complexes.cxDelta1 x f =
        restrictWordLinear (Lx.syndromeRegion x) sigma ∧
      HammingWeight (A.contract.support_decomposition.cxFlow x f) ≤
        HammingWeight (restrictWordLinear (Lx.syndromeRegion x) sigma)
  let Pτ : Word Field (LocalRegionIndex (Lx.correctionRegion x)) → Prop :=
    fun f => A.contract.rx_local_complexes.cxDelta1 x f =
        restrictWordLinear (Lx.syndromeRegion x) tau ∧
      HammingWeight (A.contract.support_decomposition.cxFlow x f) ≤
        HammingWeight (restrictWordLinear (Lx.syndromeRegion x) tau)
  have hPred : Pσ = Pτ := by
    funext f
    dsimp [Pσ, Pτ]
    rw [hRestr]
  have hChoose : ∀ (eσ : ∃ f, Pσ f) (eτ : ∃ f, Pτ f),
      @Classical.choose _ Pσ eσ = @Classical.choose _ Pτ eτ := by
    rw [hPred]
    intro eσ eτ
    rfl
  have eσ : ∃ f, Pσ f := by
    simpa [Pσ] using
      (A.contract.local_boundary_weight_budgets.cx x
        (restrictWordLinear (Lx.syndromeRegion x) sigma) h)
  have eτ : ∃ f, Pτ f := by
    simpa [Pτ] using
      (A.contract.local_boundary_weight_budgets.cx x
        (restrictWordLinear (Lx.syndromeRegion x) tau) h')
  simpa [cxWitnessAt, Pσ, Pτ] using hChoose eσ eτ

noncomputable def cxCorrectionTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
    D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Correction i.succ := by
  classical
  exact ∑ x : X, if h : CxLocalRangeAt A sigma x then
    extendWordLinear (Lx.correctionRegion x) (cxWitnessAt A sigma x h)
  else 0

noncomputable def cxComponentTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
    D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) : D.family.Correction i.succ := by
  classical
  exact if h : CxLocalRangeAt A sigma x then
    extendWordLinear (Lx.correctionRegion x) (cxWitnessAt A sigma x h)
  else 0

def CqLocalRange
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : Prop :=
  ∀ q, restrictWordLinear (Lq.syndromeRegion q)
      (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)) ∈
    LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)

def CqLocalRangeAt
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) : Prop :=
  restrictWordLinear (Lq.syndromeRegion q)
      (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)) ∈
    LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)

private noncomputable def cqWitnessAt
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q)
    (h : CqLocalRangeAt A sigma q) :
    Word Field (LocalRegionIndex (Lq.correctionRegion q)) :=
  Classical.choose (A.contract.local_boundary_weight_budgets.cq q
    (restrictWordLinear (Lq.syndromeRegion q)
      (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma))) h)

private theorem cqWitnessAt_eq_of_cleaned_restrict_eq
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (q : Q)
    (h : CqLocalRangeAt A sigma q) (h' : CqLocalRangeAt A tau q)
    (hRestr : restrictWordLinear (Lq.syndromeRegion q)
        (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)) =
      restrictWordLinear (Lq.syndromeRegion q)
        (tau + D.family.coboundary1 i.succ (cxCorrectionTotal A tau))) :
    cqWitnessAt A sigma q h = cqWitnessAt A tau q h' := by
  let Pσ : Word Field (LocalRegionIndex (Lq.correctionRegion q)) → Prop :=
    fun f => A.contract.rx_local_complexes.cqDelta1 q f =
      restrictWordLinear (Lq.syndromeRegion q)
          (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)) ∧
      HammingWeight (A.contract.support_decomposition.cqFlow q f) ≤
        HammingWeight (restrictWordLinear (Lq.syndromeRegion q)
          (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)))
  let Pτ : Word Field (LocalRegionIndex (Lq.correctionRegion q)) → Prop :=
    fun f => A.contract.rx_local_complexes.cqDelta1 q f =
      restrictWordLinear (Lq.syndromeRegion q)
          (tau + D.family.coboundary1 i.succ (cxCorrectionTotal A tau)) ∧
      HammingWeight (A.contract.support_decomposition.cqFlow q f) ≤
        HammingWeight (restrictWordLinear (Lq.syndromeRegion q)
          (tau + D.family.coboundary1 i.succ (cxCorrectionTotal A tau)))
  have hPred : Pσ = Pτ := by
    funext f
    dsimp [Pσ, Pτ]
    rw [hRestr]
  have hChoose : ∀ (eσ : ∃ f, Pσ f) (eτ : ∃ f, Pτ f),
      @Classical.choose _ Pσ eσ = @Classical.choose _ Pτ eτ := by
    rw [hPred]
    intro eσ eτ
    rfl
  have eσ : ∃ f, Pσ f := by
    simpa [Pσ] using
      (A.contract.local_boundary_weight_budgets.cq q
        (restrictWordLinear (Lq.syndromeRegion q)
          (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma))) h)
  have eτ : ∃ f, Pτ f := by
    simpa [Pτ] using
      (A.contract.local_boundary_weight_budgets.cq q
        (restrictWordLinear (Lq.syndromeRegion q)
          (tau + D.family.coboundary1 i.succ (cxCorrectionTotal A tau))) h')
  simpa [cqWitnessAt, Pσ, Pτ] using hChoose eσ eτ

noncomputable def cqCorrectionTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
    D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Correction i.succ := by
  classical
  exact ∑ q : Q, if h : CqLocalRangeAt A sigma q then
    extendWordLinear (Lq.correctionRegion q)
      (cqWitnessAt A sigma q h)
  else 0

noncomputable def cqComponentTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
    D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) : D.family.Correction i.succ := by
  classical
  exact if h : CqLocalRangeAt A sigma q then
    extendWordLinear (Lq.correctionRegion q)
      (cqWitnessAt A sigma q h)
  else 0

noncomputable def rxCorrectionTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Correction i.succ :=
  cxCorrectionTotal A sigma + cqCorrectionTotal A sigma

noncomputable def rxSigmaAfterCx
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.succ :=
  sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)

noncomputable def rxSigmaAfterCq
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.succ :=
  rxSigmaAfterCx A sigma + D.family.coboundary1 i.succ (cqCorrectionTotal A sigma)

noncomputable def rxCoarseWord
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.castSucc :=
  coarseProjection A (rxSigmaAfterCq A sigma)

theorem cxCorrectionTotal_eq_explicit
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (h : CxLocalRange A sigma) :
    cxCorrectionTotal A sigma = cxCorrectionRG A sigma h := by
  classical
  dsimp [cxCorrectionTotal, cxCorrectionRG]
  apply Finset.sum_congr rfl
  intro x hx
  split
  · rfl
  · rename_i hnot
    exact False.elim (hnot (h x))

theorem cxCorrectionTotal_eq_of_unique
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (h : CxLocalRange A sigma)
    (w : ∀ x, Word Field (LocalRegionIndex (Lx.correctionRegion x)))
    (huniq : ∀ x f,
      A.contract.rx_local_complexes.cxDelta1 x f =
        restrictWordLinear (Lx.syndromeRegion x) sigma → f = w x) :
    cxCorrectionTotal A sigma =
      ∑ x : X, extendWordLinear (Lx.correctionRegion x) (w x) := by
  rw [cxCorrectionTotal_eq_explicit A sigma h]
  unfold cxCorrectionRG
  apply Finset.sum_congr rfl
  intro x hx
  have hspec := (cxWitnessRG_spec A sigma (fun x => h x) x).1
  rw [huniq x (cxWitnessRG A sigma (fun x => h x) x) hspec]

theorem cxComponentTotal_eq_explicit
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X)
    (h : CxLocalRangeAt A sigma x) :
    cxComponentTotal A sigma x =
      extendWordLinear (Lx.correctionRegion x) (cxWitnessAt A sigma x h) := by
  classical
  rw [cxComponentTotal, dif_pos h]

theorem cqCorrectionTotal_eq_explicit
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (h : CqLocalRange A sigma) :
    cqCorrectionTotal A sigma = cqCorrectionRG A
      (rxSigmaAfterCx A sigma) h := by
  classical
  dsimp [cqCorrectionTotal, cqCorrectionRG, rxSigmaAfterCx]
  apply Finset.sum_congr rfl
  intro q hq
  split
  · rfl
  · rename_i hnot
    exact False.elim (hnot (h q))

theorem cqCorrectionTotal_eq_of_unique
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (h : CqLocalRange A sigma)
    (w : ∀ q, Word Field (LocalRegionIndex (Lq.correctionRegion q)))
    (huniq : ∀ q f,
      (A.contract.rx_local_complexes.cqDelta1 q f =
          restrictWordLinear (Lq.syndromeRegion q)
            (rxSigmaAfterCx A sigma) ∧
        HammingWeight (A.contract.support_decomposition.cqFlow q f) ≤
          HammingWeight (restrictWordLinear (Lq.syndromeRegion q)
            (rxSigmaAfterCx A sigma))) → f = w q) :
    cqCorrectionTotal A sigma =
      ∑ q : Q, extendWordLinear (Lq.correctionRegion q) (w q) := by
  rw [cqCorrectionTotal_eq_explicit A sigma h]
  unfold cqCorrectionRG
  apply Finset.sum_congr rfl
  intro q hq
  have hspec := (cqWitnessRG_spec A (rxSigmaAfterCx A sigma)
    (fun q => h q) q).1
  rw [huniq q (cqWitnessRG A (rxSigmaAfterCx A sigma) (fun q => h q) q)
    (cqWitnessRG_spec A (rxSigmaAfterCx A sigma) (fun q => h q) q)]

theorem cqComponentTotal_eq_explicit
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q)
    (h : CqLocalRangeAt A sigma q) :
    cqComponentTotal A sigma q =
      extendWordLinear (Lq.correctionRegion q)
        (cqWitnessAt A sigma q h) := by
  classical
  rw [cqComponentTotal, dif_pos h]

theorem cxComponentTotal_local_delta
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X)
    (h : CxLocalRangeAt A sigma x) :
    A.contract.rx_local_complexes.cxDelta1 x
      (restrictWordLinear (Lx.correctionRegion x)
        (cxComponentTotal A sigma x)) =
      restrictWordLinear (Lx.syndromeRegion x) sigma := by
  rw [cxComponentTotal_eq_explicit A sigma x h]
  have hrestrict :
      restrictWordLinear (Lx.correctionRegion x)
          (extendWordLinear (Lx.correctionRegion x)
            (cxWitnessAt A sigma x h)) =
        cxWitnessAt A sigma x h := by
    ext j
    change extendLocalSignal (Lx.correctionRegion x) (cxWitnessAt A sigma x h) j.1 = _
    simp [extendLocalSignal, j.property]
  rw [hrestrict]
  simpa [cxWitnessAt] using
    (Classical.choose_spec (A.contract.local_boundary_weight_budgets.cx x
      (restrictWordLinear (Lx.syndromeRegion x) sigma) h)).1

theorem cxComponentTotal_local_flow_weight
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X)
    (h : CxLocalRangeAt A sigma x) :
    HammingWeight
        (A.contract.support_decomposition.cxFlow x
          (restrictWordLinear (Lx.correctionRegion x)
            (cxComponentTotal A sigma x))) ≤
      HammingWeight (restrictWordLinear (Lx.syndromeRegion x) sigma) := by
  rw [cxComponentTotal_eq_explicit A sigma x h]
  have hrestrict :
      restrictWordLinear (Lx.correctionRegion x)
          (extendWordLinear (Lx.correctionRegion x)
            (cxWitnessAt A sigma x h)) =
        cxWitnessAt A sigma x h := by
    ext j
    change extendLocalSignal (Lx.correctionRegion x) (cxWitnessAt A sigma x h) j.1 = _
    simp [extendLocalSignal, j.property]
  rw [hrestrict]
  simpa [cxWitnessAt] using
    (Classical.choose_spec (A.contract.local_boundary_weight_budgets.cx x
      (restrictWordLinear (Lx.syndromeRegion x) sigma) h)).2

theorem cqComponentTotal_local_delta
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q)
    (h : CqLocalRangeAt A sigma q) :
    A.contract.rx_local_complexes.cqDelta1 q
      (restrictWordLinear (Lq.correctionRegion q)
        (cqComponentTotal A sigma q)) =
      restrictWordLinear (Lq.syndromeRegion q)
        (rxSigmaAfterCx A sigma) := by
  rw [cqComponentTotal_eq_explicit A sigma q h]
  have hrestrict :
      restrictWordLinear (Lq.correctionRegion q)
          (extendWordLinear (Lq.correctionRegion q)
            (cqWitnessAt A sigma q h)) =
        cqWitnessAt A sigma q h := by
    ext j
    change extendLocalSignal (Lq.correctionRegion q) (cqWitnessAt A sigma q h) j.1 = _
    simp [extendLocalSignal, j.property]
  rw [hrestrict]
  exact
    (Classical.choose_spec (A.contract.local_boundary_weight_budgets.cq q
      (restrictWordLinear (Lq.syndromeRegion q)
        (rxSigmaAfterCx A sigma)) h)).1

theorem cqComponentTotal_local_flow_weight
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q)
    (h : CqLocalRangeAt A sigma q) :
    HammingWeight
        (A.contract.support_decomposition.cqFlow q
          (restrictWordLinear (Lq.correctionRegion q)
            (cqComponentTotal A sigma q))) ≤
      HammingWeight (restrictWordLinear (Lq.syndromeRegion q)
        (rxSigmaAfterCx A sigma)) := by
  rw [cqComponentTotal_eq_explicit A sigma q h]
  have hrestrict :
      restrictWordLinear (Lq.correctionRegion q)
          (extendWordLinear (Lq.correctionRegion q)
            (cqWitnessAt A sigma q h)) =
        cqWitnessAt A sigma q h := by
    ext j
    change extendLocalSignal (Lq.correctionRegion q) (cqWitnessAt A sigma q h) j.1 = _
    simp [extendLocalSignal, j.property]
  rw [hrestrict]
  exact
    (Classical.choose_spec (A.contract.local_boundary_weight_budgets.cq q
      (restrictWordLinear (Lq.syndromeRegion q)
        (rxSigmaAfterCx A sigma)) h)).2

noncomputable def rxLocalComponents
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    LocalCorrectionComponents (RXVertex X Q Z) (C2 i.succ) (C1 i.succ)
      Field Field (rxXiLocalComplex A) where
  component := fun v sigma =>
    match v with
    | Sum.inl x => cxComponentTotal A sigma x
    | Sum.inr (Sum.inl q) => cqComponentTotal A sigma q
    | Sum.inr (Sum.inr _z) => 0

noncomputable def rxLocalInterface
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    LocalComputabilityInterface (RXVertex X Q Z) (C2 i.succ) (C1 i.succ)
      (C2 i.castSucc) Field Field (rxXiLocalComplex A) A.levelGraph.graph where
  correction := rxCorrectionTotal A
  components := rxLocalComponents A
  coarseSyndrome := rxCoarseWord A
  coarseCenter := A.coarseCenter

structure RXLocalComputabilityCertificate
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) where
  totalCorrectionDecomposition :
    LocalComputabilityInterface.totalCorrectionDecomposition
      (rxLocalInterface A)
  componentSupported :
    LocalComputabilityInterface.componentSupported
      (rxLocalInterface A)
  maskedTotalCorrectionEqComponent :
    LocalComputabilityInterface.maskedTotalCorrectionEqComponent
      (rxLocalInterface A)
  componentInvariantAtXiOne :
    LocalComputabilityInterface.componentInvariantAtXiOne
      (rxLocalInterface A)
  coarseCoordinateInvariantAtXiTwo :
    LocalComputabilityInterface.coarseCoordinateInvariantAtXiTwo
      (rxLocalInterface A)

theorem cxComponentTotal_supported
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) (p : C1 i.succ)
    (hp : p ∉ Lx.correctionRegion x) : cxComponentTotal A sigma x p = 0 := by
  classical
  by_cases h : CxLocalRangeAt A sigma x
  · simp [cxComponentTotal, h, extendWordLinear, extendLocalSignal, hp]
  · simp [cxComponentTotal, h]

theorem cqComponentTotal_supported
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) (p : C1 i.succ)
    (hp : p ∉ Lq.correctionRegion q) : cqComponentTotal A sigma q p = 0 := by
  classical
  by_cases h : CqLocalRangeAt A sigma q
  · simp [cqComponentTotal, h, extendWordLinear, extendLocalSignal, hp]
  · simp [cqComponentTotal, h]

theorem rx_total_eq_components
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) :
    rxCorrectionTotal A sigma =
      (∑ x : X, cxComponentTotal A sigma x) +
        ∑ q : Q, cqComponentTotal A sigma q := by
  rfl

theorem rx_mask_total_at_x
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) :
    maskWord (Lx.correctionRegion x) (rxCorrectionTotal A sigma) =
      cxComponentTotal A sigma x := by
  classical
  funext p
  by_cases hp : p ∈ Lx.correctionRegion x
  · rw [rx_total_eq_components]
    simp only [maskWord, if_pos hp, Pi.add_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · have hqsum : (∑ q : Q, cqComponentTotal A sigma q p) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        apply cqComponentTotal_supported A sigma q p
        intro hpq
        have hpX : p ∈ correctionRegionUnion Lx :=
          Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, hp⟩
        have hpQ : p ∈ A.qCorrectionSector := by
          rw [A.qCorrectionSector_eq_regions]
          exact Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, hpq⟩
        exact (Finset.disjoint_left.1 A.correction_sectors_disjoint) hpX hpQ
      rw [hqsum, add_zero]
    · intro x' hx' hne
      apply cxComponentTotal_supported A sigma x' p
      intro hpx'
      exact (Finset.disjoint_left.1
        (A.cx_correction_regions_pairwise_disjoint x' x hne)) hpx' hp
    · simp
  · simp [maskWord, hp,
      cxComponentTotal_supported A sigma x p hp]

theorem rx_mask_total_at_q
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) :
    maskWord (Lq.correctionRegion q) (rxCorrectionTotal A sigma) =
      cqComponentTotal A sigma q := by
  classical
  funext p
  by_cases hp : p ∈ Lq.correctionRegion q
  · rw [rx_total_eq_components]
    simp only [maskWord, if_pos hp, Pi.add_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single q]
    · have hxsum : (∑ x : X, cxComponentTotal A sigma x p) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        apply cxComponentTotal_supported A sigma x p
        intro hpx
        have hpX : p ∈ correctionRegionUnion Lx :=
          Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, hpx⟩
        have hpQ : p ∈ A.qCorrectionSector := by
          rw [A.qCorrectionSector_eq_regions]
          exact Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, hp⟩
        exact (Finset.disjoint_left.1 A.correction_sectors_disjoint) hpX hpQ
      rw [hxsum, zero_add]
    · intro q' hq' hne
      apply cqComponentTotal_supported A sigma q' p
      intro hpq'
      exact (Finset.disjoint_left.1
        (A.cq_correction_regions_pairwise_disjoint q' q hne)) hpq' hp
    · simp
  · simp [maskWord, hp,
      cqComponentTotal_supported A sigma q p hp]

theorem rx_cx_component_boundary_apply_of_range
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) (p : C2 i.succ)
    (h : CxLocalRangeAt A sigma x) :
    D.family.coboundary1 i.succ (cxComponentTotal A sigma x) p =
      (extendWordLinear (Lx.syndromeRegion x)
        (A.contract.rx_local_complexes.cxDelta1 x
          (cxWitnessAt A sigma x h)) p +
        A.contract.support_decomposition.cxFlow x
          (cxWitnessAt A sigma x h) p) := by
  classical
  simp only [cxComponentTotal, dif_pos h]
  exact congrFun
    (A.contract.support_decomposition.cxDelta1_decomposition x
      (cxWitnessAt A sigma x h)) p

theorem rx_cx_component_boundary_apply_of_not_range
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) (p : C2 i.succ)
    (h : ¬ CxLocalRangeAt A sigma x) :
    D.family.coboundary1 i.succ (cxComponentTotal A sigma x) p = 0 := by
  classical
  simp [cxComponentTotal, h]

theorem rx_cq_component_boundary_apply_of_range
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) (p : C2 i.succ)
    (h : CqLocalRangeAt A sigma q) :
    D.family.coboundary1 i.succ (cqComponentTotal A sigma q) p =
      (extendWordLinear (Lq.syndromeRegion q)
        (A.contract.rx_local_complexes.cqDelta1 q
          (cqWitnessAt A sigma q h)) p +
        A.contract.support_decomposition.cqFlow q
          (cqWitnessAt A sigma q h) p) := by
  classical
  simp only [cqComponentTotal, dif_pos h]
  exact congrFun
    (A.contract.support_decomposition.cqDelta1_decomposition q
      (cqWitnessAt A sigma q h)) p

theorem rx_cq_component_boundary_apply_of_not_range
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) (p : C2 i.succ)
    (h : ¬ CqLocalRangeAt A sigma q) :
    D.family.coboundary1 i.succ (cqComponentTotal A sigma q) p = 0 := by
  classical
  simp [cqComponentTotal, h]

theorem rx_cx_component_boundary_eq_at_q
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (q : Q) (x : X)
    (p : C2 i.succ) (hpq : p ∈ Lq.syndromeRegion q)
    (hAgree : rxSignalAgreementWithin A (Sum.inr (Sum.inl q)) 1 sigma tau) :
    D.family.coboundary1 i.succ (cxComponentTotal A sigma x) p =
      D.family.coboundary1 i.succ (cxComponentTotal A tau x) p := by
  classical
  have hpTop : A.topCenter p = Sum.inr (Sum.inl q) :=
    (A.topCenter_q_iff q p).1 hpq
  have hpXnot : p ∉ Lx.syndromeRegion x := by
    intro hpx
    have hxTop := (A.topCenter_x_iff x p).1 hpx
    have hbad : Sum.inl x = Sum.inr (Sum.inl q) := hxTop.symm.trans hpTop
    cases hbad
  by_cases hDist : DirectedGraph.distance A.levelGraph.graph
      (Sum.inl x) (Sum.inr (Sum.inl q)) ≤ 1
  · have hRestr' := rx_restrict_eq_of_agreement A sigma tau
      (Sum.inr (Sum.inl q)) 1 hAgree (Sum.inl x) hDist
    have hRestr : restrictWordLinear (Lx.syndromeRegion x) sigma =
        restrictWordLinear (Lx.syndromeRegion x) tau := by
      exact hRestr'
    by_cases hσ : CxLocalRangeAt A sigma x
    · have hτ : CxLocalRangeAt A tau x := by
        simpa [CxLocalRangeAt, hRestr] using hσ
      have hw := cxWitnessAt_eq_of_restrict_eq A sigma tau x hσ hτ hRestr
      rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
        rx_cx_component_boundary_apply_of_range A tau x p hτ]
      have hzero : ∀ (w : Word Field (LocalRegionIndex (Lx.correctionRegion x))),
          extendWordLinear (Lx.syndromeRegion x)
            (A.contract.rx_local_complexes.cxDelta1 x w) p = 0 := by
        intro w
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      rw [hzero, hzero, hw]
    · have hτ : ¬ CxLocalRangeAt A tau x := by
        intro hτ
        apply hσ
        simpa [CxLocalRangeAt, hRestr] using hτ
      rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
        rx_cx_component_boundary_apply_of_not_range A tau x p hτ]
  · have hflow_zero : ∀ (s : D.family.Cochain2 i.succ)
        (hs : CxLocalRangeAt A s x),
        A.contract.support_decomposition.cxFlow x
          (cxWitnessAt A s x hs) p = 0 := by
      intro s hs
      by_contra hne
      have hd := A.cxFlow_radius_one x (cxWitnessAt A s x hs) p hne
      apply hDist
      simpa [hpTop] using hd
    by_cases hσ : CxLocalRangeAt A sigma x
    · by_cases hτ : CxLocalRangeAt A tau x
      · rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_range A tau x p hτ,
          hflow_zero sigma hσ, hflow_zero tau hτ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      · rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_not_range A tau x p hτ,
          hflow_zero sigma hσ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
    · by_cases hτ : CxLocalRangeAt A tau x
      · rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_range A tau x p hτ,
          hflow_zero tau hτ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      · rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_not_range A tau x p hτ]

theorem rx_cx_component_boundary_eq_at_center
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (x : X)
    (p : C2 i.succ) (center : RXVertex X Q Z) (radius : Nat)
    (hpXnot : p ∉ Lx.syndromeRegion x)
    (hTop : A.topCenter p = center)
    (hRadiusOne : (1 : WithTop Nat) ≤ radius)
    (hAgree : rxSignalAgreementWithin A center radius sigma tau) :
    D.family.coboundary1 i.succ (cxComponentTotal A sigma x) p =
      D.family.coboundary1 i.succ (cxComponentTotal A tau x) p := by
  classical
  by_cases hDist : DirectedGraph.distance A.levelGraph.graph
      (Sum.inl x) center ≤ radius
  · have hRestr' := rx_restrict_eq_of_agreement A sigma tau
      center radius hAgree (Sum.inl x) hDist
    have hRestr : restrictWordLinear (Lx.syndromeRegion x) sigma =
        restrictWordLinear (Lx.syndromeRegion x) tau := by
      exact hRestr'
    by_cases hσ : CxLocalRangeAt A sigma x
    · have hτ : CxLocalRangeAt A tau x := by
        simpa [CxLocalRangeAt, hRestr] using hσ
      have hw := cxWitnessAt_eq_of_restrict_eq A sigma tau x hσ hτ hRestr
      rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
        rx_cx_component_boundary_apply_of_range A tau x p hτ]
      have hzero : ∀ (w : Word Field (LocalRegionIndex (Lx.correctionRegion x))),
          extendWordLinear (Lx.syndromeRegion x)
            (A.contract.rx_local_complexes.cxDelta1 x w) p = 0 := by
        intro w
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      rw [hzero, hzero, hw]
    · have hτ : ¬ CxLocalRangeAt A tau x := by
        intro hτ
        apply hσ
        simpa [CxLocalRangeAt, hRestr] using hτ
      rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
        rx_cx_component_boundary_apply_of_not_range A tau x p hτ]
  · have hflow_zero : ∀ (s : D.family.Cochain2 i.succ)
        (hs : CxLocalRangeAt A s x),
        A.contract.support_decomposition.cxFlow x
          (cxWitnessAt A s x hs) p = 0 := by
      intro s hs
      by_contra hne
      have hd := A.cxFlow_radius_one x (cxWitnessAt A s x hs) p hne
      apply hDist
      rw [hTop] at hd
      exact hd.trans hRadiusOne
    by_cases hσ : CxLocalRangeAt A sigma x
    · by_cases hτ : CxLocalRangeAt A tau x
      · rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_range A tau x p hτ,
          hflow_zero sigma hσ, hflow_zero tau hτ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      · rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_not_range A tau x p hτ,
          hflow_zero sigma hσ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
    · by_cases hτ : CxLocalRangeAt A tau x
      · rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_range A tau x p hτ,
          hflow_zero tau hτ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      · rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_not_range A tau x p hτ]

theorem rx_cx_component_boundary_eq_at_q_center
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (q : Q) (x : X)
    (p : C2 i.succ) (hpq : p ∈ Lq.syndromeRegion q)
    (center : RXVertex X Q Z)
    (hQOne : DirectedGraph.distance A.levelGraph.graph
      (Sum.inr (Sum.inl q)) center ≤ 1)
    (hAgree : rxSignalAgreementWithin A center 2 sigma tau) :
    D.family.coboundary1 i.succ (cxComponentTotal A sigma x) p =
      D.family.coboundary1 i.succ (cxComponentTotal A tau x) p := by
  classical
  have hpTop : A.topCenter p = Sum.inr (Sum.inl q) :=
    (A.topCenter_q_iff q p).1 hpq
  have hpXnot : p ∉ Lx.syndromeRegion x := by
    intro hpx
    have hxTop := (A.topCenter_x_iff x p).1 hpx
    have hbad : Sum.inl x = Sum.inr (Sum.inl q) := hxTop.symm.trans hpTop
    cases hbad
  by_cases hDist : DirectedGraph.distance A.levelGraph.graph
      (Sum.inl x) (Sum.inr (Sum.inl q)) ≤ 1
  · have hDistCenter : DirectedGraph.distance A.levelGraph.graph
        (Sum.inl x) center ≤ 2 :=
      A.distance_one_comp (Sum.inl x) (Sum.inr (Sum.inl q)) center
        hDist hQOne
    have hRestr' := rx_restrict_eq_of_agreement A sigma tau center 2
      hAgree (Sum.inl x) hDistCenter
    have hRestr : restrictWordLinear (Lx.syndromeRegion x) sigma =
        restrictWordLinear (Lx.syndromeRegion x) tau := by
      exact hRestr'
    by_cases hσ : CxLocalRangeAt A sigma x
    · have hτ : CxLocalRangeAt A tau x := by
        simpa [CxLocalRangeAt, hRestr] using hσ
      have hw := cxWitnessAt_eq_of_restrict_eq A sigma tau x hσ hτ hRestr
      rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
        rx_cx_component_boundary_apply_of_range A tau x p hτ]
      have hzero : ∀ (w : Word Field (LocalRegionIndex (Lx.correctionRegion x))),
          extendWordLinear (Lx.syndromeRegion x)
            (A.contract.rx_local_complexes.cxDelta1 x w) p = 0 := by
        intro w
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      rw [hzero, hzero, hw]
    · have hτ : ¬ CxLocalRangeAt A tau x := by
        intro hτ
        apply hσ
        simpa [CxLocalRangeAt, hRestr] using hτ
      rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
        rx_cx_component_boundary_apply_of_not_range A tau x p hτ]
  · have hflow_zero : ∀ (s : D.family.Cochain2 i.succ)
        (hs : CxLocalRangeAt A s x),
        A.contract.support_decomposition.cxFlow x
          (cxWitnessAt A s x hs) p = 0 := by
      intro s hs
      by_contra hne
      have hd := A.cxFlow_radius_one x (cxWitnessAt A s x hs) p hne
      apply hDist
      simpa [hpTop] using hd
    by_cases hσ : CxLocalRangeAt A sigma x
    · by_cases hτ : CxLocalRangeAt A tau x
      · rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_range A tau x p hτ,
          hflow_zero sigma hσ, hflow_zero tau hτ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      · rw [rx_cx_component_boundary_apply_of_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_not_range A tau x p hτ,
          hflow_zero sigma hσ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
    · by_cases hτ : CxLocalRangeAt A tau x
      · rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_range A tau x p hτ,
          hflow_zero tau hτ]
        simp [extendWordLinear, extendLocalSignal, hpXnot]
      · rw [rx_cx_component_boundary_apply_of_not_range A sigma x p hσ,
          rx_cx_component_boundary_apply_of_not_range A tau x p hτ]

theorem rx_cx_component_invariant
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) :
    cxComponentTotal A sigma x =
      cxComponentTotal A (rxXiSignal A sigma (Sum.inl x) 1) x := by
  let tau := rxXiSignal A sigma (Sum.inl x) 1
  have hSelf : DirectedGraph.distance A.levelGraph.graph
      (Sum.inl x) (Sum.inl x) ≤ 1 := by
    rw [rx_distance_self]
    simp
  have hAgree := rxXiSignal_agrees A sigma (Sum.inl x) 1
  have hRestr : restrictWordLinear (Lx.syndromeRegion x) sigma =
      restrictWordLinear (Lx.syndromeRegion x) tau := by
    exact
      (rx_restrict_eq_of_agreement A sigma tau (Sum.inl x) 1 hAgree
        (Sum.inl x) hSelf)
  by_cases h : CxLocalRangeAt A sigma x
  · have h' : CxLocalRangeAt A tau x := by
      simpa [CxLocalRangeAt, hRestr] using h
    have h'' : CxLocalRangeAt A (rxXiSignal A sigma (Sum.inl x) 1) x := by
      simpa [tau] using h'
    simp only [cxComponentTotal, dif_pos h, dif_pos h'']
    congr 1
    unfold cxWitnessAt
    let Pσ : Word Field (LocalRegionIndex (Lx.correctionRegion x)) → Prop :=
      fun f => A.contract.rx_local_complexes.cxDelta1 x f =
          restrictWordLinear (Lx.syndromeRegion x) sigma ∧
        HammingWeight (A.contract.support_decomposition.cxFlow x f) ≤
          HammingWeight (restrictWordLinear (Lx.syndromeRegion x) sigma)
    let Pτ : Word Field (LocalRegionIndex (Lx.correctionRegion x)) → Prop :=
      fun f => A.contract.rx_local_complexes.cxDelta1 x f =
          restrictWordLinear (Lx.syndromeRegion x) tau ∧
        HammingWeight (A.contract.support_decomposition.cxFlow x f) ≤
          HammingWeight (restrictWordLinear (Lx.syndromeRegion x) tau)
    have hPred : Pσ = Pτ := by
      funext f
      dsimp [Pσ, Pτ]
      rw [hRestr]
    have hChoose : ∀ (eσ : ∃ f, Pσ f) (eτ : ∃ f, Pτ f),
        @Classical.choose _ Pσ eσ = @Classical.choose _ Pτ eτ := by
      rw [hPred]
      intro eσ eτ
      rfl
    have eσ : ∃ f, Pσ f := by
      simpa [Pσ] using
        (A.contract.local_boundary_weight_budgets.cx x
          (restrictWordLinear (Lx.syndromeRegion x) sigma) h)
    have eτ : ∃ f, Pτ f := by
      simpa [Pτ] using
        (A.contract.local_boundary_weight_budgets.cx x
          (restrictWordLinear (Lx.syndromeRegion x)
            (rxXiSignal A sigma (Sum.inl x) 1)) h'')
    simpa [Pσ, Pτ] using hChoose eσ eτ
  · have h' : ¬ CxLocalRangeAt A tau x := by
      intro h'
      apply h
      simpa [CxLocalRangeAt, hRestr] using h'
    simp [cxComponentTotal, h, h', tau]

theorem rx_q_cleaned_restrict_eq
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (q : Q)
    (hAgree : rxSignalAgreementWithin A (Sum.inr (Sum.inl q)) 1 sigma tau) :
    restrictWordLinear (Lq.syndromeRegion q) (rxSigmaAfterCx A sigma) =
      restrictWordLinear (Lq.syndromeRegion q) (rxSigmaAfterCx A tau) := by
  classical
  funext u
  change rxSigmaAfterCx A sigma u.1 = rxSigmaAfterCx A tau u.1
  have hpq : u.1 ∈ Lq.syndromeRegion q := u.property
  have hcx : D.family.coboundary1 i.succ (cxCorrectionTotal A sigma) u.1 =
      D.family.coboundary1 i.succ (cxCorrectionTotal A tau) u.1 := by
    rw [show cxCorrectionTotal A sigma =
          ∑ x : X, cxComponentTotal A sigma x by rfl,
      show cxCorrectionTotal A tau =
          ∑ x : X, cxComponentTotal A tau x by rfl,
      map_sum, map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro x hx
    exact rx_cx_component_boundary_eq_at_q A sigma tau q x u.1 hpq hAgree
  have hpTop : A.topCenter u.1 = Sum.inr (Sum.inl q) :=
    (A.topCenter_q_iff q u.1).1 hpq
  have hdist : DirectedGraph.distance A.levelGraph.graph
      (A.topCenter u.1) (Sum.inr (Sum.inl q)) ≤ 1 := by
    rw [hpTop, rx_distance_self]
    simp
  have hsigma := hAgree u.1 hdist
  simp [rxSigmaAfterCx, Pi.add_apply, hsigma, hcx]

theorem rx_q_component_invariant
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) :
    cqComponentTotal A sigma q =
      cqComponentTotal A
        (rxXiSignal A sigma (Sum.inr (Sum.inl q)) 1) q := by
  let tau := rxXiSignal A sigma (Sum.inr (Sum.inl q)) 1
  have hAgree := rxXiSignal_agrees A sigma (Sum.inr (Sum.inl q)) 1
  have hRestr := rx_q_cleaned_restrict_eq A sigma tau q hAgree
  by_cases h : CqLocalRangeAt A sigma q
  · have h' : CqLocalRangeAt A tau q := by
      have hs : restrictWordLinear (Lq.syndromeRegion q)
          (rxSigmaAfterCx A sigma) ∈
          LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q) := by
        simpa [CqLocalRangeAt, rxSigmaAfterCx] using h
      change restrictWordLinear (Lq.syndromeRegion q)
          (rxSigmaAfterCx A tau) ∈
          LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)
      rw [← hRestr]
      exact hs
    have h'' : CqLocalRangeAt A
        (rxXiSignal A sigma (Sum.inr (Sum.inl q)) 1) q := by
      simpa [tau] using h'
    simp only [cqComponentTotal, dif_pos h, dif_pos h'']
    congr 1
    exact cqWitnessAt_eq_of_cleaned_restrict_eq A sigma tau q h h' hRestr
  · have h' : ¬ CqLocalRangeAt A tau q := by
      intro h'
      apply h
      have ht : restrictWordLinear (Lq.syndromeRegion q)
          (rxSigmaAfterCx A tau) ∈
          LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q) := by
        simpa [CqLocalRangeAt, rxSigmaAfterCx] using h'
      have hs := ht
      rw [← hRestr] at hs
      simpa [CqLocalRangeAt, rxSigmaAfterCx] using hs
    simp [cqComponentTotal, h, h', tau]

theorem rx_q_cleaned_restrict_eq_at_center
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (q : Q)
    (center : RXVertex X Q Z)
    (hQOne : DirectedGraph.distance A.levelGraph.graph
      (Sum.inr (Sum.inl q)) center ≤ 1)
    (hAgree : rxSignalAgreementWithin A center 2 sigma tau) :
    restrictWordLinear (Lq.syndromeRegion q) (rxSigmaAfterCx A sigma) =
      restrictWordLinear (Lq.syndromeRegion q) (rxSigmaAfterCx A tau) := by
  classical
  funext u
  change rxSigmaAfterCx A sigma u.1 = rxSigmaAfterCx A tau u.1
  have hpq : u.1 ∈ Lq.syndromeRegion q := u.property
  have hpTop : A.topCenter u.1 = Sum.inr (Sum.inl q) :=
    (A.topCenter_q_iff q u.1).1 hpq
  have hdist : DirectedGraph.distance A.levelGraph.graph
      (A.topCenter u.1) center ≤ 2 := by
    rw [hpTop]
    exact hQOne.trans (by norm_num)
  have hsigma := hAgree u.1 hdist
  have hcx : D.family.coboundary1 i.succ (cxCorrectionTotal A sigma) u.1 =
      D.family.coboundary1 i.succ (cxCorrectionTotal A tau) u.1 := by
    rw [show cxCorrectionTotal A sigma =
          ∑ x : X, cxComponentTotal A sigma x by rfl,
      show cxCorrectionTotal A tau =
          ∑ x : X, cxComponentTotal A tau x by rfl,
      map_sum, map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro x hx
    exact rx_cx_component_boundary_eq_at_q_center A sigma tau q x u.1 hpq
      center hQOne hAgree
  simp [rxSigmaAfterCx, Pi.add_apply, hsigma, hcx]

theorem rx_cq_component_boundary_eq_at_center
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (q : Q)
    (p : C2 i.succ) (center : RXVertex X Q Z)
    (hpQnot : p ∉ Lq.syndromeRegion q)
    (hTop : A.topCenter p = center)
    (hAgree : rxSignalAgreementWithin A center 2 sigma tau) :
    D.family.coboundary1 i.succ (cqComponentTotal A sigma q) p =
      D.family.coboundary1 i.succ (cqComponentTotal A tau q) p := by
  classical
  by_cases hQOne : DirectedGraph.distance A.levelGraph.graph
      (Sum.inr (Sum.inl q)) center ≤ 1
  · have hRestr := rx_q_cleaned_restrict_eq_at_center A sigma tau q center
      hQOne hAgree
    by_cases hσ : CqLocalRangeAt A sigma q
    · have hτ : CqLocalRangeAt A tau q := by
        have hs : restrictWordLinear (Lq.syndromeRegion q)
            (rxSigmaAfterCx A sigma) ∈
            LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q) := by
          simpa [CqLocalRangeAt, rxSigmaAfterCx] using hσ
        change restrictWordLinear (Lq.syndromeRegion q)
            (rxSigmaAfterCx A tau) ∈
            LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)
        rw [← hRestr]
        exact hs
      have hw := cqWitnessAt_eq_of_cleaned_restrict_eq A sigma tau q hσ hτ hRestr
      rw [rx_cq_component_boundary_apply_of_range A sigma q p hσ,
        rx_cq_component_boundary_apply_of_range A tau q p hτ]
      have hzero : ∀ (w : Word Field (LocalRegionIndex (Lq.correctionRegion q))),
          extendWordLinear (Lq.syndromeRegion q)
            (A.contract.rx_local_complexes.cqDelta1 q w) p = 0 := by
        intro w
        simp [extendWordLinear, extendLocalSignal, hpQnot]
      rw [hzero, hzero, hw]
    · have hτ : ¬ CqLocalRangeAt A tau q := by
        intro hτ
        apply hσ
        have ht : restrictWordLinear (Lq.syndromeRegion q)
            (rxSigmaAfterCx A tau) ∈
            LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q) := by
          simpa [CqLocalRangeAt, rxSigmaAfterCx] using hτ
        rw [← hRestr] at ht
        simpa [CqLocalRangeAt, rxSigmaAfterCx] using ht
      rw [rx_cq_component_boundary_apply_of_not_range A sigma q p hσ,
        rx_cq_component_boundary_apply_of_not_range A tau q p hτ]
  · have hflow_zero : ∀ (s : D.family.Cochain2 i.succ)
        (hs : CqLocalRangeAt A s q),
        A.contract.support_decomposition.cqFlow q
          (cqWitnessAt A s q hs) p = 0 := by
      intro s hs
      by_contra hne
      have hd := A.cqFlow_radius_one q (cqWitnessAt A s q hs) p hne
      apply hQOne
      rw [hTop] at hd
      exact hd
    by_cases hσ : CqLocalRangeAt A sigma q
    · by_cases hτ : CqLocalRangeAt A tau q
      · rw [rx_cq_component_boundary_apply_of_range A sigma q p hσ,
          rx_cq_component_boundary_apply_of_range A tau q p hτ,
          hflow_zero sigma hσ, hflow_zero tau hτ]
        simp [extendWordLinear, extendLocalSignal, hpQnot]
      · rw [rx_cq_component_boundary_apply_of_range A sigma q p hσ,
          rx_cq_component_boundary_apply_of_not_range A tau q p hτ,
          hflow_zero sigma hσ]
        simp [extendWordLinear, extendLocalSignal, hpQnot]
    · by_cases hτ : CqLocalRangeAt A tau q
      · rw [rx_cq_component_boundary_apply_of_not_range A sigma q p hσ,
          rx_cq_component_boundary_apply_of_range A tau q p hτ,
          hflow_zero tau hτ]
        simp [extendWordLinear, extendLocalSignal, hpQnot]
      · rw [rx_cq_component_boundary_apply_of_not_range A sigma q p hσ,
          rx_cq_component_boundary_apply_of_not_range A tau q p hτ]

theorem rx_coarse_word_invariant_at_center
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (z : C2 i.castSucc) :
    rxCoarseWord A sigma z =
      rxCoarseWord A (rxXiSignal A sigma (A.coarseCenter z) 2) z := by
  classical
  let tau := rxXiSignal A sigma (A.coarseCenter z) 2
  let p₀ := (A.induced.zPairEquiv (z, 0)).1
  have hTop : A.topCenter p₀ = A.coarseCenter z := by
    simpa [p₀] using A.topCenter_coarse_pair z 0
  have hAgree := rxXiSignal_agrees A sigma (A.coarseCenter z) 2
  have hSigmaP : sigma p₀ = tau p₀ := by
    apply hAgree p₀
    rw [hTop, rx_distance_self]
    simp
  have hCxBoundary :
      D.family.coboundary1 i.succ (cxCorrectionTotal A sigma) p₀ =
        D.family.coboundary1 i.succ (cxCorrectionTotal A tau) p₀ := by
    rw [show cxCorrectionTotal A sigma =
          ∑ x : X, cxComponentTotal A sigma x by rfl,
      show cxCorrectionTotal A tau =
          ∑ x : X, cxComponentTotal A tau x by rfl,
      map_sum, map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro x hx
    have hpXnot : p₀ ∉ Lx.syndromeRegion x := by
      intro hpx
      have hxTop := (A.topCenter_x_iff x p₀).1 hpx
      obtain ⟨z₀, hz₀⟩ := A.coarseCenter_is_z z
      have hbad : Sum.inl x = Sum.inr (Sum.inr z₀) :=
        hxTop.symm.trans (hTop.trans hz₀)
      cases hbad
    exact rx_cx_component_boundary_eq_at_center A sigma tau x p₀
      (A.coarseCenter z) 2 hpXnot hTop (by norm_num) hAgree
  have hAfterCx : rxSigmaAfterCx A sigma p₀ = rxSigmaAfterCx A tau p₀ := by
    simp [rxSigmaAfterCx, hSigmaP, hCxBoundary]
  have hCqBoundary :
      D.family.coboundary1 i.succ (cqCorrectionTotal A sigma) p₀ =
        D.family.coboundary1 i.succ (cqCorrectionTotal A tau) p₀ := by
    rw [show cqCorrectionTotal A sigma =
          ∑ q : Q, cqComponentTotal A sigma q by rfl,
      show cqCorrectionTotal A tau =
          ∑ q : Q, cqComponentTotal A tau q by rfl,
      map_sum, map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro q hq
    have hpQnot : p₀ ∉ Lq.syndromeRegion q := by
      intro hpq
      have hqTop := (A.topCenter_q_iff q p₀).1 hpq
      obtain ⟨z₀, hz₀⟩ := A.coarseCenter_is_z z
      have hbad : Sum.inr (Sum.inl q) = Sum.inr (Sum.inr z₀) :=
        hqTop.symm.trans (hTop.trans hz₀)
      cases hbad
    exact rx_cq_component_boundary_eq_at_center A sigma tau q p₀
      (A.coarseCenter z) hpQnot hTop hAgree
  have hAfterCq : rxSigmaAfterCq A sigma p₀ = rxSigmaAfterCq A tau p₀ := by
    simp [rxSigmaAfterCq, hAfterCx, hCqBoundary]
  change rxSigmaAfterCq A sigma p₀ = rxSigmaAfterCq A tau p₀
  exact hAfterCq

theorem rx_total_correction_decomposition
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    ∀ sigma, rxCorrectionTotal A sigma =
      LocalCorrectionComponents.totalCorrection (rxLocalComponents A) sigma := by
  intro sigma
  rw [rx_total_eq_components]
  unfold LocalCorrectionComponents.totalCorrection
  ext p
  simp [rxLocalComponents, Fintype.sum_sum_type]

theorem rx_component_supported
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    LocalComputabilityInterface.componentSupported (rxLocalInterface A) := by
  intro v sigma p hp
  cases v with
  | inl x => exact cxComponentTotal_supported A sigma x p hp
  | inr v =>
      cases v with
      | inl q => exact cqComponentTotal_supported A sigma q p hp
      | inr z =>
          change (0 : D.family.Correction i.succ) p = 0
          rfl

theorem rx_masked_total_correction_eq_component
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    LocalComputabilityInterface.maskedTotalCorrectionEqComponent
      (rxLocalInterface A) := by
  intro v sigma
  unfold LocalCorrectionComponents.totalCorrection
  have hfun :
      (∑ x : X, cxComponentTotal A sigma x) +
          ∑ q : Q, cqComponentTotal A sigma q =
        (fun p => ∑ x : X, cxComponentTotal A sigma x p +
          ∑ q : Q, cqComponentTotal A sigma q p) := by
    ext p
    simp [Finset.sum_apply]
  cases v with
  | inl x =>
      have hx := rx_mask_total_at_x A sigma x
      rw [rx_total_eq_components A sigma] at hx
      rw [hfun] at hx
      simpa [rxLocalInterface, rxLocalComponents, rxXiLocalComplex,
        Finset.sum_apply] using
        hx
  | inr v =>
      cases v with
      | inl q =>
          have hq := rx_mask_total_at_q A sigma q
          rw [rx_total_eq_components A sigma] at hq
          rw [hfun] at hq
          simpa [rxLocalInterface, rxLocalComponents, rxXiLocalComplex,
            Finset.sum_apply] using
            hq
      | inr z =>
          ext p
          simp [rxLocalInterface, rxLocalComponents, rxXiLocalComplex, maskWord]

theorem rx_local_computability_certificate
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    RXLocalComputabilityCertificate A := by
  refine
    { totalCorrectionDecomposition := ?_
      componentSupported := ?_
      maskedTotalCorrectionEqComponent := ?_
      componentInvariantAtXiOne := ?_
      coarseCoordinateInvariantAtXiTwo := ?_ }
  · intro sigma
    exact rx_total_correction_decomposition A sigma
  · exact rx_component_supported A
  · exact rx_masked_total_correction_eq_component A
  · intro v sigma
    cases v with
    | inl x => exact rx_cx_component_invariant A sigma x
    | inr v =>
        cases v with
        | inl q => exact rx_q_component_invariant A sigma q
        | inr z => rfl
  · intro z sigma
    exact rx_coarse_word_invariant_at_center A sigma z

theorem rx_coarse_graining_odd
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (sigma : D.family.Syndrome i.succ) :
    ∃ sigma' : D.family.Syndrome i.castSucc,
      ∃ correction : D.family.Correction i.succ,
        (sigma' : D.family.Cochain2 i.castSucc) =
            rxCoarseWord A (sigma : D.family.Cochain2 i.succ) ∧
        correction = rxCorrectionTotal A (sigma : D.family.Cochain2 i.succ) ∧
        (sigma : D.family.Cochain2 i.succ) =
            D.family.coboundary1 i.succ correction +
              (D.selectedMap i).map2 sigma' ∧
        2 * HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) ∧
        HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) / 2 ∧
        SupportedOn A.zSector ((D.selectedMap i).map2 sigma') ∧
        (∀ p ∈ A.xSector, ((D.selectedMap i).map2 sigma') p = 0) ∧
        (∀ p ∈ A.qSector, ((D.selectedMap i).map2 sigma') p = 0) := by
  classical
  let hCxLocal := A.contract.cx_local_ranges_of_syndrome sigma
  let cxCorrection := cxCorrectionRG A sigma.1 hCxLocal
  let sigma₁ := sigma.1 + D.family.coboundary1 i.succ cxCorrection
  have hCx := cx_cleaning_explicit A sigma
  have hSigma₁Weight : HammingWeight sigma₁ ≤ HammingWeight sigma.1 := by
    simpa [sigma₁, cxCorrection] using hCx.1
  have hSigma₁X : ∀ p ∈ A.xSector, sigma₁ p = 0 := by
    simpa [sigma₁, cxCorrection] using hCx.2
  obtain ⟨error, hError⟩ := sigma.property
  let error₁ := error + cxCorrection
  have hError₁ : D.family.coboundary1 i.succ error₁ = sigma₁ := by
    dsimp [error₁, sigma₁]
    rw [map_add, hError]
  have hCxCocycle : ∀ x,
      A.contract.rx_local_complexes.cxDelta1 x
        (restrictWordLinear (Lx.correctionRegion x) error₁) = 0 := by
    intro x
    have hz : restrictWordLinear (Lx.syndromeRegion x)
        (D.family.coboundary1 i.succ error₁) = 0 := by
      funext j
      have hj : (j : C2 i.succ) ∈ A.xSector := by
        apply xSector_mem_of_region A
        exact Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, j.property⟩
      change D.family.coboundary1 i.succ error₁ j.1 = 0
      rw [hError₁]
      exact hSigma₁X j.1 hj
    rw [← A.contract.support_decomposition.cxDelta1_restriction_global x error₁]
    exact hz
  obtain ⟨stabilizers, hStabilizers⟩ :=
    A.contract.cx_error_cleaning_all error₁ hCxCocycle
  let stabilizerCorrection : D.family.Correction i.succ :=
    D.family.coboundary0 i.succ
      (∑ x : X, A.contract.support_decomposition.cxLift0 x (stabilizers x))
  have hStabilizerZero : D.family.coboundary1 i.succ stabilizerCorrection = 0 := by
    dsimp [stabilizerCorrection]
    have hcomp := BDL26CochainFamily.coboundary1_comp_coboundary0
      D.family i.succ
    have hcomp' := LinearMap.congr_fun hcomp
      (∑ x : X, A.contract.support_decomposition.cxLift0 x (stabilizers x))
    simpa [LinearMap.comp_apply] using hcomp'
  let error₂ := error₁ + stabilizerCorrection
  have hError₂X : ∀ p ∈ correctionRegionUnion Lx, error₂ p = 0 := by
    intro p hp
    rcases Finset.mem_biUnion.1 hp with ⟨x, hx, hpx⟩
    have hlocal := hStabilizers x
    have hlocal' := congrFun hlocal ⟨p, hpx⟩
    exact hlocal'
  have hError₂ : D.family.coboundary1 i.succ error₂ = sigma₁ := by
    dsimp [error₂, stabilizerCorrection]
    rw [map_add]
    rw [hStabilizerZero, add_zero, hError₁]
  have hError₂Supported : SupportedOn A.qCorrectionSector error₂ := by
    intro p hp
    have hcover : p ∈ correctionRegionUnion Lx ∪ A.qCorrectionSector := by
      rw [A.correction_sectors_cover]
      exact Finset.mem_univ p
    have hpX : p ∈ correctionRegionUnion Lx := by
      rcases (by simpa only [Finset.mem_union] using hcover) with hpX | hpQ
      · exact hpX
      · exact (hp hpQ).elim
    exact hError₂X p hpX
  have hError₂XRestrictions : ∀ x,
      restrictWordLinear (Lx.correctionRegion x) error₂ = 0 := by
    intro x
    funext p
    exact hError₂X p.1 (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.2⟩)
  let hCqLocalRaw := A.contract.cq_local_ranges_of_error error₂ hError₂XRestrictions
  have hCqLocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma₁ ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q) := by
    intro q
    rw [← hError₂]
    exact hCqLocalRaw q
  let cqCorrection := cqCorrectionRG A sigma₁ hCqLocal
  let sigma₂ := sigma₁ + D.family.coboundary1 i.succ cqCorrection
  have hCq := cq_cleaning_explicit A sigma₁ hCqLocal hSigma₁X
  have hSigma₂Weight : HammingWeight sigma₂ ≤ HammingWeight sigma₁ := by
    simpa [sigma₂, cqCorrection] using hCq.1
  have hSigma₂X : ∀ p ∈ A.xSector, sigma₂ p = 0 := by
    simpa [sigma₂, cqCorrection] using hCq.2.2
  have hSigma₂Q : ∀ p ∈ A.qSector, sigma₂ p = 0 := by
    simpa [sigma₂, cqCorrection] using hCq.2.1
  let error₃ := error₂ + cqCorrection
  have hError₃ : D.family.coboundary1 i.succ error₃ = sigma₂ := by
    dsimp [error₃, sigma₂]
    rw [map_add, hError₂]
  have hError₃Supported : SupportedOn A.qCorrectionSector error₃ := by
    intro p hp
    change error₂ p + cqCorrectionRG A sigma₁ hCqLocal p = 0
    rw [hError₂Supported p hp,
      cqCorrectionRG_supported A sigma₁ hCqLocal p hp, zero_add]
  have hError₃XRestrictions : ∀ x,
      restrictWordLinear (Lx.correctionRegion x) error₃ = 0 := by
    intro x
    funext p
    apply hError₃Supported p.1
    intro hpQ
    exact Finset.disjoint_left.mp A.correction_sectors_disjoint
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.2⟩) hpQ
  have hError₃CqCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error₃) = 0 := by
    intro q
    have hz : restrictWordLinear (Lq.syndromeRegion q)
        (D.family.coboundary1 i.succ error₃) = 0 := by
      funext j
      have hj : (j : C2 i.succ) ∈ A.qSector := by
        apply qSector_mem_of_region A
        exact Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, j.property⟩
      change D.family.coboundary1 i.succ error₃ j.1 = 0
      rw [hError₃]
      exact hSigma₂Q j.1 hj
    rw [← A.contract.support_decomposition.cqDelta1_restriction_global q error₃ hError₃XRestrictions]
    exact hz
  have hError₃SupportedOnRegions :
      SupportedOn (correctionRegionUnion Lq) error₃ := by
    intro p hp
    apply hError₃Supported p
    simpa [A.qCorrectionSector_eq_regions] using hp
  have hError₃Decomposition :
      error₃ = ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        (restrictWordLinear (Lq.correctionRegion q) error₃) := by
    rw [extend_restrict_sum_eq_mask
      (fun q => Lq.correctionRegion q)
      A.cq_correction_regions_pairwise_disjoint error₃]
    funext p
    by_cases hp : p ∈ correctionRegionUnion Lq
    · change error₃ p = if p ∈ correctionRegionUnion Lq then error₃ p else 0
      rw [if_pos hp]
    · change error₃ p = if p ∈ correctionRegionUnion Lq then error₃ p else 0
      rw [if_neg hp]
      exact hError₃SupportedOnRegions p hp
  let qClasses := qCohomologyClass A error₃ hError₃CqCocycle
  have hRepresentativeDifference : ∀ q, ∃ s : Word Field (Q0 q),
      A.contract.rx_local_complexes.cqDelta0 q s =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error₃ := by
    intro q
    exact cqRepresentative_difference_exists A error₃ hError₃CqCocycle q
  let cqStabilizers : ∀ q, Word Field (Q0 q) :=
    fun q => Classical.choose (hRepresentativeDifference q)
  have hCqStabilizers : ∀ q,
      A.contract.rx_local_complexes.cqDelta0 q (cqStabilizers q) =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error₃ := by
    intro q
    exact Classical.choose_spec (hRepresentativeDifference q)
  let lowerCorrection := A.qCohomologyEquiv qClasses
  let qStabilizerCorrection : D.family.Correction i.succ :=
    D.family.coboundary0 i.succ
      (∑ q : Q, A.contract.support_decomposition.cqLift0 q
        (cqStabilizers q))
  let error₄ := error₃ + qStabilizerCorrection
  have hQStabilizerZero :
      D.family.coboundary1 i.succ qStabilizerCorrection = 0 := by
    dsimp [qStabilizerCorrection]
    have hcomp := BDL26CochainFamily.coboundary1_comp_coboundary0
      D.family i.succ
    have hcomp' := LinearMap.congr_fun hcomp
      (∑ q : Q, A.contract.support_decomposition.cqLift0 q
        (cqStabilizers q))
    simpa [LinearMap.comp_apply] using hcomp'
  have hError₄ : D.family.coboundary1 i.succ error₄ = sigma₂ := by
    dsimp [error₄]
    rw [map_add, hQStabilizerZero, add_zero, hError₃]
  have hRepresentativeSum :
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        ((A.cqRepresentative q (qClasses q)).1)) = error₄ := by
    calc
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
          ((A.cqRepresentative q (qClasses q)).1)) =
        ∑ q : Q, (extendWordLinear (Lq.correctionRegion q)
          (restrictWordLinear (Lq.correctionRegion q) error₃) +
          extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (cqStabilizers q))) := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqdiff := hCqStabilizers q
            have hqrep :
                (A.cqRepresentative q (qClasses q)).1 =
                  restrictWordLinear (Lq.correctionRegion q) error₃ +
                    A.contract.rx_local_complexes.cqDelta0 q
                      (cqStabilizers q) := by
              have hrr :
                  restrictWordLinear (Lq.correctionRegion q) error₃ +
                      restrictWordLinear (Lq.correctionRegion q) error₃ =
                    (0 : Word Field (LocalRegionIndex (Lq.correctionRegion q))) := by
                ext p
                exact ZModModule.add_self _
              calc
                (A.cqRepresentative q (qClasses q)).1 =
                    ((A.cqRepresentative q (qClasses q)).1 +
                      restrictWordLinear (Lq.correctionRegion q) error₃) +
                      restrictWordLinear (Lq.correctionRegion q) error₃ := by
                        symm
                        rw [add_assoc, hrr, add_zero]
                _ = A.contract.rx_local_complexes.cqDelta0 q
                      (cqStabilizers q) +
                      restrictWordLinear (Lq.correctionRegion q) error₃ := by
                        rw [hqdiff, ZModModule.sub_eq_add,
                          add_assoc, hrr, add_zero]
                _ = restrictWordLinear (Lq.correctionRegion q) error₃ +
                      A.contract.rx_local_complexes.cqDelta0 q
                        (cqStabilizers q) := by abel
            rw [hqrep, map_add]
      _ = (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (restrictWordLinear (Lq.correctionRegion q) error₃)) +
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (cqStabilizers q))) := by
            rw [Finset.sum_add_distrib]
      _ = error₃ + D.family.coboundary0 i.succ
          (∑ q : Q, A.contract.support_decomposition.cqLift0 q
            (cqStabilizers q)) := by
            rw [← hError₃Decomposition]
            rw [← A.cqDelta0_sum_decomposition]
      _ = error₄ := by rfl
  have hMap1 : (D.rxMap i).map1 lowerCorrection = error₄ := by
    rw [A.rxMap1_eq_cqRepresentative lowerCorrection]
    simpa [lowerCorrection] using hRepresentativeSum
  let lowerSyndrome : D.family.Syndrome i.castSucc :=
    ⟨D.family.coboundary1 i.castSucc lowerCorrection, by
      exact ⟨lowerCorrection, rfl⟩⟩
  have hMap2 : (D.rxMap i).map2 lowerSyndrome = sigma₂ := by
    have hcomm := LinearMap.congr_fun (D.rxMap i).commutes_coboundary1 lowerCorrection
    simp only [LinearMap.comp_apply] at hcomm
    rw [hMap1] at hcomm
    rw [hError₄] at hcomm
    exact hcomm.symm
  have hSelected := selectedMap_eq_rx_of_odd_input D i hOdd
  have hMap2Selected : (D.selectedMap i).map2 lowerSyndrome = sigma₂ := by
    rw [hSelected]
    exact hMap2
  have hCoarseProjection : coarseProjection A sigma₂ =
      (lowerSyndrome : D.family.Cochain2 i.castSucc) :=
    coarseProjection_eq_of_map2 A sigma₂
      (lowerSyndrome : D.family.Cochain2 i.castSucc) hMap2
  let coarseRange : coarseProjection A sigma₂ ∈
      LinearMap.range (D.family.coboundary1 i.castSucc) := by
    rw [hCoarseProjection]
    exact lowerSyndrome.property
  let coarseSyndrome : D.family.Syndrome i.castSucc :=
    ⟨coarseProjection A sigma₂, coarseRange⟩
  have hSyndromeEq : coarseSyndrome = lowerSyndrome := by
    apply Subtype.ext
    exact hCoarseProjection
  have hMap2Coarse : (D.selectedMap i).map2 coarseSyndrome = sigma₂ := by
    rw [hSelected]
    rw [hSyndromeEq]
    exact hMap2
  have hCxTotal : cxCorrectionTotal A sigma.1 = cxCorrection := by
    simpa [cxCorrection] using
      (cxCorrectionTotal_eq_explicit A sigma.1 hCxLocal)
  have hSigmaAfterCx : rxSigmaAfterCx A sigma.1 = sigma₁ := by
    simp [rxSigmaAfterCx, hCxTotal, sigma₁]
  have hCqLocalTotal : CqLocalRange A sigma.1 := by
    intro q
    change restrictWordLinear (Lq.syndromeRegion q)
      (rxSigmaAfterCx A sigma.1) ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)
    rw [hSigmaAfterCx]
    exact hCqLocal q
  have hCqTotal : cqCorrectionTotal A sigma.1 = cqCorrection := by
    have h := cqCorrectionTotal_eq_explicit A sigma.1 hCqLocalTotal
    calc
      cqCorrectionTotal A sigma.1 =
          cqCorrectionRG A (rxSigmaAfterCx A sigma.1) hCqLocalTotal := h
      _ = cqCorrection := by
        dsimp [cqCorrection]
        congr 1
  have hSigmaAfterCq : rxSigmaAfterCq A sigma.1 = sigma₂ := by
    simp [rxSigmaAfterCq, hSigmaAfterCx, hCqTotal, sigma₂]
  have hCoarseWord : rxCoarseWord A sigma.1 =
      (coarseSyndrome : D.family.Cochain2 i.castSucc) := by
    rw [rxCoarseWord, hSigmaAfterCq, hCoarseProjection]
    exact congrArg Subtype.val hSyndromeEq.symm
  have hSigma₂WeightFinal : HammingWeight sigma₂ ≤ HammingWeight sigma.1 :=
    hSigma₂Weight.trans hSigma₁Weight
  have hDouble : 2 * HammingWeight
        (lowerSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 := by
    calc
      2 * HammingWeight (lowerSyndrome : D.family.Cochain2 i.castSucc) =
          HammingWeight ((D.rxMap i).map2 lowerSyndrome) := by
            symm
            exact hammingWeight_map2_eq_double A lowerSyndrome
      _ = HammingWeight sigma₂ := by rw [hMap2]
      _ ≤ HammingWeight sigma.1 := hSigma₂WeightFinal
  have hHalf : HammingWeight
        (lowerSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 / 2 := by omega
  have hSupportZ : SupportedOn A.zSector sigma₂ :=
    RXCoarseGrainingData.zero_outside_sector_of_zero_x_zero_q A hSigma₂X hSigma₂Q
  let correction : D.family.Correction i.succ :=
    cxCorrection + cqCorrection
  have hCorrectionTotal : rxCorrectionTotal A sigma.1 = correction := by
    simp [rxCorrectionTotal, correction, hCxTotal, hCqTotal]
  have hDoubleCoarse : 2 * HammingWeight
        (coarseSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 := by
    simpa [coarseSyndrome, hCoarseProjection] using hDouble
  have hHalfCoarse : HammingWeight
        (coarseSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 / 2 := by
    simpa [coarseSyndrome, hCoarseProjection] using hHalf
  refine ⟨coarseSyndrome, correction, ?_, ?_, ?_, hDoubleCoarse, hHalfCoarse, ?_, ?_, ?_⟩
  · exact hCoarseWord.symm
  · exact hCorrectionTotal.symm
  · have hRel : sigma.1 =
        D.family.coboundary1 i.succ correction + sigma₂ := by
      dsimp [correction]
      rw [map_add]
      rw [← hError₃]
      dsimp [error₃, error₂, error₁]
      rw [map_add, map_add, map_add, hError, hStabilizerZero]
      abel
      simp [two_smul, ZModModule.add_self]
    rw [hMap2Coarse]
    exact hRel
  · rw [hMap2Coarse]
    exact hSupportZ
  · rw [hMap2Coarse]
    exact hSigma₂X
  · rw [hMap2Coarse]
    exact hSigma₂Q

end RXCoarseGrainingData

end RXCoarseGraining
end MultiscaleDecoder
end Coding
end QEC


/-! ## Canonical RX reduction independent of the global parity label

The original odd-input theorem and canonical correction functions remain
unchanged. A literal local edge can prove the selected-map equality directly;
this permits the source dual tower's opposite physical parity without changing
the global replacementKind convention or choosing a different correction.
-/
namespace QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
namespace RXCoarseGrainingData

/-- The full canonical reduction, with actual selected-map compatibility in
place of an unrelated physical parity label. All conclusions are derived. -/
theorem rx_coarse_graining_selected
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hSelected : D.selectedMap i = D.rxMap i)
    (sigma : D.family.Syndrome i.succ) :
    ∃ sigma' : D.family.Syndrome i.castSucc,
      ∃ correction : D.family.Correction i.succ,
        (sigma' : D.family.Cochain2 i.castSucc) =
            rxCoarseWord A (sigma : D.family.Cochain2 i.succ) ∧
        correction = rxCorrectionTotal A (sigma : D.family.Cochain2 i.succ) ∧
        (sigma : D.family.Cochain2 i.succ) =
            D.family.coboundary1 i.succ correction +
              (D.selectedMap i).map2 sigma' ∧
        2 * HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) ∧
        HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) / 2 ∧
        SupportedOn A.zSector ((D.selectedMap i).map2 sigma') ∧
        (∀ p ∈ A.xSector, ((D.selectedMap i).map2 sigma') p = 0) ∧
        (∀ p ∈ A.qSector, ((D.selectedMap i).map2 sigma') p = 0) := by
  classical
  let hCxLocal := A.contract.cx_local_ranges_of_syndrome sigma
  let cxCorrection := cxCorrectionRG A sigma.1 hCxLocal
  let sigma₁ := sigma.1 + D.family.coboundary1 i.succ cxCorrection
  have hCx := cx_cleaning_explicit A sigma
  have hSigma₁Weight : HammingWeight sigma₁ ≤ HammingWeight sigma.1 := by
    simpa [sigma₁, cxCorrection] using hCx.1
  have hSigma₁X : ∀ p ∈ A.xSector, sigma₁ p = 0 := by
    simpa [sigma₁, cxCorrection] using hCx.2
  obtain ⟨error, hError⟩ := sigma.property
  let error₁ := error + cxCorrection
  have hError₁ : D.family.coboundary1 i.succ error₁ = sigma₁ := by
    dsimp [error₁, sigma₁]
    rw [map_add, hError]
  have hCxCocycle : ∀ x,
      A.contract.rx_local_complexes.cxDelta1 x
        (restrictWordLinear (Lx.correctionRegion x) error₁) = 0 := by
    intro x
    have hz : restrictWordLinear (Lx.syndromeRegion x)
        (D.family.coboundary1 i.succ error₁) = 0 := by
      funext j
      have hj : (j : C2 i.succ) ∈ A.xSector := by
        apply xSector_mem_of_region A
        exact Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, j.property⟩
      change D.family.coboundary1 i.succ error₁ j.1 = 0
      rw [hError₁]
      exact hSigma₁X j.1 hj
    rw [← A.contract.support_decomposition.cxDelta1_restriction_global x error₁]
    exact hz
  obtain ⟨stabilizers, hStabilizers⟩ :=
    A.contract.cx_error_cleaning_all error₁ hCxCocycle
  let stabilizerCorrection : D.family.Correction i.succ :=
    D.family.coboundary0 i.succ
      (∑ x : X, A.contract.support_decomposition.cxLift0 x (stabilizers x))
  have hStabilizerZero : D.family.coboundary1 i.succ stabilizerCorrection = 0 := by
    dsimp [stabilizerCorrection]
    have hcomp := BDL26CochainFamily.coboundary1_comp_coboundary0
      D.family i.succ
    have hcomp' := LinearMap.congr_fun hcomp
      (∑ x : X, A.contract.support_decomposition.cxLift0 x (stabilizers x))
    simpa [LinearMap.comp_apply] using hcomp'
  let error₂ := error₁ + stabilizerCorrection
  have hError₂X : ∀ p ∈ correctionRegionUnion Lx, error₂ p = 0 := by
    intro p hp
    rcases Finset.mem_biUnion.1 hp with ⟨x, hx, hpx⟩
    have hlocal := hStabilizers x
    have hlocal' := congrFun hlocal ⟨p, hpx⟩
    exact hlocal'
  have hError₂ : D.family.coboundary1 i.succ error₂ = sigma₁ := by
    dsimp [error₂, stabilizerCorrection]
    rw [map_add]
    rw [hStabilizerZero, add_zero, hError₁]
  have hError₂Supported : SupportedOn A.qCorrectionSector error₂ := by
    intro p hp
    have hcover : p ∈ correctionRegionUnion Lx ∪ A.qCorrectionSector := by
      rw [A.correction_sectors_cover]
      exact Finset.mem_univ p
    have hpX : p ∈ correctionRegionUnion Lx := by
      rcases (by simpa only [Finset.mem_union] using hcover) with hpX | hpQ
      · exact hpX
      · exact (hp hpQ).elim
    exact hError₂X p hpX
  have hError₂XRestrictions : ∀ x,
      restrictWordLinear (Lx.correctionRegion x) error₂ = 0 := by
    intro x
    funext p
    exact hError₂X p.1 (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.2⟩)
  let hCqLocalRaw := A.contract.cq_local_ranges_of_error error₂ hError₂XRestrictions
  have hCqLocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma₁ ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q) := by
    intro q
    rw [← hError₂]
    exact hCqLocalRaw q
  let cqCorrection := cqCorrectionRG A sigma₁ hCqLocal
  let sigma₂ := sigma₁ + D.family.coboundary1 i.succ cqCorrection
  have hCq := cq_cleaning_explicit A sigma₁ hCqLocal hSigma₁X
  have hSigma₂Weight : HammingWeight sigma₂ ≤ HammingWeight sigma₁ := by
    simpa [sigma₂, cqCorrection] using hCq.1
  have hSigma₂X : ∀ p ∈ A.xSector, sigma₂ p = 0 := by
    simpa [sigma₂, cqCorrection] using hCq.2.2
  have hSigma₂Q : ∀ p ∈ A.qSector, sigma₂ p = 0 := by
    simpa [sigma₂, cqCorrection] using hCq.2.1
  let error₃ := error₂ + cqCorrection
  have hError₃ : D.family.coboundary1 i.succ error₃ = sigma₂ := by
    dsimp [error₃, sigma₂]
    rw [map_add, hError₂]
  have hError₃Supported : SupportedOn A.qCorrectionSector error₃ := by
    intro p hp
    change error₂ p + cqCorrectionRG A sigma₁ hCqLocal p = 0
    rw [hError₂Supported p hp,
      cqCorrectionRG_supported A sigma₁ hCqLocal p hp, zero_add]
  have hError₃XRestrictions : ∀ x,
      restrictWordLinear (Lx.correctionRegion x) error₃ = 0 := by
    intro x
    funext p
    apply hError₃Supported p.1
    intro hpQ
    exact Finset.disjoint_left.mp A.correction_sectors_disjoint
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.2⟩) hpQ
  have hError₃CqCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error₃) = 0 := by
    intro q
    have hz : restrictWordLinear (Lq.syndromeRegion q)
        (D.family.coboundary1 i.succ error₃) = 0 := by
      funext j
      have hj : (j : C2 i.succ) ∈ A.qSector := by
        apply qSector_mem_of_region A
        exact Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, j.property⟩
      change D.family.coboundary1 i.succ error₃ j.1 = 0
      rw [hError₃]
      exact hSigma₂Q j.1 hj
    rw [← A.contract.support_decomposition.cqDelta1_restriction_global q error₃ hError₃XRestrictions]
    exact hz
  have hError₃SupportedOnRegions :
      SupportedOn (correctionRegionUnion Lq) error₃ := by
    intro p hp
    apply hError₃Supported p
    simpa [A.qCorrectionSector_eq_regions] using hp
  have hError₃Decomposition :
      error₃ = ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        (restrictWordLinear (Lq.correctionRegion q) error₃) := by
    rw [extend_restrict_sum_eq_mask
      (fun q => Lq.correctionRegion q)
      A.cq_correction_regions_pairwise_disjoint error₃]
    funext p
    by_cases hp : p ∈ correctionRegionUnion Lq
    · change error₃ p = if p ∈ correctionRegionUnion Lq then error₃ p else 0
      rw [if_pos hp]
    · change error₃ p = if p ∈ correctionRegionUnion Lq then error₃ p else 0
      rw [if_neg hp]
      exact hError₃SupportedOnRegions p hp
  let qClasses := qCohomologyClass A error₃ hError₃CqCocycle
  have hRepresentativeDifference : ∀ q, ∃ s : Word Field (Q0 q),
      A.contract.rx_local_complexes.cqDelta0 q s =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error₃ := by
    intro q
    exact cqRepresentative_difference_exists A error₃ hError₃CqCocycle q
  let cqStabilizers : ∀ q, Word Field (Q0 q) :=
    fun q => Classical.choose (hRepresentativeDifference q)
  have hCqStabilizers : ∀ q,
      A.contract.rx_local_complexes.cqDelta0 q (cqStabilizers q) =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error₃ := by
    intro q
    exact Classical.choose_spec (hRepresentativeDifference q)
  let lowerCorrection := A.qCohomologyEquiv qClasses
  let qStabilizerCorrection : D.family.Correction i.succ :=
    D.family.coboundary0 i.succ
      (∑ q : Q, A.contract.support_decomposition.cqLift0 q
        (cqStabilizers q))
  let error₄ := error₃ + qStabilizerCorrection
  have hQStabilizerZero :
      D.family.coboundary1 i.succ qStabilizerCorrection = 0 := by
    dsimp [qStabilizerCorrection]
    have hcomp := BDL26CochainFamily.coboundary1_comp_coboundary0
      D.family i.succ
    have hcomp' := LinearMap.congr_fun hcomp
      (∑ q : Q, A.contract.support_decomposition.cqLift0 q
        (cqStabilizers q))
    simpa [LinearMap.comp_apply] using hcomp'
  have hError₄ : D.family.coboundary1 i.succ error₄ = sigma₂ := by
    dsimp [error₄]
    rw [map_add, hQStabilizerZero, add_zero, hError₃]
  have hRepresentativeSum :
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        ((A.cqRepresentative q (qClasses q)).1)) = error₄ := by
    calc
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
          ((A.cqRepresentative q (qClasses q)).1)) =
        ∑ q : Q, (extendWordLinear (Lq.correctionRegion q)
          (restrictWordLinear (Lq.correctionRegion q) error₃) +
          extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (cqStabilizers q))) := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqdiff := hCqStabilizers q
            have hqrep :
                (A.cqRepresentative q (qClasses q)).1 =
                  restrictWordLinear (Lq.correctionRegion q) error₃ +
                    A.contract.rx_local_complexes.cqDelta0 q
                      (cqStabilizers q) := by
              have hrr :
                  restrictWordLinear (Lq.correctionRegion q) error₃ +
                      restrictWordLinear (Lq.correctionRegion q) error₃ =
                    (0 : Word Field (LocalRegionIndex (Lq.correctionRegion q))) := by
                ext p
                exact ZModModule.add_self _
              calc
                (A.cqRepresentative q (qClasses q)).1 =
                    ((A.cqRepresentative q (qClasses q)).1 +
                      restrictWordLinear (Lq.correctionRegion q) error₃) +
                      restrictWordLinear (Lq.correctionRegion q) error₃ := by
                        symm
                        rw [add_assoc, hrr, add_zero]
                _ = A.contract.rx_local_complexes.cqDelta0 q
                      (cqStabilizers q) +
                      restrictWordLinear (Lq.correctionRegion q) error₃ := by
                        rw [hqdiff, ZModModule.sub_eq_add,
                          add_assoc, hrr, add_zero]
                _ = restrictWordLinear (Lq.correctionRegion q) error₃ +
                      A.contract.rx_local_complexes.cqDelta0 q
                        (cqStabilizers q) := by abel
            rw [hqrep, map_add]
      _ = (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (restrictWordLinear (Lq.correctionRegion q) error₃)) +
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (cqStabilizers q))) := by
            rw [Finset.sum_add_distrib]
      _ = error₃ + D.family.coboundary0 i.succ
          (∑ q : Q, A.contract.support_decomposition.cqLift0 q
            (cqStabilizers q)) := by
            rw [← hError₃Decomposition]
            rw [← A.cqDelta0_sum_decomposition]
      _ = error₄ := by rfl
  have hMap1 : (D.rxMap i).map1 lowerCorrection = error₄ := by
    rw [A.rxMap1_eq_cqRepresentative lowerCorrection]
    simpa [lowerCorrection] using hRepresentativeSum
  let lowerSyndrome : D.family.Syndrome i.castSucc :=
    ⟨D.family.coboundary1 i.castSucc lowerCorrection, by
      exact ⟨lowerCorrection, rfl⟩⟩
  have hMap2 : (D.rxMap i).map2 lowerSyndrome = sigma₂ := by
    have hcomm := LinearMap.congr_fun (D.rxMap i).commutes_coboundary1 lowerCorrection
    simp only [LinearMap.comp_apply] at hcomm
    rw [hMap1] at hcomm
    rw [hError₄] at hcomm
    exact hcomm.symm
  have hMap2Selected : (D.selectedMap i).map2 lowerSyndrome = sigma₂ := by
    rw [hSelected]
    exact hMap2
  have hCoarseProjection : coarseProjection A sigma₂ =
      (lowerSyndrome : D.family.Cochain2 i.castSucc) :=
    coarseProjection_eq_of_map2 A sigma₂
      (lowerSyndrome : D.family.Cochain2 i.castSucc) hMap2
  let coarseRange : coarseProjection A sigma₂ ∈
      LinearMap.range (D.family.coboundary1 i.castSucc) := by
    rw [hCoarseProjection]
    exact lowerSyndrome.property
  let coarseSyndrome : D.family.Syndrome i.castSucc :=
    ⟨coarseProjection A sigma₂, coarseRange⟩
  have hSyndromeEq : coarseSyndrome = lowerSyndrome := by
    apply Subtype.ext
    exact hCoarseProjection
  have hMap2Coarse : (D.selectedMap i).map2 coarseSyndrome = sigma₂ := by
    rw [hSelected]
    rw [hSyndromeEq]
    exact hMap2
  have hCxTotal : cxCorrectionTotal A sigma.1 = cxCorrection := by
    simpa [cxCorrection] using
      (cxCorrectionTotal_eq_explicit A sigma.1 hCxLocal)
  have hSigmaAfterCx : rxSigmaAfterCx A sigma.1 = sigma₁ := by
    simp [rxSigmaAfterCx, hCxTotal, sigma₁]
  have hCqLocalTotal : CqLocalRange A sigma.1 := by
    intro q
    change restrictWordLinear (Lq.syndromeRegion q)
      (rxSigmaAfterCx A sigma.1) ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)
    rw [hSigmaAfterCx]
    exact hCqLocal q
  have hCqTotal : cqCorrectionTotal A sigma.1 = cqCorrection := by
    have h := cqCorrectionTotal_eq_explicit A sigma.1 hCqLocalTotal
    calc
      cqCorrectionTotal A sigma.1 =
          cqCorrectionRG A (rxSigmaAfterCx A sigma.1) hCqLocalTotal := h
      _ = cqCorrection := by
        dsimp [cqCorrection]
        congr 1
  have hSigmaAfterCq : rxSigmaAfterCq A sigma.1 = sigma₂ := by
    simp [rxSigmaAfterCq, hSigmaAfterCx, hCqTotal, sigma₂]
  have hCoarseWord : rxCoarseWord A sigma.1 =
      (coarseSyndrome : D.family.Cochain2 i.castSucc) := by
    rw [rxCoarseWord, hSigmaAfterCq, hCoarseProjection]
    exact congrArg Subtype.val hSyndromeEq.symm
  have hSigma₂WeightFinal : HammingWeight sigma₂ ≤ HammingWeight sigma.1 :=
    hSigma₂Weight.trans hSigma₁Weight
  have hDouble : 2 * HammingWeight
        (lowerSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 := by
    calc
      2 * HammingWeight (lowerSyndrome : D.family.Cochain2 i.castSucc) =
          HammingWeight ((D.rxMap i).map2 lowerSyndrome) := by
            symm
            exact hammingWeight_map2_eq_double A lowerSyndrome
      _ = HammingWeight sigma₂ := by rw [hMap2]
      _ ≤ HammingWeight sigma.1 := hSigma₂WeightFinal
  have hHalf : HammingWeight
        (lowerSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 / 2 := by omega
  have hSupportZ : SupportedOn A.zSector sigma₂ :=
    RXCoarseGrainingData.zero_outside_sector_of_zero_x_zero_q A hSigma₂X hSigma₂Q
  let correction : D.family.Correction i.succ :=
    cxCorrection + cqCorrection
  have hCorrectionTotal : rxCorrectionTotal A sigma.1 = correction := by
    simp [rxCorrectionTotal, correction, hCxTotal, hCqTotal]
  have hDoubleCoarse : 2 * HammingWeight
        (coarseSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 := by
    simpa [coarseSyndrome, hCoarseProjection] using hDouble
  have hHalfCoarse : HammingWeight
        (coarseSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 / 2 := by
    simpa [coarseSyndrome, hCoarseProjection] using hHalf
  refine ⟨coarseSyndrome, correction, ?_, ?_, ?_, hDoubleCoarse, hHalfCoarse, ?_, ?_, ?_⟩
  · exact hCoarseWord.symm
  · exact hCorrectionTotal.symm
  · have hRel : sigma.1 =
        D.family.coboundary1 i.succ correction + sigma₂ := by
      dsimp [correction]
      rw [map_add]
      rw [← hError₃]
      dsimp [error₃, error₂, error₁]
      rw [map_add, map_add, map_add, hError, hStabilizerZero]
      abel
      simp [two_smul, ZModModule.add_self]
    rw [hMap2Coarse]
    exact hRel
  · rw [hMap2Coarse]
    exact hSupportZ
  · rw [hMap2Coarse]
    exact hSigma₂X
  · rw [hMap2Coarse]
    exact hSigma₂Q

end RXCoarseGrainingData
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining
