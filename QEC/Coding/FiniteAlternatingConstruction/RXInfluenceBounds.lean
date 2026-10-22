import QEC.Coding.FiniteAlternatingConstruction.RXCoarseInfluence
import QEC.Coding.FiniteAlternatingConstruction.GraphQuantitativeBounds
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformReadoutWeight

/-!
# Uniform quantitative influence of actual RX error perturbations

BDL26 Section 4, `paper.tex:2431-2458,2475-2486,2659-2678`, gives the
incoming X-to-Q-to-Z read dependence. Counting the actual reverse dependency
of one input coordinate uses an outgoing radius-two ball, never a symmetry
of directed distance. The conservative constant 228 is derived here from
actual basis-syndrome valence four and Tanner degree seven. It bounds the
nonlinear canonical coarse readout, without parent or component claims.
-/
noncomputable section
namespace QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

section DirectedCounting
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Outgoing neighbors, distinct from the incoming read neighborhood. -/
def outNeighbors (G : DirectedGraph V) (u : V) : Finset V :=
  Finset.univ.filter fun v => G.edge u v = true

def forwardTwo (G : DirectedGraph V) (u : V) : Finset V :=
  insert u (outNeighbors G u ∪ (outNeighbors G u).biUnion (outNeighbors G))

theorem mem_forwardTwo (G : DirectedGraph V) (u v : V) :
    v ∈ forwardTwo G u ↔ v = u ∨ G.edge u v = true ∨
      ∃ w, G.edge u w = true ∧ G.edge w v = true := by
  simp only [forwardTwo, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
    outNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem reachable_one (G : DirectedGraph V) (u v : V) :
    G.reachableWithin 1 u v = true ↔ u = v ∨ G.edge u v = true := by
  simp [DirectedGraph.reachableWithin]

/-- Extract the bounded path without assuming that the vertex type has size at least two. -/
theorem distance_le_two_mem_forwardTwo (G : DirectedGraph V) (u v : V)
    (h : G.distance u v ≤ (2 : WithTop Nat)) : v ∈ forwardTwo G u := by
  have hr : G.reachableWithin 2 u v = true := by
    cases hs : G.distanceAux u v (Fintype.card V) with
    | none => simp [DirectedGraph.distance, hs] at h
    | some k =>
        have hk : k ≤ 2 := by simpa [DirectedGraph.distance, hs] using h
        exact DirectedGraph.reachableWithin_mono G u v hk
          (DirectedGraph.distanceAux_some_spec G u v hs).2
  change (G.reachableWithin 1 u v ||
    decide (∃ w, G.edge u w = true ∧ G.reachableWithin 1 w v = true)) = true at hr
  simp only [Bool.or_eq_true_eq_eq_true_or_eq_true, decide_eq_true_eq] at hr
  apply (mem_forwardTwo G u v).mpr
  rcases hr with hr | ⟨w, huw, hwv⟩
  · rcases (reachable_one G u v).mp hr with huv | huv
    · exact Or.inl huv.symm
    · exact Or.inr (Or.inl huv)
  · rcases (reachable_one G w v).mp hwv with hwv | hwv
    · subst v; exact Or.inr (Or.inl huw)
    · exact Or.inr (Or.inr ⟨w, huw, hwv⟩)

theorem forwardTwo_card_le (G : DirectedGraph V)
    (hdegree : ∀ u, (outNeighbors G u).card ≤ 7) (u : V) :
    (forwardTwo G u).card ≤ 57 := by
  have hbi := Finset.card_biUnion_le_card_mul (outNeighbors G u) (outNeighbors G) 7
    (fun w _ => hdegree w)
  have hu := hdegree u
  have hmul : (outNeighbors G u).card * 7 ≤ 49 := by omega
  have hsecond : ((outNeighbors G u).biUnion (outNeighbors G)).card ≤ 49 := hbi.trans hmul
  have hsum := Finset.card_union_le (outNeighbors G u)
    ((outNeighbors G u).biUnion (outNeighbors G))
  have hins := Finset.card_insert_le u
    (outNeighbors G u ∪ (outNeighbors G u).biUnion (outNeighbors G))
  change (insert u (outNeighbors G u ∪ (outNeighbors G u).biUnion (outNeighbors G))).card ≤ 57
  omega
end DirectedCounting

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

private theorem directed_edge_adjacent (P : TannerSquarePresentation) (u v : Vertex P)
    (he : (tannerLevel P).graph.edge u v = true) : tannerAdjacent P u v := by
  rw [tannerLevel_edge] at he
  cases u <;> cases v <;> simp_all [tannerDirected, tannerAdjacent]

/-- Measured actual Tanner degree bounds outgoing edges; directed symmetry is unused. -/
theorem actual_outNeighbors_card_le
    (u : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z) :
    (outNeighbors (rxData S depth i h).levelGraph.graph u).card ≤ 7 := by
  let P := (state S i.val).presentation
  have hc : (outNeighbors (rxData S depth i h).levelGraph.graph u).card ≤
      tannerDegree P (vertexEquiv P u) := by
    unfold tannerDegree
    rw [Fintype.card_subtype]
    apply Finset.card_le_card_of_injOn (vertexEquiv P)
    · intro v hv
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have he := (Finset.mem_filter.mp hv).2
      rw [rxData_graph_edge S depth i h] at he
      exact directed_edge_adjacent P _ _ he
    · exact (vertexEquiv P).injective.injOn
  exact hc.trans (state_tannerDegree_le S i.val (vertexEquiv P u))

/-- This is the count of coarse centers reading p, not the coordinate size of U(z). -/
def readers (p : FamilyZ S depth i.succ) : Finset (FamilyZ S depth i.castSucc) :=
  Finset.univ.filter fun z => p ∈ readRegion S depth i h z

theorem syndrome_owner_iff (p : FamilyZ S depth i.succ)
    (v : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z) :
    p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v ↔
      (rxData S depth i h).topCenter p = v :=
  rxXiLocalComplex_region_mem_iff _ _ _

theorem syndrome_owner_unique (p : FamilyZ S depth i.succ) :
    ∃! v, p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v := by
  refine ⟨(rxData S depth i h).topCenter p, (syndrome_owner_iff S depth i h p _).mpr rfl, ?_⟩
  intro v hv
  exact ((syndrome_owner_iff S depth i h p v).mp hv).symm

theorem readRegion_iff_distance (p : FamilyZ S depth i.succ) (z : FamilyZ S depth i.castSucc) :
    p ∈ readRegion S depth i h z ↔
      DirectedGraph.distance (rxData S depth i h).levelGraph.graph
        ((rxData S depth i h).topCenter p) ((rxData S depth i h).coarseCenter z) ≤ 2 := by
  rw [mem_readRegion]
  constructor
  · rintro ⟨v, hv, hp⟩
    have he := (rxXiLocalComplex_region_mem_iff (rxData S depth i h) v p).mp hp
    subst v
    exact (Finset.mem_filter.mp hv).2
  · intro hp
    refine ⟨(rxData S depth i h).topCenter p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    · exact (rxXiLocalComplex_region_mem_iff _ _ _).mpr rfl

theorem coarseCenter_injective : Function.Injective (rxData S depth i h).coarseCenter := by
  intro z w he
  change Sum.inr (Sum.inr z) = Sum.inr (Sum.inr w) at he
  exact Sum.inr.inj (Sum.inr.inj he)

theorem readers_card_le (p : FamilyZ S depth i.succ) : (readers S depth i h p).card ≤ 57 := by
  have hc : (readers S depth i h p).card ≤
      (forwardTwo (rxData S depth i h).levelGraph.graph ((rxData S depth i h).topCenter p)).card := by
    apply Finset.card_le_card_of_injOn (rxData S depth i h).coarseCenter
    · intro z hz
      exact distance_le_two_mem_forwardTwo _ _ _
        ((readRegion_iff_distance S depth i h p z).mp (Finset.mem_filter.mp hz).2)
    · exact (coarseCenter_injective S depth i h).injOn
  exact hc.trans (forwardTwo_card_le _ (actual_outNeighbors_card_le S depth i h) _)

/-- The literal upper basis coboundary has at most four incident Z coordinates. -/
theorem basisSyndrome_weight_le_four (q : FamilyQ S depth i.succ) :
    HammingWeight (basisSyndrome S depth i q) ≤ 4 := by
  unfold basisSyndrome
  rw [indexedFamily_coboundary1, BDL26UniformHistoryObstruction.basis_coboundary_weight]
  exact ((state_boundedValence S i.succ.val).2.2 q).2.1

theorem influence_eq_readers (q : FamilyQ S depth i.succ) :
    influence S depth i h q = (hammingSupport (basisSyndrome S depth i q)).biUnion
      (readers S depth i h) := by
  ext z
  rw [mem_influence, Finset.mem_biUnion]
  simp only [readers, hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]

theorem influence_card_le (q : FamilyQ S depth i.succ) : (influence S depth i h q).card ≤ 228 := by
  rw [influence_eq_readers]
  have hc := Finset.card_biUnion_le_card_mul (hammingSupport (basisSyndrome S depth i q))
    (readers S depth i h) 57 (fun p _ => readers_card_le S depth i h p)
  have hb := basisSyndrome_weight_le_four S depth i q
  change (hammingSupport (basisSyndrome S depth i q)).card ≤ 4 at hb
  omega

/-- Finite union of the existing actual basis influences, with no selector linearity. -/
def errorInfluence (e : (indexedFamily S depth).Cochain1 i.succ) :
    Finset (FamilyZ S depth i.castSucc) :=
  (hammingSupport e).biUnion (influence S depth i h)

theorem mem_errorInfluence (e : (indexedFamily S depth).Cochain1 i.succ)
    (z : FamilyZ S depth i.castSucc) :
    z ∈ errorInfluence S depth i h e ↔ ∃ q, e q ≠ 0 ∧ z ∈ influence S depth i h q := by
  simp only [errorInfluence, Finset.mem_biUnion, hammingSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem errorInfluence_card_le (e : (indexedFamily S depth).Cochain1 i.succ) :
    (errorInfluence S depth i h e).card ≤ 228 * HammingWeight e := by
  exact (Finset.card_biUnion_le_card_mul (hammingSupport e) (influence S depth i h) 228
    (fun q _ => influence_card_le S depth i h q)).trans_eq (by
      simp only [HammingWeight, Nat.mul_comm])

/-- Actual finite coordinate expansion, used only for the linear differential. -/
theorem error_basis_expansion (e : (indexedFamily S depth).Cochain1 i.succ) :
    e = ∑ q, e q • (canonicalBasisWord (F := BDL26Field) q) := by
  funext p
  simp [canonicalBasisWord, Pi.single_apply, Finset.sum_apply, eq_comm]

/-- Every term of the actual error coboundary vanishes on an unread region. -/
theorem error_coboundary_zero_on_readRegion (e : (indexedFamily S depth).Cochain1 i.succ)
    (z : FamilyZ S depth i.castSucc) (hz : z ∉ errorInfluence S depth i h e)
    (p : FamilyZ S depth i.succ) (hp : p ∈ readRegion S depth i h z) :
    (indexedFamily S depth).coboundary1 i.succ e p = 0 := by
  conv_lhs => rw [error_basis_expansion S depth i e]
  rw [map_sum]
  change (∑ q, (indexedFamily S depth).coboundary1 i.succ
    (e q • canonicalBasisWord q)) p = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q _
  by_cases he : e q = 0
  · simp [he]
  · have hq : z ∉ influence S depth i h q := by
      intro hq
      exact hz ((mem_errorInfluence S depth i h e z).mpr ⟨q, he, hq⟩)
    rw [map_smul]
    change e q * basisSyndrome S depth i q p = 0
    rw [basisSyndrome_zero_on_readRegion S depth i h q z hq p hp, mul_zero]

/-- Validity is derived from an actual preimage plus e. -/
def sigmaPlusError (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) : (indexedFamily S depth).Syndrome i.succ :=
  ⟨sigma.val + (indexedFamily S depth).coboundary1 i.succ e, by
    obtain ⟨a, ha⟩ := sigma.property
    exact ⟨a + e, by rw [map_add, ha]⟩⟩

theorem sigmaPlusError_value (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) :
    (sigmaPlusError S depth i sigma e).val =
      sigma.val + (indexedFamily S depth).coboundary1 i.succ e := rfl

theorem input_agreement (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ errorInfluence S depth i h e) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) :
    sigma.val p = (sigmaPlusError S depth i sigma e).val p := by
  change sigma.val p = sigma.val p + (indexedFamily S depth).coboundary1 i.succ e p
  rw [error_coboundary_zero_on_readRegion S depth i h e z hz p hp, add_zero]

theorem aggregate_agreement (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ errorInfluence S depth i h e) :
    rxXiSignal (rxData S depth i h) sigma.val ((rxData S depth i h).coarseCenter z) 2 =
      rxXiSignal (rxData S depth i h) (sigmaPlusError S depth i sigma e).val
        ((rxData S depth i h).coarseCenter z) 2 := by
  funext p
  change Finset.sum _ (fun v => maskWord ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v)
      sigma.val p) = Finset.sum _ (fun v =>
        maskWord ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v)
          (sigmaPlusError S depth i sigma e).val p)
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hp : p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v
  · simp only [maskWord, if_pos hp]
    exact input_agreement S depth i h sigma e z hz p
      ((mem_readRegion S depth i h z p).mpr ⟨v, hv, hp⟩)
  · simp only [maskWord, if_neg hp]

theorem coarse_eq_outside_errorInfluence (hi : 2 ≤ i.val)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ errorInfluence S depth i h e) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val z := by
  rw [canonical_coarse, canonical_coarse]
  exact (rx_coarse_word_invariant_at_center (rxData S depth i h) sigma.val z).trans
    ((congrArg (fun word => rxCoarseWord (rxData S depth i h) word z)
      (aggregate_agreement S depth i h sigma e z hz)).trans
        (rx_coarse_word_invariant_at_center (rxData S depth i h)
          (sigmaPlusError S depth i sigma e).val z).symm)

theorem coarse_difference_support (hi : 2 ≤ i.val)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) :
    hammingSupport ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val) ⊆
        errorInfluence S depth i h e := by
  intro z hz
  by_contra hnot
  have heq := coarse_eq_outside_errorInfluence S depth i h hi sigma e z hnot
  have hn := (Finset.mem_filter.mp hz).2
  apply hn
  change (rxStepOutput S depth i h sigma).coarse.val z +
    (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val z = 0
  rw [← heq]
  exact ZModModule.add_self _

theorem coarse_difference_weight_le (hi : 2 ≤ i.val)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) :
    HammingWeight ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val) ≤
        228 * HammingWeight e :=
  (Finset.card_le_card (coarse_difference_support S depth i h hi sigma e)).trans
    (errorInfluence_card_le S depth i h e)

@[simp] theorem errorInfluence_zero : errorInfluence S depth i h 0 = ∅ := by
  simp [errorInfluence, hammingSupport]

@[simp] theorem sigmaPlusError_zero (sigma : (indexedFamily S depth).Syndrome i.succ) :
    sigmaPlusError S depth i sigma 0 = sigma := by
  apply Subtype.ext
  simp [sigmaPlusError]

theorem errorInfluence_basis (q : FamilyQ S depth i.succ) :
    errorInfluence S depth i h (canonicalBasisWord (F := BDL26Field) q) =
      influence S depth i h q := by
  have hs : hammingSupport (canonicalBasisWord (F := BDL26Field) q) = {q} := by
    ext p
    simp [hammingSupport, canonicalBasisWord, Pi.single_apply, eq_comm]
  simp only [errorInfluence, hs, Finset.singleton_biUnion]

theorem sigmaPlusError_basis (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) :
    sigmaPlusError S depth i sigma (canonicalBasisWord (F := BDL26Field) q) =
      sigmaPlus S depth i sigma q := rfl

end QEC.Coding.BDL26RXInfluenceBounds
