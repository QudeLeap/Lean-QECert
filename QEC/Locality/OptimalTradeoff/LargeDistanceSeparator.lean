import QEC.Locality.OptimalTradeoff.RecursivePartition
import QEC.Locality.OptimalTradeoff.BadSquareSubdivision
import QEC.Locality.CorrectableRegions.TwoCorrectableRegionsDimension
/-!
# Dai--Li large-distance recursive-separator branch

This internal module formalizes Part I of Dai--Li (DL24, `main.tex`,
lines 739--890).  Its target is the contradiction branch for a finite binary
stabilizer presentation with a fixed independent generator family and a
unit-separated planar embedding.  The source assumes that there are at most
`d / 200` interactions at length `d / (200 sqrt n)` and recursively constructs
geometric separators until every retained region is distance-correctable.

The initial definitions below deliberately record only the source's *negated
conclusion*: the threshold is computed from `d` and `n`, and the smallness
condition is an arithmetic inequality on the existing finite set of distinct
unordered interactions.  In particular, no separator, recursive partition,
recovery, or long-interaction lower bound is supplied as data.

The eventual terminal theorem in this module constructs the separator
recursion and contradicts a positive encoded-qubit count.  It is an internal
handoff and does not establish a public theorem lifecycle state.
-/

noncomputable section

namespace QEC.Locality

open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- DL24 Part I's explicit length scale `d / (200 sqrt n)`.  The square root
is the principal nonnegative root. -/
noncomputable def daiLiLargeDistanceThreshold (d n : Nat) : ℝ :=
  (d : ℝ) / (200 * Real.sqrt (n : ℝ))

/-- DL24's contradiction assumption, expressed over the actual cardinality of
the finite unordered long-interaction set.  The coefficient form avoids any
rounding convention for `d / 200`. -/
def DaiLiLargeDistanceFewLongInteractions
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat) : Prop :=
  200 * P.longInteractionCount embedding
      (daiLiLargeDistanceThreshold d (Fintype.card ι)) ≤ d

/-- The source's few-long-interactions assumption bounds the total actual
endpoint incidence counter.  This uses the proved degree-sum identity for the
same unordered interaction set, rather than an ordered-pair substitute. -/
theorem daiLiLargeDistance_totalIncidence_budget
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) :
    10 * (∑ q : ι,
      P.daiLiInteractionCounter embedding
        (daiLiLargeDistanceThreshold d (Fintype.card ι)) q) ≤ d := by
  unfold DaiLiLargeDistanceFewLongInteractions at hFew
  rw [P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding
    (daiLiLargeDistanceThreshold d (Fintype.card ι))]
  omega

/-- The same global source budget applies to every concrete finite region.
This is the budget consumed by each actual separator-growth boundary. -/
theorem daiLiLargeDistance_regionIncidence_budget
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d)
    (region : Finset ι) :
    10 * regionInteractionCounter P embedding
        (daiLiLargeDistanceThreshold d (Fintype.card ι)) region ≤ d := by
  have hRegion := regionInteractionCounter_mono P embedding
    (daiLiLargeDistanceThreshold d (Fintype.card ι))
    (show region ⊆ Finset.univ by simp)
  have hGlobal := daiLiLargeDistance_totalIncidence_budget P embedding d hFew
  simpa [regionInteractionCounter] using
    (Nat.mul_le_mul_left 10 hRegion |>.trans hGlobal)

/-- The concrete one-qubit subsystem used in the `ell < 1` source branch. -/
def daiLiSingletonSubsystem (q : ι) : FiniteSubsystem ι :=
  ⟨{q}⟩

/-- A concrete finite subsystem for a coordinate finset, kept local to the
Part-I argument so this module does not import unrelated BGKL machinery. -/
def daiLiFiniteSubsystem (vertices : Finset ι) : FiniteSubsystem ι :=
  ⟨vertices⟩

/-- The few-long-interaction hypothesis makes the actual endpoint set strictly
smaller than the distance in the nontrivial source branch. -/
theorem card_longInteractionEndpointQubits_lt_distance
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) (hd : 0 < d) :
    (longInteractionEndpointQubits P embedding
      (daiLiLargeDistanceThreshold d (Fintype.card ι))).card < d := by
  have hEndpoints := card_longInteractionEndpointQubits_le_sum_counter P embedding
    (daiLiLargeDistanceThreshold d (Fintype.card ι))
  have hBudget := daiLiLargeDistance_totalIncidence_budget P embedding d hFew
  have hEndpointBudget :
      10 * (longInteractionEndpointQubits P embedding
        (daiLiLargeDistanceThreshold d (Fintype.card ι))).card ≤ d :=
    (Nat.mul_le_mul_left 10 hEndpoints).trans hBudget
  omega

/-- A vertex outside the actual long-endpoint set cannot participate in any
fixed-generator interaction when the Part-I threshold is below one. -/
theorem no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {threshold : ℝ}
    (hThreshold : threshold < 1) {p q : ι}
    (hp : p ∉ longInteractionEndpointQubits P embedding threshold)
    (hInteraction : P.fixedGeneratorInteraction p q) : False := by
  apply no_long_interaction_from_outside_endpoint_set P embedding threshold p q hp
  refine ⟨hInteraction, hThreshold.le.trans ?_⟩
  apply embedding.one_le_distance_of_ne
  intro hpq
  subst q
  exact P.fixedGeneratorInteractionGraph_loopless p hInteraction

/-- Distinct singleton pieces outside the actual long-endpoint set are
fixed-generator decoupled in the `ell < 1` source corner. -/
theorem daiLiSingletonsOutsideLongEndpoints_fixedGeneratorDecoupled
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {threshold : ℝ}
    (hThreshold : threshold < 1) {p q : ι}
    (hp : p ∈ (longInteractionEndpointQubits P embedding threshold)ᶜ)
    (hpq : p ≠ q) :
    P.fixedGeneratorDecoupled
      ((daiLiSingletonSubsystem p).selected : Set ι)
      ((daiLiSingletonSubsystem q).selected : Set ι) := by
  refine (P.fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction _ _).2 ⟨?_, ?_⟩
  · simp [daiLiSingletonSubsystem, hpq]
  · intro x hx y hy j hSupport
    have hx' : x = p := by simpa [daiLiSingletonSubsystem] using hx
    have hy' : y = q := by simpa [daiLiSingletonSubsystem] using hy
    subst x
    subst y
    have hInteraction : P.fixedGeneratorInteraction p q :=
      (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
        ⟨hpq, j, hSupport.1, hSupport.2⟩
    exact no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
      P embedding hThreshold (Finset.mem_compl.mp hp) hInteraction

/-- The `ell < 1` source corner constructs a concrete recovery after erasure
of every physical qubit.  The construction has no supplied recovery or
interaction partition: the exceptional set is the actual long-endpoint set,
and its complement is assembled from concrete singleton recoveries. -/
theorem exists_erasureRecovery_daiLiLargeDistance_threshold_lt_one
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d)
    (hdTwo : 2 ≤ d)
    (hThreshold : daiLiLargeDistanceThreshold d (Fintype.card ι) < 1) :
    ∃ recovery : QuantumChannel
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).erasureChannelFromRegister
        recovery := by
  classical
  let threshold := daiLiLargeDistanceThreshold d (Fintype.card ι)
  let endpoints := longInteractionEndpointQubits P embedding threshold
  let endpointSubsystem : FiniteSubsystem ι := ⟨endpoints⟩
  let outsideSubsystem := familyUnionSubsystem
    (fun q : ι => daiLiSingletonSubsystem q) endpointsᶜ
  have hdPos : 0 < d := by omega
  have hEndpointCard : endpoints.card < d := by
    simpa [endpoints, threshold] using
      card_longInteractionEndpointQubits_lt_distance P embedding d hFew hdPos
  obtain ⟨endpointRecovery, hEndpointRecovery⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      endpointSubsystem (by simpa [endpointSubsystem] using hEndpointCard)
  obtain ⟨outsideRecovery, hOutsideRecovery⟩ :=
    exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
      (fun q : ι => daiLiSingletonSubsystem q) endpointsᶜ
      (by
        intro q hq
        apply semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
        change 1 < d
        omega)
      (by
        intro p hp q _hq hpq
        exact daiLiSingletonsOutsideLongEndpoints_fixedGeneratorDecoupled
          P embedding (by simpa [threshold] using hThreshold) hp hpq)
  have hEndpointOutsideDecoupled : P.fixedGeneratorDecoupled
      (endpointSubsystem.selected : Set ι) (outsideSubsystem.selected : Set ι) := by
    refine (P.fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction _ _).2 ⟨?_, ?_⟩
    · apply Set.disjoint_left.mpr
      intro p hp hOutside
      have hpEndpoint : p ∈ endpoints := by simpa [endpointSubsystem] using hp
      have hpOutside : p ∈ endpointsᶜ := by
        simpa [outsideSubsystem, familyUnionSubsystem, daiLiSingletonSubsystem] using hOutside
      exact (Finset.mem_compl.mp hpOutside) hpEndpoint
    · intro p hp q hq j hSupport
      have hqOutside : q ∈ endpointsᶜ := by
        simpa [outsideSubsystem, familyUnionSubsystem, daiLiSingletonSubsystem] using hq
      have hInteraction : P.fixedGeneratorInteraction p q :=
        (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
          ⟨by
            intro hpq
            subst q
            exact (Finset.mem_compl.mp hqOutside) (by simpa [endpointSubsystem] using hp),
            j, hSupport.1, hSupport.2⟩
      exact no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
        P embedding (by simpa [threshold] using hThreshold)
        (p := q) (q := p) (Finset.mem_compl.mp hqOutside)
        (P.fixedGeneratorInteractionGraph_symmetric hInteraction)
  obtain ⟨recovery, hRecovery⟩ := exists_erasureRecovery_of_fixedGeneratorDecoupled P
    endpointSubsystem outsideSubsystem endpointRecovery outsideRecovery hEndpointRecovery hOutsideRecovery
      hEndpointOutsideDecoupled
  have hAll : unionSubsystem endpointSubsystem outsideSubsystem =
      daiLiFiniteSubsystem (Finset.univ : Finset ι) := by
    apply congrArg (fun selected : Finset ι => (⟨selected⟩ : FiniteSubsystem ι))
    ext q
    simp [endpointSubsystem, outsideSubsystem, familyUnionSubsystem,
      daiLiSingletonSubsystem]
  rw [← hAll]
  exact ⟨recovery, hRecovery⟩

/-- Therefore the source's `ell < 1` corner contradicts a positive encoded
dimension.  This is the first completed branch of DL24 Part I; the remaining
`ell >= 1` branch will supply the genuine recursive strip construction. -/
theorem daiLiLargeDistance_threshold_lt_one_encodedQubits_eq_zero
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d)
    (hdTwo : 2 ≤ d)
    (hThreshold : daiLiLargeDistanceThreshold d (Fintype.card ι) < 1) :
    P.encodedQubits = 0 := by
  obtain ⟨recoveryAll, hRecoveryAll⟩ :=
    exists_erasureRecovery_daiLiLargeDistance_threshold_lt_one P embedding d
      hDistance hFew hdTwo hThreshold
  let allSubsystem : FiniteSubsystem ι :=
    daiLiFiniteSubsystem (Finset.univ : Finset ι)
  let emptySubsystem : FiniteSubsystem ι := daiLiFiniteSubsystem (∅ : Finset ι)
  obtain ⟨recoveryEmpty, hRecoveryEmpty⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      emptySubsystem (by
        change 0 < d
        omega)
  have hBound := two_correctable_regions_encodedQubits_le_separator_card P
    allSubsystem emptySubsystem emptySubsystem
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    (by simp [emptySubsystem, daiLiFiniteSubsystem])
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    recoveryAll (by simpa [allSubsystem] using hRecoveryAll)
    recoveryEmpty hRecoveryEmpty
  simpa [emptySubsystem, daiLiFiniteSubsystem] using hBound

/-- Consequently, the positive-encoded-dimension branch of DL24 Part I may
work under the source's remaining case assumption `1 <= ell`.  This is a
derived case split, not a hypothesis smuggled into the recursive argument. -/
theorem one_le_daiLiLargeDistanceThreshold_of_positive_encodedQubits
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d)
    (hdTwo : 2 ≤ d) (hEncoded : 0 < P.encodedQubits) :
    1 ≤ daiLiLargeDistanceThreshold d (Fintype.card ι) := by
  by_contra hThreshold
  have hZero := daiLiLargeDistance_threshold_lt_one_encodedQubits_eq_zero
    P embedding d hDistance hFew hdTwo (lt_of_not_ge hThreshold)
  omega

/-! ## Exact finite tenth-coordinate selectors

DL24's plane-separator proof begins with the extremal coordinates containing
at least ten percent of the actual finite parent.  The selectors below use
`ceil(|V| / 10)` rather than an informal real-valued count, so their discrete
meaning is exact even when `|V|` is not divisible by ten.
-/

/-- The exact integral meaning of ``at least one tenth'' of a finite region. -/
def daiLiTenthCount (region : Finset ι) : Nat :=
  (region.card + 9) / 10

/-- The finite coordinate support of one actual parent region. -/
def daiLiCoordinateSupport (region : Finset ι) (coordinate : ι → ℝ) : Finset ℝ :=
  region.image coordinate

/-- Candidate lower tenth coordinates: actual occupied coordinates whose
closed lower halfspace contains at least one tenth of the parent. -/
def daiLiLowerTenthCandidates (region : Finset ι) (coordinate : ι → ℝ) : Finset ℝ :=
  (daiLiCoordinateSupport region coordinate).filter fun cut =>
    daiLiTenthCount region ≤ (region.filter fun q => coordinate q ≤ cut).card

omit [Fintype ι] [DecidableEq ι] in
/-- The lower-tenth candidate set is nonempty for every nonempty finite
region: its maximum occupied coordinate is a concrete candidate. -/
theorem daiLiLowerTenthCandidates_nonempty
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    (daiLiLowerTenthCandidates region coordinate).Nonempty := by
  classical
  let support := daiLiCoordinateSupport region coordinate
  have hSupport : support.Nonempty := by
    simpa [support, daiLiCoordinateSupport] using hRegion.image coordinate
  let high := support.max' hSupport
  refine ⟨high, Finset.mem_filter.mpr ⟨Finset.max'_mem support hSupport, ?_⟩⟩
  have hAll : region.filter (fun q => coordinate q ≤ high) = region := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    change coordinate q ≤ support.max' hSupport
    apply Finset.le_max'
    simpa [support, daiLiCoordinateSupport] using
      (Finset.mem_image.mpr ⟨q, hq, rfl⟩ : coordinate q ∈ region.image coordinate)
  rw [hAll]
  change (region.card + 9) / 10 ≤ region.card
  omega

/-- The extremal lower coordinate used in DL24's plane-separator argument. -/
noncomputable def daiLiLowerTenthCoordinate
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) : ℝ :=
  (daiLiLowerTenthCandidates region coordinate).min'
    (daiLiLowerTenthCandidates_nonempty region coordinate hRegion)

omit [Fintype ι] [DecidableEq ι] in
/-- The selected lower-tenth coordinate is an actual occupied coordinate and
its closed lower halfspace contains at least one tenth of the parent. -/
theorem mem_daiLiLowerTenthCandidates
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    daiLiLowerTenthCoordinate region coordinate hRegion ∈
      daiLiLowerTenthCandidates region coordinate := by
  unfold daiLiLowerTenthCoordinate
  exact Finset.min'_mem _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The selected lower-tenth coordinate is genuinely extremal among concrete
candidate coordinates. -/
theorem daiLiLowerTenthCoordinate_le
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty)
    {candidate : ℝ} (hCandidate : candidate ∈ daiLiLowerTenthCandidates region coordinate) :
    daiLiLowerTenthCoordinate region coordinate hRegion ≤ candidate := by
  unfold daiLiLowerTenthCoordinate
  exact Finset.min'_le _ _ hCandidate

/-- Candidate upper tenth coordinates: actual occupied coordinates whose
closed upper halfspace contains at least one tenth of the parent. -/
def daiLiUpperTenthCandidates (region : Finset ι) (coordinate : ι → ℝ) : Finset ℝ :=
  (daiLiCoordinateSupport region coordinate).filter fun cut =>
    daiLiTenthCount region ≤ (region.filter fun q => cut ≤ coordinate q).card

omit [Fintype ι] [DecidableEq ι] in
/-- The upper-tenth candidate set is nonempty: its minimum occupied coordinate
is a concrete candidate. -/
theorem daiLiUpperTenthCandidates_nonempty
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    (daiLiUpperTenthCandidates region coordinate).Nonempty := by
  classical
  let support := daiLiCoordinateSupport region coordinate
  have hSupport : support.Nonempty := by
    simpa [support, daiLiCoordinateSupport] using hRegion.image coordinate
  let low := support.min' hSupport
  refine ⟨low, Finset.mem_filter.mpr ⟨Finset.min'_mem support hSupport, ?_⟩⟩
  have hAll : region.filter (fun q => low ≤ coordinate q) = region := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    change support.min' hSupport ≤ coordinate q
    apply Finset.min'_le
    simpa [support, daiLiCoordinateSupport] using
      (Finset.mem_image.mpr ⟨q, hq, rfl⟩ : coordinate q ∈ region.image coordinate)
  rw [hAll]
  change (region.card + 9) / 10 ≤ region.card
  omega

/-- The extremal upper coordinate used in DL24's plane-separator argument. -/
noncomputable def daiLiUpperTenthCoordinate
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) : ℝ :=
  (daiLiUpperTenthCandidates region coordinate).max'
    (daiLiUpperTenthCandidates_nonempty region coordinate hRegion)

omit [Fintype ι] [DecidableEq ι] in
/-- The selected upper-tenth coordinate is an actual occupied coordinate and
its closed upper halfspace contains at least one tenth of the parent. -/
theorem mem_daiLiUpperTenthCandidates
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    daiLiUpperTenthCoordinate region coordinate hRegion ∈
      daiLiUpperTenthCandidates region coordinate := by
  unfold daiLiUpperTenthCoordinate
  exact Finset.max'_mem _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The selected upper-tenth coordinate is genuinely extremal among concrete
candidate coordinates. -/
theorem le_daiLiUpperTenthCoordinate
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty)
    {candidate : ℝ} (hCandidate : candidate ∈ daiLiUpperTenthCandidates region coordinate) :
    candidate ≤ daiLiUpperTenthCoordinate region coordinate hRegion := by
  unfold daiLiUpperTenthCoordinate
  exact Finset.le_max' _ _ hCandidate

omit [Fintype ι] [DecidableEq ι] in
/-- A nonempty finite region has a positive exact tenth count. -/
theorem daiLiTenthCount_pos
    (region : Finset ι) (hRegion : region.Nonempty) :
    0 < daiLiTenthCount region := by
  unfold daiLiTenthCount
  have hCard : 0 < region.card := Finset.card_pos.mpr hRegion
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- Strictly below the selected lower-tenth coordinate lie fewer than one
tenth of the actual finite parent.  This proves the extremality fact used in
DL24 rather than storing it as part of a separator witness. -/
theorem card_coordinate_lt_daiLiLowerTenthCoordinate_lt_tenth
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    (region.filter fun q => coordinate q <
      daiLiLowerTenthCoordinate region coordinate hRegion).card <
      daiLiTenthCount region := by
  classical
  let lower := daiLiLowerTenthCoordinate region coordinate hRegion
  let below := region.filter fun q => coordinate q < lower
  by_contra hSmall
  have hCount : daiLiTenthCount region ≤ below.card := Nat.le_of_not_gt hSmall
  have hBelowNonempty : below.Nonempty := by
    apply Finset.card_pos.mp
    exact (daiLiTenthCount_pos region hRegion).trans_le hCount
  let belowSupport : Finset ℝ := below.image coordinate
  have hBelowSupport : belowSupport.Nonempty := by
    simpa [belowSupport] using hBelowNonempty.image coordinate
  let high := belowSupport.max' hBelowSupport
  have hHighInRegionSupport : high ∈ daiLiCoordinateSupport region coordinate := by
    have hHighInBelowSupport : high ∈ belowSupport := Finset.max'_mem _ _
    rcases Finset.mem_image.mp hHighInBelowSupport with ⟨q, hqBelow, hqHigh⟩
    exact Finset.mem_image.mpr ⟨q, (Finset.mem_filter.mp hqBelow).1, hqHigh⟩
  have hBelowSubset : below ⊆ region.filter fun q => coordinate q ≤ high := by
    intro q hqBelow
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqBelow).1, ?_⟩
    change coordinate q ≤ belowSupport.max' hBelowSupport
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨q, hqBelow, rfl⟩
  have hHighCandidate : high ∈ daiLiLowerTenthCandidates region coordinate := by
    refine Finset.mem_filter.mpr ⟨hHighInRegionSupport, ?_⟩
    exact hCount.trans (Finset.card_le_card hBelowSubset)
  have hLowerLeHigh : lower ≤ high := by
    simpa [lower] using
      (daiLiLowerTenthCoordinate_le region coordinate hRegion hHighCandidate)
  have hHighLtLower : high < lower := by
    have hHighInBelowSupport : high ∈ belowSupport := Finset.max'_mem _ _
    rcases Finset.mem_image.mp hHighInBelowSupport with ⟨q, hqBelow, hqHigh⟩
    rw [← hqHigh]
    exact (Finset.mem_filter.mp hqBelow).2
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Strictly above the selected upper-tenth coordinate lie fewer than one
tenth of the actual finite parent. -/
theorem card_daiLiUpperTenthCoordinate_lt_coordinate_lt_tenth
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    (region.filter fun q =>
      daiLiUpperTenthCoordinate region coordinate hRegion < coordinate q).card <
      daiLiTenthCount region := by
  classical
  let upper := daiLiUpperTenthCoordinate region coordinate hRegion
  let above := region.filter fun q => upper < coordinate q
  by_contra hSmall
  have hCount : daiLiTenthCount region ≤ above.card := Nat.le_of_not_gt hSmall
  have hAboveNonempty : above.Nonempty := by
    apply Finset.card_pos.mp
    exact (daiLiTenthCount_pos region hRegion).trans_le hCount
  let aboveSupport : Finset ℝ := above.image coordinate
  have hAboveSupport : aboveSupport.Nonempty := by
    simpa [aboveSupport] using hAboveNonempty.image coordinate
  let low := aboveSupport.min' hAboveSupport
  have hLowInRegionSupport : low ∈ daiLiCoordinateSupport region coordinate := by
    have hLowInAboveSupport : low ∈ aboveSupport := Finset.min'_mem _ _
    rcases Finset.mem_image.mp hLowInAboveSupport with ⟨q, hqAbove, hqLow⟩
    exact Finset.mem_image.mpr ⟨q, (Finset.mem_filter.mp hqAbove).1, hqLow⟩
  have hAboveSubset : above ⊆ region.filter fun q => low ≤ coordinate q := by
    intro q hqAbove
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqAbove).1, ?_⟩
    change aboveSupport.min' hAboveSupport ≤ coordinate q
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨q, hqAbove, rfl⟩
  have hLowCandidate : low ∈ daiLiUpperTenthCandidates region coordinate := by
    refine Finset.mem_filter.mpr ⟨hLowInRegionSupport, ?_⟩
    exact hCount.trans (Finset.card_le_card hAboveSubset)
  have hLowLeUpper : low ≤ upper := by
    simpa [upper] using
      (le_daiLiUpperTenthCoordinate region coordinate hRegion hLowCandidate)
  have hUpperLtLow : upper < low := by
    have hLowInAboveSupport : low ∈ aboveSupport := Finset.min'_mem _ _
    rcases Finset.mem_image.mp hLowInAboveSupport with ⟨q, hqAbove, hqLow⟩
    rw [← hqLow]
    exact (Finset.mem_filter.mp hqAbove).2
  linarith

/-- The central rectangle retained by the four extremal tenth coordinates. -/
noncomputable def daiLiTenthCore
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) : Finset ι :=
  region.filter fun q =>
    daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion ≤
        (embedding.point q).1 ∧
      (embedding.point q).1 ≤
        daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion ∧
      daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion ≤
        (embedding.point q).2 ∧
      (embedding.point q).2 ≤
        daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion

/-- The four strict exterior tails excluded by the tenth-coordinate rectangle. -/
noncomputable def daiLiTenthExterior
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) : Finset ι :=
  (region.filter fun q => (embedding.point q).1 <
      daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion) ∪
    (region.filter fun q =>
      daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
        (embedding.point q).1) ∪
    (region.filter fun q => (embedding.point q).2 <
      daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion) ∪
    (region.filter fun q =>
      daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
        (embedding.point q).2)

omit [Fintype ι] in
/-- The complement of the actual central rectangle is covered by its four
strict tenth-coordinate exterior tails. -/
theorem daiLiTenthCore_complement_subset_exterior
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) :
    region \ daiLiTenthCore embedding region hRegion ⊆
      daiLiTenthExterior embedding region hRegion := by
  classical
  intro q hq
  have hqRegion := (Finset.mem_sdiff.mp hq).1
  have hqNotCore := (Finset.mem_sdiff.mp hq).2
  by_cases hXLower : (embedding.point q).1 <
      daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion
  · simp [daiLiTenthExterior, hXLower, hqRegion]
  by_cases hXUpper : daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
      (embedding.point q).1
  · simp [daiLiTenthExterior, hXLower, hXUpper, hqRegion]
  by_cases hYLower : (embedding.point q).2 <
      daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion
  · simp [daiLiTenthExterior, hXLower, hXUpper, hYLower, hqRegion]
  by_cases hYUpper : daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
      (embedding.point q).2
  · simp [daiLiTenthExterior, hXLower, hXUpper, hYLower, hYUpper, hqRegion]
  exfalso
  apply hqNotCore
  refine Finset.mem_filter.mpr ⟨hqRegion, ?_⟩
  constructor
  · exact le_of_not_gt hXLower
  constructor
  · exact le_of_not_gt hXUpper
  constructor
  · exact le_of_not_gt hYLower
  · exact le_of_not_gt hYUpper

omit [Fintype ι] in
/-- The four exterior tails together contain at most four times one less than
the exact tenth count.  Keeping this integer slack is essential for the
source's strict sixty-percent central-region estimate. -/
theorem card_daiLiTenthExterior_le_four_mul_tenth_pred
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) :
    (daiLiTenthExterior embedding region hRegion).card ≤
      4 * (daiLiTenthCount region - 1) := by
  classical
  have hXLower := card_coordinate_lt_daiLiLowerTenthCoordinate_lt_tenth
    region (fun p => (embedding.point p).1) hRegion
  have hXUpper := card_daiLiUpperTenthCoordinate_lt_coordinate_lt_tenth
    region (fun p => (embedding.point p).1) hRegion
  have hYLower := card_coordinate_lt_daiLiLowerTenthCoordinate_lt_tenth
    region (fun p => (embedding.point p).2) hRegion
  have hYUpper := card_daiLiUpperTenthCoordinate_lt_coordinate_lt_tenth
    region (fun p => (embedding.point p).2) hRegion
  unfold daiLiTenthExterior
  calc
    _ ≤ ((region.filter fun q => (embedding.point q).1 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion) ∪
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
            (embedding.point q).1) ∪
        (region.filter fun q => (embedding.point q).2 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion)).card +
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
            (embedding.point q).2).card := Finset.card_union_le _ _
    _ ≤ (((region.filter fun q => (embedding.point q).1 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion) ∪
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
            (embedding.point q).1)).card +
        (region.filter fun q => (embedding.point q).2 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion).card) +
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
            (embedding.point q).2).card := by
      exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (((region.filter fun q => (embedding.point q).1 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion).card +
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
            (embedding.point q).1).card) +
        (region.filter fun q => (embedding.point q).2 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion).card) +
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
            (embedding.point q).2).card := by
      exact Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ 4 * (daiLiTenthCount region - 1) := by omega

omit [Fintype ι] in
/-- For `|V| >= 10`, the actual tenth-coordinate rectangle retains more than
sixty percent of the parent.  This is the finite cardinal inequality used by
DL24 before applying the planar packing estimate. -/
theorem six_tenths_region_card_lt_daiLiTenthCore_card
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) (hTen : 10 ≤ region.card) :
    6 * region.card / 10 < (daiLiTenthCore embedding region hRegion).card := by
  classical
  have hCoreSubset : daiLiTenthCore embedding region hRegion ⊆ region :=
    Finset.filter_subset _ _
  have hComplement := daiLiTenthCore_complement_subset_exterior embedding region hRegion
  have hExterior := card_daiLiTenthExterior_le_four_mul_tenth_pred embedding region hRegion
  have hComplementCard : (region \ daiLiTenthCore embedding region hRegion).card ≤
      4 * (daiLiTenthCount region - 1) :=
    (Finset.card_le_card hComplement).trans hExterior
  have hSplit := Finset.card_sdiff_add_card_eq_card hCoreSubset
  unfold daiLiTenthCount at hComplementCard
  omega

omit [Fintype ι] in
/-- Integer-scaled form of the strict sixty-percent central-region estimate,
suited for transport to the real packing inequalities. -/
theorem three_mul_region_card_lt_five_mul_daiLiTenthCore_card
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) (hTen : 10 ≤ region.card) :
    3 * region.card < 5 * (daiLiTenthCore embedding region hRegion).card := by
  have hCore := six_tenths_region_card_lt_daiLiTenthCore_card embedding region hRegion hTen
  omega

/-- The lower corner of the actual tenth-coordinate rectangle. -/
noncomputable def daiLiTenthCoreLower
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) : ℝ × ℝ :=
  (daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion,
    daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion)

/-- The upper corner of the actual tenth-coordinate rectangle. -/
noncomputable def daiLiTenthCoreUpper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) : ℝ × ℝ :=
  (daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion,
    daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion)

omit [Fintype ι] [DecidableEq ι] in
/-- Every retained central point is geometrically contained in its concrete
tenth-coordinate rectangle. -/
theorem mem_daiLiTenthCore_rectangle
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) {q : ι}
    (hq : q ∈ daiLiTenthCore embedding region hRegion) :
    embedding.point q ∈ rectangle
      (daiLiTenthCoreLower embedding region hRegion)
      (daiLiTenthCoreUpper embedding region hRegion) := by
  rcases Finset.mem_filter.mp hq with ⟨_, hxLower, hxUpper, hyLower, hyUpper⟩
  exact ⟨⟨hxLower, hxUpper⟩, ⟨hyLower, hyUpper⟩⟩

omit [Fintype ι] in
/-- The source's geometric wide-axis conclusion for the actual central
tenth-coordinate rectangle.  It follows from the proved finite packing
inequality, including the small-side corner through the expanded-box bound. -/
theorem daiLiTenthCore_has_wide_axis
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) (hTen : 10 ≤ region.card) :
    Real.sqrt ((region.card : ℝ) / 10) <
        (daiLiTenthCoreUpper embedding region hRegion).1 -
          (daiLiTenthCoreLower embedding region hRegion).1 ∨
      Real.sqrt ((region.card : ℝ) / 10) <
        (daiLiTenthCoreUpper embedding region hRegion).2 -
          (daiLiTenthCoreLower embedding region hRegion).2 := by
  classical
  let core := daiLiTenthCore embedding region hRegion
  let lower := daiLiTenthCoreLower embedding region hRegion
  let upper := daiLiTenthCoreUpper embedding region hRegion
  let width := upper.1 - lower.1
  let height := upper.2 - lower.2
  let radius := Real.sqrt ((region.card : ℝ) / 10)
  have hThreeNat := three_mul_region_card_lt_five_mul_daiLiTenthCore_card
    embedding region hRegion hTen
  have hThreeCoreNat : 3 * region.card < 5 * core.card := by
    simpa [core] using hThreeNat
  have hThree : 3 * (region.card : ℝ) < 5 * (core.card : ℝ) := by
    exact_mod_cast hThreeCoreNat
  have hCorePos : 0 < core.card := by
    omega
  obtain ⟨q, hqCore⟩ := Finset.card_pos.mp hCorePos
  have hqRectangle : embedding.point q ∈ rectangle lower upper := by
    simpa [core, lower, upper] using
      (mem_daiLiTenthCore_rectangle embedding region hRegion hqCore)
  rcases hqRectangle with ⟨⟨hqxLower, hqxUpper⟩, ⟨hqyLower, hqyUpper⟩⟩
  have hWidthNonneg : 0 ≤ width := by
    dsimp [width]
    linarith
  have hHeightNonneg : 0 ≤ height := by
    dsimp [height]
    linarith
  have hRadicand : 0 ≤ (region.card : ℝ) / 10 := by positivity
  have hRadiusNonneg : 0 ≤ radius := by
    dsimp [radius]
    exact Real.sqrt_nonneg _
  have hRadiusSq : radius ^ 2 = (region.card : ℝ) / 10 := by
    dsimp [radius]
    exact Real.sq_sqrt hRadicand
  have hRegionReal : (10 : ℝ) ≤ region.card := by exact_mod_cast hTen
  have hRadiusOne : 1 ≤ radius := by
    nlinarith
  by_contra hWide
  push Not at hWide
  obtain ⟨hWidth, hHeight⟩ := hWide
  have hPack := packing_card_div_two_le_expanded_area embedding core lower upper
    (by dsimp [lower, upper]; linarith)
    (by dsimp [lower, upper]; linarith)
    (by
      intro p hp
      simpa [core, lower, upper] using
        (mem_daiLiTenthCore_rectangle embedding region hRegion hp))
  have hWidthBound : width + 2 * packingRadius ≤ (1 + 2 * packingRadius) * radius := by
    calc
      width + 2 * packingRadius ≤ radius + 2 * packingRadius := by linarith
      _ ≤ (1 + 2 * packingRadius) * radius := by
        nlinarith [packingRadius_pos.le]
  have hHeightBound : height + 2 * packingRadius ≤ (1 + 2 * packingRadius) * radius := by
    calc
      height + 2 * packingRadius ≤ radius + 2 * packingRadius := by linarith
      _ ≤ (1 + 2 * packingRadius) * radius := by
        nlinarith [packingRadius_pos.le]
  have hExpanded : (width + 2 * packingRadius) * (height + 2 * packingRadius) ≤
      3 * radius ^ 2 := by
    calc
      _ ≤ ((1 + 2 * packingRadius) * radius) *
          ((1 + 2 * packingRadius) * radius) := by
        apply mul_le_mul hWidthBound hHeightBound
        · nlinarith [packingRadius_pos.le]
        · exact mul_nonneg (by nlinarith [packingRadius_pos.le]) hRadiusNonneg
      _ = (1 + 2 * packingRadius) ^ 2 * radius ^ 2 := by ring
      _ ≤ 3 * radius ^ 2 := by
        exact mul_le_mul_of_nonneg_right one_add_two_mul_packingRadius_sq_le_three
          (sq_nonneg radius)
  dsimp [width, height] at hPack hExpanded
  nlinarith

/-- The `i`th half-open equal-width vertical band of an actual finite region.
Half-open ownership is deliberate: it makes the finite pigeonhole family
pairwise disjoint before support-free cuts are perturbed inside a selected
band. -/
def daiLiVerticalEqualBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lower upper : ℝ) (m : Nat) (i : Fin m) : Finset ι :=
  region.filter fun q =>
    lower + (i : ℝ) * ((upper - lower) / m) ≤ (embedding.point q).1 ∧
      (embedding.point q).1 < lower + ((i : ℝ) + 1) * ((upper - lower) / m)

omit [Fintype ι] in
/-- Distinct half-open equal-width vertical bands are disjoint whenever the
source interval has positive span. -/
theorem daiLiVerticalEqualBand_pairwise_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper : ℝ} {m : Nat} (hM : 0 < m) (hSpan : 0 < upper - lower) :
    ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (daiLiVerticalEqualBand embedding region lower upper m) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro i hi j hj hij
  by_contra hneq
  obtain ⟨q, hq⟩ := hij
  have hqi := (Finset.mem_inter.mp hq).1
  have hqj := (Finset.mem_inter.mp hq).2
  have hStep : 0 < (upper - lower) / (m : ℝ) := by
    apply div_pos hSpan
    exact_mod_cast hM
  have hqiBounds := (Finset.mem_filter.mp hqi).2
  have hqjBounds := (Finset.mem_filter.mp hqj).2
  rcases lt_or_gt_of_ne hneq with hij | hji
  · have hIndexNat : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hij
    have hIndex : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hIndexNat
    nlinarith
  · have hIndexNat : j.val + 1 ≤ i.val := Nat.succ_le_iff.mpr hji
    have hIndex : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hIndexNat
    nlinarith

omit [Fintype ι] in
/-- Finite pigeonhole for the actual equal-width bands.  The hypothesis is
the source average inequality, not a supplied low-count band: pairwise
disjointness and containment in `region` force one concrete band below it. -/
theorem exists_daiLiVerticalEqualBand_card_le
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper bound : ℝ} {m : Nat}
    (hM : 0 < m) (hSpan : 0 < upper - lower)
    (hAverage : (region.card : ℝ) ≤ m * bound) :
    ∃ i : Fin m,
      ((daiLiVerticalEqualBand embedding region lower upper m i).card : ℝ) ≤ bound := by
  classical
  let bands := daiLiVerticalEqualBand embedding region lower upper m
  have hDisjoint : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint bands := by
    simpa [bands] using daiLiVerticalEqualBand_pairwise_disjoint
      embedding region hM hSpan
  have hUnionSubset : (Finset.univ.biUnion bands) ⊆ region := by
    intro q hq
    rcases Finset.mem_biUnion.mp hq with ⟨i, _hi, hqBand⟩
    exact (Finset.mem_filter.mp hqBand).1
  have hUnionCard : (Finset.univ.biUnion bands).card ≤ region.card :=
    Finset.card_le_card hUnionSubset
  have hSumNat : ∑ i ∈ (Finset.univ : Finset (Fin m)), (bands i).card ≤ region.card := by
    rw [← Finset.card_biUnion hDisjoint]
    exact hUnionCard
  have hSumReal : ∑ i ∈ (Finset.univ : Finset (Fin m)), ((bands i).card : ℝ) ≤
      region.card := by
    exact_mod_cast hSumNat
  by_contra hExists
  push Not at hExists
  have hEach : ∀ i : Fin m, bound < ((bands i).card : ℝ) := by
    intro i
    simpa [bands] using hExists i
  have hSumStrict : (m : ℝ) * bound <
      ∑ i ∈ (Finset.univ : Finset (Fin m)), ((bands i).card : ℝ) := by
    calc
      (m : ℝ) * bound = ∑ _i ∈ (Finset.univ : Finset (Fin m)), bound := by simp
      _ < ∑ i ∈ (Finset.univ : Finset (Fin m)), ((bands i).card : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨⟨0, hM⟩, Finset.mem_univ _⟩
        · intro i _hi
          exact hEach i
  linarith

/-- The explicit number of source-scale bands used for the plane-separator
pigeonhole.  The successor removes floor-boundary ambiguity and leaves room
for support-free perturbation inside a selected band. -/
noncomputable def daiLiSeparatorBandCount (ell : ℝ) (n : Nat) : Nat :=
  Nat.floor (Real.sqrt n / (8 * ell)) + 1

/-- The explicit band count is positive without any side condition. -/
theorem daiLiSeparatorBandCount_pos (ell : ℝ) (n : Nat) :
    0 < daiLiSeparatorBandCount ell n := by
  unfold daiLiSeparatorBandCount
  omega

/-- Under the source's positive length scale, the chosen number of bands is
strictly larger than `sqrt(n) / (8 ell)`. -/
theorem daiLi_lt_separatorBandCount
    {ell : ℝ} {n : Nat} (hEll : 0 < ell) :
    Real.sqrt n / (8 * ell) < daiLiSeparatorBandCount ell n := by
  unfold daiLiSeparatorBandCount
  have hNonneg : 0 ≤ Real.sqrt n / (8 * ell) := by positivity
  have hFloor : Real.sqrt n / (8 * ell) <
      (Nat.floor (Real.sqrt n / (8 * ell)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  simpa using hFloor

/-- In the `ell >= 1` source regime, the selected band count leaves strictly
more than `ell` of geometric width before the wide-axis endpoint. -/
theorem daiLi_separatorBandCount_mul_ell_lt_sqrt_tenth
    {ell : ℝ} {n : Nat} (hN : 0 < n) (hEll : 0 < ell)
    (hScale : ell ≤ Real.sqrt n / 8) :
    (daiLiSeparatorBandCount ell n : ℝ) * ell < Real.sqrt ((n : ℝ) / 10) := by
  let m := daiLiSeparatorBandCount ell n
  let radius := Real.sqrt (n : ℝ)
  let tenthRadius := Real.sqrt ((n : ℝ) / 10)
  have hMFloor : (m : ℝ) ≤ radius / (8 * ell) + 1 := by
    dsimp [m, daiLiSeparatorBandCount, radius]
    have hNonneg : 0 ≤ Real.sqrt (n : ℝ) / (8 * ell) := by positivity
    have hFloor := Nat.floor_le hNonneg
    norm_num at hFloor ⊢
    linarith
  have hMul : (m : ℝ) * ell ≤ radius / 8 + ell := by
    calc
      (m : ℝ) * ell ≤ (radius / (8 * ell) + 1) * ell :=
        mul_le_mul_of_nonneg_right hMFloor hEll.le
      _ = radius / 8 + ell := by
        field_simp [hEll.ne']
  have hRadiusSq : radius ^ 2 = (n : ℝ) := by
    dsimp [radius]
    exact Real.sq_sqrt (by positivity)
  have hTenthRadiusSq : tenthRadius ^ 2 = (n : ℝ) / 10 := by
    dsimp [tenthRadius]
    exact Real.sq_sqrt (by positivity)
  have hRadiusPos : 0 < radius := by
    dsimp [radius]
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hTenthRadiusNonneg : 0 ≤ tenthRadius := by
    dsimp [tenthRadius]
    exact Real.sqrt_nonneg _
  have hQuarterLt : radius / 4 < tenthRadius := by
    nlinarith
  have hScale' : ell ≤ radius / 8 := by simpa [radius] using hScale
  calc
    (m : ℝ) * ell ≤ radius / 8 + ell := hMul
    _ ≤ radius / 4 := by linarith
    _ < tenthRadius := hQuarterLt

/-- The explicit band count makes the source average `8 ell sqrt(n)` large
enough to cover all `n` points. -/
theorem daiLi_separatorBandCount_average
    {ell : ℝ} {n : Nat} (hN : 0 < n) (hEll : 0 < ell) :
    (n : ℝ) ≤ (daiLiSeparatorBandCount ell n : ℝ) *
      (8 * ell * Real.sqrt n) := by
  let m := daiLiSeparatorBandCount ell n
  let radius := Real.sqrt (n : ℝ)
  have hRatio : radius / (8 * ell) < (m : ℝ) := by
    simpa [m, radius] using daiLi_lt_separatorBandCount (n := n) hEll
  have hDenPos : 0 < 8 * ell := by positivity
  have hProduct : radius < (m : ℝ) * (8 * ell) := by
    exact (div_lt_iff₀ hDenPos).mp hRatio
  have hRadiusPos : 0 < radius := by
    dsimp [radius]
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hRadiusSq : radius ^ 2 = (n : ℝ) := by
    dsimp [radius]
    exact Real.sq_sqrt (by positivity)
  have hSquare : radius ^ 2 < ((m : ℝ) * (8 * ell)) * radius := by
    simpa [pow_two] using mul_lt_mul_of_pos_right hProduct hRadiusPos
  dsimp [m, radius] at hSquare hRadiusSq ⊢
  nlinarith

/-- The two geometric endpoints of an indexed equal-width vertical band. -/
def daiLiVerticalBandLower (lower upper : ℝ) (m : Nat) (i : Fin m) : ℝ :=
  lower + (i : ℝ) * ((upper - lower) / m)

def daiLiVerticalBandUpper (lower upper : ℝ) (m : Nat) (i : Fin m) : ℝ :=
  lower + ((i : ℝ) + 1) * ((upper - lower) / m)

/-- Source-faithful equal-band selection in one already-wide vertical axis.
The index is constructed by the finite pigeonhole argument, and the returned
width is strict so it can be support-free perturbed without enlarging the
selected strip. -/
theorem exists_daiLiVerticalLowBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {ell lower upper : ℝ} {n : Nat}
    (hN : 0 < n) (hEll : 0 < ell) (hScale : ell ≤ Real.sqrt n / 8)
    (hCard : region.card ≤ n)
    (hSpan : Real.sqrt ((n : ℝ) / 10) < upper - lower) :
    ∃ i : Fin (daiLiSeparatorBandCount ell n),
      ell < daiLiVerticalBandUpper lower upper (daiLiSeparatorBandCount ell n) i -
        daiLiVerticalBandLower lower upper (daiLiSeparatorBandCount ell n) i ∧
      ((daiLiVerticalEqualBand embedding region lower upper
        (daiLiSeparatorBandCount ell n) i).card : ℝ) ≤
        8 * ell * Real.sqrt n := by
  let m := daiLiSeparatorBandCount ell n
  have hM : 0 < m := by
    simpa [m] using daiLiSeparatorBandCount_pos ell n
  have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
  have hBandBudget : (m : ℝ) * ell < upper - lower := by
    calc
      (m : ℝ) * ell < Real.sqrt ((n : ℝ) / 10) := by
        simpa [m] using daiLi_separatorBandCount_mul_ell_lt_sqrt_tenth hN hEll hScale
      _ < upper - lower := hSpan
  have hBandWidth : ell < (upper - lower) / m := by
    apply (lt_div_iff₀ hMReal).2
    nlinarith
  have hAverage : (region.card : ℝ) ≤ (m : ℝ) * (8 * ell * Real.sqrt n) := by
    have hRegionCard : (region.card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hCard
    exact hRegionCard.trans (by
      simpa [m] using daiLi_separatorBandCount_average hN hEll)
  have hPositiveSpan : 0 < upper - lower := by
    exact (Real.sqrt_nonneg ((n : ℝ) / 10)).trans_lt hSpan
  obtain ⟨i, hi⟩ := exists_daiLiVerticalEqualBand_card_le embedding region
    hM hPositiveSpan hAverage
  refine ⟨i, ?_, ?_⟩
  · dsimp [daiLiVerticalBandUpper, daiLiVerticalBandLower]
    linarith
  · simpa [m] using hi

/-- The horizontal counterpart of the actual half-open equal-width bands.
Keeping both orientations explicit means the plane selector below does not
silently rotate or replace the given physical embedding. -/
def daiLiHorizontalEqualBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lower upper : ℝ) (m : Nat) (i : Fin m) : Finset ι :=
  region.filter fun q =>
    lower + (i : ℝ) * ((upper - lower) / m) ≤ (embedding.point q).2 ∧
      (embedding.point q).2 < lower + ((i : ℝ) + 1) * ((upper - lower) / m)

omit [Fintype ι] in
theorem daiLiHorizontalEqualBand_pairwise_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper : ℝ} {m : Nat} (hM : 0 < m) (hSpan : 0 < upper - lower) :
    ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (daiLiHorizontalEqualBand embedding region lower upper m) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro i hi j hj hij
  by_contra hneq
  obtain ⟨q, hq⟩ := hij
  have hqi := (Finset.mem_inter.mp hq).1
  have hqj := (Finset.mem_inter.mp hq).2
  have hStep : 0 < (upper - lower) / (m : ℝ) := by
    apply div_pos hSpan
    exact_mod_cast hM
  have hqiBounds := (Finset.mem_filter.mp hqi).2
  have hqjBounds := (Finset.mem_filter.mp hqj).2
  rcases lt_or_gt_of_ne hneq with hij | hji
  · have hIndexNat : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hij
    have hIndex : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hIndexNat
    nlinarith
  · have hIndexNat : j.val + 1 ≤ i.val := Nat.succ_le_iff.mpr hji
    have hIndex : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hIndexNat
    nlinarith

omit [Fintype ι] in
theorem exists_daiLiHorizontalEqualBand_card_le
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper bound : ℝ} {m : Nat}
    (hM : 0 < m) (hSpan : 0 < upper - lower)
    (hAverage : (region.card : ℝ) ≤ m * bound) :
    ∃ i : Fin m,
      ((daiLiHorizontalEqualBand embedding region lower upper m i).card : ℝ) ≤ bound := by
  classical
  let bands := daiLiHorizontalEqualBand embedding region lower upper m
  have hDisjoint : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint bands := by
    simpa [bands] using daiLiHorizontalEqualBand_pairwise_disjoint
      embedding region hM hSpan
  have hUnionSubset : (Finset.univ.biUnion bands) ⊆ region := by
    intro q hq
    rcases Finset.mem_biUnion.mp hq with ⟨i, _hi, hqBand⟩
    exact (Finset.mem_filter.mp hqBand).1
  have hUnionCard : (Finset.univ.biUnion bands).card ≤ region.card :=
    Finset.card_le_card hUnionSubset
  have hSumNat : ∑ i ∈ (Finset.univ : Finset (Fin m)), (bands i).card ≤ region.card := by
    rw [← Finset.card_biUnion hDisjoint]
    exact hUnionCard
  have hSumReal : ∑ i ∈ (Finset.univ : Finset (Fin m)), ((bands i).card : ℝ) ≤
      region.card := by
    exact_mod_cast hSumNat
  by_contra hExists
  push Not at hExists
  have hEach : ∀ i : Fin m, bound < ((bands i).card : ℝ) := by
    intro i
    simpa [bands] using hExists i
  have hSumStrict : (m : ℝ) * bound <
      ∑ i ∈ (Finset.univ : Finset (Fin m)), ((bands i).card : ℝ) := by
    calc
      (m : ℝ) * bound = ∑ _i ∈ (Finset.univ : Finset (Fin m)), bound := by simp
      _ < ∑ i ∈ (Finset.univ : Finset (Fin m)), ((bands i).card : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨⟨0, hM⟩, Finset.mem_univ _⟩
        · intro i _hi
          exact hEach i
  linarith

theorem exists_daiLiHorizontalLowBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {ell lower upper : ℝ} {n : Nat}
    (hN : 0 < n) (hEll : 0 < ell) (hScale : ell ≤ Real.sqrt n / 8)
    (hCard : region.card ≤ n)
    (hSpan : Real.sqrt ((n : ℝ) / 10) < upper - lower) :
    ∃ i : Fin (daiLiSeparatorBandCount ell n),
      ell < daiLiVerticalBandUpper lower upper (daiLiSeparatorBandCount ell n) i -
        daiLiVerticalBandLower lower upper (daiLiSeparatorBandCount ell n) i ∧
      ((daiLiHorizontalEqualBand embedding region lower upper
        (daiLiSeparatorBandCount ell n) i).card : ℝ) ≤
        8 * ell * Real.sqrt n := by
  let m := daiLiSeparatorBandCount ell n
  have hM : 0 < m := by
    simpa [m] using daiLiSeparatorBandCount_pos ell n
  have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
  have hBandBudget : (m : ℝ) * ell < upper - lower := by
    calc
      (m : ℝ) * ell < Real.sqrt ((n : ℝ) / 10) := by
        simpa [m] using daiLi_separatorBandCount_mul_ell_lt_sqrt_tenth hN hEll hScale
      _ < upper - lower := hSpan
  have hBandWidth : ell < (upper - lower) / m := by
    apply (lt_div_iff₀ hMReal).2
    nlinarith
  have hAverage : (region.card : ℝ) ≤ (m : ℝ) * (8 * ell * Real.sqrt n) := by
    have hRegionCard : (region.card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hCard
    exact hRegionCard.trans (by
      simpa [m] using daiLi_separatorBandCount_average hN hEll)
  have hPositiveSpan : 0 < upper - lower := by
    exact (Real.sqrt_nonneg ((n : ℝ) / 10)).trans_lt hSpan
  obtain ⟨i, hi⟩ := exists_daiLiHorizontalEqualBand_card_le embedding region
    hM hPositiveSpan hAverage
  refine ⟨i, ?_, ?_⟩
  · dsimp [daiLiVerticalBandUpper, daiLiVerticalBandLower]
    linarith
  · simpa [m] using hi

/-! ## Concrete two-line separator geometry

The source's recursive branch uses two support-free parallel lines.  These
definitions deliberately retain the actual finite parent region and both
coordinates; they are not a separator witness structure.  The selector which
constructs suitable cuts is the remaining geometric obligation.
-/

/-- Qubits of a finite region strictly below the first horizontal cut. -/
def daiLiHorizontalSeparatorLower
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι) (lowerCut : ℝ) : Finset ι :=
  region.filter fun q => (embedding.point q).2 < lowerCut

/-- Qubits of a finite region strictly between two horizontal cuts. -/
def daiLiHorizontalSeparatorStrip
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lowerCut upperCut : ℝ) : Finset ι :=
  region.filter fun q => lowerCut < (embedding.point q).2 ∧ (embedding.point q).2 < upperCut

/-- Qubits of a finite region strictly above the second horizontal cut. -/
def daiLiHorizontalSeparatorUpper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι) (upperCut : ℝ) : Finset ι :=
  region.filter fun q => upperCut < (embedding.point q).2

/-- Both separator lines avoid all embedded points assigned to the finite
parent region. -/
def DaiLiHorizontalCutsAvoid
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lowerCut upperCut : ℝ) : Prop :=
  ∀ q ∈ region,
    (embedding.point q).2 ≠ lowerCut ∧ (embedding.point q).2 ≠ upperCut

omit [Fintype ι] in
/-- The three actual pieces cover the parent region when both selected lines
are support-free. -/
theorem daiLiHorizontalSeparator_cover
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut) :
    daiLiHorizontalSeparatorLower embedding region lowerCut ∪
        daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiHorizontalSeparatorUpper embedding region upperCut = region := by
  classical
  ext q
  by_cases hq : q ∈ region
  · obtain ⟨hNotLower, hNotUpper⟩ := hAvoid q hq
    by_cases hBelow : (embedding.point q).2 < lowerCut
    · have hNotMiddle : ¬ lowerCut < (embedding.point q).2 := not_lt_of_ge hBelow.le
      simp [daiLiHorizontalSeparatorLower, daiLiHorizontalSeparatorStrip,
        daiLiHorizontalSeparatorUpper, hq, hBelow, hNotMiddle]
    · have hLower : lowerCut < (embedding.point q).2 := by
        rcases lt_or_eq_of_le (le_of_not_gt hBelow) with hlt | heq
        · exact hlt
        · exact False.elim (hNotLower heq.symm)
      by_cases hMiddle : (embedding.point q).2 < upperCut
      · have hNotUpperSide : ¬ upperCut < (embedding.point q).2 := not_lt_of_ge hMiddle.le
        simp [daiLiHorizontalSeparatorLower, daiLiHorizontalSeparatorStrip,
          daiLiHorizontalSeparatorUpper, hq, hBelow, hLower, hMiddle, hNotUpperSide]
      · have hUpper : upperCut < (embedding.point q).2 := by
          rcases lt_or_eq_of_le (le_of_not_gt hMiddle) with hlt | heq
          · exact hlt
          · exact False.elim (hNotUpper heq.symm)
        simp [daiLiHorizontalSeparatorLower, daiLiHorizontalSeparatorStrip,
          daiLiHorizontalSeparatorUpper, hq, hBelow, hLower, hMiddle, hUpper]
  · simp [daiLiHorizontalSeparatorLower, daiLiHorizontalSeparatorStrip,
      daiLiHorizontalSeparatorUpper, hq]

omit [Fintype ι] [DecidableEq ι] in
/-- The two exterior sides are disjoint whenever the two selected lines are
ordered. -/
theorem daiLiHorizontalSeparatorLower_disjoint_upper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ} (hCuts : lowerCut ≤ upperCut) :
    Disjoint (daiLiHorizontalSeparatorLower embedding region lowerCut)
      (daiLiHorizontalSeparatorUpper embedding region upperCut) := by
  apply Finset.disjoint_left.mpr
  intro q hLower hUpper
  have hBelow := (Finset.mem_filter.mp hLower).2
  have hAbove := (Finset.mem_filter.mp hUpper).2
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- A lower bound on a vertical coordinate difference gives the same lower
bound on the stored Euclidean distance.  This local version is kept here
because the Part-I selector must not depend on the later grid partition. -/
private theorem daiLi_le_distance_of_le_abs_vertical_coordinate
    (embedding : UnitSeparatedEmbedding2D ι) {p q : ι} {r : ℝ}
    (h : r ≤ |(embedding.point p).2 - (embedding.point q).2|) :
    r ≤ embedding.distance p q := by
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  have hSq : ((embedding.point p).2 - (embedding.point q).2) ^ 2 ≤
      ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
    nlinarith [sq_nonneg ((embedding.point p).1 - (embedding.point q).1)]
  exact h.trans (Real.abs_le_sqrt hSq)

omit [Fintype ι] [DecidableEq ι] in
/-- The two exterior pieces constructed by actual horizontal cuts are at least
the cut width apart in the Euclidean embedding. -/
theorem daiLiHorizontalSeparatorSides_separated
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut threshold : ℝ} (hWidth : threshold ≤ upperCut - lowerCut)
    {p q : ι}
    (hp : p ∈ daiLiHorizontalSeparatorLower embedding region lowerCut)
    (hq : q ∈ daiLiHorizontalSeparatorUpper embedding region upperCut) :
    threshold ≤ embedding.distance p q := by
  have hpBelow := (Finset.mem_filter.mp hp).2
  have hqAbove := (Finset.mem_filter.mp hq).2
  apply daiLi_le_distance_of_le_abs_vertical_coordinate embedding
  rw [le_abs]
  right
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- A strictly over-wide candidate band can be perturbed to two actual
support-free horizontal cuts while retaining the source separation scale.
This is the finite form of the final perturbation sentence in DL24's
plane-separator lemma; no cut is supplied by the caller. -/
theorem exists_daiLiHorizontalCutsAvoid_of_lt_width
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {candidateLower candidateUpper threshold : ℝ}
    (hThreshold : 0 ≤ threshold)
    (hWidth : threshold < candidateUpper - candidateLower) :
    ∃ lowerCut upperCut : ℝ,
      candidateLower < lowerCut ∧ lowerCut < candidateUpper ∧
      candidateLower < upperCut ∧ upperCut < candidateUpper ∧
      threshold < upperCut - lowerCut ∧
      DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut := by
  classical
  let support : Finset ℝ := region.image fun q => (embedding.point q).2
  let lowerWindowUpper := (candidateLower + candidateUpper - threshold) / 2
  let upperWindowLower := (candidateLower + candidateUpper + threshold) / 2
  have hLowerWindow : candidateLower < lowerWindowUpper := by
    dsimp [lowerWindowUpper]
    linarith
  have hUpperWindow : upperWindowLower < candidateUpper := by
    dsimp [upperWindowLower]
    linarith
  obtain ⟨lowerCut, hLower, hLowerUpper, hLowerFree⟩ :=
    exists_real_in_openInterval_not_mem_finset support hLowerWindow
  obtain ⟨upperCut, hUpperLower, hUpper, hUpperFree⟩ :=
    exists_real_in_openInterval_not_mem_finset support hUpperWindow
  refine ⟨lowerCut, upperCut, hLower, hLowerUpper.trans
    (by dsimp [lowerWindowUpper]; linarith),
    (by dsimp [upperWindowLower] at hUpperLower; linarith), hUpper, ?_, ?_⟩
  · dsimp [lowerWindowUpper] at hLowerUpper
    dsimp [upperWindowLower] at hUpperLower
    linarith
  · intro q hq
    constructor
    · intro hqLower
      apply hLowerFree
      exact Finset.mem_image.mpr ⟨q, hq, hqLower⟩
    · intro hqUpper
      apply hUpperFree
      exact Finset.mem_image.mpr ⟨q, hq, hqUpper⟩

/-- Qubits of a finite region strictly left of the first vertical cut. -/
def daiLiVerticalSeparatorLower
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι) (lowerCut : ℝ) : Finset ι :=
  region.filter fun q => (embedding.point q).1 < lowerCut

/-- Qubits of a finite region strictly between two vertical cuts. -/
def daiLiVerticalSeparatorStrip
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lowerCut upperCut : ℝ) : Finset ι :=
  region.filter fun q => lowerCut < (embedding.point q).1 ∧ (embedding.point q).1 < upperCut

/-- Qubits of a finite region strictly right of the second vertical cut. -/
def daiLiVerticalSeparatorUpper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι) (upperCut : ℝ) : Finset ι :=
  region.filter fun q => upperCut < (embedding.point q).1

/-- Both vertical separator lines avoid every embedded point in the actual
finite parent region. -/
def DaiLiVerticalCutsAvoid
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lowerCut upperCut : ℝ) : Prop :=
  ∀ q ∈ region,
    (embedding.point q).1 ≠ lowerCut ∧ (embedding.point q).1 ≠ upperCut

omit [Fintype ι] in
/-- Support-free vertical cuts partition their actual finite parent into three
disjointly owned pieces. -/
theorem daiLiVerticalSeparator_cover
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut) :
    daiLiVerticalSeparatorLower embedding region lowerCut ∪
        daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiVerticalSeparatorUpper embedding region upperCut = region := by
  classical
  ext q
  by_cases hq : q ∈ region
  · obtain ⟨hNotLower, hNotUpper⟩ := hAvoid q hq
    by_cases hBelow : (embedding.point q).1 < lowerCut
    · have hNotMiddle : ¬ lowerCut < (embedding.point q).1 := not_lt_of_ge hBelow.le
      simp [daiLiVerticalSeparatorLower, daiLiVerticalSeparatorStrip,
        daiLiVerticalSeparatorUpper, hq, hBelow, hNotMiddle]
    · have hLower : lowerCut < (embedding.point q).1 := by
        rcases lt_or_eq_of_le (le_of_not_gt hBelow) with hlt | heq
        · exact hlt
        · exact False.elim (hNotLower heq.symm)
      by_cases hMiddle : (embedding.point q).1 < upperCut
      · have hNotUpperSide : ¬ upperCut < (embedding.point q).1 := not_lt_of_ge hMiddle.le
        simp [daiLiVerticalSeparatorLower, daiLiVerticalSeparatorStrip,
          daiLiVerticalSeparatorUpper, hq, hBelow, hLower, hMiddle, hNotUpperSide]
      · have hUpper : upperCut < (embedding.point q).1 := by
          rcases lt_or_eq_of_le (le_of_not_gt hMiddle) with hlt | heq
          · exact hlt
          · exact False.elim (hNotUpper heq.symm)
        simp [daiLiVerticalSeparatorLower, daiLiVerticalSeparatorStrip,
          daiLiVerticalSeparatorUpper, hq, hBelow, hLower, hMiddle, hUpper]
  · simp [daiLiVerticalSeparatorLower, daiLiVerticalSeparatorStrip,
      daiLiVerticalSeparatorUpper, hq]

omit [Fintype ι] [DecidableEq ι] in
/-- Opposite vertical sides are separated in the actual Euclidean embedding. -/
theorem daiLiVerticalSeparatorSides_separated
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut threshold : ℝ} (hWidth : threshold ≤ upperCut - lowerCut)
    {p q : ι}
    (hp : p ∈ daiLiVerticalSeparatorLower embedding region lowerCut)
    (hq : q ∈ daiLiVerticalSeparatorUpper embedding region upperCut) :
    threshold ≤ embedding.distance p q := by
  have hpBelow := (Finset.mem_filter.mp hp).2
  have hqAbove := (Finset.mem_filter.mp hq).2
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  have hSq : ((embedding.point p).1 - (embedding.point q).1) ^ 2 ≤
      ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
    nlinarith [sq_nonneg ((embedding.point p).2 - (embedding.point q).2)]
  have hCoordinate : upperCut - lowerCut ≤
      (embedding.point q).1 - (embedding.point p).1 := by
    linarith
  calc
    threshold ≤ upperCut - lowerCut := hWidth
    _ ≤ (embedding.point q).1 - (embedding.point p).1 := hCoordinate
    _ ≤ |(embedding.point p).1 - (embedding.point q).1| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    _ ≤ _ := Real.abs_le_sqrt hSq

omit [Fintype ι] [DecidableEq ι] in
/-- The source's perturbation step is available in the vertical orientation
as well, computed only from the finite parent support. -/
theorem exists_daiLiVerticalCutsAvoid_of_lt_width
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {candidateLower candidateUpper threshold : ℝ}
    (hThreshold : 0 ≤ threshold)
    (hWidth : threshold < candidateUpper - candidateLower) :
    ∃ lowerCut upperCut : ℝ,
      candidateLower < lowerCut ∧ lowerCut < candidateUpper ∧
      candidateLower < upperCut ∧ upperCut < candidateUpper ∧
      threshold < upperCut - lowerCut ∧
      DaiLiVerticalCutsAvoid embedding region lowerCut upperCut := by
  classical
  let support : Finset ℝ := region.image fun q => (embedding.point q).1
  let lowerWindowUpper := (candidateLower + candidateUpper - threshold) / 2
  let upperWindowLower := (candidateLower + candidateUpper + threshold) / 2
  have hLowerWindow : candidateLower < lowerWindowUpper := by
    dsimp [lowerWindowUpper]
    linarith
  have hUpperWindow : upperWindowLower < candidateUpper := by
    dsimp [upperWindowLower]
    linarith
  obtain ⟨lowerCut, hLower, hLowerUpper, hLowerFree⟩ :=
    exists_real_in_openInterval_not_mem_finset support hLowerWindow
  obtain ⟨upperCut, hUpperLower, hUpper, hUpperFree⟩ :=
    exists_real_in_openInterval_not_mem_finset support hUpperWindow
  refine ⟨lowerCut, upperCut, hLower, hLowerUpper.trans
    (by dsimp [lowerWindowUpper]; linarith),
    (by dsimp [upperWindowLower] at hUpperLower; linarith), hUpper, ?_, ?_⟩
  · dsimp [lowerWindowUpper] at hLowerUpper
    dsimp [upperWindowLower] at hUpperLower
    linarith
  · intro q hq
    constructor
    · intro hqLower
      apply hLowerFree
      exact Finset.mem_image.mpr ⟨q, hq, hqLower⟩
    · intro hqUpper
      apply hUpperFree
      exact Finset.mem_image.mpr ⟨q, hq, hqUpper⟩

/-! ## The finite plane-separator selector

The following lemmas turn the tenth-coordinate and equal-band construction
into the source's actual two-line separator.  They are deliberately phrased
as existential conclusions rather than a caller-supplied partition object.
-/

omit [Fintype ι] [DecidableEq ι] in
private theorem ten_mul_card_coordinate_lt_cut_le_nine_mul_card
    (region : Finset ι) (coordinate : ι → ℝ) {cut upperTenth : ℝ}
    (hTail : daiLiTenthCount region ≤
      (region.filter fun q => upperTenth ≤ coordinate q).card)
    (hCut : cut < upperTenth) :
    10 * (region.filter fun q => coordinate q < cut).card ≤ 9 * region.card := by
  classical
  let lower := region.filter fun q => coordinate q < cut
  let upper := region.filter fun q => upperTenth ≤ coordinate q
  have hDisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro q hLower hUpper
    have hqLower := (Finset.mem_filter.mp hLower).2
    have hqUpper := (Finset.mem_filter.mp hUpper).2
    linarith
  have hUnionSubset : lower ∪ upper ⊆ region := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (Finset.mem_filter.mp hq).1
    · exact (Finset.mem_filter.mp hq).1
  have hSum : lower.card + upper.card ≤ region.card := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_card hUnionSubset
  change daiLiTenthCount region ≤ upper.card at hTail
  have hTenth : region.card ≤ 10 * daiLiTenthCount region := by
    unfold daiLiTenthCount
    omega
  change 10 * lower.card ≤ 9 * region.card
  omega

omit [Fintype ι] [DecidableEq ι] in
private theorem ten_mul_card_coordinate_gt_cut_le_nine_mul_card
    (region : Finset ι) (coordinate : ι → ℝ) {lowerTenth cut : ℝ}
    (hTail : daiLiTenthCount region ≤
      (region.filter fun q => coordinate q ≤ lowerTenth).card)
    (hCut : lowerTenth < cut) :
    10 * (region.filter fun q => cut < coordinate q).card ≤ 9 * region.card := by
  classical
  let lower := region.filter fun q => coordinate q ≤ lowerTenth
  let upper := region.filter fun q => cut < coordinate q
  have hDisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro q hLower hUpper
    have hqLower := (Finset.mem_filter.mp hLower).2
    have hqUpper := (Finset.mem_filter.mp hUpper).2
    linarith
  have hUnionSubset : lower ∪ upper ⊆ region := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (Finset.mem_filter.mp hq).1
    · exact (Finset.mem_filter.mp hq).1
  have hSum : lower.card + upper.card ≤ region.card := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_card hUnionSubset
  change daiLiTenthCount region ≤ lower.card at hTail
  have hTenth : region.card ≤ 10 * daiLiTenthCount region := by
    unfold daiLiTenthCount
    omega
  change 10 * upper.card ≤ 9 * region.card
  omega

omit [Fintype ι] [DecidableEq ι] in
private theorem daiLiVerticalSeparatorStrip_subset_equalBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper lowerCut upperCut : ℝ} {m : Nat} {i : Fin m}
    (hLower : daiLiVerticalBandLower lower upper m i < lowerCut)
    (hUpper : upperCut < daiLiVerticalBandUpper lower upper m i) :
    daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ⊆
      daiLiVerticalEqualBand embedding region lower upper m i := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqRegion, hqLower, hqUpper⟩
  apply Finset.mem_filter.mpr
  refine ⟨hqRegion, ?_, ?_⟩
  · exact hLower.le.trans (le_of_lt hqLower)
  · exact hqUpper.trans hUpper

omit [Fintype ι] [DecidableEq ι] in
private theorem daiLiHorizontalSeparatorStrip_subset_equalBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper lowerCut upperCut : ℝ} {m : Nat} {i : Fin m}
    (hLower : daiLiVerticalBandLower lower upper m i < lowerCut)
    (hUpper : upperCut < daiLiVerticalBandUpper lower upper m i) :
    daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ⊆
      daiLiHorizontalEqualBand embedding region lower upper m i := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqRegion, hqLower, hqUpper⟩
  apply Finset.mem_filter.mpr
  refine ⟨hqRegion, ?_, ?_⟩
  · exact hLower.le.trans (le_of_lt hqLower)
  · exact hqUpper.trans hUpper

/-- DL24 Lemma 1 as an actual finite construction.  Every cut, its
orientation, its strict width, the strip bound, and both balance bounds are
constructed from the supplied finite point region. -/
theorem exists_daiLiPlaneSeparator
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {ell : ℝ} (hRegion : region.Nonempty) (hTen : 10 ≤ region.card)
    (hEll : 0 < ell) (hScale : ell ≤ Real.sqrt region.card / 8) :
    (∃ lowerCut upperCut : ℝ,
      DaiLiVerticalCutsAvoid embedding region lowerCut upperCut ∧
      ell < upperCut - lowerCut ∧
      ((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
        8 * ell * Real.sqrt region.card ∧
      10 * (daiLiVerticalSeparatorLower embedding region lowerCut).card ≤ 9 * region.card ∧
      10 * (daiLiVerticalSeparatorUpper embedding region upperCut).card ≤ 9 * region.card) ∨
    (∃ lowerCut upperCut : ℝ,
      DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut ∧
      ell < upperCut - lowerCut ∧
      ((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
        8 * ell * Real.sqrt region.card ∧
      10 * (daiLiHorizontalSeparatorLower embedding region lowerCut).card ≤ 9 * region.card ∧
      10 * (daiLiHorizontalSeparatorUpper embedding region upperCut).card ≤ 9 * region.card) := by
  classical
  let lowerX := daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion
  let upperX := daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion
  let lowerY := daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion
  let upperY := daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion
  have hN : 0 < region.card := Finset.card_pos.mpr hRegion
  have hWide := daiLiTenthCore_has_wide_axis embedding region hRegion hTen
  rcases hWide with hWide | hWide
  · have hWideX : Real.sqrt ((region.card : ℝ) / 10) < upperX - lowerX := by
      simpa [lowerX, upperX, daiLiTenthCoreLower, daiLiTenthCoreUpper] using hWide
    obtain ⟨i, hBandWidth, hBandCard⟩ := exists_daiLiVerticalLowBand embedding region
      hN hEll hScale le_rfl hWideX
    let m := daiLiSeparatorBandCount ell region.card
    obtain ⟨lowerCut, upperCut, hLower, hLowerUpper, hUpperLower, hUpper,
      hCutWidth, hAvoid⟩ :=
      exists_daiLiVerticalCutsAvoid_of_lt_width embedding region hEll.le
        (by simpa [m] using hBandWidth)
    change daiLiVerticalBandLower lowerX upperX m i < lowerCut at hLower
    change lowerCut < daiLiVerticalBandUpper lowerX upperX m i at hLowerUpper
    change daiLiVerticalBandLower lowerX upperX m i < upperCut at hUpperLower
    change upperCut < daiLiVerticalBandUpper lowerX upperX m i at hUpper
    have hM : 0 < m := by
      simpa [m] using daiLiSeparatorBandCount_pos ell region.card
    have hSpan : 0 < upperX - lowerX := by
      exact (Real.sqrt_nonneg ((region.card : ℝ) / 10)).trans_lt hWideX
    have hBandUpperLe : daiLiVerticalBandUpper lowerX upperX m i ≤ upperX := by
      dsimp [daiLiVerticalBandUpper]
      have hIndex : (i : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt i.isLt
      have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
      have hStep : 0 ≤ (upperX - lowerX) / m := by positivity
      field_simp [ne_of_gt hMReal]
      nlinarith
    have hLowerBandLe : lowerX ≤ daiLiVerticalBandLower lowerX upperX m i := by
      dsimp [daiLiVerticalBandLower]
      have hIndex : 0 ≤ (i : ℝ) := by positivity
      have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
      have hStep : 0 ≤ (upperX - lowerX) / m := by positivity
      nlinarith
    apply Or.inl
    refine ⟨lowerCut, upperCut, hAvoid, hCutWidth, ?_, ?_, ?_⟩
    · have hSubset := daiLiVerticalSeparatorStrip_subset_equalBand embedding region
        (lower := lowerX) (upper := upperX) (i := i) hLower hUpper
      have hSubsetReal : ((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
          ((daiLiVerticalEqualBand embedding region lowerX upperX m i).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSubset
      exact hSubsetReal.trans (by simpa [m] using hBandCard)
    · have hTail := (Finset.mem_filter.mp
        (mem_daiLiUpperTenthCandidates region (fun p => (embedding.point p).1) hRegion)).2
      simpa [daiLiVerticalSeparatorLower, upperX] using
        ten_mul_card_coordinate_lt_cut_le_nine_mul_card region
          (fun p => (embedding.point p).1) hTail (hLowerUpper.trans_le hBandUpperLe)
    · have hTail := (Finset.mem_filter.mp
        (mem_daiLiLowerTenthCandidates region (fun p => (embedding.point p).1) hRegion)).2
      simpa [daiLiVerticalSeparatorUpper, lowerX] using
        ten_mul_card_coordinate_gt_cut_le_nine_mul_card region
          (fun p => (embedding.point p).1) hTail (lt_of_le_of_lt hLowerBandLe hUpperLower)
  · have hWideY : Real.sqrt ((region.card : ℝ) / 10) < upperY - lowerY := by
      simpa [lowerY, upperY, daiLiTenthCoreLower, daiLiTenthCoreUpper] using hWide
    obtain ⟨i, hBandWidth, hBandCard⟩ := exists_daiLiHorizontalLowBand embedding region
      hN hEll hScale le_rfl hWideY
    let m := daiLiSeparatorBandCount ell region.card
    obtain ⟨lowerCut, upperCut, hLower, hLowerUpper, hUpperLower, hUpper,
      hCutWidth, hAvoid⟩ :=
      exists_daiLiHorizontalCutsAvoid_of_lt_width embedding region hEll.le
        (by simpa [m] using hBandWidth)
    change daiLiVerticalBandLower lowerY upperY m i < lowerCut at hLower
    change lowerCut < daiLiVerticalBandUpper lowerY upperY m i at hLowerUpper
    change daiLiVerticalBandLower lowerY upperY m i < upperCut at hUpperLower
    change upperCut < daiLiVerticalBandUpper lowerY upperY m i at hUpper
    have hM : 0 < m := by
      simpa [m] using daiLiSeparatorBandCount_pos ell region.card
    have hSpan : 0 < upperY - lowerY := by
      exact (Real.sqrt_nonneg ((region.card : ℝ) / 10)).trans_lt hWideY
    have hBandUpperLe : daiLiVerticalBandUpper lowerY upperY m i ≤ upperY := by
      dsimp [daiLiVerticalBandUpper]
      have hIndex : (i : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt i.isLt
      have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
      have hStep : 0 ≤ (upperY - lowerY) / m := by positivity
      field_simp [ne_of_gt hMReal]
      nlinarith
    have hLowerBandLe : lowerY ≤ daiLiVerticalBandLower lowerY upperY m i := by
      dsimp [daiLiVerticalBandLower]
      have hIndex : 0 ≤ (i : ℝ) := by positivity
      have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
      have hStep : 0 ≤ (upperY - lowerY) / m := by positivity
      nlinarith
    apply Or.inr
    refine ⟨lowerCut, upperCut, hAvoid, hCutWidth, ?_, ?_, ?_⟩
    · have hSubset := daiLiHorizontalSeparatorStrip_subset_equalBand embedding region
        (lower := lowerY) (upper := upperY) (i := i) hLower hUpper
      have hSubsetReal : ((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
          ((daiLiHorizontalEqualBand embedding region lowerY upperY m i).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSubset
      exact hSubsetReal.trans (by simpa [m] using hBandCard)
    · have hTail := (Finset.mem_filter.mp
        (mem_daiLiUpperTenthCandidates region (fun p => (embedding.point p).2) hRegion)).2
      simpa [daiLiHorizontalSeparatorLower, upperY] using
        ten_mul_card_coordinate_lt_cut_le_nine_mul_card region
          (fun p => (embedding.point p).2) hTail (hLowerUpper.trans_le hBandUpperLe)
    · have hTail := (Finset.mem_filter.mp
        (mem_daiLiLowerTenthCandidates region (fun p => (embedding.point p).2) hRegion)).2
      simpa [daiLiHorizontalSeparatorUpper, lowerY] using
        ten_mul_card_coordinate_gt_cut_le_nine_mul_card region
          (fun p => (embedding.point p).2) hTail (lt_of_le_of_lt hLowerBandLe hUpperLower)

/-! ## Recursive potential and actual exterior neighbours -/

/-- The finite potential charged to good interaction endpoints outside a
recursive region.  It is zero at the full system and has enough slack to pay
for every `9/10`-balanced separator on a branch. -/
noncomputable def daiLiRecursivePotential (ell : ℝ) (root region : Nat) : ℝ :=
  160 * ell * (Real.sqrt root - Real.sqrt region)

/-- A `9/10`-balanced child gains at least the source strip charge in the
finite potential.  The rational estimate `sqrt(9/10) < 19/20` avoids any
unverified analytic approximation. -/
theorem daiLiRecursivePotential_step {ell : ℝ} {root parent child : Nat}
    (hEll : 0 ≤ ell) (hBalanced : 10 * child ≤ 9 * parent) :
    daiLiRecursivePotential ell root parent + 8 * ell * Real.sqrt parent ≤
      daiLiRecursivePotential ell root child := by
  have hChildBound : (child : ℝ) ≤ (361 : ℝ) / 400 * parent := by
    have hBalancedReal : (10 : ℝ) * child ≤ 9 * parent := by
      exact_mod_cast hBalanced
    nlinarith
  have hChildNonneg : 0 ≤ (child : ℝ) := by positivity
  have hParentNonneg : 0 ≤ (parent : ℝ) := by positivity
  have hScaledNonneg : 0 ≤ (19 : ℝ) / 20 * Real.sqrt parent := by positivity
  have hScaledSq : (((19 : ℝ) / 20 * Real.sqrt parent) ^ 2) =
      (361 : ℝ) / 400 * parent := by
    rw [mul_pow, Real.sq_sqrt hParentNonneg]
    ring
  have hSqrtChild : Real.sqrt child ≤ (19 : ℝ) / 20 * Real.sqrt parent := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hScaledNonneg).mp
    rw [Real.sq_sqrt hChildNonneg, hScaledSq]
    exact hChildBound
  unfold daiLiRecursivePotential
  nlinarith

/-- DL24's exterior good-neighbour set: actual qubits outside a finite region
joined to it by a fixed-generator interaction shorter than the current
threshold.  Long interactions are intentionally excluded here because their
endpoints are removed before the union step. -/
noncomputable def daiLiGoodExteriorNeighbors
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι) : Finset ι :=
  by
    classical
    exact (Finset.univ \ region).filter fun q =>
      ∃ p : ι, p ∈ region ∧ P.fixedGeneratorInteraction p q ∧
        embedding.distance p q < ell

@[simp]
theorem mem_daiLiGoodExteriorNeighbors_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι) (q : ι) :
    q ∈ daiLiGoodExteriorNeighbors P embedding ell region ↔
      q ∉ region ∧ ∃ p : ι, p ∈ region ∧ P.fixedGeneratorInteraction p q ∧
        embedding.distance p q < ell := by
  simp [daiLiGoodExteriorNeighbors]

private theorem daiLiGoodExteriorNeighbors_vertical_lower_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut) :
    daiLiGoodExteriorNeighbors P embedding ell
        (daiLiVerticalSeparatorLower embedding region lowerCut) ⊆
      daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiGoodExteriorNeighbors P embedding ell region := by
  intro q hq
  rcases (mem_daiLiGoodExteriorNeighbors_iff P embedding ell
    (daiLiVerticalSeparatorLower embedding region lowerCut) q).1 hq with
    ⟨hqNotLower, p, hpLower, hpq, hpqShort⟩
  by_cases hqRegion : q ∈ region
  · have hqPieces : q ∈ daiLiVerticalSeparatorLower embedding region lowerCut ∪
        daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
          daiLiVerticalSeparatorUpper embedding region upperCut := by
      rw [daiLiVerticalSeparator_cover embedding region hAvoid]
      exact hqRegion
    rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
    · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
      · exact False.elim (hqNotLower hqLower)
      · exact Finset.mem_union_left _ hqStrip
    · have hSeparated := daiLiVerticalSeparatorSides_separated embedding region hWidth
        hpLower hqUpper
      exact False.elim (not_lt_of_ge hSeparated hpqShort)
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    exact ⟨hqRegion, p, (Finset.mem_filter.mp hpLower).1, hpq, hpqShort⟩

private theorem daiLiGoodExteriorNeighbors_vertical_upper_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut) :
    daiLiGoodExteriorNeighbors P embedding ell
        (daiLiVerticalSeparatorUpper embedding region upperCut) ⊆
      daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiGoodExteriorNeighbors P embedding ell region := by
  intro q hq
  rcases (mem_daiLiGoodExteriorNeighbors_iff P embedding ell
    (daiLiVerticalSeparatorUpper embedding region upperCut) q).1 hq with
    ⟨hqNotUpper, p, hpUpper, hpq, hpqShort⟩
  by_cases hqRegion : q ∈ region
  · have hqPieces : q ∈ daiLiVerticalSeparatorLower embedding region lowerCut ∪
        daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
          daiLiVerticalSeparatorUpper embedding region upperCut := by
      rw [daiLiVerticalSeparator_cover embedding region hAvoid]
      exact hqRegion
    rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
    · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
      · have hSeparated := daiLiVerticalSeparatorSides_separated embedding region hWidth
            hqLower hpUpper
        exact False.elim (not_lt_of_ge (by
          simpa [UnitSeparatedEmbedding2D.distance_comm] using hSeparated) hpqShort)
      · exact Finset.mem_union_left _ hqStrip
    · exact False.elim (hqNotUpper hqUpper)
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    exact ⟨hqRegion, p, (Finset.mem_filter.mp hpUpper).1, hpq, hpqShort⟩

private theorem daiLiGoodExteriorNeighbors_horizontal_lower_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut) :
    daiLiGoodExteriorNeighbors P embedding ell
        (daiLiHorizontalSeparatorLower embedding region lowerCut) ⊆
      daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiGoodExteriorNeighbors P embedding ell region := by
  intro q hq
  rcases (mem_daiLiGoodExteriorNeighbors_iff P embedding ell
    (daiLiHorizontalSeparatorLower embedding region lowerCut) q).1 hq with
    ⟨hqNotLower, p, hpLower, hpq, hpqShort⟩
  by_cases hqRegion : q ∈ region
  · have hqPieces : q ∈ daiLiHorizontalSeparatorLower embedding region lowerCut ∪
        daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
          daiLiHorizontalSeparatorUpper embedding region upperCut := by
      rw [daiLiHorizontalSeparator_cover embedding region hAvoid]
      exact hqRegion
    rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
    · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
      · exact False.elim (hqNotLower hqLower)
      · exact Finset.mem_union_left _ hqStrip
    · have hSeparated := daiLiHorizontalSeparatorSides_separated embedding region hWidth
        hpLower hqUpper
      exact False.elim (not_lt_of_ge hSeparated hpqShort)
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    exact ⟨hqRegion, p, (Finset.mem_filter.mp hpLower).1, hpq, hpqShort⟩

private theorem daiLiGoodExteriorNeighbors_horizontal_upper_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut) :
    daiLiGoodExteriorNeighbors P embedding ell
        (daiLiHorizontalSeparatorUpper embedding region upperCut) ⊆
      daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiGoodExteriorNeighbors P embedding ell region := by
  intro q hq
  rcases (mem_daiLiGoodExteriorNeighbors_iff P embedding ell
    (daiLiHorizontalSeparatorUpper embedding region upperCut) q).1 hq with
    ⟨hqNotUpper, p, hpUpper, hpq, hpqShort⟩
  by_cases hqRegion : q ∈ region
  · have hqPieces : q ∈ daiLiHorizontalSeparatorLower embedding region lowerCut ∪
        daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
          daiLiHorizontalSeparatorUpper embedding region upperCut := by
      rw [daiLiHorizontalSeparator_cover embedding region hAvoid]
      exact hqRegion
    rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
    · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
      · have hSeparated := daiLiHorizontalSeparatorSides_separated embedding region hWidth
            hqLower hpUpper
        exact False.elim (not_lt_of_ge (by
          simpa [UnitSeparatedEmbedding2D.distance_comm] using hSeparated) hpqShort)
      · exact Finset.mem_union_left _ hqStrip
    · exact False.elim (hqNotUpper hqUpper)
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    exact ⟨hqRegion, p, (Finset.mem_filter.mp hpUpper).1, hpq, hpqShort⟩

/-- The retained child region after removing every actual endpoint of a
threshold-long interaction. -/
def daiLiRecursiveGoodPart
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι) : Finset ι :=
  region \ longInteractionEndpointQubits P embedding ell

private theorem card_region_inter_longInteractionEndpoints_le_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι) :
    (region ∩ longInteractionEndpointQubits P embedding ell).card ≤
      regionInteractionCounter P embedding ell region := by
  classical
  let endpoints := longInteractionEndpointQubits P embedding ell
  let counter := fun q : ι => P.daiLiInteractionCounter embedding ell q
  calc
    (region ∩ endpoints).card = ∑ q ∈ region ∩ endpoints, 1 := by simp
    _ ≤ ∑ q ∈ region ∩ endpoints, counter q := by
      apply Finset.sum_le_sum
      intro q hq
      have hPositive : 0 < counter q := by
        exact (mem_longInteractionEndpointQubits_iff P embedding ell q).1
          (by simpa [endpoints] using (Finset.mem_inter.mp hq).2)
      omega
    _ ≤ ∑ q ∈ region, counter q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
        (fun _ _ _ => Nat.zero_le _)
    _ = regionInteractionCounter P embedding ell region := by
      rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem daiLiVerticalSeparatorLower_disjoint_upper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ} (hCuts : lowerCut ≤ upperCut) :
    Disjoint (daiLiVerticalSeparatorLower embedding region lowerCut)
      (daiLiVerticalSeparatorUpper embedding region upperCut) := by
  apply Finset.disjoint_left.mpr
  intro q hLower hUpper
  have hBelow := (Finset.mem_filter.mp hLower).2
  have hAbove := (Finset.mem_filter.mp hUpper).2
  linarith

private theorem daiLiVertical_unretained_subset_strip_union_endpoints
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut) :
    region \ (daiLiRecursiveGoodPart P embedding ell
        (daiLiVerticalSeparatorLower embedding region lowerCut) ∪
      daiLiRecursiveGoodPart P embedding ell
        (daiLiVerticalSeparatorUpper embedding region upperCut)) ⊆
      daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        (region ∩ longInteractionEndpointQubits P embedding ell) := by
  intro q hq
  have hqRegion := (Finset.mem_sdiff.mp hq).1
  have hqNotRetained := (Finset.mem_sdiff.mp hq).2
  have hqPieces : q ∈ daiLiVerticalSeparatorLower embedding region lowerCut ∪
      daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiVerticalSeparatorUpper embedding region upperCut := by
    rw [daiLiVerticalSeparator_cover embedding region hAvoid]
    exact hqRegion
  rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
  · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
    · apply Finset.mem_union_right
      apply Finset.mem_inter.mpr
      refine ⟨hqRegion, ?_⟩
      by_contra hqNotEndpoint
      apply hqNotRetained
      apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hqLower, hqNotEndpoint⟩
    · exact Finset.mem_union_left _ hqStrip
  · apply Finset.mem_union_right
    apply Finset.mem_inter.mpr
    refine ⟨hqRegion, ?_⟩
    by_contra hqNotEndpoint
    apply hqNotRetained
    apply Finset.mem_union_right
    exact Finset.mem_sdiff.mpr ⟨hqUpper, hqNotEndpoint⟩

private theorem daiLiHorizontal_unretained_subset_strip_union_endpoints
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut) :
    region \ (daiLiRecursiveGoodPart P embedding ell
        (daiLiHorizontalSeparatorLower embedding region lowerCut) ∪
      daiLiRecursiveGoodPart P embedding ell
        (daiLiHorizontalSeparatorUpper embedding region upperCut)) ⊆
      daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        (region ∩ longInteractionEndpointQubits P embedding ell) := by
  intro q hq
  have hqRegion := (Finset.mem_sdiff.mp hq).1
  have hqNotRetained := (Finset.mem_sdiff.mp hq).2
  have hqPieces : q ∈ daiLiHorizontalSeparatorLower embedding region lowerCut ∪
      daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiHorizontalSeparatorUpper embedding region upperCut := by
    rw [daiLiHorizontalSeparator_cover embedding region hAvoid]
    exact hqRegion
  rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
  · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
    · apply Finset.mem_union_right
      apply Finset.mem_inter.mpr
      refine ⟨hqRegion, ?_⟩
      by_contra hqNotEndpoint
      apply hqNotRetained
      apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hqLower, hqNotEndpoint⟩
    · exact Finset.mem_union_left _ hqStrip
  · apply Finset.mem_union_right
    apply Finset.mem_inter.mpr
    refine ⟨hqRegion, ?_⟩
    by_contra hqNotEndpoint
    apply hqNotRetained
    apply Finset.mem_union_right
    exact Finset.mem_sdiff.mpr ⟨hqUpper, hqNotEndpoint⟩

private theorem fixedGeneratorOuterBoundary_vertical_goodSides_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut) :
    P.fixedGeneratorOuterBoundary
        ((daiLiRecursiveGoodPart P embedding ell
            (daiLiVerticalSeparatorLower embedding region lowerCut) ∪
          daiLiRecursiveGoodPart P embedding ell
            (daiLiVerticalSeparatorUpper embedding region upperCut) : Finset ι) : Set ι) ⊆
      (((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
          (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
        daiLiGoodExteriorNeighbors P embedding ell region : Finset ι) : Set ι) := by
  let retained : Finset ι := daiLiRecursiveGoodPart P embedding ell
      (daiLiVerticalSeparatorLower embedding region lowerCut) ∪
    daiLiRecursiveGoodPart P embedding ell
      (daiLiVerticalSeparatorUpper embedding region upperCut)
  intro q hq
  rcases (P.mem_fixedGeneratorOuterBoundary_iff (retained : Set ι) q).1 hq with
    ⟨hqNotRetained, p, hpRetained, hpq⟩
  have hpOutside : p ∉ longInteractionEndpointQubits P embedding ell := by
    rcases Finset.mem_union.mp hpRetained with hpLower | hpUpper
    · exact (Finset.mem_sdiff.mp hpLower).2
    · exact (Finset.mem_sdiff.mp hpUpper).2
  by_cases hqRegion : q ∈ region
  · apply Finset.mem_union_left
    apply daiLiVertical_unretained_subset_strip_union_endpoints P embedding ell region hAvoid
    refine Finset.mem_sdiff.mpr ⟨hqRegion, ?_⟩
    simpa [retained] using hqNotRetained
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    have hpRegion : p ∈ region := by
      rcases Finset.mem_union.mp hpRetained with hpLower | hpUpper
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpLower).1).1
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpUpper).1).1
    have hNotLong : ¬ ell ≤ embedding.distance p q := by
      intro hLong
      apply no_long_interaction_from_outside_endpoint_set P embedding ell p q hpOutside
      change P.fixedGeneratorInteraction p q at hpq
      exact ⟨hpq, hLong⟩
    exact ⟨hqRegion, p, hpRegion, hpq, lt_of_not_ge hNotLong⟩

private theorem fixedGeneratorOuterBoundary_horizontal_goodSides_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut) :
    P.fixedGeneratorOuterBoundary
        ((daiLiRecursiveGoodPart P embedding ell
            (daiLiHorizontalSeparatorLower embedding region lowerCut) ∪
          daiLiRecursiveGoodPart P embedding ell
            (daiLiHorizontalSeparatorUpper embedding region upperCut) : Finset ι) : Set ι) ⊆
      (((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
          (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
        daiLiGoodExteriorNeighbors P embedding ell region : Finset ι) : Set ι) := by
  let retained : Finset ι := daiLiRecursiveGoodPart P embedding ell
      (daiLiHorizontalSeparatorLower embedding region lowerCut) ∪
    daiLiRecursiveGoodPart P embedding ell
      (daiLiHorizontalSeparatorUpper embedding region upperCut)
  intro q hq
  rcases (P.mem_fixedGeneratorOuterBoundary_iff (retained : Set ι) q).1 hq with
    ⟨hqNotRetained, p, hpRetained, hpq⟩
  have hpOutside : p ∉ longInteractionEndpointQubits P embedding ell := by
    rcases Finset.mem_union.mp hpRetained with hpLower | hpUpper
    · exact (Finset.mem_sdiff.mp hpLower).2
    · exact (Finset.mem_sdiff.mp hpUpper).2
  by_cases hqRegion : q ∈ region
  · apply Finset.mem_union_left
    apply daiLiHorizontal_unretained_subset_strip_union_endpoints P embedding ell region hAvoid
    refine Finset.mem_sdiff.mpr ⟨hqRegion, ?_⟩
    simpa [retained] using hqNotRetained
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    have hpRegion : p ∈ region := by
      rcases Finset.mem_union.mp hpRetained with hpLower | hpUpper
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpLower).1).1
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpUpper).1).1
    have hNotLong : ¬ ell ≤ embedding.distance p q := by
      intro hLong
      apply no_long_interaction_from_outside_endpoint_set P embedding ell p q hpOutside
      change P.fixedGeneratorInteraction p q at hpq
      exact ⟨hpq, hLong⟩
    exact ⟨hqRegion, p, hpRegion, hpq, lt_of_not_ge hNotLong⟩

private theorem exists_erasureRecovery_daiLiFiniteSubsystem_subset
    (S T : Finset ι) (hST : S ⊆ T)
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (hRecovery : ∃ recovery : QuantumChannel (daiLiFiniteSubsystem T).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem T).complementSystem
        P.semanticCode (daiLiFiniteSubsystem T).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel (daiLiFiniteSubsystem S).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem S).complementSystem
        P.semanticCode (daiLiFiniteSubsystem S).erasureChannelFromRegister recovery := by
  exact
    (exists_qudit_erasureRecovery_of_subset
      (quditSubsystemOfFinite (daiLiFiniteSubsystem S))
      (quditSubsystemOfFinite (daiLiFiniteSubsystem T)) hST P.semanticCode hRecovery)

private theorem exists_erasureRecovery_of_daiLiVerticalRecursiveStep
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell : ℝ) (region : Finset ι) {lowerCut upperCut : ℝ}
    (hEll : 0 ≤ ell)
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut)
    (hLowerRecovery : ∃ recovery : QuantumChannel
      (daiLiFiniteSubsystem (daiLiVerticalSeparatorLower embedding region lowerCut)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (daiLiVerticalSeparatorLower embedding region lowerCut)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (daiLiVerticalSeparatorLower embedding region lowerCut)).erasureChannelFromRegister
          recovery)
    (hUpperRecovery : ∃ recovery : QuantumChannel
      (daiLiFiniteSubsystem (daiLiVerticalSeparatorUpper embedding region upperCut)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (daiLiVerticalSeparatorUpper embedding region upperCut)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (daiLiVerticalSeparatorUpper embedding region upperCut)).erasureChannelFromRegister
          recovery)
    (hBufferSmall :
      ((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
        daiLiGoodExteriorNeighbors P embedding ell region).card < d) :
    ∃ recovery : QuantumChannel (daiLiFiniteSubsystem region).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem region).complementSystem
        P.semanticCode (daiLiFiniteSubsystem region).erasureChannelFromRegister recovery := by
  let lower := daiLiVerticalSeparatorLower embedding region lowerCut
  let upper := daiLiVerticalSeparatorUpper embedding region upperCut
  let goodLower := daiLiRecursiveGoodPart P embedding ell lower
  let goodUpper := daiLiRecursiveGoodPart P embedding ell upper
  let retained := goodLower ∪ goodUpper
  let buffer := (daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
      (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
    daiLiGoodExteriorNeighbors P embedding ell region
  obtain ⟨recoveryGoodLower, hRecoveryGoodLower⟩ :=
    exists_erasureRecovery_daiLiFiniteSubsystem_subset goodLower lower
      Finset.sdiff_subset P (by simpa [lower] using hLowerRecovery)
  obtain ⟨recoveryGoodUpper, hRecoveryGoodUpper⟩ :=
    exists_erasureRecovery_daiLiFiniteSubsystem_subset goodUpper upper
      Finset.sdiff_subset P (by simpa [upper] using hUpperRecovery)
  have hCutOrder : lowerCut ≤ upperCut := by linarith
  have hGoodDisjoint : Disjoint goodLower goodUpper := by
    apply (daiLiVerticalSeparatorLower_disjoint_upper embedding region
      (lowerCut := lowerCut) (upperCut := upperCut) hCutOrder).mono
    · exact Finset.sdiff_subset
    · exact Finset.sdiff_subset
  have hGoodDecoupled : P.fixedGeneratorDecoupled (goodLower : Set ι) (goodUpper : Set ι) := by
    apply fixedGeneratorDecoupled_of_separated_outside_longEndpoints P embedding ell
      goodLower goodUpper hGoodDisjoint
    · intro q hq
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hq).2
    · intro q hq
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hq).2
    · intro p hp q hq
      apply daiLiVerticalSeparatorSides_separated embedding region
        (lowerCut := lowerCut) (upperCut := upperCut) hWidth
      · exact Finset.sdiff_subset hp
      · exact Finset.sdiff_subset hq
  obtain ⟨recoveryRetained, hRecoveryRetained⟩ :=
    exists_erasureRecovery_of_fixedGeneratorDecoupled P
      (daiLiFiniteSubsystem goodLower) (daiLiFiniteSubsystem goodUpper)
      recoveryGoodLower recoveryGoodUpper hRecoveryGoodLower hRecoveryGoodUpper
      (by simpa [daiLiFiniteSubsystem] using hGoodDecoupled)
  obtain ⟨recoveryBuffer, hRecoveryBuffer⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      (daiLiFiniteSubsystem buffer) hBufferSmall
  let retainedSubsystem := unionSubsystem
    (daiLiFiniteSubsystem goodLower) (daiLiFiniteSubsystem goodUpper)
  let bufferSubsystem := daiLiFiniteSubsystem buffer
  have hBoundary : P.fixedGeneratorOuterBoundary
      (retainedSubsystem.selected : Set ι) ⊆ (bufferSubsystem.selected : Set ι) := by
    change P.fixedGeneratorOuterBoundary (retained : Set ι) ⊆ (buffer : Set ι)
    simpa [retained, buffer, Set.union_assoc] using
      (fixedGeneratorOuterBoundary_vertical_goodSides_subset P embedding ell region hAvoid)
  obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
    exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset P
      retainedSubsystem bufferSubsystem recoveryRetained recoveryBuffer
      (by simpa [retainedSubsystem] using hRecoveryRetained)
      hRecoveryBuffer hBoundary
  have hParentSubset : region ⊆ (unionSubsystem retainedSubsystem bufferSubsystem).selected := by
    change region ⊆ retained ∪ buffer
    intro q hq
    by_cases hqRetained : q ∈ retained
    · apply Finset.mem_union_left
      simpa [retainedSubsystem, retained, daiLiFiniteSubsystem] using hqRetained
    · apply Finset.mem_union_right
      have hqBuffer : q ∈ buffer := by
        apply Finset.mem_union_left
        apply daiLiVertical_unretained_subset_strip_union_endpoints P embedding ell region hAvoid
        exact Finset.mem_sdiff.mpr ⟨hq, hqRetained⟩
      exact hqBuffer
  exact exists_erasureRecovery_daiLiFiniteSubsystem_subset region
    (unionSubsystem retainedSubsystem bufferSubsystem).selected hParentSubset P
    ⟨recoveryExpanded, hRecoveryExpanded⟩

private theorem exists_erasureRecovery_of_daiLiHorizontalRecursiveStep
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell : ℝ) (region : Finset ι) {lowerCut upperCut : ℝ}
    (hEll : 0 ≤ ell)
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut)
    (hLowerRecovery : ∃ recovery : QuantumChannel
      (daiLiFiniteSubsystem (daiLiHorizontalSeparatorLower embedding region lowerCut)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (daiLiHorizontalSeparatorLower embedding region lowerCut)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (daiLiHorizontalSeparatorLower embedding region lowerCut)).erasureChannelFromRegister
          recovery)
    (hUpperRecovery : ∃ recovery : QuantumChannel
      (daiLiFiniteSubsystem (daiLiHorizontalSeparatorUpper embedding region upperCut)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (daiLiHorizontalSeparatorUpper embedding region upperCut)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (daiLiHorizontalSeparatorUpper embedding region upperCut)).erasureChannelFromRegister
          recovery)
    (hBufferSmall :
      ((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
        daiLiGoodExteriorNeighbors P embedding ell region).card < d) :
    ∃ recovery : QuantumChannel (daiLiFiniteSubsystem region).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem region).complementSystem
        P.semanticCode (daiLiFiniteSubsystem region).erasureChannelFromRegister recovery := by
  let lower := daiLiHorizontalSeparatorLower embedding region lowerCut
  let upper := daiLiHorizontalSeparatorUpper embedding region upperCut
  let goodLower := daiLiRecursiveGoodPart P embedding ell lower
  let goodUpper := daiLiRecursiveGoodPart P embedding ell upper
  let retained := goodLower ∪ goodUpper
  let buffer := (daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
      (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
    daiLiGoodExteriorNeighbors P embedding ell region
  obtain ⟨recoveryGoodLower, hRecoveryGoodLower⟩ :=
    exists_erasureRecovery_daiLiFiniteSubsystem_subset goodLower lower
      Finset.sdiff_subset P (by simpa [lower] using hLowerRecovery)
  obtain ⟨recoveryGoodUpper, hRecoveryGoodUpper⟩ :=
    exists_erasureRecovery_daiLiFiniteSubsystem_subset goodUpper upper
      Finset.sdiff_subset P (by simpa [upper] using hUpperRecovery)
  have hCutOrder : lowerCut ≤ upperCut := by linarith
  have hGoodDisjoint : Disjoint goodLower goodUpper := by
    apply (daiLiHorizontalSeparatorLower_disjoint_upper embedding region hCutOrder).mono
    · exact Finset.sdiff_subset
    · exact Finset.sdiff_subset
  have hGoodDecoupled : P.fixedGeneratorDecoupled (goodLower : Set ι) (goodUpper : Set ι) := by
    apply fixedGeneratorDecoupled_of_separated_outside_longEndpoints P embedding ell
      goodLower goodUpper hGoodDisjoint
    · intro q hq
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hq).2
    · intro q hq
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hq).2
    · intro p hp q hq
      apply daiLiHorizontalSeparatorSides_separated embedding region
        (lowerCut := lowerCut) (upperCut := upperCut) hWidth
      · exact Finset.sdiff_subset hp
      · exact Finset.sdiff_subset hq
  obtain ⟨recoveryRetained, hRecoveryRetained⟩ :=
    exists_erasureRecovery_of_fixedGeneratorDecoupled P
      (daiLiFiniteSubsystem goodLower) (daiLiFiniteSubsystem goodUpper)
      recoveryGoodLower recoveryGoodUpper hRecoveryGoodLower hRecoveryGoodUpper
      (by simpa [daiLiFiniteSubsystem] using hGoodDecoupled)
  obtain ⟨recoveryBuffer, hRecoveryBuffer⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      (daiLiFiniteSubsystem buffer) hBufferSmall
  let retainedSubsystem := unionSubsystem
    (daiLiFiniteSubsystem goodLower) (daiLiFiniteSubsystem goodUpper)
  let bufferSubsystem := daiLiFiniteSubsystem buffer
  have hBoundary : P.fixedGeneratorOuterBoundary
      (retainedSubsystem.selected : Set ι) ⊆ (bufferSubsystem.selected : Set ι) := by
    change P.fixedGeneratorOuterBoundary (retained : Set ι) ⊆ (buffer : Set ι)
    simpa [retained, buffer, Set.union_assoc] using
      (fixedGeneratorOuterBoundary_horizontal_goodSides_subset P embedding ell region hAvoid)
  obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
    exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset P
      retainedSubsystem bufferSubsystem recoveryRetained recoveryBuffer
      (by simpa [retainedSubsystem] using hRecoveryRetained)
      hRecoveryBuffer hBoundary
  have hParentSubset : region ⊆ (unionSubsystem retainedSubsystem bufferSubsystem).selected := by
    change region ⊆ retained ∪ buffer
    intro q hq
    by_cases hqRetained : q ∈ retained
    · apply Finset.mem_union_left
      simpa [retainedSubsystem, retained, daiLiFiniteSubsystem] using hqRetained
    · apply Finset.mem_union_right
      have hqBuffer : q ∈ buffer := by
        apply Finset.mem_union_left
        apply daiLiHorizontal_unretained_subset_strip_union_endpoints P embedding ell region hAvoid
        exact Finset.mem_sdiff.mpr ⟨hq, hqRetained⟩
      exact hqBuffer
  exact exists_erasureRecovery_daiLiFiniteSubsystem_subset region
    (unionSubsystem retainedSubsystem bufferSubsystem).selected hParentSubset P
    ⟨recoveryExpanded, hRecoveryExpanded⟩

private theorem daiLiThreshold_le_sqrt_region_div_eight
    {d root region : Nat} (hd : 0 < d) (hRoot : d ≤ root) (hRegion : d ≤ region) :
    (d : ℝ) / (200 * Real.sqrt root) ≤ Real.sqrt region / 8 := by
  have hRootPositive : 0 < (root : ℝ) := by exact_mod_cast (lt_of_lt_of_le hd hRoot)
  have hRootSqrtPositive : 0 < Real.sqrt (root : ℝ) := Real.sqrt_pos.2 hRootPositive
  have hDroot : (d : ℝ) ≤ root := by exact_mod_cast hRoot
  have hDregion : (d : ℝ) ≤ region := by exact_mod_cast hRegion
  have hdNonneg : 0 ≤ (d : ℝ) := by positivity
  have hSq : (d : ℝ) ^ 2 ≤ (root : ℝ) * region := by
    calc
      (d : ℝ) ^ 2 = (d : ℝ) * d := by ring
      _ ≤ (root : ℝ) * d := mul_le_mul_of_nonneg_right hDroot hdNonneg
      _ ≤ (root : ℝ) * region := mul_le_mul_of_nonneg_left hDregion (by positivity)
  have hRootSq : (Real.sqrt (root : ℝ)) ^ 2 = (root : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hRegionSq : (Real.sqrt (region : ℝ)) ^ 2 = (region : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hProduct : (d : ℝ) ≤ Real.sqrt root * Real.sqrt region := by
    have hProductNonneg : 0 ≤ Real.sqrt (root : ℝ) * Real.sqrt region := by positivity
    nlinarith
  have hDiv : (d : ℝ) / (200 * Real.sqrt root) ≤
      (Real.sqrt root * Real.sqrt region) / (200 * Real.sqrt root) := by
    exact div_le_div_of_nonneg_right hProduct (by positivity)
  calc
    (d : ℝ) / (200 * Real.sqrt root) ≤
        (Real.sqrt root * Real.sqrt region) / (200 * Real.sqrt root) := hDiv
    _ = Real.sqrt region / 200 := by
      field_simp [hRootSqrtPositive.ne']
    _ ≤ Real.sqrt region / 8 := by
      have : 0 ≤ Real.sqrt (region : ℝ) := Real.sqrt_nonneg _
      nlinarith

private theorem daiLiRecursivePotential_le_four_fifths_distance
    {ell : ℝ} {d root region : Nat}
    (hEll : 0 ≤ ell) (hRootPositive : 0 < root)
    (hScale : ell = (d : ℝ) / (200 * Real.sqrt root)) :
    daiLiRecursivePotential ell root region ≤ 4 * (d : ℝ) / 5 := by
  have hRootSqrtPositive : 0 < Real.sqrt (root : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hRootPositive)
  have hRegionSqrt : 0 ≤ Real.sqrt (region : ℝ) := Real.sqrt_nonneg _
  have hRaw : daiLiRecursivePotential ell root region ≤
      160 * ell * Real.sqrt root := by
    unfold daiLiRecursivePotential
    nlinarith
  calc
    daiLiRecursivePotential ell root region ≤ 160 * ell * Real.sqrt root := hRaw
    _ = 4 * (d : ℝ) / 5 := by
      rw [hScale]
      field_simp [hRootSqrtPositive.ne']
      ring

private theorem daiLiRecursiveBuffer_card_lt_distance
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d root : Nat) (ell : ℝ)
    (hDistancePositive : 0 < d) (hRootPositive : 0 < root)
    (hEll : 0 ≤ ell)
    (hScale : ell = (d : ℝ) / (200 * Real.sqrt root))
    (region strip : Finset ι) (hRegionRoot : region.card ≤ root)
    (hStrip : (strip.card : ℝ) ≤ 8 * ell * Real.sqrt region.card)
    (hCounter : 10 * regionInteractionCounter P embedding ell region ≤ d)
    (hExterior : ((daiLiGoodExteriorNeighbors P embedding ell region).card : ℝ) ≤
      daiLiRecursivePotential ell root region.card) :
    ((strip ∪ (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
      daiLiGoodExteriorNeighbors P embedding ell region).card < d := by
  let endpoints := region ∩ longInteractionEndpointQubits P embedding ell
  let exterior := daiLiGoodExteriorNeighbors P embedding ell region
  have hEndpoint : endpoints.card ≤ regionInteractionCounter P embedding ell region := by
    simpa [endpoints] using
      card_region_inter_longInteractionEndpoints_le_counter P embedding ell region
  have hUnionNat : ((strip ∪ endpoints) ∪ exterior).card ≤
      strip.card + endpoints.card + exterior.card := by
    calc
      _ ≤ (strip ∪ endpoints).card + exterior.card := Finset.card_union_le _ _
      _ ≤ (strip.card + endpoints.card) + exterior.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by omega
  have hUnionReal : (((strip ∪ endpoints) ∪ exterior).card : ℝ) ≤
      (strip.card : ℝ) + endpoints.card + exterior.card := by
    exact_mod_cast hUnionNat
  have hCounterReal : (regionInteractionCounter P embedding ell region : ℝ) ≤
      (d : ℝ) / 10 := by
    have hCounterCast : (10 : ℝ) *
        (regionInteractionCounter P embedding ell region : ℝ) ≤ d := by
      exact_mod_cast hCounter
    nlinarith
  have hSqrtMono : Real.sqrt (region.card : ℝ) ≤ Real.sqrt (root : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hRegionRoot)
  have hStripRoot : (strip.card : ℝ) ≤ 8 * ell * Real.sqrt root := by
    calc
      (strip.card : ℝ) ≤ 8 * ell * Real.sqrt region.card := hStrip
      _ ≤ 8 * ell * Real.sqrt root := by
        have hScaleNonneg : 0 ≤ 8 * ell := by positivity
        exact mul_le_mul_of_nonneg_left hSqrtMono hScaleNonneg
  have hRootSqrtPositive : 0 < Real.sqrt (root : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hRootPositive)
  have hStripBudget : 8 * ell * Real.sqrt root = (d : ℝ) / 25 := by
    rw [hScale]
    field_simp [hRootSqrtPositive.ne']
    ring
  have hPotentialBudget := daiLiRecursivePotential_le_four_fifths_distance
    (d := d) (region := region.card) hEll hRootPositive hScale
  have hTotal : (((strip ∪ endpoints) ∪ exterior).card : ℝ) ≤
      47 * (d : ℝ) / 50 := by
    have hEndpointReal : (endpoints.card : ℝ) ≤
        (regionInteractionCounter P embedding ell region : ℝ) := by
      exact_mod_cast hEndpoint
    have hExterior' : (exterior.card : ℝ) ≤
        daiLiRecursivePotential ell root region.card := by
      simpa [exterior] using hExterior
    rw [hStripBudget] at hStripRoot
    linarith
  have hStrict : 47 * (d : ℝ) / 50 < d := by
    have : (0 : ℝ) < d := by exact_mod_cast hDistancePositive
    linarith
  have hCard : ((strip ∪ endpoints) ∪ exterior).card < d := by
    exact_mod_cast (hTotal.trans_lt hStrict)
  simpa [endpoints, exterior] using hCard

/-- The source Claim 1, realized by strong induction on the actual finite
region cardinality.  The separator, child budgets, endpoint deletion, and
semantic recovery composition are all constructed in the proof. -/
private theorem exists_erasureRecovery_daiLiRecursiveSeparator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d root : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hDistancePositive : 0 < d) (hTenDistance : 10 ≤ d) (hDistanceLeRoot : d ≤ root)
    (ell : ℝ) (hEll : 1 ≤ ell)
    (hScale : ell = (d : ℝ) / (200 * Real.sqrt root))
    (region : Finset ι) (hRegionRoot : region.card ≤ root)
    (hCounter : 10 * regionInteractionCounter P embedding ell region ≤ d)
    (hExterior : ((daiLiGoodExteriorNeighbors P embedding ell region).card : ℝ) ≤
      daiLiRecursivePotential ell root region.card) :
    ∃ recovery : QuantumChannel (daiLiFiniteSubsystem region).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem region).complementSystem
        P.semanticCode (daiLiFiniteSubsystem region).erasureChannelFromRegister recovery := by
  let statement : Nat → Prop := fun size =>
    ∀ region : Finset ι, region.card ≤ size → region.card ≤ root →
      10 * regionInteractionCounter P embedding ell region ≤ d →
      ((daiLiGoodExteriorNeighbors P embedding ell region).card : ℝ) ≤
        daiLiRecursivePotential ell root region.card →
      ∃ recovery : QuantumChannel (daiLiFiniteSubsystem region).complementSystem
        (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem region).complementSystem
          P.semanticCode (daiLiFiniteSubsystem region).erasureChannelFromRegister recovery
  have hStatement : ∀ size, statement size := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro region hSize hRegionRoot hCounter hExterior
      have hEllNonneg : 0 ≤ ell := by linarith
      by_cases hSmall : region.card < d
      · exact semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
          (daiLiFiniteSubsystem region) (by simpa [daiLiFiniteSubsystem] using hSmall)
      · have hRegionLarge : d ≤ region.card := Nat.le_of_not_gt hSmall
        have hRegionNonempty : region.Nonempty :=
          Finset.card_pos.mp (lt_of_lt_of_le hDistancePositive hRegionLarge)
        have hRegionTen : 10 ≤ region.card := hTenDistance.trans hRegionLarge
        have hPlaneScale : ell ≤ Real.sqrt region.card / 8 := by
          rw [hScale]
          exact daiLiThreshold_le_sqrt_region_div_eight hDistancePositive
            hDistanceLeRoot hRegionLarge
        rcases exists_daiLiPlaneSeparator embedding region hRegionNonempty hRegionTen
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hEll) hPlaneScale with
          hVertical | hHorizontal
        · rcases hVertical with ⟨lowerCut, upperCut, hAvoid, hWidth, hStrip,
            hLowerBalanced, hUpperBalanced⟩
          let lower := daiLiVerticalSeparatorLower embedding region lowerCut
          let upper := daiLiVerticalSeparatorUpper embedding region upperCut
          let strip := daiLiVerticalSeparatorStrip embedding region lowerCut upperCut
          have hLowerSubset : lower ⊆ region := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hUpperSubset : upper ⊆ region := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hLowerRoot : lower.card ≤ root :=
            (Finset.card_le_card hLowerSubset).trans hRegionRoot
          have hUpperRoot : upper.card ≤ root :=
            (Finset.card_le_card hUpperSubset).trans hRegionRoot
          have hLowerCounter : 10 * regionInteractionCounter P embedding ell lower ≤ d := by
            exact (Nat.mul_le_mul_left 10
              (regionInteractionCounter_mono P embedding ell hLowerSubset)).trans hCounter
          have hUpperCounter : 10 * regionInteractionCounter P embedding ell upper ≤ d := by
            exact (Nat.mul_le_mul_left 10
              (regionInteractionCounter_mono P embedding ell hUpperSubset)).trans hCounter
          have hLowerBalanced' : 10 * lower.card ≤ 9 * region.card := by
            simpa [lower] using hLowerBalanced
          have hUpperBalanced' : 10 * upper.card ≤ 9 * region.card := by
            simpa [upper] using hUpperBalanced
          have hLowerLt : lower.card < region.card := by
            have hPositive : 0 < region.card := Finset.card_pos.mpr hRegionNonempty
            omega
          have hUpperLt : upper.card < region.card := by
            have hPositive : 0 < region.card := Finset.card_pos.mpr hRegionNonempty
            omega
          have hStrip' : (strip.card : ℝ) ≤ 8 * ell * Real.sqrt region.card := by
            simpa [strip] using hStrip
          have hLowerExterior :
              ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                daiLiRecursivePotential ell root lower.card := by
            have hSubset := daiLiGoodExteriorNeighbors_vertical_lower_subset
              P embedding ell region hAvoid hWidth.le
            have hCardNat : (daiLiGoodExteriorNeighbors P embedding ell lower).card ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)
            have hCardReal : ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact_mod_cast hCardNat
            calc
              ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                  strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := hCardReal
              _ ≤ 8 * ell * Real.sqrt region.card +
                  daiLiRecursivePotential ell root region.card :=
                add_le_add hStrip' hExterior
              _ ≤ daiLiRecursivePotential ell root lower.card := by
                nlinarith [daiLiRecursivePotential_step (root := root)
                  hEllNonneg hLowerBalanced']
          have hUpperExterior :
              ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                daiLiRecursivePotential ell root upper.card := by
            have hSubset := daiLiGoodExteriorNeighbors_vertical_upper_subset
              P embedding ell region hAvoid hWidth.le
            have hCardNat : (daiLiGoodExteriorNeighbors P embedding ell upper).card ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)
            have hCardReal : ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact_mod_cast hCardNat
            calc
              ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                  strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := hCardReal
              _ ≤ 8 * ell * Real.sqrt region.card +
                  daiLiRecursivePotential ell root region.card :=
                add_le_add hStrip' hExterior
              _ ≤ daiLiRecursivePotential ell root upper.card := by
                nlinarith [daiLiRecursivePotential_step (root := root)
                  hEllNonneg hUpperBalanced']
          have hLowerRecovery := ih lower.card (lt_of_lt_of_le hLowerLt hSize) lower
            le_rfl hLowerRoot hLowerCounter hLowerExterior
          have hUpperRecovery := ih upper.card (lt_of_lt_of_le hUpperLt hSize) upper
            le_rfl hUpperRoot hUpperCounter hUpperExterior
          have hBufferSmall := daiLiRecursiveBuffer_card_lt_distance P embedding d root ell
            hDistancePositive (lt_of_lt_of_le hDistancePositive hDistanceLeRoot) hEllNonneg hScale
            region strip hRegionRoot hStrip' hCounter hExterior
          exact exists_erasureRecovery_of_daiLiVerticalRecursiveStep P embedding d hDistance
            ell region hEllNonneg hAvoid hWidth.le
            (by simpa [lower] using hLowerRecovery)
            (by simpa [upper] using hUpperRecovery)
            (by simpa [strip] using hBufferSmall)
        · rcases hHorizontal with ⟨lowerCut, upperCut, hAvoid, hWidth, hStrip,
            hLowerBalanced, hUpperBalanced⟩
          let lower := daiLiHorizontalSeparatorLower embedding region lowerCut
          let upper := daiLiHorizontalSeparatorUpper embedding region upperCut
          let strip := daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut
          have hLowerSubset : lower ⊆ region := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hUpperSubset : upper ⊆ region := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hLowerRoot : lower.card ≤ root :=
            (Finset.card_le_card hLowerSubset).trans hRegionRoot
          have hUpperRoot : upper.card ≤ root :=
            (Finset.card_le_card hUpperSubset).trans hRegionRoot
          have hLowerCounter : 10 * regionInteractionCounter P embedding ell lower ≤ d := by
            exact (Nat.mul_le_mul_left 10
              (regionInteractionCounter_mono P embedding ell hLowerSubset)).trans hCounter
          have hUpperCounter : 10 * regionInteractionCounter P embedding ell upper ≤ d := by
            exact (Nat.mul_le_mul_left 10
              (regionInteractionCounter_mono P embedding ell hUpperSubset)).trans hCounter
          have hLowerBalanced' : 10 * lower.card ≤ 9 * region.card := by
            simpa [lower] using hLowerBalanced
          have hUpperBalanced' : 10 * upper.card ≤ 9 * region.card := by
            simpa [upper] using hUpperBalanced
          have hLowerLt : lower.card < region.card := by
            have hPositive : 0 < region.card := Finset.card_pos.mpr hRegionNonempty
            omega
          have hUpperLt : upper.card < region.card := by
            have hPositive : 0 < region.card := Finset.card_pos.mpr hRegionNonempty
            omega
          have hStrip' : (strip.card : ℝ) ≤ 8 * ell * Real.sqrt region.card := by
            simpa [strip] using hStrip
          have hLowerExterior :
              ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                daiLiRecursivePotential ell root lower.card := by
            have hSubset := daiLiGoodExteriorNeighbors_horizontal_lower_subset
              P embedding ell region hAvoid hWidth.le
            have hCardNat : (daiLiGoodExteriorNeighbors P embedding ell lower).card ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)
            have hCardReal : ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact_mod_cast hCardNat
            calc
              ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                  strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := hCardReal
              _ ≤ 8 * ell * Real.sqrt region.card +
                  daiLiRecursivePotential ell root region.card :=
                add_le_add hStrip' hExterior
              _ ≤ daiLiRecursivePotential ell root lower.card := by
                nlinarith [daiLiRecursivePotential_step (root := root)
                  hEllNonneg hLowerBalanced']
          have hUpperExterior :
              ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                daiLiRecursivePotential ell root upper.card := by
            have hSubset := daiLiGoodExteriorNeighbors_horizontal_upper_subset
              P embedding ell region hAvoid hWidth.le
            have hCardNat : (daiLiGoodExteriorNeighbors P embedding ell upper).card ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)
            have hCardReal : ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact_mod_cast hCardNat
            calc
              ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                  strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := hCardReal
              _ ≤ 8 * ell * Real.sqrt region.card +
                  daiLiRecursivePotential ell root region.card :=
                add_le_add hStrip' hExterior
              _ ≤ daiLiRecursivePotential ell root upper.card := by
                nlinarith [daiLiRecursivePotential_step (root := root)
                  hEllNonneg hUpperBalanced']
          have hLowerRecovery := ih lower.card (lt_of_lt_of_le hLowerLt hSize) lower
            le_rfl hLowerRoot hLowerCounter hLowerExterior
          have hUpperRecovery := ih upper.card (lt_of_lt_of_le hUpperLt hSize) upper
            le_rfl hUpperRoot hUpperCounter hUpperExterior
          have hBufferSmall := daiLiRecursiveBuffer_card_lt_distance P embedding d root ell
            hDistancePositive (lt_of_lt_of_le hDistancePositive hDistanceLeRoot) hEllNonneg hScale
            region strip hRegionRoot hStrip' hCounter hExterior
          exact exists_erasureRecovery_of_daiLiHorizontalRecursiveStep P embedding d hDistance
            ell region hEllNonneg hAvoid hWidth.le
            (by simpa [lower] using hLowerRecovery)
            (by simpa [upper] using hUpperRecovery)
            (by simpa [strip] using hBufferSmall)
  exact hStatement region.card region le_rfl hRegionRoot hCounter hExterior

/-- Recoverability of the full physical register forces the encoded dimension
to vanish.  Keeping this conversion local prevents the terminal Part-I claim
from taking any recovery or dimension bound as an input. -/
private theorem encodedQubits_eq_zero_of_daiLiFullRecovery
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d) (hd : 0 < d)
    (recoveryAll : QuantumChannel
      (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem
      (Qubit.QubitRegister ι))
    (hRecoveryAll : Correctable (Qubit.QubitRegister ι)
      (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem P.semanticCode
      (daiLiFiniteSubsystem (Finset.univ : Finset ι)).erasureChannelFromRegister
        recoveryAll) :
    P.encodedQubits = 0 := by
  let allSubsystem : FiniteSubsystem ι :=
    daiLiFiniteSubsystem (Finset.univ : Finset ι)
  let emptySubsystem : FiniteSubsystem ι := daiLiFiniteSubsystem (∅ : Finset ι)
  obtain ⟨recoveryEmpty, hRecoveryEmpty⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      emptySubsystem (by
        change 0 < d
        exact hd)
  have hBound := two_correctable_regions_encodedQubits_le_separator_card P
    allSubsystem emptySubsystem emptySubsystem
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    (by simp [emptySubsystem, daiLiFiniteSubsystem])
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    recoveryAll (by simpa [allSubsystem] using hRecoveryAll)
    recoveryEmpty hRecoveryEmpty
  simpa [emptySubsystem, daiLiFiniteSubsystem] using hBound

private theorem encodedQubits_le_blockLength
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _

/-- DL24 Part I's actual recursive-separator contradiction.  The source's
large-distance inequality is retained as an explicit branch condition; the
Part-I argument itself proves the stronger statement using its finite
above-BPT hypothesis and never assumes a separator, a recovery, or an
interaction-count conclusion. -/
theorem daiLiLargeDistance_fewLongInteractions_encodedQubits_eq_zero
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hAboveBPT : 100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2)
    (hLargeDistance : Real.sqrt ((P.encodedQubits : ℝ) * (Fintype.card ι : ℝ)) ≤ d)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) :
    P.encodedQubits = 0 := by
  by_contra hNonzero
  have hEncodedPositive : 0 < P.encodedQubits := Nat.pos_of_ne_zero hNonzero
  have hEncodedLeBlock : P.encodedQubits ≤ Fintype.card ι :=
    encodedQubits_le_blockLength P
  have hBlockPositive : 0 < Fintype.card ι :=
    lt_of_lt_of_le hEncodedPositive hEncodedLeBlock
  have hDistancePositive : 0 < d := by
    by_contra hDistanceNonpositive
    have hdZero : d = 0 := Nat.eq_zero_of_not_pos hDistanceNonpositive
    simp [hdZero] at hAboveBPT
    omega
  have hTenDistance : 10 ≤ d := by
    have hScaled : 100 * Fintype.card ι ≤ Fintype.card ι * d ^ 2 := by
      calc
        100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2 := hAboveBPT
        _ ≤ Fintype.card ι * d ^ 2 :=
          Nat.mul_le_mul_right (d ^ 2) hEncodedLeBlock
    have hSquared : 100 ≤ d ^ 2 := by
      exact Nat.le_of_mul_le_mul_left
        (by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hScaled)
        hBlockPositive
    by_contra hTen
    have hNine : d ≤ 9 := by omega
    interval_cases d <;> norm_num at hSquared
  by_cases hDistanceLeBlock : d ≤ Fintype.card ι
  · let ell := daiLiLargeDistanceThreshold d (Fintype.card ι)
    have hEll : 1 ≤ ell := by
      dsimp [ell]
      exact one_le_daiLiLargeDistanceThreshold_of_positive_encodedQubits
        P embedding d hDistance hFew (by omega) hEncodedPositive
    have hCounter : 10 * regionInteractionCounter P embedding ell (Finset.univ : Finset ι) ≤ d := by
      simpa [ell] using daiLiLargeDistance_regionIncidence_budget P embedding d hFew
        (Finset.univ : Finset ι)
    have hExteriorEmpty : daiLiGoodExteriorNeighbors P embedding ell
        (Finset.univ : Finset ι) = ∅ := by
      simp [daiLiGoodExteriorNeighbors]
    have hExterior :
        ((daiLiGoodExteriorNeighbors P embedding ell (Finset.univ : Finset ι)).card : ℝ) ≤
          daiLiRecursivePotential ell (Fintype.card ι) (Finset.univ : Finset ι).card := by
      simp [hExteriorEmpty, daiLiRecursivePotential]
    obtain ⟨recoveryAll, hRecoveryAll⟩ :=
      exists_erasureRecovery_daiLiRecursiveSeparator P embedding d (Fintype.card ι)
        hDistance hDistancePositive hTenDistance hDistanceLeBlock ell hEll
        (by rfl) (Finset.univ : Finset ι) (by simp) hCounter hExterior
    exact hNonzero (encodedQubits_eq_zero_of_daiLiFullRecovery P d hDistance
      hDistancePositive recoveryAll hRecoveryAll)
  · have hBlockLtDistance : Fintype.card ι < d := Nat.lt_of_not_ge hDistanceLeBlock
    obtain ⟨recoveryAll, hRecoveryAll⟩ :=
      semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)) (by
          simpa [daiLiFiniteSubsystem] using hBlockLtDistance)
    exact hNonzero (encodedQubits_eq_zero_of_daiLiFullRecovery P d hDistance
      hDistancePositive recoveryAll hRecoveryAll)

/-- Contrapositive count conclusion of DL24 Part I.  In the exact finite
large-distance branch, the actual `Finset (Sym2 ι)` of unordered
fixed-generator interactions has at least `d / 200` elements at Euclidean
length at least `d / (200 sqrt n)`, in coefficient form to avoid rounding. -/
theorem daiLiLargeDistance_interaction_count_lower_bound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hAboveBPT : 100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2)
    (hLargeDistance : Real.sqrt ((P.encodedQubits : ℝ) * (Fintype.card ι : ℝ)) ≤ d)
    (hEncodedPositive : 0 < P.encodedQubits) :
    d ≤ 200 * P.longInteractionCount embedding
      (daiLiLargeDistanceThreshold d (Fintype.card ι)) := by
  by_contra hCount
  have hFew : DaiLiLargeDistanceFewLongInteractions P embedding d := by
    unfold DaiLiLargeDistanceFewLongInteractions
    omega
  have hZero := daiLiLargeDistance_fewLongInteractions_encodedQubits_eq_zero
    P embedding d hDistance hAboveBPT hLargeDistance hFew
  omega

end QEC.Locality
