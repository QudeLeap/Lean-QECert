import QEC.Locality.CorrectablePartition.Core
import QEC.Locality.ConnectivityTradeoff.QuantitativeRecurrence
import QEC.Locality.CorrectableRegions.TwoCorrectableRegionsDimension
/-!
# BGKL restricted-connectivity terminal

This module realizes the finite binary-stabilizer specialization of the BGKL
restricted-connectivity tradeoff. For `0 < c < 1`, it first consumes the correctable
partition built from the explicit edge division, then runs the one-pass BK
partition on its actual complement. The two correctable-region dimension lemma
bounds the encoded dimension by the final remainder. The endpoint `c = 1` is
deliberately separate and uses the finite stabilizer dimension bound `k <= n`.

The public theorem takes the actual induced-subgraph (2/3)-balanced profile
of each fixed stabilizer presentation as its hypothesis. The `c = 1` endpoint
is a Lean-QEC repair, not a claim about the BGKL r-division derivation.
-/

noncomputable section

namespace QEC.Locality

open QEC Semantics Coding

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- The terminal-piece union of one concrete BK recursive partition. -/
private def bgklBKPartitionRegion
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) : FiniteSubsystem ι :=
  ⟨partition.pieces.biUnion id⟩

private theorem bkRpowCoefficient_pos
    {beta c : ℝ} (hbeta : 0 < beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < bkRpowCoefficient beta c := by
  unfold bkRpowCoefficient
  exact div_pos hbeta
    (mul_pos (bkRpowGap_pos hc0 hc1)
      (Real.rpow_pos_of_pos (by norm_num) _))

private theorem encodedQubits_le_blockLength
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _

private theorem bgkl_endpoint_one_bound
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) :
    (P.encodedQubits : ℝ) * Real.rpow d ((1 - (1 : ℝ) ^ 2) / 1) ≤
      Fintype.card ι := by
  have hdimension : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast encodedQubits_le_blockLength P
  simpa using hdimension

/--
The uniform finite code-level BGKL bridge. The `0 < c < 1` branch is the
actual #383-plus-one-pass-BK construction; it does not take a partition,
recovery, or conclusion as input.
-/
private theorem exists_bgklRestrictedConnectivityCodeBound_of_two_le
    (beta c : ℝ) (hbeta : 1 ≤ beta) (hc : 0 < c ∧ c ≤ 1) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        {κ : Type v} [Fintype κ]
        (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
        (d : Nat), 2 ≤ d → d ≤ Fintype.card ι →
        StabilizerCode.SemanticStabilizerDistance P.code d →
        P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta c →
        (P.encodedQubits : ℝ) *
          Real.rpow d ((1 - c ^ 2) / c) ≤ alpha * Fintype.card ι := by
  by_cases hcOne : c = 1
  · subst c
    refine ⟨1, by norm_num, ?_⟩
    intro ι instFintype instDecidableEq κ instFintypeK P d _hd _hdn _hDistance _hProfile
    simpa using bgkl_endpoint_one_bound P d
  have hcLt : c < 1 := lt_of_le_of_ne hc.2 hcOne
  rcases exists_bgklCorrectablePartition beta c hbeta ⟨hc.1, hcLt⟩ with
    ⟨partitionAlpha, hpartitionAlphaPos, hpartition⟩
  let recurrenceAlpha := bkRpowCoefficient beta c
  have hbetaNonneg : 0 ≤ beta := by linarith
  refine ⟨partitionAlpha * recurrenceAlpha,
    mul_pos hpartitionAlphaPos
      (bkRpowCoefficient_pos (zero_lt_one.trans_le hbeta) hc.1.le hcLt), ?_⟩
  intro ι instFintype instDecidableEq κ instFintypeK P d hd hdn hDistance hProfile
  rcases hpartition P d (Nat.zero_lt_two.trans_le hd) hdn hDistance hProfile with
    ⟨A, recoveryA, hRecoveryA, hAComplement⟩
  let ARegion : FiniteSubsystem ι := finiteSubsystemOfFinset A
  let remaining : Finset ι := Finset.univ \ A
  have hremainingCard : (remaining.card : ℝ) ≤
      partitionAlpha * Fintype.card ι / Real.rpow d ((1 - c) / c) := by
    simpa [remaining] using hAComplement
  have hdPos : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_two.trans_le hd)
  have hfirstPowerPos : 0 < Real.rpow d ((1 - c) / c) :=
    Real.rpow_pos_of_pos hdPos _
  have hsecondPowerPos : 0 < Real.rpow d (1 - c) :=
    Real.rpow_pos_of_pos hdPos _
  have htargetPower : ((1 - c ^ 2) / c) = (1 - c) / c + (1 - c) := by
    field_simp [ne_of_gt hc.1]
    ring
  by_cases hdRemaining : d ≤ remaining.card
  · rcases P.exists_bkRecursiveSeparatorPartition d hDistance
        (Nat.zero_lt_two.trans_le hd) remaining with ⟨partition, recoveryB, hRecoveryB⟩
    let BRegion := bgklBKPartitionRegion partition
    let CRegion : FiniteSubsystem ι := ⟨partition.remainder⟩
    have hBSubset : BRegion.selected ⊆ remaining := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨piece, hpiece, hxpiece⟩
      exact partition.piece_subset piece hpiece hxpiece
    have hCSubset : CRegion.selected ⊆ remaining := partition.remainder_subset
    have hAB : Disjoint ARegion.selected BRegion.selected := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.mem_sdiff.mp (hBSubset hxB)).2 hxA
    have hAC : Disjoint ARegion.selected CRegion.selected := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxC
      exact (Finset.mem_sdiff.mp (hCSubset hxC)).2 hxA
    have hBC : Disjoint BRegion.selected CRegion.selected := by
      exact partition.pieces_remainder_disjoint
    have hCover : ARegion.selected ∪ BRegion.selected ∪ CRegion.selected = Finset.univ := by
      change A ∪ partition.pieces.biUnion id ∪ partition.remainder = Finset.univ
      rw [Finset.union_assoc, partition.covers]
      exact Finset.union_sdiff_of_subset (Finset.subset_univ A)
    have hdimension : P.encodedQubits ≤ CRegion.selected.card :=
      two_correctable_regions_encodedQubits_le_separator_card P ARegion BRegion CRegion hAB hAC hBC
        hCover recoveryA (by simpa [ARegion] using hRecoveryA) recoveryB
        hRecoveryB
    have hprofileRange : ∀ scale : Nat, d ≤ scale → scale ≤ remaining.card →
        (twoThirdsSeparationProfile P.fixedGeneratorInteractionGraph scale : ℝ) ≤
          beta * Real.rpow scale c := by
      intro scale hdscale hscale
      have hscalePos : 1 ≤ scale := by omega
      exact hProfile.2.2.2 scale hscalePos
        (hscale.trans (Finset.card_le_card Finset.sdiff_subset))
    have hrecurrence : (partition.remainder.card : ℝ) ≤
        recurrenceAlpha * remaining.card / Real.rpow d (1 - c) := by
      have hcharge : partition.remainder.card ≤
          bkSumPreservingRecurrence P.fixedGeneratorInteractionGraph d remaining.card := by
        simpa [remaining] using partition.remainder_card_le_bkSumPreservingRecurrence
      have hquantitative := bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
        P.fixedGeneratorInteractionGraph d remaining.card remaining.card beta c hbetaNonneg hc.1.le hcLt
        hd hdRemaining le_rfl hprofileRange
      have hchargeReal : (partition.remainder.card : ℝ) ≤
          (bkSumPreservingRecurrence P.fixedGeneratorInteractionGraph d remaining.card : ℝ) := by
        exact_mod_cast hcharge
      exact hchargeReal.trans hquantitative
    have hdimensionReal : (P.encodedQubits : ℝ) ≤ partition.remainder.card := by
      exact_mod_cast hdimension
    have hcoefficientNonneg : 0 ≤ recurrenceAlpha :=
      bkRpowCoefficient_nonneg hbetaNonneg hc.1.le hcLt
    have hscaledRemaining : recurrenceAlpha * (remaining.card : ℝ) /
        Real.rpow d (1 - c) ≤
        recurrenceAlpha * (partitionAlpha * Fintype.card ι /
          Real.rpow d ((1 - c) / c)) / Real.rpow d (1 - c) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hremainingCard hcoefficientNonneg) hsecondPowerPos.le
    have hbaseBound : (P.encodedQubits : ℝ) ≤
        (partitionAlpha * recurrenceAlpha) * Fintype.card ι /
          (Real.rpow d ((1 - c) / c) * Real.rpow d (1 - c)) := by
      calc
        (P.encodedQubits : ℝ) ≤ partition.remainder.card := hdimensionReal
        _ ≤ recurrenceAlpha * remaining.card / Real.rpow d (1 - c) := hrecurrence
        _ ≤ recurrenceAlpha * (partitionAlpha * Fintype.card ι /
            Real.rpow d ((1 - c) / c)) / Real.rpow d (1 - c) := hscaledRemaining
        _ = (partitionAlpha * recurrenceAlpha) * Fintype.card ι /
            (Real.rpow d ((1 - c) / c) * Real.rpow d (1 - c)) := by
          field_simp [hfirstPowerPos.ne', hsecondPowerPos.ne']
    have hproductPower : Real.rpow d ((1 - c) / c) * Real.rpow d (1 - c) =
        Real.rpow d ((1 - c ^ 2) / c) := by
      calc
        Real.rpow d ((1 - c) / c) * Real.rpow d (1 - c) =
            Real.rpow d ((1 - c) / c + (1 - c)) :=
          (Real.rpow_add hdPos _ _).symm
        _ = Real.rpow d ((1 - c ^ 2) / c) := by rw [htargetPower]
    have htradeoff : (P.encodedQubits : ℝ) ≤
        (partitionAlpha * recurrenceAlpha) * Fintype.card ι /
          Real.rpow d ((1 - c ^ 2) / c) := by
      rw [hproductPower] at hbaseBound
      exact hbaseBound
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hdPos _)).mp at htradeoff
    rw [mul_assoc]
    simpa [mul_comm, mul_left_comm] using htradeoff
  · have hremainingSmall : remaining.card < d := Nat.lt_of_not_ge hdRemaining
    let BRegion : FiniteSubsystem ι := finiteSubsystemOfFinset remaining
    let CRegion : FiniteSubsystem ι := finiteSubsystemOfFinset ∅
    rcases semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance BRegion hremainingSmall with
      ⟨recoveryB, hRecoveryB⟩
    have hAB : Disjoint ARegion.selected BRegion.selected := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.mem_sdiff.mp hxB).2 hxA
    have hAC : Disjoint ARegion.selected CRegion.selected := by
      simp [ARegion, CRegion, finiteSubsystemOfFinset]
    have hBC : Disjoint BRegion.selected CRegion.selected := by
      simp [BRegion, CRegion, finiteSubsystemOfFinset]
    have hCover : ARegion.selected ∪ BRegion.selected ∪ CRegion.selected = Finset.univ := by
      change A ∪ (Finset.univ \ A) ∪ ∅ = Finset.univ
      rw [Finset.union_empty]
      exact Finset.union_sdiff_of_subset (Finset.subset_univ A)
    have hdimension : P.encodedQubits ≤ CRegion.selected.card :=
      two_correctable_regions_encodedQubits_le_separator_card P ARegion BRegion CRegion hAB hAC hBC
        hCover recoveryA (by simpa [ARegion] using hRecoveryA) recoveryB
        hRecoveryB
    have hzero : (P.encodedQubits : ℝ) = 0 := by
      have : P.encodedQubits = 0 := by
        exact Nat.eq_zero_of_le_zero (by simpa [CRegion, finiteSubsystemOfFinset] using hdimension)
      exact_mod_cast this
    rw [hzero, zero_mul]
    exact mul_nonneg (mul_nonneg hpartitionAlphaPos.le
      (bkRpowCoefficient_nonneg hbetaNonneg hc.1.le hcLt)) (Nat.cast_nonneg _)

/--
The uniform finite code-level BGKL bridge for every positive semantic distance.
The `d = 1` case is a separate finite `k <= n` bound; the nontrivial branch
uses the explicit #383 partition followed by one BK partition.
-/
theorem exists_bgklRestrictedConnectivityCodeBound
    (beta c : ℝ) (hbeta : 1 ≤ beta) (hc : 0 < c ∧ c ≤ 1) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        {κ : Type v} [Fintype κ]
        (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
        (d : Nat), 1 ≤ d → d ≤ Fintype.card ι →
        StabilizerCode.SemanticStabilizerDistance P.code d →
        P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta c →
        (P.encodedQubits : ℝ) *
          Real.rpow d ((1 - c ^ 2) / c) ≤ alpha * Fintype.card ι := by
  rcases exists_bgklRestrictedConnectivityCodeBound_of_two_le beta c hbeta hc with
    ⟨twoAlpha, htwoAlphaPos, htwoBound⟩
  refine ⟨max 1 twoAlpha, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ι instFintype instDecidableEq κ instFintypeK P d hd hdn hDistance hProfile
  by_cases hdOne : d = 1
  · subst d
    have hdimension : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast encodedQubits_le_blockLength P
    have hbase : (P.encodedQubits : ℝ) *
        ((↑(1 : Nat) : ℝ) ^ ((1 - c ^ 2) / c)) ≤ Fintype.card ι := by
      simpa using hdimension
    exact hbase.trans (by
      calc
        (Fintype.card ι : ℝ) = 1 * Fintype.card ι := by ring
        _ ≤ max 1 twoAlpha * Fintype.card ι :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  · have hdTwo : 2 ≤ d := by omega
    have hbase := htwoBound P d hdTwo hdn hDistance hProfile
    exact hbase.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))

/--
A finite binary stabilizer family with the actual per-index presentation and
computed parameters needed by the BGKL terminal. It intentionally has no LDPC
field and no stored separator or tradeoff conclusion.
-/
structure BGKLRestrictedConnectivityFamily
    (ι : Nat → Type u) (κ : Nat → Type v)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)] where
  validIndex : Nat → Prop
  parameterData : ∀ n, StabilizerCode.StabilizerParameterData (ι := ι n) (κ := κ n)
  blockLength_eq_index : ∀ n, validIndex n → (parameterData n).blockLength = n
  distance_pos : ∀ n, validIndex n → 1 ≤ (parameterData n).distance
  distance_le_index : ∀ n, validIndex n → (parameterData n).distance ≤ n

namespace BGKLRestrictedConnectivityFamily

variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]

/-- The valid block-length indices for this finite family. -/
abbrev Index (family : BGKLRestrictedConnectivityFamily ι κ) :=
  {n : Nat // family.validIndex n}

/--
The finite binary-stabilizer BGKL restricted-connectivity specialization
[BGKL24, Informal Theorem]. Each valid index supplies an actual independent
Pauli-generator presentation and its measured induced-subgraph profile. The
`0 < c < 1` branch uses the BGKL r-division route through #383, #380, and
#368. The `c = 1` endpoint instead uses the Lean-QEC finite stabilizer bound
`k <= n`; it is not attributed to BGKL's r-division argument.
-/
theorem exists_bgklRestrictedConnectivityTradeoff
    (family : BGKLRestrictedConnectivityFamily ι κ)
    (beta c : ℝ) (hbeta : 1 ≤ beta) (hc : 0 < c ∧ c ≤ 1)
    (hprofile : ∀ n, ∀ _hvalid : family.validIndex n, ∀ scale : Nat,
      1 ≤ scale → scale ≤ n →
        ((family.parameterData n).presentation.fixedGeneratorTwoThirdsSeparationProfile scale : ℝ) ≤
          beta * Real.rpow scale c) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ i : family.Index,
      ((family.parameterData i.1).encodedQubits : ℝ) *
        Real.rpow (family.parameterData i.1).distance ((1 - c ^ 2) / c) ≤
          alpha * i.1 := by
  rcases exists_bgklRestrictedConnectivityCodeBound beta c hbeta hc with
    ⟨alpha, halpha, hbound⟩
  refine ⟨alpha, halpha, ?_⟩
  rintro ⟨n, hvalid⟩
  have hcard : Fintype.card (ι n) = n := by
    exact family.blockLength_eq_index n hvalid
  have hprofileN :
      QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound
        (family.parameterData n).presentation beta c := by
    refine ⟨hbeta, hc.1, hc.2, ?_⟩
    intro scale hscale hscaleCard
    have hscaleIndex : scale ≤ n := by simpa [hcard] using hscaleCard
    simpa [StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorTwoThirdsSeparationProfile] using
      hprofile n hvalid scale hscale hscaleIndex
  have hboundN := hbound (family.parameterData n).presentation
    (family.parameterData n).distance (family.distance_pos n hvalid)
    (by
      calc
        (family.parameterData n).distance ≤ n := family.distance_le_index n hvalid
        _ = (family.parameterData n).blockLength := (family.blockLength_eq_index n hvalid).symm
        _ = Fintype.card (ι n) := rfl)
    (family.parameterData n).semanticDistance hprofileN
  simpa [StabilizerCode.StabilizerParameterData.encodedQubits,
    StabilizerCode.StabilizerParameterData.distance,
    hcard] using hboundN

end BGKLRestrictedConnectivityFamily

end QEC.Locality
