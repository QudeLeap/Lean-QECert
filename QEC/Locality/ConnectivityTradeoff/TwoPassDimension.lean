import QEC.Locality.ConnectivityTradeoff.QuantitativeRecurrence
import QEC.Locality.CorrectableRegions.TwoCorrectableRegionsDimension
/-!
# The two-pass Baspin--Krishna dimension bridge

This module performs the two recursive separator passes on the actual fixed-generator graph.
The first pass produces the correctable region `A`.  The second pass is run on the first
remainder (hence on its induced vertex sets) and produces the correctable region `B`.  The
second remainder is `C`.  The concrete `A / B / C` partition is then supplied to the
two-correctable-regions dimension theorem.
-/

noncomputable section

namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

open QEC Semantics Locality

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- The finite subsystem formed by all terminal pieces of a recursive partition. -/
def bkPartitionRegion {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) : FiniteSubsystem ι :=
  ⟨partition.pieces.biUnion id⟩

/--
The genuine finite two-pass BK bridge.

The witnesses expose the two recursively constructed partitions and the actual regions used by
the dimension theorem.  In particular, `B` is not a second projection of the first pass: its
partition is constructed with `first.remainder` as its vertex set.
-/
theorem exists_bkTwoPassDimensionBound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d) (hd : 0 < d) :
    ∃ first : BKRecursivePartition P.fixedGeneratorInteractionGraph d Finset.univ,
      ∃ second : BKRecursivePartition P.fixedGeneratorInteractionGraph d first.remainder,
        let A := bkPartitionRegion first
        let B := bkPartitionRegion second
        let C : FiniteSubsystem ι := ⟨second.remainder⟩
        Disjoint A.selected B.selected ∧
          Disjoint A.selected C.selected ∧
          Disjoint B.selected C.selected ∧
          A.selected ∪ B.selected ∪ C.selected = Finset.univ ∧
          ∃ recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι),
            Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
                A.erasureChannelFromRegister recoveryA ∧
              ∃ recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι),
                Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
                    B.erasureChannelFromRegister recoveryB ∧
                  P.encodedQubits ≤ C.selected.card ∧
                  first.remainder.card ≤ bkSumPreservingRecurrence
                    P.fixedGeneratorInteractionGraph d (Fintype.card ι) ∧
                  C.selected.card ≤ bkSeparatorRecurrence
                    P.fixedGeneratorInteractionGraph d first.remainder ∧
                  C.selected.card ≤ bkSumPreservingRecurrenceTwice
                    P.fixedGeneratorInteractionGraph d (Fintype.card ι) := by
  rcases exists_bkRecursivePartition P.fixedGeneratorInteractionGraph d hd Finset.univ with
    ⟨first⟩
  rcases exists_bkRecursivePartition P.fixedGeneratorInteractionGraph d hd first.remainder with
    ⟨second⟩
  let A := bkPartitionRegion first
  let B := bkPartitionRegion second
  let C : FiniteSubsystem ι := ⟨second.remainder⟩
  have hARecovery := P.bkRecursivePartition_erasureRecoverable d hDistance Finset.univ first
  have hBRecovery :=
    P.bkRecursivePartition_erasureRecoverable d hDistance first.remainder second
  rcases hARecovery with ⟨recoveryA, hRecoveryA⟩
  rcases hBRecovery with ⟨recoveryB, hRecoveryB⟩
  have hBSubset : B.selected ⊆ first.remainder := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨piece, hpiece, hxpiece⟩
    exact second.piece_subset piece hpiece hxpiece
  have hCSubset : C.selected ⊆ first.remainder := second.remainder_subset
  have hAB : Disjoint A.selected B.selected := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    exact (Finset.disjoint_left.mp first.pieces_remainder_disjoint) hxA (hBSubset hxB)
  have hAC : Disjoint A.selected C.selected := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxC
    exact (Finset.disjoint_left.mp first.pieces_remainder_disjoint) hxA (hCSubset hxC)
  have hBC : Disjoint B.selected C.selected := second.pieces_remainder_disjoint
  have hCover : A.selected ∪ B.selected ∪ C.selected = Finset.univ := by
    change first.pieces.biUnion id ∪ second.pieces.biUnion id ∪ second.remainder = Finset.univ
    rw [Finset.union_assoc, second.covers, first.covers]
  have hDimension : P.encodedQubits ≤ C.selected.card :=
    two_correctable_regions_encodedQubits_le_separator_card P A B C hAB hAC hBC hCover
      recoveryA hRecoveryA recoveryB hRecoveryB
  have hFirstCharge : first.remainder.card ≤ bkSumPreservingRecurrence
      P.fixedGeneratorInteractionGraph d (Fintype.card ι) := by
    simpa using first.remainder_card_le_bkSumPreservingRecurrence
  have hSecondCharge : second.remainder.card ≤
      bkSeparatorRecurrence P.fixedGeneratorInteractionGraph d first.remainder :=
    second.remainder_card_le
  have hSecondScale : bkSeparatorRecurrence P.fixedGeneratorInteractionGraph d
        first.remainder ≤
      bkSumPreservingRecurrenceTwice P.fixedGeneratorInteractionGraph d
        (Fintype.card ι) := by
    simpa using first.remainder_recurrence_le_bkSumPreservingRecurrenceTwice
  refine ⟨first, second, ?_⟩
  dsimp only
  exact ⟨hAB, hAC, hBC, hCover, recoveryA, hRecoveryA, recoveryB, hRecoveryB,
    hDimension, hFirstCharge, hSecondCharge, hSecondCharge.trans hSecondScale⟩

/--
The concrete two-pass construction composed with the exact #485 finite-power estimate.

The second recurrence is evaluated on the actual first remainder.  Neither a supplied
partition nor an assumed target inequality occurs in the hypotheses.
-/
theorem encodedQubits_cast_le_bkRpowCoefficient_sq
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d)
    (beta c : ℝ) (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd : 2 ≤ d) (hdn : d ≤ Fintype.card ι)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ Fintype.card ι →
      (twoThirdsSeparationProfile P.fixedGeneratorInteractionGraph scale : ℝ) ≤
        beta * (scale : ℝ) ^ c) :
    (P.encodedQubits : ℝ) ≤
      (bkRpowCoefficient beta c * bkRpowCoefficient beta c) * Fintype.card ι /
        (((d : ℝ) ^ (1 - c)) * ((d : ℝ) ^ (1 - c))) := by
  rcases exists_bkTwoPassDimensionBound P d hDistance (by omega) with
    ⟨first, second, htwoPass⟩
  dsimp only at htwoPass
  rcases htwoPass with
    ⟨_hAB, _hAC, _hBC, _hCover, _recoveryA, _hRecoveryA,
      _recoveryB, _hRecoveryB, hDimension, _hFirstCharge,
      hSecondCharge, _hSecondBound⟩
  have hDimensionReal : (P.encodedQubits : ℝ) ≤ second.remainder.card := by
    exact_mod_cast hDimension
  have hSecondChargeReal : (second.remainder.card : ℝ) ≤
      bkSeparatorRecurrence P.fixedGeneratorInteractionGraph d first.remainder := by
    exact_mod_cast hSecondCharge
  have hQuantitative :=
    first.remainder_recurrence_cast_le_bkRpowCoefficient_sq
      beta c hbeta hc0 hc1 hd (by simpa using hdn) hprofile
  exact hDimensionReal.trans (hSecondChargeReal.trans hQuantitative)

end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

namespace QEC.Locality

universe u v

namespace BKQLDPCFamily

variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]

/-- The measured `cMax` profile gives the exact finite two-pass BK dimension estimate. -/
theorem encodedQubits_cast_le_cMax_coefficient_sq
    (family : BKQLDPCFamily iota kappa) (i : family.Index) :
    (family.encodedQubits i.1 : ℝ) ≤
      (bkRpowCoefficient 1 (family.cMax i) *
          bkRpowCoefficient 1 (family.cMax i)) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
  let P := family.presentation i.1
  have hprofile : ∀ scale : Nat, family.distance i.1 ≤ scale → scale ≤ i.1 →
      (twoThirdsSeparationProfile (family.fixedGeneratorGraph i) scale : ℝ) ≤
        (scale : ℝ) ^ family.cMax i := by
    intro scale hdistance hscale
    simpa [measuredSeparationProfile] using
      family.measuredSeparationProfile_le_rpow_cMax i
        ((family.mem_validScales_iff i scale).2 ⟨hdistance, hscale⟩)
  have hbound :=
    P.encodedQubits_cast_le_bkRpowCoefficient_sq
      (family.distance i.1) (family.parameterData i.1).semanticDistance
      1 (family.cMax i) (by norm_num) (family.cMax_nonneg i)
      (family.cMax_lt_one i) (family.distance_two_le i.1 i.2) (by
        simpa [family.index_card i] using family.distance_le_index i.1 i.2) (by
        simpa [P, fixedGeneratorGraph, family.index_card i] using hprofile)
  simp only [P, family.index_card i] at hbound
  exact hbound

/-- The pointwise BK logarithmic threshold gives the explicit two-pass logarithmic bound. -/
theorem encodedQubits_cast_le_cMax_log_bound
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    (hthreshold : family.cMax i ≤
      1 + Real.logb (i.1 : ℝ) (1 / 3 : ℝ)) :
    (family.encodedQubits i.1 : ℝ) ≤
      ((3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) *
          (3 * Real.log i.1 / (bkEntropyGap * Real.log 3))) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
  let coefficient := bkRpowCoefficient 1 (family.cMax i)
  let logCoefficient := 3 * Real.log i.1 / (bkEntropyGap * Real.log 3)
  have hbase := family.encodedQubits_cast_le_cMax_coefficient_sq i
  have hnNat : 1 < i.1 :=
    lt_of_lt_of_le (by
      have := family.distance_two_le i.1 i.2
      omega) (family.distance_le_index i.1 i.2)
  have hn : (1 : ℝ) < i.1 := by exact_mod_cast hnNat
  have hcoefficient : coefficient ≤ logCoefficient := by
    simpa [coefficient, logCoefficient] using bkRpowCoefficient_le_log_bound
      (beta := 1) (c := family.cMax i) (n := (i.1 : ℝ))
      (by norm_num) (family.cMax_nonneg i) (family.cMax_lt_one i)
      hn hthreshold
  have hcoefficientNonneg : 0 ≤ coefficient :=
    bkRpowCoefficient_nonneg (by norm_num) (family.cMax_nonneg i)
      (family.cMax_lt_one i)
  have hsquare : coefficient * coefficient ≤ logCoefficient * logCoefficient :=
    mul_self_le_mul_self hcoefficientNonneg hcoefficient
  have hdistancePos : (0 : ℝ) < family.distance i.1 := by
    have hdNat : 0 < family.distance i.1 :=
      Nat.zero_lt_two.trans_le (family.distance_two_le i.1 i.2)
    exact_mod_cast hdNat
  have hdenominatorPos : 0 <
      ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
        ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
    positivity
  calc
    (family.encodedQubits i.1 : ℝ) ≤
        (coefficient * coefficient) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      simpa [coefficient] using hbase
    _ ≤ (logCoefficient * logCoefficient) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (Nat.cast_nonneg i.1))
        hdenominatorPos.le
    _ = ((3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) *
          (3 * Real.log i.1 / (bkEntropyGap * Real.log 3))) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      rfl

/--
The actual two-pass BK construction has a logarithmic coefficient under the
visible Lean-QEC `gamma`-gap on the measured exponent.  This does not derive
the gap from the pointwise strict inequality `cMax < 1`.
-/
theorem encodedQubits_cast_le_cMax_logarithmic_gap_bound
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : gamma ≤ (1 - family.cMax i) * Real.log i.1) :
    (family.encodedQubits i.1 : ℝ) ≤
      ((3 * Real.log i.1 / (bkEntropyGap * gamma)) *
          (3 * Real.log i.1 / (bkEntropyGap * gamma))) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
  let coefficient := bkRpowCoefficient 1 (family.cMax i)
  let logCoefficient := 3 * Real.log i.1 / (bkEntropyGap * gamma)
  have hbase := family.encodedQubits_cast_le_cMax_coefficient_sq i
  have hcoefficient : coefficient ≤ logCoefficient := by
    simpa [coefficient, logCoefficient] using
      bkRpowCoefficient_le_logarithmic_gap_bound
        (beta := 1) (c := family.cMax i) (n := (i.1 : ℝ)) (gamma := gamma)
        (by norm_num) (family.cMax_nonneg i) (family.cMax_lt_one i) hgamma hgap
  have hcoefficientNonneg : 0 ≤ coefficient :=
    bkRpowCoefficient_nonneg (by norm_num) (family.cMax_nonneg i)
      (family.cMax_lt_one i)
  have hsquare : coefficient * coefficient ≤ logCoefficient * logCoefficient :=
    mul_self_le_mul_self hcoefficientNonneg hcoefficient
  have hdistancePos : (0 : ℝ) < family.distance i.1 := by
    have hdNat : 0 < family.distance i.1 :=
      Nat.zero_lt_two.trans_le (family.distance_two_le i.1 i.2)
    exact_mod_cast hdNat
  have hdenominatorPos : 0 <
      ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
        ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
    positivity
  calc
    (family.encodedQubits i.1 : ℝ) ≤
        (coefficient * coefficient) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      simpa [coefficient] using hbase
    _ ≤ (logCoefficient * logCoefficient) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (Nat.cast_nonneg i.1))
        hdenominatorPos.le
    _ = ((3 * Real.log i.1 / (bkEntropyGap * gamma)) *
          (3 * Real.log i.1 / (bkEntropyGap * gamma))) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      rfl

/-- The logarithmic two-pass bound holds on the exact valid-index tail. -/
theorem eventually_encodedQubits_cast_le_cMax_log_bound
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.EventuallyCMaxAtMostBKLogThreshold) :
    family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤
        ((3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) *
            (3 * Real.log i.1 / (bkEntropyGap * Real.log 3))) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)))) := by
  rcases hfamily with ⟨start, hstart⟩
  exact ⟨start, fun n hn hvalid ↦
    family.encodedQubits_cast_le_cMax_log_bound ⟨n, hvalid⟩
      (hstart n hn hvalid)⟩

/-- The two-pass logarithmic-gap bound holds on the explicit valid-index tail. -/
theorem eventually_encodedQubits_cast_le_cMax_logarithmic_gap_bound
    (family : BKQLDPCFamily iota kappa) {gamma : ℝ} (hgamma : 0 < gamma)
    (hfamily : family.EventuallyOnValidIndices (fun i ↦
      gamma ≤ (1 - family.cMax i) * Real.log i.1)) :
    family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤
        ((3 * Real.log i.1 / (bkEntropyGap * gamma)) *
            (3 * Real.log i.1 / (bkEntropyGap * gamma))) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)))) := by
  rcases hfamily with ⟨start, hstart⟩
  exact ⟨start, fun n hn hvalid ↦
    family.encodedQubits_cast_le_cMax_logarithmic_gap_bound ⟨n, hvalid⟩ hgamma
      (hstart n hn hvalid)⟩

/--
A family-uniform exponent ceiling below one removes the logarithmic coefficient.
The distance exponent remains the sharper pointwise `cMax` exponent.
-/
theorem encodedQubits_cast_le_uniform_ceiling
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    {ceiling : ℝ} (_hceiling0 : 0 ≤ ceiling) (hceiling1 : ceiling < 1)
    (hcMax : family.cMax i ≤ ceiling) :
    (family.encodedQubits i.1 : ℝ) ≤
      ((3 / (bkEntropyGap * (1 - ceiling))) *
          (3 / (bkEntropyGap * (1 - ceiling)))) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
  let coefficient := bkRpowCoefficient 1 (family.cMax i)
  let uniformCoefficient := 3 / (bkEntropyGap * (1 - ceiling))
  have hbase := family.encodedQubits_cast_le_cMax_coefficient_sq i
  have hpointwise := bkRpowCoefficient_le_entropy_bound
    (beta := (1 : ℝ)) (c := family.cMax i) (by norm_num)
      (family.cMax_nonneg i) (family.cMax_lt_one i)
  have hceilingDenominatorPos : 0 < bkEntropyGap * (1 - ceiling) :=
    mul_pos bkEntropyGap_pos (sub_pos.mpr hceiling1)
  have hdenominatorOrder :
      bkEntropyGap * (1 - ceiling) ≤
        bkEntropyGap * (1 - family.cMax i) :=
    mul_le_mul_of_nonneg_left (by linarith) bkEntropyGap_pos.le
  have hcoefficient : coefficient ≤ uniformCoefficient := by
    have hdiv :
        (3 : ℝ) / (bkEntropyGap * (1 - family.cMax i)) ≤
          3 / (bkEntropyGap * (1 - ceiling)) :=
      div_le_div_of_nonneg_left (by norm_num) hceilingDenominatorPos
        hdenominatorOrder
    have hpointwise' : coefficient ≤
        3 / (bkEntropyGap * (1 - family.cMax i)) := by
      simpa [coefficient] using hpointwise
    have hdiv' : 3 / (bkEntropyGap * (1 - family.cMax i)) ≤
        uniformCoefficient := by
      simpa [uniformCoefficient] using hdiv
    exact hpointwise'.trans hdiv'
  have hcoefficientNonneg : 0 ≤ coefficient :=
    bkRpowCoefficient_nonneg (by norm_num) (family.cMax_nonneg i)
      (family.cMax_lt_one i)
  have hsquare : coefficient * coefficient ≤
      uniformCoefficient * uniformCoefficient :=
    mul_self_le_mul_self hcoefficientNonneg hcoefficient
  have hdistancePos : (0 : ℝ) < family.distance i.1 := by
    have hdNat : 0 < family.distance i.1 :=
      Nat.zero_lt_two.trans_le (family.distance_two_le i.1 i.2)
    exact_mod_cast hdNat
  have hdenominatorPos : 0 <
      ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
        ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
    positivity
  calc
    (family.encodedQubits i.1 : ℝ) ≤
        (coefficient * coefficient) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      simpa [coefficient] using hbase
    _ ≤ (uniformCoefficient * uniformCoefficient) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (Nat.cast_nonneg i.1))
        hdenominatorPos.le
    _ = ((3 / (bkEntropyGap * (1 - ceiling))) *
          (3 / (bkEntropyGap * (1 - ceiling)))) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by
      rfl

/-- `UniformCMaxBelowOne` supplies one log-free two-pass tail and its constant. -/
theorem eventually_encodedQubits_cast_le_uniform_ceiling
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.UniformCMaxBelowOne) :
    ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
      family.EventuallyOnValidIndices (fun i ↦
        (family.encodedQubits i.1 : ℝ) ≤
          ((3 / (bkEntropyGap * (1 - ceiling))) *
              (3 / (bkEntropyGap * (1 - ceiling)))) * i.1 /
            (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
              ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)))) := by
  rcases hfamily with ⟨ceiling, hceiling0, hceiling1, start, hstart⟩
  refine ⟨ceiling, hceiling0, hceiling1, start, ?_⟩
  intro n hn hvalid
  exact family.encodedQubits_cast_le_uniform_ceiling ⟨n, hvalid⟩
    hceiling0.le hceiling1 (hstart n hn hvalid)

end BKQLDPCFamily

end QEC.Locality
