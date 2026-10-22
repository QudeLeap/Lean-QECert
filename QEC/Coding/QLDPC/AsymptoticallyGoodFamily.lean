import QEC.Coding.QLDPC.QuantumCodeFamily

/-!
# Asymptotically good quantum LDPC families

These are properties of an independently constructed family of finite-qudit
check presentations. In particular, no construction or existence theorem is
part of this interface. A single locality bound applies to every family member;
rate and distance estimates hold beyond explicit block-length thresholds.
-/

noncomputable section

namespace QEC.QLDPC

universe u v w

variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

/-- One check-weight and variable-degree bound for the entire family. -/
def HasUniformLDPC (F : QuantumCodeFamily A ι κ) : Prop :=
  ∃ B : Nat, ∀ a, Coding.BoundedLocality (F.localityProfile a) B

/-- Eventually every code has encoded dimension at least `rate` times its length. -/
def HasEventualRateAtLeast (F : QuantumCodeFamily A ι κ) (rate : ℝ) : Prop :=
  ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
    rate * (F.blockLength a : ℝ) ≤ (F.encodedDimension a : ℝ)

/-- Eventually every code has distance at least `relativeDistance` times its length. -/
def HasEventualRelativeDistanceAtLeast
    (F : QuantumCodeFamily A ι κ) (relativeDistance : ℝ) : Prop :=
  ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
    relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ)

/-- Uniform qLDPC locality, positive asymptotic rate and linear distance.
The family itself already supplies unbounded block length. -/
def IsAsymptoticallyGoodQLDPCFamily (F : QuantumCodeFamily A ι κ) : Prop :=
  HasUniformLDPC F ∧
    (∃ rate : ℝ, 0 < rate ∧ HasEventualRateAtLeast F rate) ∧
    (∃ relativeDistance : ℝ, 0 < relativeDistance ∧
      HasEventualRelativeDistanceAtLeast F relativeDistance)

/-- Uniform incidence locality is equivalent to one common bound on both
observable row weights and variable degrees. -/
theorem hasUniformLDPC_iff_components (F : QuantumCodeFamily A ι κ) :
    HasUniformLDPC F ↔
      ∃ B : Nat, ∀ a, F.maxCheckWeight a ≤ B ∧ F.maxVariableDegree a ≤ B := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun a => (F.boundedLocality_iff a B).mp (hB a)⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, fun a => (F.boundedLocality_iff a B).mpr (hB a)⟩

/-- A common bound on the actual check regions and incidence degrees yields
family-wide LDPC locality, not merely separate bounds for each member. -/
theorem hasUniformLDPC_of_region_bounds
    (F : QuantumCodeFamily A ι κ) (B : Nat)
    (hcheck : ∀ a checkIndex,
      ((F.presentation a).checks checkIndex).region.selected.card ≤ B)
    (hcoordinate : ∀ a coordinate,
      ((F.presentation a).incidence.variableSupport coordinate).card ≤ B) :
    HasUniformLDPC F := by
  exact ⟨B, fun a =>
    F.boundedLocality_of_region_bounds a (hcheck a) (hcoordinate a)⟩

/-- The eventual rate and distance bounds can be used at one common threshold. -/
theorem eventual_rate_and_distance_at_common_threshold
    (F : QuantumCodeFamily A ι κ) (rate relativeDistance : ℝ)
    (hRate : HasEventualRateAtLeast F rate)
    (hDistance : HasEventualRelativeDistanceAtLeast F relativeDistance) :
    ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
      rate * (F.blockLength a : ℝ) ≤ (F.encodedDimension a : ℝ) ∧
      relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ) := by
  obtain ⟨NRate, hRate⟩ := hRate
  obtain ⟨NDistance, hDistance⟩ := hDistance
  refine ⟨max NRate NDistance, ?_⟩
  intro a hLength
  exact ⟨hRate a (le_trans (le_max_left _ _) hLength),
    hDistance a (le_trans (le_max_right _ _) hLength)⟩

/-- An eventual relative-distance lower bound and the universal distance cap
give two-sided estimates beyond one threshold. A positive lower-bound constant
therefore supplies both sides of linear distance. -/
theorem eventual_two_sided_distance_bounds
    (F : QuantumCodeFamily A ι κ) (relativeDistance : ℝ)
    (hDistance : HasEventualRelativeDistanceAtLeast F relativeDistance) :
    ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
      relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ) ∧
        (F.distance a : ℝ) ≤ (F.blockLength a : ℝ) := by
  obtain ⟨N, hN⟩ := hDistance
  refine ⟨N, fun a ha => ⟨hN a ha, ?_⟩⟩
  exact_mod_cast F.distance_le_blockLength a

/-- An asymptotically good family has arbitrarily large members for which
the same positive rate and relative-distance constants apply. -/
theorem exists_large_good_member
    (F : QuantumCodeFamily A ι κ) (hGood : IsAsymptoticallyGoodQLDPCFamily F) :
    ∃ rate relativeDistance : ℝ, 0 < rate ∧ 0 < relativeDistance ∧
      ∀ M : Nat, ∃ a : A, M ≤ F.blockLength a ∧
        rate * (F.blockLength a : ℝ) ≤ (F.encodedDimension a : ℝ) ∧
        relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ) := by
  obtain ⟨_hLocality, ⟨rate, hRatePos, hRate⟩,
    ⟨relativeDistance, hDistancePos, hDistance⟩⟩ := hGood
  obtain ⟨N, hBoth⟩ :=
    eventual_rate_and_distance_at_common_threshold F rate relativeDistance hRate hDistance
  refine ⟨rate, relativeDistance, hRatePos, hDistancePos, ?_⟩
  intro M
  obtain ⟨a, ha⟩ := F.exists_blockLength_ge (max M N)
  exact ⟨a, le_trans (le_max_left _ _) ha,
    (hBoth a (le_trans (le_max_right _ _) ha)).1,
    (hBoth a (le_trans (le_max_right _ _) ha)).2⟩

end QEC.QLDPC
