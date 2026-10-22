import QEC.Coding.QuantumTanner.HeavyEdges
import QEC.Coding.ExpanderCodes.DegreeSelection

/-!
# Selecting a heavily connected vertex with few exceptional neighbors

The useful and bad degrees here are actual finite Cayley incidence sums.
Their budgets select a genuine vertex, as in [LZ22, Claim claim:alpha/4].
Deriving the source's asymptotic budgets from the fixed-degree parameters is
separate from this finite selection argument.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

open Classical QEC.Coding.SmallSetExpansion

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- Select an actual opposite vertex using a heavy-coverage lower bound and
an actual exceptional-incidence upper bound. -/
theorem exists_high_heavy_low_exceptional_vertex
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (normal exceptional : Finset G) (hNormal : normal.Nonempty)
    (hDegreePositive : 0 < Fintype.card A + Fintype.card B)
    (threshold badAverage badCutoff : ℝ)
    (hThreshold : 0 < threshold) (hCutoff : 0 ≤ badCutoff)
    (hHeavyCoverage : normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal
      (X.oppositeHeavySet side x cutoff normal))
    (hUsefulAverage : 2 * threshold * (X.oppositeHeavySet side x cutoff normal).card ≤
      (normal.card : ℝ))
    (hBadAverage : (crossCount X.unionCayleyGraph exceptional
      (X.oppositeHeavySet side x cutoff normal) : ℝ) ≤
      badAverage * (X.oppositeHeavySet side x cutoff normal).card)
    (hBudgets : badAverage * (Fintype.card A + Fintype.card B : Nat) ≤
      badCutoff * threshold) :
    ∃ h ∈ X.oppositeHeavySet side x cutoff normal,
      threshold ≤ (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h : Nat) ∧
      (∑ g ∈ exceptional, X.unionCayleyGraph g h : Nat) ≤ badCutoff := by
  let T := X.oppositeHeavySet side x cutoff normal
  let useful : G → ℝ := fun h => (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h : Nat)
  let bad : G → ℝ := fun h => (∑ g ∈ exceptional, X.unionCayleyGraph g h : Nat)
  have hT : T.Nonempty := by
    by_contra h
    have hEmpty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hZero : crossCount (X.heavyUnionGraph side x cutoff) normal T = 0 := by
      simp [crossCount, hEmpty]
    have hNormalCard := Finset.card_pos.mpr hNormal
    change normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal T at hHeavyCoverage
    omega
  have hUsefulBound (h : G) : useful h ≤ (Fintype.card A + Fintype.card B : Nat) := by
    have hNat : (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
        Fintype.card A + Fintype.card B := by
      calc
        (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
            ∑ g ∈ normal, X.unionCayleyGraph g h :=
          Finset.sum_le_sum fun g _ => X.heavyUnionGraph_le_unionCayleyGraph side x cutoff g h
        _ ≤ ∑ g : G, X.unionCayleyGraph g h := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ normal)
          intro g hg hNot
          exact Nat.zero_le _
        _ = Fintype.card A + Fintype.card B := X.unionCayleyGraph_incoming_regular h
    dsimp [useful]
    exact_mod_cast hNat
  have hUsefulSum : (∑ h ∈ T, useful h) =
      (crossCount (X.heavyUnionGraph side x cutoff) normal T : ℝ) := by
    simp only [useful, crossCount, Nat.cast_sum]
    exact Finset.sum_comm
  have hBadSum : (∑ h ∈ T, bad h) = (crossCount X.unionCayleyGraph exceptional T : ℝ) := by
    simp only [bad, crossCount, Nat.cast_sum]
    exact Finset.sum_comm
  apply exists_high_degree_low_bad_degree T hT useful bad
    (Fintype.card A + Fintype.card B : Nat) threshold badAverage badCutoff
  · exact_mod_cast hDegreePositive
  · exact hThreshold
  · exact hCutoff
  · intro h hh
    exact hUsefulBound h
  · intro h hh
    exact Nat.cast_nonneg _
  · rw [hUsefulSum]
    have hCoverage : (normal.card : ℝ) ≤
        crossCount (X.heavyUnionGraph side x cutoff) normal T := by exact_mod_cast hHeavyCoverage
    exact hUsefulAverage.trans hCoverage
  · rw [hBadSum]
    exact hBadAverage
  · exact hBudgets

/-- Heavy coverage and a small exceptional fraction force the ambient active
set to be only linear in the opposite heavy set. -/
theorem active_card_le_twice_degree_opposite_card
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (S exceptional : Finset G) (hExceptional : 2 * (S ∩ exceptional).card ≤ S.card)
    (hCoverage : (S \ exceptional).card ≤
      crossCount (X.heavyUnionGraph side x cutoff) (S \ exceptional)
        (X.oppositeHeavySet side x cutoff (S \ exceptional))) :
    S.card ≤ 2 * (Fintype.card A + Fintype.card B) *
      (X.oppositeHeavySet side x cutoff (S \ exceptional)).card := by
  have hCross : crossCount (X.heavyUnionGraph side x cutoff) (S \ exceptional)
      (X.oppositeHeavySet side x cutoff (S \ exceptional)) ≤
      crossCount X.unionCayleyGraph (S \ exceptional)
        (X.oppositeHeavySet side x cutoff (S \ exceptional)) := by
    apply Finset.sum_le_sum
    intro g hg
    apply Finset.sum_le_sum
    intro h hh
    exact X.heavyUnionGraph_le_unionCayleyGraph side x cutoff g h
  have hDegree := X.crossCount_unionCayleyGraph_le_degree_card_right
    (S \ exceptional) (X.oppositeHeavySet side x cutoff (S \ exceptional))
  have hPartition := Finset.card_sdiff_add_card_inter S exceptional
  nlinarith

/-- Derive the bad-incidence budget from actual mixing, exceptional-set size,
and heavy coverage, instead of postulating the bad-incidence sum. -/
theorem exceptional_crossCount_le_of_heavy_coverage
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (S exceptional : Finset G) (spectral fraction uniformBudget : ℝ)
    (hSpectral : 0 ≤ spectral) (hFraction : 0 ≤ fraction)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) spectral)
    (hExceptional : 2 * (S ∩ exceptional).card ≤ S.card)
    (hFractionBound : (exceptional.card : ℝ) ≤ fraction * S.card)
    (hMean : (Fintype.card A + Fintype.card B : Nat) * (exceptional.card : ℝ) ≤
      uniformBudget * Fintype.card G)
    (hCoverage : (S \ exceptional).card ≤
      crossCount (X.heavyUnionGraph side x cutoff) (S \ exceptional)
        (X.oppositeHeavySet side x cutoff (S \ exceptional))) :
    (crossCount X.unionCayleyGraph exceptional
      (X.oppositeHeavySet side x cutoff (S \ exceptional)) : ℝ) ≤
      (uniformBudget + spectral * Real.sqrt
        (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) *
      (X.oppositeHeavySet side x cutoff (S \ exceptional)).card := by
  apply crossCount_le_linear_of_card_ratio X.unionCayleyGraph
    (Fintype.card A + Fintype.card B) spectral fraction
    (2 * (Fintype.card A + Fintype.card B : Nat)) uniformBudget
    hSpectral hFraction (by positivity) hMixing exceptional S
    (X.oppositeHeavySet side x cutoff (S \ exceptional)) hFractionBound
  · exact_mod_cast X.active_card_le_twice_degree_opposite_card side x cutoff
      S exceptional hExceptional hCoverage
  · exact hMean

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
