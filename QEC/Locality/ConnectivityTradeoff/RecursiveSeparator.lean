import QEC.Locality.SeparatorProfile.Core
import QEC.Locality.CorrectableRegions.SemanticDistanceErasure
import QEC.Locality.CorrectableRegions.CorrectableRegionClosure
/-!
# Finite Baspin--Krishna recursive separator partitions

This module implements the finite recursive construction behind the BK
separator argument.  At every nonterminal induced vertex set it chooses a
separator attaining the measured `2/3` profile, recurses on the two retained
regions, and charges the separator to a well-founded finite recurrence.

The final fixed-generator theorem also turns the pairwise source-decoupled
small regions into a concrete CPTP-erasure-correctable region.  Thus the graph
partition is not used as a proxy for semantic correctability.
-/

noncomputable section

namespace QEC.Locality

open QEC Semantics Coding

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- One chosen separator attaining the measured minimum on `vertices`. -/
noncomputable def measuredTwoThirdsSeparator
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset ι :=
  Classical.choose (exists_minimumTwoThirdsBalancedVertexSeparator G vertices)

theorem measuredTwoThirdsSeparator_spec
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    measuredTwoThirdsSeparator G vertices ⊆ vertices ∧
      IsTwoThirdsBalancedVertexSeparator G vertices
        (measuredTwoThirdsSeparator G vertices) ∧
      (measuredTwoThirdsSeparator G vertices).card =
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices :=
  Classical.choose_spec (exists_minimumTwoThirdsBalancedVertexSeparator G vertices)

/-- The chosen left retained region for the measured separator. -/
noncomputable def measuredTwoThirdsLeft
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset ι :=
  Classical.choose (measuredTwoThirdsSeparator_spec G vertices).2.1

/-- The chosen right retained region for the measured separator. -/
noncomputable def measuredTwoThirdsRight
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset ι :=
  Classical.choose (Classical.choose_spec
    (measuredTwoThirdsSeparator_spec G vertices).2.1)

/-- The chosen minimum separator and retained regions obey the exact `2/3` convention. -/
theorem measuredTwoThirdsSplit_spec
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    TwoThirdsBalancedPartitionAfterDeleting G vertices
      (measuredTwoThirdsLeft G vertices)
      (measuredTwoThirdsSeparator G vertices)
      (measuredTwoThirdsRight G vertices) :=
  Classical.choose_spec (Classical.choose_spec
    (measuredTwoThirdsSeparator_spec G vertices).2.1)

theorem measuredTwoThirdsLeft_subset
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    measuredTwoThirdsLeft G vertices ⊆ vertices := by
  intro x hx
  have hsplit := measuredTwoThirdsSplit_spec G vertices
  have hxDiff : x ∈ vertices \ measuredTwoThirdsSeparator G vertices := by
    rw [← hsplit.2.1]
    exact Finset.mem_union_left _ hx
  exact (Finset.mem_sdiff.mp hxDiff).1

theorem measuredTwoThirdsRight_subset
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    measuredTwoThirdsRight G vertices ⊆ vertices := by
  intro x hx
  have hsplit := measuredTwoThirdsSplit_spec G vertices
  have hxDiff : x ∈ vertices \ measuredTwoThirdsSeparator G vertices := by
    rw [← hsplit.2.1]
    exact Finset.mem_union_right _ hx
  exact (Finset.mem_sdiff.mp hxDiff).1

theorem measuredTwoThirdsLeft_card_lt
    (G : ConnectivityGraph ι) (vertices : Finset ι) (hvertices : vertices.Nonempty) :
    (measuredTwoThirdsLeft G vertices).card < vertices.card := by
  have hbalance := (measuredTwoThirdsSplit_spec G vertices).2.2.2.1
  have hpositive : 0 < vertices.card := Finset.card_pos.mpr hvertices
  omega

theorem measuredTwoThirdsRight_card_lt
    (G : ConnectivityGraph ι) (vertices : Finset ι) (hvertices : vertices.Nonempty) :
    (measuredTwoThirdsRight G vertices).card < vertices.card := by
  have hbalance := (measuredTwoThirdsSplit_spec G vertices).2.2.2.2.1
  have hpositive : 0 < vertices.card := Finset.card_pos.mpr hvertices
  omega

/-- A BK recursion stops on the empty set or once its region is strictly smaller than `d`. -/
def bkSeparatorTerminal (d : Nat) (vertices : Finset ι) : Prop :=
  vertices = ∅ ∨ vertices.card < d

/--
The exact finite BK separator charge along the measured `2/3` recursion.

The empty-set clause makes the definition total even at `d = 0`; theorem use
requires `0 < d`.  Every recursive call is on an explicitly chosen retained
region with smaller cardinality, as certified by `measuredTwoThirdsSplit_spec`.
-/
noncomputable def bkSeparatorRecurrence
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) : Nat := by
  classical
  exact if bkSeparatorTerminal d vertices then 0
    else
      twoThirdsSeparationProfile G vertices.card +
        bkSeparatorRecurrence G d (measuredTwoThirdsLeft G vertices) +
        bkSeparatorRecurrence G d (measuredTwoThirdsRight G vertices)
termination_by vertices.card
decreasing_by
  all_goals
    have hnonempty : vertices.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply ‹¬bkSeparatorTerminal d vertices›
      exact Or.inl hempty
    first
    | exact measuredTwoThirdsLeft_card_lt G vertices hnonempty
    | exact measuredTwoThirdsRight_card_lt G vertices hnonempty

theorem bkSeparatorRecurrence_eq_zero_of_terminal
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι)
    (hterminal : bkSeparatorTerminal d vertices) :
    bkSeparatorRecurrence G d vertices = 0 := by
  rw [bkSeparatorRecurrence]
  simp [hterminal]

theorem bkSeparatorRecurrence_eq_profile_add
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι)
    (hterminal : ¬bkSeparatorTerminal d vertices) :
    bkSeparatorRecurrence G d vertices =
      twoThirdsSeparationProfile G vertices.card +
        bkSeparatorRecurrence G d (measuredTwoThirdsLeft G vertices) +
        bkSeparatorRecurrence G d (measuredTwoThirdsRight G vertices) := by
  rw [bkSeparatorRecurrence]
  simp [hterminal]

/-- The source-scale BK recursion stops at scale zero or below the distance threshold. -/
def bkScaleTerminal (d r : Nat) : Prop :=
  r = 0 ∨ r < d

/-- The largest integer child scale allowed by the exact `2/3` balance convention. -/
def bkTwoThirdsChildScale (r : Nat) : Nat :=
  2 * r / 3

theorem bkTwoThirdsChildScale_lt (r : Nat) (hr : 0 < r) :
    bkTwoThirdsChildScale r < r := by
  simp only [bkTwoThirdsChildScale]
  omega

theorem bkTwoThirdsChildScale_mono {small large : Nat} (h : small ≤ large) :
    bkTwoThirdsChildScale small ≤ bkTwoThirdsChildScale large := by
  simp only [bkTwoThirdsChildScale]
  omega

/--
The finite source-scale BK recurrence `S_d(r)`.

It charges the exact measured separation profile at scale `r` and recursively
charges both children at the largest integer scale permitted by `2/3` balance.
This is a worst-case envelope over all concrete induced vertex sets of size at
most `r`, rather than the charge of one chosen separator tree.
-/
noncomputable def bkScaleRecurrence
    (G : ConnectivityGraph ι) (d r : Nat) : Nat := by
  classical
  exact if bkScaleTerminal d r then 0
    else
      twoThirdsSeparationProfile G r +
        bkScaleRecurrence G d (bkTwoThirdsChildScale r) +
        bkScaleRecurrence G d (bkTwoThirdsChildScale r)
termination_by r
decreasing_by
  all_goals
    apply bkTwoThirdsChildScale_lt
    by_contra hr
    apply ‹¬bkScaleTerminal d r›
    exact Or.inl (Nat.eq_zero_of_not_pos hr)

theorem bkScaleRecurrence_eq_zero_of_terminal
    (G : ConnectivityGraph ι) (d r : Nat) (hterminal : bkScaleTerminal d r) :
    bkScaleRecurrence G d r = 0 := by
  rw [bkScaleRecurrence]
  simp [hterminal]

theorem bkScaleRecurrence_eq_profile_add
    (G : ConnectivityGraph ι) (d r : Nat) (hterminal : ¬bkScaleTerminal d r) :
    bkScaleRecurrence G d r =
      twoThirdsSeparationProfile G r +
        bkScaleRecurrence G d (bkTwoThirdsChildScale r) +
        bkScaleRecurrence G d (bkTwoThirdsChildScale r) := by
  rw [bkScaleRecurrence]
  simp [hterminal]

/-- The worst-case finite BK scale recurrence is monotone in its scale. -/
theorem bkScaleRecurrence_mono
    (G : ConnectivityGraph ι) (d : Nat) {small large : Nat} (hscale : small ≤ large) :
    bkScaleRecurrence G d small ≤ bkScaleRecurrence G d large := by
  induction large using Nat.strong_induction_on generalizing small with
  | h large ih =>
      by_cases hlargeTerminal : bkScaleTerminal d large
      · have hsmallTerminal : bkScaleTerminal d small := by
          rcases hlargeTerminal with hlargeZero | hlargeSmall
          · left
            omega
          · right
            omega
        rw [bkScaleRecurrence_eq_zero_of_terminal G d small hsmallTerminal]
        rw [bkScaleRecurrence_eq_zero_of_terminal G d large hlargeTerminal]
      · by_cases hsmallTerminal : bkScaleTerminal d small
        · rw [bkScaleRecurrence_eq_zero_of_terminal G d small hsmallTerminal]
          exact Nat.zero_le _
        · rw [bkScaleRecurrence_eq_profile_add G d small hsmallTerminal]
          rw [bkScaleRecurrence_eq_profile_add G d large hlargeTerminal]
          have hchildScale : bkTwoThirdsChildScale small ≤
              bkTwoThirdsChildScale large := bkTwoThirdsChildScale_mono hscale
          have hlargePositive : 0 < large := by
            by_contra h
            apply hlargeTerminal
            exact Or.inl (Nat.eq_zero_of_not_pos h)
          have hchildLt : bkTwoThirdsChildScale large < large :=
            bkTwoThirdsChildScale_lt large hlargePositive
          have hrecurrence := ih (bkTwoThirdsChildScale large) hchildLt hchildScale
          have hprofile := twoThirdsSeparationProfile_mono G hscale
          omega

/-- Every balanced child cardinality is bounded by the source-scale child. -/
theorem card_le_bkTwoThirdsChildScale {childCard parentCard : Nat}
    (hbalanced : 3 * childCard ≤ 2 * parentCard) :
    childCard ≤ bkTwoThirdsChildScale parentCard := by
  simp only [bkTwoThirdsChildScale]
  omega

/--
A finite recursive separator partition: the listed pieces cover `vertices`
together with `remainder`, every piece is smaller than `d`, and distinct pieces
are disjoint and have no graph edge between them.
-/
structure BKRecursivePartition
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) where
  pieces : Finset (Finset ι)
  remainder : Finset ι
  piece_subset : ∀ piece, piece ∈ pieces → piece ⊆ vertices
  remainder_subset : remainder ⊆ vertices
  covers : pieces.biUnion id ∪ remainder = vertices
  pieces_remainder_disjoint : Disjoint (pieces.biUnion id) remainder
  piece_card_lt : ∀ piece, piece ∈ pieces → piece.card < d
  pairwise_decoupled : ∀ left, left ∈ pieces → ∀ right, right ∈ pieces → left ≠ right →
    Disjoint left right ∧ NoEdgeBetween G left right
  remainder_card_le : remainder.card ≤ bkSeparatorRecurrence G d vertices

theorem NoEdgeBetween.mono {G : ConnectivityGraph ι}
    {left right left' right' : Finset ι}
    (h : NoEdgeBetween G left right) (hleft : left' ⊆ left) (hright : right' ⊆ right) :
    NoEdgeBetween G left' right' := by
  intro x hx y hy
  exact h (hleft hx) (hright hy)

theorem NoEdgeBetween.symm {G : ConnectivityGraph ι} {left right : Finset ι}
    (h : NoEdgeBetween G left right) : NoEdgeBetween G right left := by
  intro y hy x hx hxy
  exact h hx hy (G.symmetric hxy)

/-- The chosen measured recursion constructs the complete finite partition. -/
theorem exists_bkRecursivePartition
    (G : ConnectivityGraph ι) (d : Nat) (hd : 0 < d) (vertices : Finset ι) :
    Nonempty (BKRecursivePartition G d vertices) := by
  induction vertices using (measure Finset.card).wf.induction with
  | h vertices ih =>
      classical
      by_cases hterminal : bkSeparatorTerminal d vertices
      · have hsmall : vertices.card < d := by
          rcases hterminal with hempty | hsmall
          · subst vertices
            simpa using hd
          · exact hsmall
        refine ⟨{
          pieces := {vertices}
          remainder := ∅
          piece_subset := ?_
          remainder_subset := ?_
          covers := ?_
          pieces_remainder_disjoint := ?_
          piece_card_lt := ?_
          pairwise_decoupled := ?_
          remainder_card_le := ?_ }⟩
        · intro piece hpiece
          have : piece = vertices := Finset.mem_singleton.mp hpiece
          subst piece
          exact subset_rfl
        · simp
        · simp
        · simp
        · intro piece hpiece
          have : piece = vertices := Finset.mem_singleton.mp hpiece
          subst piece
          exact hsmall
        · intro left hleft right hright hne
          simp at hleft hright
          subst left
          subst right
          exact (hne rfl).elim
        · simp [bkSeparatorRecurrence, hterminal]
      · have hnonempty : vertices.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          exact hterminal (Or.inl hempty)
        let left := measuredTwoThirdsLeft G vertices
        let right := measuredTwoThirdsRight G vertices
        let separator := measuredTwoThirdsSeparator G vertices
        have hleft_lt : left.card < vertices.card := by
          exact measuredTwoThirdsLeft_card_lt G vertices hnonempty
        have hright_lt : right.card < vertices.card := by
          exact measuredTwoThirdsRight_card_lt G vertices hnonempty
        rcases ih left hleft_lt with ⟨leftPartition⟩
        rcases ih right hright_lt with ⟨rightPartition⟩
        have hsplit : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right := by
          exact measuredTwoThirdsSplit_spec G vertices
        let pieces := leftPartition.pieces ∪ rightPartition.pieces
        let remainder := separator ∪ leftPartition.remainder ∪ rightPartition.remainder
        have hleft_subset : left ⊆ vertices := measuredTwoThirdsLeft_subset G vertices
        have hright_subset : right ⊆ vertices := measuredTwoThirdsRight_subset G vertices
        have hseparator_subset : separator ⊆ vertices := hsplit.1
        refine ⟨{
          pieces := pieces
          remainder := remainder
          piece_subset := ?_
          remainder_subset := ?_
          covers := ?_
          pieces_remainder_disjoint := ?_
          piece_card_lt := ?_
          pairwise_decoupled := ?_
          remainder_card_le := ?_ }⟩
        · intro piece hpiece
          rcases Finset.mem_union.mp hpiece with hpiece | hpiece
          · exact (leftPartition.piece_subset piece hpiece).trans hleft_subset
          · exact (rightPartition.piece_subset piece hpiece).trans hright_subset
        · exact Finset.union_subset
            (Finset.union_subset hseparator_subset
              (leftPartition.remainder_subset.trans hleft_subset))
            (rightPartition.remainder_subset.trans hright_subset)
        · dsimp [pieces, remainder]
          ext x
          constructor
          · intro hx
            rcases Finset.mem_union.mp hx with hxpieces | hxremainder
            · rcases Finset.mem_biUnion.mp hxpieces with ⟨piece, hp, hxp⟩
              rcases Finset.mem_union.mp hp with hp | hp
              · exact hleft_subset (leftPartition.piece_subset piece hp hxp)
              · exact hright_subset (rightPartition.piece_subset piece hp hxp)
            · rcases Finset.mem_union.mp hxremainder with hxseparatorOrLeft | hxright
              rcases Finset.mem_union.mp hxseparatorOrLeft with hxseparator | hxleft
              · exact hseparator_subset hxseparator
              · exact hleft_subset (leftPartition.remainder_subset hxleft)
              · exact hright_subset (rightPartition.remainder_subset hxright)
          · intro hx
            by_cases hxsep : x ∈ separator
            · exact Finset.mem_union_right _
                (Finset.mem_union_left _ (Finset.mem_union_left _ hxsep))
            · have hxdiff : x ∈ vertices \ separator := Finset.mem_sdiff.mpr ⟨hx, hxsep⟩
              rw [← hsplit.2.1] at hxdiff
              rcases Finset.mem_union.mp hxdiff with hxleft | hxright
              · have hcovered : x ∈ leftPartition.pieces.biUnion id ∪
                    leftPartition.remainder := by
                  rw [leftPartition.covers]
                  exact hxleft
                rcases Finset.mem_union.mp hcovered with hxpieces | hxrem
                · rcases Finset.mem_biUnion.mp hxpieces with ⟨piece, hp, hxp⟩
                  exact Finset.mem_union_left _
                    (Finset.mem_biUnion.mpr ⟨piece, Finset.mem_union_left _ hp, hxp⟩)
                · exact Finset.mem_union_right _
                    (Finset.mem_union_left _ (Finset.mem_union_right _ hxrem))
              · have hcovered : x ∈ rightPartition.pieces.biUnion id ∪
                    rightPartition.remainder := by
                  rw [rightPartition.covers]
                  exact hxright
                rcases Finset.mem_union.mp hcovered with hxpieces | hxrem
                · rcases Finset.mem_biUnion.mp hxpieces with ⟨piece, hp, hxp⟩
                  exact Finset.mem_union_left _
                    (Finset.mem_biUnion.mpr ⟨piece, Finset.mem_union_right _ hp, hxp⟩)
                · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxrem)
        · dsimp [pieces, remainder]
          apply Finset.disjoint_left.mpr
          intro x hxpieces hxremainder
          rcases Finset.mem_biUnion.mp hxpieces with ⟨piece, hpiece, hxpiece⟩
          rcases Finset.mem_union.mp hpiece with hpieceLeft | hpieceRight
          · have hxleft : x ∈ left := leftPartition.piece_subset piece hpieceLeft hxpiece
            rcases Finset.mem_union.mp hxremainder with hxseparatorOrLeft | hxrightRem
            · rcases Finset.mem_union.mp hxseparatorOrLeft with hxseparator | hxleftRem
              · have hxdiff : x ∈ vertices \ separator := by
                  rw [← hsplit.2.1]
                  exact Finset.mem_union_left _ hxleft
                exact (Finset.mem_sdiff.mp hxdiff).2 hxseparator
              · exact (Finset.disjoint_left.mp leftPartition.pieces_remainder_disjoint)
                  (Finset.mem_biUnion.mpr ⟨piece, hpieceLeft, hxpiece⟩) hxleftRem
            · exact (Finset.disjoint_left.mp hsplit.2.2.1) hxleft
                (rightPartition.remainder_subset hxrightRem)
          · have hxright : x ∈ right := rightPartition.piece_subset piece hpieceRight hxpiece
            rcases Finset.mem_union.mp hxremainder with hxseparatorOrLeft | hxrightRem
            · rcases Finset.mem_union.mp hxseparatorOrLeft with hxseparator | hxleftRem
              · have hxdiff : x ∈ vertices \ separator := by
                  rw [← hsplit.2.1]
                  exact Finset.mem_union_right _ hxright
                exact (Finset.mem_sdiff.mp hxdiff).2 hxseparator
              · exact (Finset.disjoint_left.mp hsplit.2.2.1)
                  (leftPartition.remainder_subset hxleftRem) hxright
            · exact (Finset.disjoint_left.mp rightPartition.pieces_remainder_disjoint)
                (Finset.mem_biUnion.mpr ⟨piece, hpieceRight, hxpiece⟩) hxrightRem
        · intro piece hpiece
          rcases Finset.mem_union.mp hpiece with hpiece | hpiece
          · exact leftPartition.piece_card_lt piece hpiece
          · exact rightPartition.piece_card_lt piece hpiece
        · intro pieceA hA pieceB hB hne
          rcases Finset.mem_union.mp hA with hAL | hAR
          · rcases Finset.mem_union.mp hB with hBL | hBR
            · exact leftPartition.pairwise_decoupled pieceA hAL pieceB hBL hne
            · refine ⟨?_, ?_⟩
              · apply Finset.disjoint_left.mpr
                intro x hxA hxB
                exact (Finset.disjoint_left.mp hsplit.2.2.1)
                  (leftPartition.piece_subset pieceA hAL hxA)
                  (rightPartition.piece_subset pieceB hBR hxB)
              · exact hsplit.2.2.2.2.2.mono
                  (leftPartition.piece_subset pieceA hAL)
                  (rightPartition.piece_subset pieceB hBR)
          · rcases Finset.mem_union.mp hB with hBL | hBR
            · refine ⟨?_, ?_⟩
              · apply Finset.disjoint_left.mpr
                intro x hxA hxB
                exact (Finset.disjoint_left.mp hsplit.2.2.1)
                  (leftPartition.piece_subset pieceB hBL hxB)
                  (rightPartition.piece_subset pieceA hAR hxA)
              · exact (hsplit.2.2.2.2.2.mono
                  (leftPartition.piece_subset pieceB hBL)
                  (rightPartition.piece_subset pieceA hAR)).symm
            · exact rightPartition.pairwise_decoupled pieceA hAR pieceB hBR hne
        · dsimp [remainder]
          calc
            (separator ∪ leftPartition.remainder ∪ rightPartition.remainder).card
                ≤ (separator ∪ leftPartition.remainder).card + rightPartition.remainder.card :=
              Finset.card_union_le _ _
            _ ≤ separator.card + leftPartition.remainder.card + rightPartition.remainder.card := by
              exact Nat.add_le_add_right (Finset.card_union_le _ _) _
            _ ≤ separator.card + bkSeparatorRecurrence G d left +
                  bkSeparatorRecurrence G d right := by
              exact Nat.add_le_add
                (Nat.add_le_add_left leftPartition.remainder_card_le separator.card)
                rightPartition.remainder_card_le
            _ ≤ twoThirdsSeparationProfile G vertices.card +
                  bkSeparatorRecurrence G d left + bkSeparatorRecurrence G d right := by
              have hseparatorProfile : separator.card ≤
                  twoThirdsSeparationProfile G vertices.card := by
                rw [(measuredTwoThirdsSeparator_spec G vertices).2.2]
                exact minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
                  G vertices.card vertices (by simp) le_rfl
              omega
            _ = bkSeparatorRecurrence G d vertices := by
              exact (bkSeparatorRecurrence_eq_profile_add G d vertices hterminal).symm

/-- The charge of every concrete chosen separator tree is bounded by `S_d` at its size. -/
theorem bkSeparatorRecurrence_le_bkScaleRecurrence_card
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) :
    bkSeparatorRecurrence G d vertices ≤ bkScaleRecurrence G d vertices.card := by
  induction vertices using (measure Finset.card).wf.induction with
  | h vertices ih =>
      by_cases hterminal : bkSeparatorTerminal d vertices
      · rw [bkSeparatorRecurrence_eq_zero_of_terminal G d vertices hterminal]
        exact Nat.zero_le _
      · have hnonempty : vertices.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          exact hterminal (Or.inl hempty)
        let left := measuredTwoThirdsLeft G vertices
        let right := measuredTwoThirdsRight G vertices
        have hleftLt : left.card < vertices.card :=
          measuredTwoThirdsLeft_card_lt G vertices hnonempty
        have hrightLt : right.card < vertices.card :=
          measuredTwoThirdsRight_card_lt G vertices hnonempty
        have hleftRecurrence := ih left hleftLt
        have hrightRecurrence := ih right hrightLt
        have hsplit := measuredTwoThirdsSplit_spec G vertices
        have hleftScale : left.card ≤ bkTwoThirdsChildScale vertices.card :=
          card_le_bkTwoThirdsChildScale hsplit.2.2.2.1
        have hrightScale : right.card ≤ bkTwoThirdsChildScale vertices.card :=
          card_le_bkTwoThirdsChildScale hsplit.2.2.2.2.1
        have hleftMonotone := bkScaleRecurrence_mono G d hleftScale
        have hrightMonotone := bkScaleRecurrence_mono G d hrightScale
        have hleftBound : bkSeparatorRecurrence G d
              (measuredTwoThirdsLeft G vertices) ≤
            bkScaleRecurrence G d (bkTwoThirdsChildScale vertices.card) :=
          hleftRecurrence.trans hleftMonotone
        have hrightBound : bkSeparatorRecurrence G d
              (measuredTwoThirdsRight G vertices) ≤
            bkScaleRecurrence G d (bkTwoThirdsChildScale vertices.card) :=
          hrightRecurrence.trans hrightMonotone
        have hscaleNonterminal : ¬bkScaleTerminal d vertices.card := by
          intro hscale
          rcases hscale with hcardZero | hcardSmall
          · apply hterminal
            left
            exact Finset.card_eq_zero.mp hcardZero
          · exact hterminal (Or.inr hcardSmall)
        rw [bkSeparatorRecurrence_eq_profile_add G d vertices hterminal]
        rw [bkScaleRecurrence_eq_profile_add G d vertices.card hscaleNonterminal]
        omega

/-- Every concrete recursive charge below scale `r` is dominated by `S_d(r)`. -/
theorem bkSeparatorRecurrence_le_bkScaleRecurrence
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) (r : Nat)
    (hcard : vertices.card ≤ r) :
    bkSeparatorRecurrence G d vertices ≤ bkScaleRecurrence G d r :=
  (bkSeparatorRecurrence_le_bkScaleRecurrence_card G d vertices).trans
    (bkScaleRecurrence_mono G d hcard)

/-- The explicit two-pass scale bound needed by the downstream BK dimension argument. -/
def bkScaleRecurrenceTwice (G : ConnectivityGraph ι) (d r : Nat) : Nat :=
  bkScaleRecurrence G d (bkScaleRecurrence G d r)

theorem BKRecursivePartition.remainder_card_le_bkScaleRecurrence
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) (r : Nat)
    (hvertices : vertices.card ≤ r) :
    partition.remainder.card ≤ bkScaleRecurrence G d r :=
  partition.remainder_card_le.trans
    (bkSeparatorRecurrence_le_bkScaleRecurrence G d vertices r hvertices)

/--
After one partition below scale `r`, the recursive charge of its remainder is
bounded by the source-scale composition `S_d(S_d(r))` for the second pass.
-/
theorem BKRecursivePartition.remainder_recurrence_le_bkScaleRecurrenceTwice
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) (r : Nat)
    (hvertices : vertices.card ≤ r) :
    bkSeparatorRecurrence G d partition.remainder ≤ bkScaleRecurrenceTwice G d r := by
  exact bkSeparatorRecurrence_le_bkScaleRecurrence G d partition.remainder
    (bkScaleRecurrence G d r)
    (partition.remainder_card_le_bkScaleRecurrence r hvertices)

end QEC.Locality

namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

open QEC Semantics Locality

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/--
The union of all small pieces in a BK recursive partition has a concrete CPTP
erasure recovery: distance handles each leaf, and source decoupling handles the
finite union.
-/
theorem bkRecursivePartition_erasureRecoverable
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d)
    (vertices : Finset ι)
    (partition : BKRecursivePartition P.fixedGeneratorInteractionGraph d vertices) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
          partition.pieces).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
          partition.pieces).complementSystem
        P.semanticCode
        (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
          partition.pieces).erasureChannelFromRegister recovery := by
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
  · intro region hregion
    exact semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance (⟨region⟩ : FiniteSubsystem ι)
        (partition.piece_card_lt region hregion)
  · intro left hleft right hright hne
    rcases partition.pairwise_decoupled left hleft right hright hne with
      ⟨hdisjoint, hnoedge⟩
    exact ⟨by simpa using hdisjoint, hnoedge⟩

/--
The source-faithful BK finite recursive separator theorem on the actual fixed
generator interaction graph.
-/
theorem exists_bkRecursiveSeparatorPartition
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d)
    (hd : 0 < d) (vertices : Finset ι) :
    ∃ partition : BKRecursivePartition P.fixedGeneratorInteractionGraph d vertices,
      ∃ recovery : QuantumChannel
          (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
            partition.pieces).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
            partition.pieces).complementSystem
          P.semanticCode
          (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
            partition.pieces).erasureChannelFromRegister recovery := by
  rcases exists_bkRecursivePartition P.fixedGeneratorInteractionGraph d hd vertices with
    ⟨partition⟩
  exact ⟨partition, P.bkRecursivePartition_erasureRecoverable d hDistance vertices partition⟩

end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
