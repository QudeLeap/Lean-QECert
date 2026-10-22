import QEC.Locality.ConnectivityTradeoff.RecursiveSeparator
import QEC.Locality.ConnectivityTradeoff.MaxFamily
/-!
# Sum-preserving Baspin--Krishna separator recurrence

This module replaces the quantitatively too coarse pair of independently
maximal `2r/3` children by one finite maximum over admissible child pairs.
The pair keeps both the balance inequalities and the source-critical
`left + right <= parent` invariant.

The construction is an internal finite API.  It does not assert the public BK
tradeoff and does not change any public theorem lifecycle record.
-/

noncomputable section

namespace QEC.Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The exact natural-number side conditions for one BK separator split. -/
def BKAdmissibleChildPair (parent : Nat) (children : Nat × Nat) : Prop :=
  children.1 + children.2 ≤ parent ∧
    3 * children.1 ≤ 2 * parent ∧
    3 * children.2 ≤ 2 * parent
deriving Decidable

/-- All admissible strict child pairs at a positive parent scale. -/
def bkAdmissibleChildPairs (parent : Nat) : Finset (Nat × Nat) :=
  ((Finset.range parent).product (Finset.range parent)).filter
    (fun children => decide (BKAdmissibleChildPair parent children))

theorem mem_bkAdmissibleChildPairs_iff {parent : Nat} {children : Nat × Nat} :
    children ∈ bkAdmissibleChildPairs parent ↔
      children.1 < parent ∧ children.2 < parent ∧
        BKAdmissibleChildPair parent children := by
  simp [bkAdmissibleChildPairs, and_assoc]

theorem zero_zero_mem_bkAdmissibleChildPairs {parent : Nat} (hparent : 0 < parent) :
    (0, 0) ∈ bkAdmissibleChildPairs parent := by
  apply mem_bkAdmissibleChildPairs_iff.mpr
  exact ⟨hparent, hparent, by simp [BKAdmissibleChildPair]⟩

/--
The finite, source-faithful BK scale recurrence.

At each nonterminal scale the recursive contribution is one maximum over
admissible *pairs*.  Consequently a maximizing left child and a maximizing
right child must come from the same sum-preserving split.
-/
noncomputable def bkSumPreservingRecurrence
    (G : ConnectivityGraph ι) (d parent : Nat) : Nat := by
  classical
  exact if bkScaleTerminal d parent then 0
    else
      twoThirdsSeparationProfile G parent +
        (bkAdmissibleChildPairs parent).sup (fun children =>
          if _hchildren : children ∈ bkAdmissibleChildPairs parent then
            bkSumPreservingRecurrence G d children.1 +
              bkSumPreservingRecurrence G d children.2
          else 0)
termination_by parent
decreasing_by
  all_goals
    have hchildren := (mem_bkAdmissibleChildPairs_iff).1 ‹children ∈ _›
    omega

theorem bkSumPreservingRecurrence_eq_zero_of_terminal
    (G : ConnectivityGraph ι) (d parent : Nat)
    (hterminal : bkScaleTerminal d parent) :
    bkSumPreservingRecurrence G d parent = 0 := by
  rw [bkSumPreservingRecurrence]
  simp [hterminal]

theorem bkSumPreservingRecurrence_eq_profile_add
    (G : ConnectivityGraph ι) (d parent : Nat)
    (hterminal : ¬bkScaleTerminal d parent) :
    bkSumPreservingRecurrence G d parent =
      twoThirdsSeparationProfile G parent +
        (bkAdmissibleChildPairs parent).sup (fun children =>
          if _hchildren : children ∈ bkAdmissibleChildPairs parent then
            bkSumPreservingRecurrence G d children.1 +
              bkSumPreservingRecurrence G d children.2
          else 0) := by
  rw [bkSumPreservingRecurrence]
  simp [hterminal]

/-- The actual measured children from #380 preserve their parent cardinality sum. -/
theorem measuredTwoThirdsChildren_card_add_le
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    (measuredTwoThirdsLeft G vertices).card +
        (measuredTwoThirdsRight G vertices).card ≤ vertices.card := by
  have hsplit := measuredTwoThirdsSplit_spec G vertices
  have hcardUnion :
      (measuredTwoThirdsLeft G vertices ∪ measuredTwoThirdsRight G vertices).card =
        (measuredTwoThirdsLeft G vertices).card +
          (measuredTwoThirdsRight G vertices).card :=
    Finset.card_union_of_disjoint hsplit.2.2.1
  have hsubset :
      measuredTwoThirdsLeft G vertices ∪ measuredTwoThirdsRight G vertices ⊆ vertices := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact measuredTwoThirdsLeft_subset G vertices hx
    · exact measuredTwoThirdsRight_subset G vertices hx
  rw [← hcardUnion]
  exact Finset.card_le_card hsubset

/-- The actual #380 split supplies one witness in the admissible-pair maximum. -/
theorem measuredTwoThirdsChildren_mem_bkAdmissibleChildPairs
    (G : ConnectivityGraph ι) (vertices : Finset ι) (hvertices : vertices.Nonempty) :
    ((measuredTwoThirdsLeft G vertices).card,
      (measuredTwoThirdsRight G vertices).card) ∈
        bkAdmissibleChildPairs vertices.card := by
  apply (mem_bkAdmissibleChildPairs_iff).2
  have hsplit := measuredTwoThirdsSplit_spec G vertices
  exact ⟨measuredTwoThirdsLeft_card_lt G vertices hvertices,
    measuredTwoThirdsRight_card_lt G vertices hvertices,
    measuredTwoThirdsChildren_card_add_le G vertices,
    hsplit.2.2.2.1,
    hsplit.2.2.2.2.1⟩

/--
The concrete measured separator charge from #380 is controlled by the
sum-preserving scale recurrence at its exact parent cardinality.
-/
theorem bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) :
    bkSeparatorRecurrence G d vertices ≤
      bkSumPreservingRecurrence G d vertices.card := by
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
        have hleftBound := ih left hleftLt
        have hrightBound := ih right hrightLt
        have hpair : (left.card, right.card) ∈
            bkAdmissibleChildPairs vertices.card := by
          exact measuredTwoThirdsChildren_mem_bkAdmissibleChildPairs G vertices hnonempty
        have hchildren :
            bkSumPreservingRecurrence G d left.card +
                bkSumPreservingRecurrence G d right.card ≤
              (bkAdmissibleChildPairs vertices.card).sup (fun children =>
                if hchildren : children ∈ bkAdmissibleChildPairs vertices.card then
                  bkSumPreservingRecurrence G d children.1 +
                    bkSumPreservingRecurrence G d children.2
                else 0) := by
          have hsup := Finset.le_sup
            (f := fun children : Nat × Nat =>
              if hchildren : children ∈ bkAdmissibleChildPairs vertices.card then
                bkSumPreservingRecurrence G d children.1 +
                  bkSumPreservingRecurrence G d children.2
              else 0) hpair
          simpa [hpair] using hsup
        have hscaleNonterminal : ¬bkScaleTerminal d vertices.card := by
          intro hscale
          rcases hscale with hcardZero | hcardSmall
          · apply hterminal
            left
            exact Finset.card_eq_zero.mp hcardZero
          · exact hterminal (Or.inr hcardSmall)
        rw [bkSeparatorRecurrence_eq_profile_add G d vertices hterminal]
        rw [bkSumPreservingRecurrence_eq_profile_add G d vertices.card hscaleNonterminal]
        have hrecursive := (Nat.add_le_add hleftBound hrightBound).trans hchildren
        simpa [left, right, Nat.add_assoc] using
          Nat.add_le_add_left hrecursive (twoThirdsSeparationProfile G vertices.card)

/-- The concrete #380 partition remainder inherits the source-faithful bound. -/
theorem BKRecursivePartition.remainder_card_le_bkSumPreservingRecurrence
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) :
    partition.remainder.card ≤ bkSumPreservingRecurrence G d vertices.card :=
  partition.remainder_card_le.trans
    (bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card G d vertices)

theorem bkAdmissibleChildPairs_mono {small large : Nat} (hscale : small ≤ large) :
    bkAdmissibleChildPairs small ⊆ bkAdmissibleChildPairs large := by
  intro children hchildren
  have hsmall := (mem_bkAdmissibleChildPairs_iff).1 hchildren
  apply (mem_bkAdmissibleChildPairs_iff).2
  exact ⟨by omega, by omega, by
    unfold BKAdmissibleChildPair at hsmall ⊢
    omega⟩

/-- The source-faithful recurrence is monotone in its parent scale. -/
theorem bkSumPreservingRecurrence_mono
    (G : ConnectivityGraph ι) (d : Nat) {small large : Nat} (hscale : small ≤ large) :
    bkSumPreservingRecurrence G d small ≤ bkSumPreservingRecurrence G d large := by
  by_cases hlargeTerminal : bkScaleTerminal d large
  · have hsmallTerminal : bkScaleTerminal d small := by
      rcases hlargeTerminal with hlargeZero | hlargeSmall
      · left
        omega
      · right
        omega
    rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d small hsmallTerminal]
    rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d large hlargeTerminal]
  · by_cases hsmallTerminal : bkScaleTerminal d small
    · rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d small hsmallTerminal]
      exact Nat.zero_le _
    · rw [bkSumPreservingRecurrence_eq_profile_add G d small hsmallTerminal]
      rw [bkSumPreservingRecurrence_eq_profile_add G d large hlargeTerminal]
      have hprofile := twoThirdsSeparationProfile_mono G hscale
      have hsup :
          (bkAdmissibleChildPairs small).sup (fun children =>
              if hchildren : children ∈ bkAdmissibleChildPairs small then
                bkSumPreservingRecurrence G d children.1 +
                  bkSumPreservingRecurrence G d children.2
              else 0) ≤
            (bkAdmissibleChildPairs large).sup (fun children =>
              if hchildren : children ∈ bkAdmissibleChildPairs large then
                bkSumPreservingRecurrence G d children.1 +
                  bkSumPreservingRecurrence G d children.2
              else 0) := by
        apply Finset.sup_le
        intro children hchildren
        have hchildrenLarge := bkAdmissibleChildPairs_mono hscale hchildren
        have hle := Finset.le_sup
          (f := fun children : Nat × Nat =>
            if h : children ∈ bkAdmissibleChildPairs large then
              bkSumPreservingRecurrence G d children.1 +
                bkSumPreservingRecurrence G d children.2
            else 0) hchildrenLarge
        simpa [hchildren, hchildrenLarge] using hle
      exact Nat.add_le_add hprofile hsup

/-- The exact source-faithful scale composition used for a second partition pass. -/
def bkSumPreservingRecurrenceTwice
    (G : ConnectivityGraph ι) (d parent : Nat) : Nat :=
  bkSumPreservingRecurrence G d (bkSumPreservingRecurrence G d parent)

/-- The second concrete #380 charge is controlled by the sum-preserving composition. -/
theorem BKRecursivePartition.remainder_recurrence_le_bkSumPreservingRecurrenceTwice
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) :
    bkSeparatorRecurrence G d partition.remainder ≤
      bkSumPreservingRecurrenceTwice G d vertices.card := by
  exact (bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
      G d partition.remainder).trans
    (bkSumPreservingRecurrence_mono G d
      partition.remainder_card_le_bkSumPreservingRecurrence)

/-!
## Explicit finite logarithmic-depth estimate

`bkTwoThirdsDepth d r` is the exact number of successive integral `2/3`
scale reductions before the terminal threshold.  It is a finite replacement
for an asymptotic logarithm: no Big-O assumption occurs in the API.
-/

/-- The exact finite number of `2/3` scale layers above threshold `d`. -/
noncomputable def bkTwoThirdsDepth (d parent : Nat) : Nat := by
  classical
  exact if bkScaleTerminal d parent then 0
    else 1 + bkTwoThirdsDepth d (bkTwoThirdsChildScale parent)
termination_by parent
decreasing_by
  apply bkTwoThirdsChildScale_lt
  by_contra hparent
  apply ‹¬bkScaleTerminal d parent›
  exact Or.inl (Nat.eq_zero_of_not_pos hparent)

theorem bkTwoThirdsDepth_eq_zero_of_terminal
    (d parent : Nat) (hterminal : bkScaleTerminal d parent) :
    bkTwoThirdsDepth d parent = 0 := by
  rw [bkTwoThirdsDepth]
  simp [hterminal]

theorem bkTwoThirdsDepth_eq_succ
    (d parent : Nat) (hterminal : ¬bkScaleTerminal d parent) :
    bkTwoThirdsDepth d parent =
      1 + bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
  rw [bkTwoThirdsDepth]
  simp [hterminal]

/-- The finite `2/3` depth is monotone in the starting scale. -/
theorem bkTwoThirdsDepth_mono
    (d : Nat) {small large : Nat} (hscale : small ≤ large) :
    bkTwoThirdsDepth d small ≤ bkTwoThirdsDepth d large := by
  induction large using Nat.strong_induction_on generalizing small with
  | h large ih =>
      by_cases hlargeTerminal : bkScaleTerminal d large
      · have hsmallTerminal : bkScaleTerminal d small := by
          rcases hlargeTerminal with hlargeZero | hlargeSmall
          · left
            omega
          · right
            omega
        rw [bkTwoThirdsDepth_eq_zero_of_terminal d small hsmallTerminal]
        rw [bkTwoThirdsDepth_eq_zero_of_terminal d large hlargeTerminal]
      · by_cases hsmallTerminal : bkScaleTerminal d small
        · rw [bkTwoThirdsDepth_eq_zero_of_terminal d small hsmallTerminal]
          exact Nat.zero_le _
        · rw [bkTwoThirdsDepth_eq_succ d small hsmallTerminal]
          rw [bkTwoThirdsDepth_eq_succ d large hlargeTerminal]
          apply Nat.add_le_add_left
          have hlargePositive : 0 < large := by
            by_contra hpositive
            apply hlargeTerminal
            exact Or.inl (Nat.eq_zero_of_not_pos hpositive)
          exact ih (bkTwoThirdsChildScale large)
            (bkTwoThirdsChildScale_lt large hlargePositive)
            (bkTwoThirdsChildScale_mono hscale)

/--
Any scale-linear separator charge yields an explicit finite
`coefficient * parent * two-thirds-depth` recurrence bound.
-/
theorem bkSumPreservingRecurrence_le_coefficient_mul_scale_mul_depth
    (G : ConnectivityGraph ι) (d coefficient parent : Nat)
    (hprofile : ∀ scale : Nat, d ≤ scale →
      twoThirdsSeparationProfile G scale ≤ coefficient * scale) :
    bkSumPreservingRecurrence G d parent ≤
      coefficient * parent * bkTwoThirdsDepth d parent := by
  induction parent using Nat.strong_induction_on with
  | h parent ih =>
      by_cases hterminal : bkScaleTerminal d parent
      · rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d parent hterminal]
        exact Nat.zero_le _
      · have hparentPositive : 0 < parent := by
          by_contra hpositive
          apply hterminal
          exact Or.inl (Nat.eq_zero_of_not_pos hpositive)
        have hdparent : d ≤ parent := by
          by_contra hd
          exact hterminal (Or.inr (by omega))
        have hchildScaleLt : bkTwoThirdsChildScale parent < parent :=
          bkTwoThirdsChildScale_lt parent hparentPositive
        have hsup :
            (bkAdmissibleChildPairs parent).sup (fun children =>
                if hchildren : children ∈ bkAdmissibleChildPairs parent then
                  bkSumPreservingRecurrence G d children.1 +
                    bkSumPreservingRecurrence G d children.2
                else 0) ≤
              coefficient * parent * bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
          apply Finset.sup_le
          intro children hchildren
          simp only [dif_pos hchildren]
          have hadmissible := (mem_bkAdmissibleChildPairs_iff).1 hchildren
          have hleftBound := ih children.1 hadmissible.1
          have hrightBound := ih children.2 hadmissible.2.1
          have hleftScale : children.1 ≤ bkTwoThirdsChildScale parent :=
            card_le_bkTwoThirdsChildScale hadmissible.2.2.2.1
          have hrightScale : children.2 ≤ bkTwoThirdsChildScale parent :=
            card_le_bkTwoThirdsChildScale hadmissible.2.2.2.2
          have hleftDepth := bkTwoThirdsDepth_mono d hleftScale
          have hrightDepth := bkTwoThirdsDepth_mono d hrightScale
          calc
            bkSumPreservingRecurrence G d children.1 +
                bkSumPreservingRecurrence G d children.2
                ≤ coefficient * children.1 * bkTwoThirdsDepth d children.1 +
                    coefficient * children.2 * bkTwoThirdsDepth d children.2 :=
              Nat.add_le_add hleftBound hrightBound
            _ ≤ coefficient * children.1 * bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) +
                  coefficient * children.2 * bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
              exact Nat.add_le_add
                (Nat.mul_le_mul_left (coefficient * children.1) hleftDepth)
                (Nat.mul_le_mul_left (coefficient * children.2) hrightDepth)
            _ = coefficient * (children.1 + children.2) *
                  bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
              ring
            _ ≤ coefficient * parent *
                  bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
              exact Nat.mul_le_mul_right _
                (Nat.mul_le_mul_left coefficient hadmissible.2.2.1)
        rw [bkSumPreservingRecurrence_eq_profile_add G d parent hterminal]
        rw [bkTwoThirdsDepth_eq_succ d parent hterminal]
        calc
          twoThirdsSeparationProfile G parent +
              (bkAdmissibleChildPairs parent).sup (fun children =>
                if hchildren : children ∈ bkAdmissibleChildPairs parent then
                  bkSumPreservingRecurrence G d children.1 +
                    bkSumPreservingRecurrence G d children.2
                else 0)
              ≤ coefficient * parent +
                  coefficient * parent *
                    bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) :=
            Nat.add_le_add (hprofile parent hdparent) hsup
          _ = coefficient * parent *
                (1 + bkTwoThirdsDepth d (bkTwoThirdsChildScale parent)) := by
            ring

/-- Every measured graph profile gives the universal finite logarithmic-depth bound. -/
theorem bkSumPreservingRecurrence_le_scale_mul_depth
    (G : ConnectivityGraph ι) (d parent : Nat) :
    bkSumPreservingRecurrence G d parent ≤ parent * bkTwoThirdsDepth d parent := by
  simpa using
    bkSumPreservingRecurrence_le_coefficient_mul_scale_mul_depth G d 1 parent
      (fun scale _ => by
        simpa only [Nat.one_mul] using twoThirdsSeparationProfile_le_scale G scale)

/-- The exact two-pass composition has a fully finite second-pass estimate. -/
theorem bkSumPreservingRecurrenceTwice_le_scale_mul_depth
    (G : ConnectivityGraph ι) (d parent : Nat) :
    bkSumPreservingRecurrenceTwice G d parent ≤
      bkSumPreservingRecurrence G d parent *
        bkTwoThirdsDepth d (bkSumPreservingRecurrence G d parent) := by
  exact bkSumPreservingRecurrence_le_scale_mul_depth G d
    (bkSumPreservingRecurrence G d parent)

end QEC.Locality
