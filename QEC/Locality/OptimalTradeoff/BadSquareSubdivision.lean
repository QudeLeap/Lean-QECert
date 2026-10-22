import QEC.Locality.OptimalTradeoff.RecursivePartition
/-!
# Corrected Dai--Li bad-square subdivision

This module owns the project correction to DL24 Lemma `square-3`.  The source
count bound is false; the finite greedy construction below targets the
project-owned `+1` repair.  It combines an executable Nat kernel over ordered
half-open atomic horizontal bands with a terminating support-free real
atomization and an exact actual-counter bridge.
-/

noncomputable section

namespace QEC.Locality

open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

/-- The finite set of vertical coordinates occupied by qubits in one rectangle. -/
def daiLiVerticalQubitSupport
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ) : Finset ℝ :=
  (embedding.qubitsInRectangle lower upper).image fun q => (embedding.point q).2

/-- A stronger finite support set that avoids every qubit of the embedding. -/
def daiLiGlobalVerticalQubitSupport (embedding : UnitSeparatedEmbedding2D ι) : Finset ℝ :=
  Finset.univ.image fun q => (embedding.point q).2

theorem mem_daiLiGlobalVerticalQubitSupport
    (embedding : UnitSeparatedEmbedding2D ι) (q : ι) :
    (embedding.point q).2 ∈ daiLiGlobalVerticalQubitSupport embedding := by
  exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩

/-- A finite set cannot occupy every point of a nonempty real interval. -/
theorem exists_real_in_openInterval_not_mem_finset
    (support : Finset ℝ) {lower upper : ℝ} (hInterval : lower < upper) :
    ∃ cut : ℝ, lower < cut ∧ cut < upper ∧ cut ∉ support := by
  by_contra hExists
  push Not at hExists
  have hSubset : Set.Ioo lower upper ⊆ (support : Set ℝ) := by
    intro cut hCut
    exact hExists cut hCut.1 hCut.2
  exact (Set.Ioo_infinite hInterval) (support.finite_toSet.subset hSubset)

/--
An actual support-free horizontal cut can be selected inside every nonempty
open window.  It avoids every qubit coordinate in the parent rectangle, so
half-open ownership has no ambiguous internal boundary.
-/
theorem exists_supportFreeHorizontalCut
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    {lower upper : ℝ} (hInterval : lower < upper) :
    ∃ cut : ℝ, lower < cut ∧ cut < upper ∧
      ∀ q ∈ embedding.qubitsInRectangle rectangleLower rectangleUpper,
        (embedding.point q).2 ≠ cut := by
  rcases exists_real_in_openInterval_not_mem_finset
      (daiLiVerticalQubitSupport embedding rectangleLower rectangleUpper) hInterval with
    ⟨cut, hLower, hUpper, hCut⟩
  refine ⟨cut, hLower, hUpper, ?_⟩
  intro q hq hqCut
  apply hCut
  exact Finset.mem_image.mpr ⟨q, hq, hqCut⟩

/-- The lower half of a horizontal rectangle uses the half-open ownership `y < cut`. -/
def daiLiBelowHorizontalCut
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) : Finset ι :=
  (embedding.qubitsInRectangle rectangleLower rectangleUpper).filter fun q =>
    (embedding.point q).2 < cut

/-- The upper half owns the cut with `cut <= y`, completing the half-open split. -/
def daiLiAtOrAboveHorizontalCut
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) : Finset ι :=
  (embedding.qubitsInRectangle rectangleLower rectangleUpper).filter fun q =>
    cut ≤ (embedding.point q).2

/-- The two half-open slices are genuinely disjoint. -/
theorem daiLi_halfOpenHorizontalCut_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) :
    Disjoint (daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut)
      (daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut) := by
  apply Finset.disjoint_left.mpr
  intro q hBelow hAbove
  exact (not_lt_of_ge (Finset.mem_filter.mp hAbove).2) (Finset.mem_filter.mp hBelow).2

/-- The half-open slices cover exactly the parent rectangle's finite qubit assignment. -/
theorem daiLi_halfOpenHorizontalCut_union
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) :
    daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut ∪
        daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut =
      embedding.qubitsInRectangle rectangleLower rectangleUpper := by
  ext q
  by_cases hBelow : (embedding.point q).2 < cut
  · simp [daiLiBelowHorizontalCut, daiLiAtOrAboveHorizontalCut, hBelow]
  · have hAbove : cut ≤ (embedding.point q).2 := le_of_not_gt hBelow
    simp [daiLiBelowHorizontalCut, daiLiAtOrAboveHorizontalCut, hBelow, hAbove]

/-- The actual Dai--Li incidence counter is additive across the half-open split. -/
theorem regionInteractionCounter_halfOpenHorizontal_add
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (rectangleLower rectangleUpper : ℝ × ℝ) (cut : ℝ) :
    regionInteractionCounter P embedding threshold
        (daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut) +
      regionInteractionCounter P embedding threshold
        (daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut) =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle rectangleLower rectangleUpper) := by
  unfold regionInteractionCounter
  rw [← Finset.sum_union
    (daiLi_halfOpenHorizontalCut_disjoint embedding rectangleLower rectangleUpper cut),
    daiLi_halfOpenHorizontalCut_union]

/--
At a support-free cut, the new half-open ownership agrees extensionally with
the PR #493 lower/upper API; the difference is only boundary convention.
-/
theorem daiLi_halfOpenCuts_eq_previous_api_of_supportFree
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ)
    (hSupportFree : ∀ q ∈ embedding.qubitsInRectangle rectangleLower rectangleUpper,
      (embedding.point q).2 ≠ cut) :
    daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut =
        lowerHorizontalRectangleQubits embedding rectangleLower rectangleUpper cut ∧
      daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut =
        upperHorizontalRectangleQubits embedding rectangleLower rectangleUpper cut := by
  constructor <;> ext q
  · by_cases hq : q ∈ embedding.qubitsInRectangle rectangleLower rectangleUpper
    · have hqNe := hSupportFree q hq
      by_cases hBelow : (embedding.point q).2 < cut
      · have hLower : (embedding.point q).2 ≤ cut := le_of_lt hBelow
        simp [daiLiBelowHorizontalCut, lowerHorizontalRectangleQubits, hq, hBelow, hLower]
      · have hAbove : cut < (embedding.point q).2 := by
          rcases lt_or_eq_of_le (le_of_not_gt hBelow) with hlt | heq
          · exact hlt
          · exact False.elim (hqNe heq.symm)
        have hNotLower : ¬ (embedding.point q).2 ≤ cut := not_le_of_gt hAbove
        simp [daiLiBelowHorizontalCut, lowerHorizontalRectangleQubits,
          hq, hBelow, hNotLower]
    · simp [daiLiBelowHorizontalCut, lowerHorizontalRectangleQubits, hq]
  · by_cases hq : q ∈ embedding.qubitsInRectangle rectangleLower rectangleUpper
    · have hqNe := hSupportFree q hq
      by_cases hBelow : (embedding.point q).2 < cut
      · have hNotAbove : ¬ cut ≤ (embedding.point q).2 := not_le_of_gt hBelow
        have hNotUpper : ¬ cut < (embedding.point q).2 := not_lt_of_ge (le_of_lt hBelow)
        simp [daiLiAtOrAboveHorizontalCut, upperHorizontalRectangleQubits,
          hq, hNotAbove, hNotUpper]
      · have hAbove : cut < (embedding.point q).2 := by
          rcases lt_or_eq_of_le (le_of_not_gt hBelow) with hlt | heq
          · exact hlt
          · exact False.elim (hqNe heq.symm)
        have hAtOrAbove : cut ≤ (embedding.point q).2 := le_of_lt hAbove
        simp [daiLiAtOrAboveHorizontalCut, upperHorizontalRectangleQubits,
          hq, hAbove, hAtOrAbove]
    · simp [daiLiAtOrAboveHorizontalCut, upperHorizontalRectangleQubits, hq]

/-- One physical atomic rectangle has the required Dai--Li short-height range. -/
def DaiLiShortHeight (ell lower upper : ℝ) : Prop :=
  5 * ell ≤ upper - lower ∧ upper - lower ≤ 10 * ell

/--
An ordered support-free horizontal atomization of a real interval. The
constructors encode the exact geometric cover: adjacent atoms share their
endpoint, every internal endpoint avoids the finite support, and every atom
has physical height in `[5 * ell, 10 * ell]`.
-/
inductive DaiLiHorizontalAtomization (support : Finset ℝ) (ell : ℝ) :
    ℝ → ℝ → List (ℝ × ℝ) → Prop
  | single {lower upper : ℝ}
      (hHeight : DaiLiShortHeight ell lower upper) :
      DaiLiHorizontalAtomization support ell lower upper [(lower, upper)]
  | cons {lower cut upper : ℝ} {tail : List (ℝ × ℝ)}
      (hCutFree : cut ∉ support)
      (hHeight : DaiLiShortHeight ell lower cut)
      (hTail : DaiLiHorizontalAtomization support ell cut upper tail) :
      DaiLiHorizontalAtomization support ell lower upper ((lower, cut) :: tail)

/-- Any interval between five and twenty `ell` has a finite support-free short atomization. -/
theorem exists_daiLiHorizontalAtomization_base
    (support : Finset ℝ) (ell lower upper : ℝ) (hEll : 0 < ell)
    (hMin : 5 * ell ≤ upper - lower) (hMax : upper - lower ≤ 20 * ell) :
    ∃ atoms, DaiLiHorizontalAtomization support ell lower upper atoms := by
  by_cases hOne : upper - lower ≤ 10 * ell
  · exact ⟨[(lower, upper)], DaiLiHorizontalAtomization.single ⟨hMin, hOne⟩⟩
  by_cases hTwo : upper - lower < 20 * ell
  · let left := max (lower + 5 * ell) (upper - 10 * ell)
    let right := min (lower + 10 * ell) (upper - 5 * ell)
    let midpoint := lower + (upper - lower) / 2
    have hLeftMid : left < midpoint := by
      apply (max_lt_iff).2
      constructor <;> dsimp [left, midpoint] <;> linarith
    have hMidRight : midpoint < right := by
      apply (lt_min_iff).2
      constructor <;> dsimp [right, midpoint] <;> linarith
    rcases exists_real_in_openInterval_not_mem_finset support (hLeftMid.trans hMidRight) with
      ⟨cut, hLeftCut, hCutRight, hCutFree⟩
    refine ⟨[(lower, cut), (cut, upper)],
      DaiLiHorizontalAtomization.cons hCutFree ?_ (DaiLiHorizontalAtomization.single ?_)⟩
    · constructor
      · have hLower : lower + 5 * ell ≤ left := le_max_left _ _
        linarith
      · have hUpper : right ≤ lower + 10 * ell := min_le_left _ _
        linarith
    · constructor
      · have hLower : right ≤ upper - 5 * ell := min_le_right _ _
        linarith
      · have hUpper : upper - 10 * ell ≤ left := le_max_right _ _
        linarith
  · have hExact : upper - lower = 20 * ell := le_antisymm hMax (le_of_not_gt hTwo)
    rcases exists_real_in_openInterval_not_mem_finset support
        (lower := lower + 5 * ell) (upper := lower + 6 * ell) (by linarith [hEll]) with
      ⟨firstCut, hFirstLower, hFirstUpper, hFirstFree⟩
    rcases exists_real_in_openInterval_not_mem_finset support
        (lower := lower + 12 * ell) (upper := lower + 13 * ell) (by linarith [hEll]) with
      ⟨secondCut, hSecondLower, hSecondUpper, hSecondFree⟩
    refine ⟨[(lower, firstCut), (firstCut, secondCut), (secondCut, upper)],
      DaiLiHorizontalAtomization.cons hFirstFree ?_
        (DaiLiHorizontalAtomization.cons hSecondFree ?_
          (DaiLiHorizontalAtomization.single ?_))⟩
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith

/--
The finite atomization is well-founded on an explicit Nat height budget.  A
non-base step removes a support-free band of height strictly between
`5 * ell` and `10 * ell`, so the remaining budget decreases by one.
-/
theorem exists_daiLiHorizontalAtomization_of_budget
    (support : Finset ℝ) (ell : ℝ) (hEll : 0 < ell) (budget : Nat)
    (lower upper : ℝ) (hMin : 5 * ell ≤ upper - lower)
    (hMax : upper - lower ≤ 20 * ell + (budget : ℝ) * (5 * ell)) :
    ∃ atoms, DaiLiHorizontalAtomization support ell lower upper atoms := by
  induction budget generalizing lower upper with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero] at hMax
      exact exists_daiLiHorizontalAtomization_base support ell lower upper hEll hMin hMax
  | succ budget ih =>
      by_cases hBase : upper - lower ≤ 20 * ell
      · exact exists_daiLiHorizontalAtomization_base support ell lower upper hEll hMin hBase
      · have hWindow : lower + 5 * ell < lower + 10 * ell := by linarith [hEll]
        rcases exists_real_in_openInterval_not_mem_finset support hWindow with
          ⟨cut, hLowerCut, hCutUpper, hCutFree⟩
        have hFirst : DaiLiShortHeight ell lower cut := by
          constructor <;> linarith
        have hTailMin : 5 * ell ≤ upper - cut := by
          have hLarge : 20 * ell < upper - lower := lt_of_not_ge hBase
          linarith
        have hTailMax : upper - cut ≤ 20 * ell + (budget : ℝ) * (5 * ell) := by
          simp only [Nat.cast_succ] at hMax
          linarith
        rcases ih cut upper hTailMin hTailMax with ⟨tail, hTail⟩
        exact ⟨(lower, cut) :: tail,
          DaiLiHorizontalAtomization.cons hCutFree hFirst hTail⟩

/--
Every real interval of height at least `5 * ell` has a finite ordered
support-free atomization.  The Archimedean budget is explicit, so this is a
terminating construction rather than real-height induction.
-/
theorem exists_daiLiHorizontalAtomization
    (support : Finset ℝ) (ell lower upper : ℝ) (hEll : 0 < ell)
    (hMin : 5 * ell ≤ upper - lower) :
    ∃ atoms, DaiLiHorizontalAtomization support ell lower upper atoms := by
  have hScale : 0 < 5 * ell := by linarith
  obtain ⟨budget, hBudget⟩ := exists_nat_gt ((upper - lower) / (5 * ell))
  have hBound : upper - lower ≤ 20 * ell + (budget : ℝ) * (5 * ell) := by
    have hStrict : upper - lower < (budget : ℝ) * (5 * ell) :=
      (div_lt_iff₀ hScale).mp hBudget
    linarith
  exact exists_daiLiHorizontalAtomization_of_budget support ell hEll budget lower upper hMin hBound

/-- The support-free atomization applies directly to the vertical span of an actual rectangle. -/
theorem exists_daiLiRectangleAtomization
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (ell : ℝ) (hEll : 0 < ell)
    (hHeight : 5 * ell ≤ rectangleUpper.2 - rectangleLower.2) :
    ∃ atoms,
      DaiLiHorizontalAtomization
        (daiLiVerticalQubitSupport embedding rectangleLower rectangleUpper)
        ell rectangleLower.2 rectangleUpper.2 atoms := by
  exact exists_daiLiHorizontalAtomization
    (daiLiVerticalQubitSupport embedding rectangleLower rectangleUpper)
    ell rectangleLower.2 rectangleUpper.2 hEll hHeight

/-- The rectangle atomization may use the stronger all-qubit support-free convention. -/
theorem exists_daiLiRectangleAtomization_globalSupport
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (ell : ℝ) (hEll : 0 < ell)
    (hHeight : 5 * ell ≤ rectangleUpper.2 - rectangleLower.2) :
    ∃ atoms,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
        ell rectangleLower.2 rectangleUpper.2 atoms := by
  exact exists_daiLiHorizontalAtomization
    (daiLiGlobalVerticalQubitSupport embedding)
    ell rectangleLower.2 rectangleUpper.2 hEll hHeight

/-- Every atomization has a strictly positive total height. -/
theorem DaiLiHorizontalAtomization.lower_lt_upper
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) : lower < upper := by
  induction hAtoms with
  | single hHeight =>
      rcases hHeight with ⟨hLower, _⟩
      linarith
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      rcases hHeight with ⟨hLower, _⟩
      exact (by linarith : lower < cut).trans ih

/-- Consecutive horizontal atoms meet exactly at their common cut. -/
def DaiLiAtomAdjacent (first second : ℝ × ℝ) : Prop :=
  first.2 = second.1

/-- Every atom emitted by an atomization has the required short-height bounds. -/
theorem DaiLiHorizontalAtomization.atom_short
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (atom : ℝ × ℝ) (hAtom : atom ∈ atoms) :
    DaiLiShortHeight ell atom.1 atom.2 := by
  induction hAtoms generalizing atom with
  | single hHeight =>
      simp only [List.mem_singleton] at hAtom
      subst atom
      exact hHeight
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      simp only [List.mem_cons] at hAtom
      rcases hAtom with rfl | hAtom
      · exact hHeight
      · exact ih atom hAtom

/-- An atomization always starts at its declared lower endpoint. -/
theorem DaiLiHorizontalAtomization.starts_at
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms) :
    ∃ firstUpper tail, atoms = (lower, firstUpper) :: tail := by
  cases hAtoms with
  | single hHeight => exact ⟨upper, [], rfl⟩
  | cons hCutFree hHeight hTail => exact ⟨_, _, rfl⟩

/-- The source order of an atomization is a chain of exact common endpoints. -/
theorem DaiLiHorizontalAtomization.atom_chain
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms) :
    atoms.IsChain DaiLiAtomAdjacent := by
  induction hAtoms with
  | single hHeight => exact List.isChain_singleton _
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      rcases hTail.starts_at with ⟨firstUpper, rest, hStarts⟩
      refine ih.cons_of_ne_nil ?_ ?_
      · simpa [hStarts]
      · simp [DaiLiAtomAdjacent, hStarts]

/-- The actual qubits in one geometric atom. -/
def daiLiAtomQubits
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atom : ℝ × ℝ) : Finset ι :=
  embedding.qubitsInRectangle (left, atom.1) (right, atom.2)

/-- A globally support-free lower atom is exactly the half-open lower slice. -/
theorem daiLiAtomQubits_lower_eq_halfOpen
    (embedding : UnitSeparatedEmbedding2D ι) (left right lower cut upper : ℝ)
    (hLowerCut : lower < cut) (hCutUpper : cut < upper)
    (hCutFree : cut ∉ daiLiGlobalVerticalQubitSupport embedding) :
    daiLiAtomQubits embedding left right (lower, cut) =
      daiLiBelowHorizontalCut embedding (left, lower) (right, upper) cut := by
  ext q
  have hNoBoundary : (embedding.point q).2 ≠ cut := by
    intro hq
    apply hCutFree
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩
  constructor
  · intro hAtom
    have hAtom' : q ∈ embedding.qubitsInRectangle (left, lower) (right, cut) := by
      simpa only [daiLiAtomQubits] using hAtom
    have hAtomRect := (UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
      embedding (left, lower) (right, cut) q).1 hAtom'
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨hAtomRect.1, ⟨hAtomRect.2.1, hAtomRect.2.2.trans hCutUpper.le⟩⟩
    · exact lt_of_le_of_ne hAtomRect.2.2 hNoBoundary
  · intro hBelow
    rcases Finset.mem_filter.mp hBelow with ⟨hParent, hBelowCut⟩
    have hRect := (UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
      embedding (left, lower) (right, upper) q).1 hParent
    have hAtom' : q ∈ embedding.qubitsInRectangle (left, lower) (right, cut) := by
      rw [UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨hRect.1, ⟨hRect.2.1, hBelowCut.le⟩⟩
    simpa only [daiLiAtomQubits] using hAtom'

/-- The upper child rectangle is the complementary half-open slice. -/
theorem daiLiAtomQubits_upper_eq_halfOpen
    (embedding : UnitSeparatedEmbedding2D ι) (left right lower cut upper : ℝ)
    (hLowerCut : lower < cut) (hCutUpper : cut < upper) :
    daiLiAtomQubits embedding left right (cut, upper) =
      daiLiAtOrAboveHorizontalCut embedding (left, lower) (right, upper) cut := by
  ext q
  constructor
  · intro hAtom
    have hAtom' : q ∈ embedding.qubitsInRectangle (left, cut) (right, upper) := by
      simpa only [daiLiAtomQubits] using hAtom
    have hAtomRect := (UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
      embedding (left, cut) (right, upper) q).1 hAtom'
    apply Finset.mem_filter.mpr
    refine ⟨?_, hAtomRect.2.1⟩
    rw [UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨hAtomRect.1, ⟨hLowerCut.le.trans hAtomRect.2.1, hAtomRect.2.2⟩⟩
  · intro hAbove
    rcases Finset.mem_filter.mp hAbove with ⟨hParent, hAboveCut⟩
    have hRect := (UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
      embedding (left, lower) (right, upper) q).1 hParent
    have hAtom' : q ∈ embedding.qubitsInRectangle (left, cut) (right, upper) := by
      rw [UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨hRect.1, ⟨hAboveCut, hRect.2.2⟩⟩
    simpa only [daiLiAtomQubits] using hAtom'

/-- The actual interaction counters carried by an ordered list of geometric atoms. -/
def daiLiAtomCounters
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (atoms : List (ℝ × ℝ)) : List Nat :=
  atoms.map fun atom =>
    regionInteractionCounter P embedding threshold (daiLiAtomQubits embedding left right atom)

/--
The constructed geometric atomization preserves the actual Dai--Li counter
exactly.  This is the bridge from physical rectangles to the finite Nat greedy
kernel.
-/
theorem DaiLiHorizontalAtomization.atomCounters_sum
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hEll : 0 < ell) :
    (daiLiAtomCounters P embedding threshold left right atoms).sum =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle (left, lower) (right, upper)) := by
  induction hAtoms generalizing left right with
  | single hHeight =>
      simp [daiLiAtomCounters, daiLiAtomQubits]
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      have hLowerCut : lower < cut := by
        rcases hHeight with ⟨hMin, _⟩
        linarith
      have hCutUpper : cut < upper := DaiLiHorizontalAtomization.lower_lt_upper hTail hEll
      have hHead : daiLiAtomQubits embedding left right (lower, cut) =
          daiLiBelowHorizontalCut embedding (left, lower) (right, upper) cut :=
        daiLiAtomQubits_lower_eq_halfOpen embedding left right lower cut upper
          hLowerCut hCutUpper hCutFree
      have hTailQubits : daiLiAtomQubits embedding left right (cut, upper) =
          daiLiAtOrAboveHorizontalCut embedding (left, lower) (right, upper) cut :=
        daiLiAtomQubits_upper_eq_halfOpen embedding left right lower cut upper
          hLowerCut hCutUpper
      have hTailRectangle : embedding.qubitsInRectangle (left, cut) (right, upper) =
          daiLiAtOrAboveHorizontalCut embedding (left, lower) (right, upper) cut := by
        simpa only [daiLiAtomQubits] using hTailQubits
      simp only [daiLiAtomCounters, List.map_cons, List.sum_cons]
      change regionInteractionCounter P embedding threshold
          (daiLiAtomQubits embedding left right (lower, cut)) +
          (daiLiAtomCounters P embedding threshold left right tail).sum = _
      rw [ih left right, hHead, hTailRectangle,
        regionInteractionCounter_halfOpenHorizontal_add]

/-- The finite qubits covered by an ordered list of physical horizontal atoms. -/
def daiLiAtomQubitsCover
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atoms : List (ℝ × ℝ)) : Finset ι :=
  atoms.foldr (fun atom covered => daiLiAtomQubits embedding left right atom ∪ covered) ∅

theorem daiLiAtomQubitsCover_append
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (first second : List (ℝ × ℝ)) :
    daiLiAtomQubitsCover embedding left right (first ++ second) =
      daiLiAtomQubitsCover embedding left right first ∪
        daiLiAtomQubitsCover embedding left right second := by
  induction first with
  | nil => simp [daiLiAtomQubitsCover]
  | cons atom first ih =>
      rw [List.cons_append]
      simp only [daiLiAtomQubitsCover, List.foldr_cons]
      have hFold :
          List.foldr (fun atom covered => daiLiAtomQubits embedding left right atom ∪ covered) ∅
              (first ++ second) =
            List.foldr (fun atom covered => daiLiAtomQubits embedding left right atom ∪ covered) ∅ first ∪
              List.foldr (fun atom covered => daiLiAtomQubits embedding left right atom ∪ covered) ∅ second := by
        simpa [daiLiAtomQubitsCover] using ih
      rw [hFold]
      exact (Finset.union_assoc _ _ _).symm

theorem mem_daiLiAtomQubitsCover
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atoms : List (ℝ × ℝ)) (q : ι) :
    q ∈ daiLiAtomQubitsCover embedding left right atoms ↔
      ∃ atom ∈ atoms, q ∈ daiLiAtomQubits embedding left right atom := by
  induction atoms generalizing q with
  | nil => simp [daiLiAtomQubitsCover]
  | cons atom atoms ih =>
      simp only [daiLiAtomQubitsCover, List.foldr_cons, Finset.mem_union,
        List.mem_cons]
      constructor
      · rintro (hAtom | hTail)
        · exact ⟨atom, Or.inl rfl, hAtom⟩
        · rcases (ih q).1 hTail with ⟨candidate, hCandidate, hq⟩
          exact ⟨candidate, Or.inr hCandidate, hq⟩
      · rintro ⟨candidate, rfl | hCandidate, hq⟩
        · exact Or.inl hq
        · exact Or.inr ((ih q).2 ⟨candidate, hCandidate, hq⟩)

theorem daiLiAtomQubits_subset_cover
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atoms : List (ℝ × ℝ)) (atom : ℝ × ℝ) (hAtom : atom ∈ atoms) :
    daiLiAtomQubits embedding left right atom ⊆
      daiLiAtomQubitsCover embedding left right atoms := by
  intro q hq
  exact (mem_daiLiAtomQubitsCover embedding left right atoms q).2 ⟨atom, hAtom, hq⟩

/-- An actual global-support-free atomization covers exactly its parent rectangle. -/
theorem DaiLiHorizontalAtomization.atomQubitsCover
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hEll : 0 < ell) :
    daiLiAtomQubitsCover embedding left right atoms =
      embedding.qubitsInRectangle (left, lower) (right, upper) := by
  induction hAtoms generalizing left right with
  | single hHeight =>
      simp [daiLiAtomQubitsCover, daiLiAtomQubits]
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      have hLowerCut : lower < cut := by
        rcases hHeight with ⟨hMin, _⟩
        linarith
      have hCutUpper : cut < upper := hTail.lower_lt_upper hEll
      have hHead : daiLiAtomQubits embedding left right (lower, cut) =
          daiLiBelowHorizontalCut embedding (left, lower) (right, upper) cut :=
        daiLiAtomQubits_lower_eq_halfOpen embedding left right lower cut upper
          hLowerCut hCutUpper hCutFree
      have hTailQubits : daiLiAtomQubits embedding left right (cut, upper) =
          daiLiAtOrAboveHorizontalCut embedding (left, lower) (right, upper) cut :=
        daiLiAtomQubits_upper_eq_halfOpen embedding left right lower cut upper
          hLowerCut hCutUpper
      have hTailRectangle : embedding.qubitsInRectangle (left, cut) (right, upper) =
          daiLiAtOrAboveHorizontalCut embedding (left, lower) (right, upper) cut := by
        simpa only [daiLiAtomQubits] using hTailQubits
      change daiLiAtomQubits embedding left right (lower, cut) ∪
          daiLiAtomQubitsCover embedding left right tail = _
      rw [ih left right, hHead, hTailRectangle,
        daiLi_halfOpenHorizontalCut_union]

/-- Distinct support-free atoms assign disjoint finite qubit sets. -/
theorem DaiLiHorizontalAtomization.atomQubits_pairwise
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hEll : 0 < ell) :
    (atoms.map (daiLiAtomQubits embedding left right)).Pairwise Disjoint := by
  induction hAtoms generalizing left right with
  | single hHeight => simp
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      have hLowerCut : lower < cut := by
        rcases hHeight with ⟨hMin, _⟩
        linarith
      have hCutUpper : cut < upper := hTail.lower_lt_upper hEll
      have hHead : daiLiAtomQubits embedding left right (lower, cut) =
          daiLiBelowHorizontalCut embedding (left, lower) (right, upper) cut :=
        daiLiAtomQubits_lower_eq_halfOpen embedding left right lower cut upper
          hLowerCut hCutUpper hCutFree
      have hTailQubits : daiLiAtomQubits embedding left right (cut, upper) =
          daiLiAtOrAboveHorizontalCut embedding (left, lower) (right, upper) cut :=
        daiLiAtomQubits_upper_eq_halfOpen embedding left right lower cut upper
          hLowerCut hCutUpper
      have hTailRectangle : embedding.qubitsInRectangle (left, cut) (right, upper) =
          daiLiAtOrAboveHorizontalCut embedding (left, lower) (right, upper) cut := by
        simpa only [daiLiAtomQubits] using hTailQubits
      rw [List.map_cons, List.pairwise_cons]
      constructor
      · intro candidate hCandidate
        rcases List.mem_map.mp hCandidate with ⟨atom, hAtom, rfl⟩
        apply Finset.disjoint_left.mpr
        intro q hHeadQ hAtomQ
        have hTailQ : q ∈ daiLiAtomQubitsCover embedding left right tail :=
          daiLiAtomQubits_subset_cover embedding left right tail atom hAtom hAtomQ
        rw [hTail.atomQubitsCover embedding left right hEll, hTailRectangle] at hTailQ
        rw [hHead] at hHeadQ
        exact (Finset.disjoint_left.mp
          (daiLi_halfOpenHorizontalCut_disjoint embedding (left, lower) (right, upper) cut))
          hHeadQ hTailQ
      · exact ih left right

/-- A finite atomic horizontal band contributes this many long incidences. -/
abbrev DaiLiAtomicCounter := Nat

/-- The counter carried by an ordered sequence of atomic horizontal bands. -/
def daiLiAtomicMass (bands : List DaiLiAtomicCounter) : Nat :=
  bands.sum

/-- A band is low-counter at the Dai--Li threshold `d`. -/
def DaiLiLowCounter (d : Nat) (bands : List DaiLiAtomicCounter) : Prop :=
  10 * daiLiAtomicMass bands ≤ d

/-- A short rectangle is one atom, whose physical height is at most `10 * ell`. -/
def DaiLiShortAtomicBand (bands : List DaiLiAtomicCounter) : Prop :=
  bands.length ≤ 1

/-- The counter carried by a finite ordered family of atomic bands. -/
def daiLiAtomicPiecesMass (pieces : List (List DaiLiAtomicCounter)) : Nat :=
  (pieces.map daiLiAtomicMass).sum

/-- A produced piece has positive height and is low-counter or short. -/
def DaiLiAtomicPieceAdmissible (d : Nat) (piece : List DaiLiAtomicCounter) : Prop :=
  piece ≠ [] ∧ (DaiLiLowCounter d piece ∨ DaiLiShortAtomicBand piece)

theorem daiLiAtomicMass_append (left right : List DaiLiAtomicCounter) :
    daiLiAtomicMass (left ++ right) = daiLiAtomicMass left + daiLiAtomicMass right := by
  simp [daiLiAtomicMass]

theorem daiLiAtomicPiecesMass_cons
    (piece : List DaiLiAtomicCounter) (pieces : List (List DaiLiAtomicCounter)) :
    daiLiAtomicPiecesMass (piece :: pieces) =
      daiLiAtomicMass piece + daiLiAtomicPiecesMass pieces := by
  simp [daiLiAtomicPiecesMass]

theorem daiLiAtomicPiecesMass_reverse (pieces : List (List DaiLiAtomicCounter)) :
    daiLiAtomicPiecesMass pieces.reverse = daiLiAtomicPiecesMass pieces := by
  simp [daiLiAtomicPiecesMass]

theorem daiLiAtomicPiecesMass_eq_flattenMass (pieces : List (List DaiLiAtomicCounter)) :
    daiLiAtomicPiecesMass pieces = daiLiAtomicMass pieces.flatten := by
  induction pieces with
  | nil => simp [daiLiAtomicPiecesMass, daiLiAtomicMass]
  | cons piece pieces ih =>
      change (List.map List.sum (piece :: pieces)).sum =
        (piece :: pieces).flatten.sum
      simp only [List.map, List.sum_cons, List.flatten_cons]
      have hTail : (List.map List.sum pieces).sum = pieces.flatten.sum := by
        simpa [daiLiAtomicPiecesMass, daiLiAtomicMass] using ih
      rw [hTail, List.sum_append]

/-- The greedy scan state: a low pending prefix and already emitted pieces. -/
def daiLiGreedyScan (d : Nat) : List DaiLiAtomicCounter →
    List DaiLiAtomicCounter → List (List DaiLiAtomicCounter) →
      List (List DaiLiAtomicCounter)
  | [], pending, emitted =>
      if pending = [] then emitted.reverse else (pending :: emitted).reverse
  | a :: rest, pending, emitted =>
      if hLow : 10 * (daiLiAtomicMass pending + a) ≤ d then
        daiLiGreedyScan d rest (pending ++ [a]) emitted
      else if hPending : pending = [] then
        daiLiGreedyScan d rest [] ([a] :: emitted)
      else
        daiLiGreedyScan d rest [] ([a] :: pending :: emitted)

/-- The explicit corrected greedy subdivision of an atomic horizontal tiling. -/
def daiLiGreedyAtomicSubdivision (d : Nat) (bands : List DaiLiAtomicCounter) :
    List (List DaiLiAtomicCounter) :=
  daiLiGreedyScan d bands [] []

/-- The greedy scan preserves the finite half-open atom order exactly. -/
theorem daiLiGreedyScan_join (d : Nat) :
    ∀ (remaining pending : List DaiLiAtomicCounter)
      (emitted : List (List DaiLiAtomicCounter)),
      (daiLiGreedyScan d remaining pending emitted).flatten =
        emitted.reverse.flatten ++ pending ++ remaining := by
  intro remaining
  induction remaining with
  | nil =>
      intro pending emitted
      by_cases hPending : pending = []
      · simp [daiLiGreedyScan, hPending]
      · simp [daiLiGreedyScan, hPending, List.append_assoc]
  | cons a remaining ih =>
      intro pending emitted
      by_cases hLow : 10 * (daiLiAtomicMass pending + a) ≤ d
      · simpa [daiLiGreedyScan, hLow, List.append_assoc] using
          ih (pending ++ [a]) emitted
      · by_cases hPending : pending = []
        · subst pending
          simpa [daiLiGreedyScan, hLow, List.append_assoc] using
            ih [] ([a] :: emitted)
        · simpa [daiLiGreedyScan, hLow, hPending, List.append_assoc] using
            ih [] ([a] :: pending :: emitted)

/-- The emitted family has no empty pieces and every piece is low-counter or short. -/
theorem daiLiGreedyScan_admissible (d : Nat) :
    ∀ (remaining pending : List DaiLiAtomicCounter)
      (emitted : List (List DaiLiAtomicCounter)),
      (pending = [] ∨ DaiLiLowCounter d pending) →
      (∀ piece ∈ emitted, DaiLiAtomicPieceAdmissible d piece) →
      ∀ piece ∈ daiLiGreedyScan d remaining pending emitted,
        DaiLiAtomicPieceAdmissible d piece := by
  intro remaining
  induction remaining with
  | nil =>
      intro pending emitted hPending hEmitted piece hPiece
      by_cases hEmpty : pending = []
      · change piece ∈ (if pending = [] then emitted.reverse else
            (pending :: emitted).reverse) at hPiece
        rw [if_pos hEmpty] at hPiece
        exact hEmitted piece (List.mem_reverse.mp hPiece)
      · have hPendingAdmissible : DaiLiAtomicPieceAdmissible d pending := by
          rcases hPending with h | h
          · exact False.elim (hEmpty h)
          · exact ⟨hEmpty, Or.inl h⟩
        change piece ∈ (if pending = [] then emitted.reverse else
          (pending :: emitted).reverse) at hPiece
        rw [if_neg hEmpty] at hPiece
        rw [List.mem_reverse] at hPiece
        simp only [List.mem_cons] at hPiece
        rcases hPiece with hPiece | hPiece
        · subst piece
          exact hPendingAdmissible
        · exact hEmitted piece hPiece
  | cons a remaining ih =>
      intro pending emitted hPending hEmitted piece hPiece
      by_cases hLow : 10 * (daiLiAtomicMass pending + a) ≤ d
      · apply ih (pending ++ [a]) emitted
        · right
          simp only [DaiLiLowCounter, daiLiAtomicMass_append]
          exact hLow
        · exact hEmitted
        · simpa [daiLiGreedyScan, hLow] using hPiece
      · by_cases hEmpty : pending = []
        · subst pending
          apply ih [] ([a] :: emitted)
          · exact Or.inl rfl
          · intro candidate hCandidate
            simp only [List.mem_cons] at hCandidate
            rcases hCandidate with rfl | hCandidate
            · exact ⟨by simp, Or.inr (by simp [DaiLiShortAtomicBand])⟩
            · exact hEmitted candidate hCandidate
          · simpa [daiLiGreedyScan, hLow] using hPiece
        · apply ih [] ([a] :: pending :: emitted)
          · exact Or.inl rfl
          · intro candidate hCandidate
            simp only [List.mem_cons] at hCandidate
            rcases hCandidate with rfl | hCandidate
            · exact ⟨by simp, Or.inr (by simp [DaiLiShortAtomicBand])⟩
            · rcases hCandidate with rfl | hCandidate
              · rcases hPending with h | h
                · exact False.elim (hEmpty h)
                · exact ⟨hEmpty, Or.inl h⟩
              · exact hEmitted candidate hCandidate
          · simpa [daiLiGreedyScan, hLow, hEmpty] using hPiece

/--
Every threshold crossing emits at most two pieces and pays for them with the
counter in the just-completed prefix.  A final pending low piece accounts for
the one additive `d` in the corrected bound.
-/
theorem daiLiGreedyScan_count (d : Nat) :
    ∀ (remaining pending : List DaiLiAtomicCounter)
      (emitted : List (List DaiLiAtomicCounter)),
      emitted.length * d ≤ 20 * daiLiAtomicPiecesMass emitted →
      (daiLiGreedyScan d remaining pending emitted).length * d ≤
        20 * (daiLiAtomicPiecesMass emitted + daiLiAtomicMass pending +
          daiLiAtomicMass remaining) + d := by
  intro remaining
  induction remaining with
  | nil =>
      intro pending emitted hEmitted
      by_cases hPending : pending = []
      · have hBound : emitted.length * d ≤ 20 * daiLiAtomicPiecesMass emitted + d := by
          omega
        simpa [daiLiGreedyScan, hPending, daiLiAtomicMass] using hBound
      · have hBound : (emitted.length + 1) * d ≤
            20 * (daiLiAtomicPiecesMass emitted + daiLiAtomicMass pending) + d := by
          rw [Nat.add_mul]
          omega
        simpa [daiLiGreedyScan, hPending, daiLiAtomicMass] using hBound
  | cons a remaining ih =>
      intro pending emitted hEmitted
      by_cases hLow : 10 * (daiLiAtomicMass pending + a) ≤ d
      · rw [daiLiGreedyScan, dif_pos hLow]
        simpa [daiLiAtomicMass_append, daiLiAtomicMass, Nat.add_assoc] using
          ih (pending ++ [a]) emitted hEmitted
      · by_cases hPending : pending = []
        · subst pending
          have hHigh : d < 10 * a := by
            have := Nat.lt_of_not_ge hLow
            simpa [daiLiAtomicMass] using this
          have hNew : ([a] :: emitted).length * d ≤
              20 * daiLiAtomicPiecesMass ([a] :: emitted) := by
            rw [List.length_cons, Nat.add_mul, daiLiAtomicPiecesMass_cons]
            simp [daiLiAtomicMass]
            omega
          rw [daiLiGreedyScan, dif_neg hLow, dif_pos rfl]
          simpa [daiLiAtomicPiecesMass_cons, daiLiAtomicMass,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih [] ([a] :: emitted) hNew
        · have hNew : ([a] :: pending :: emitted).length * d ≤
              20 * daiLiAtomicPiecesMass ([a] :: pending :: emitted) := by
            rw [List.length_cons, List.length_cons, Nat.add_mul, Nat.add_mul,
              daiLiAtomicPiecesMass_cons, daiLiAtomicPiecesMass_cons]
            have hHigh : d < 10 * (daiLiAtomicMass pending + a) :=
              Nat.lt_of_not_ge hLow
            simp [daiLiAtomicMass] at hHigh ⊢
            omega
          rw [daiLiGreedyScan, dif_neg hLow, dif_neg hPending]
          simpa [daiLiAtomicPiecesMass_cons, daiLiAtomicMass,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih [] ([a] :: pending :: emitted) hNew

/-- The concrete greedy subdivision covers its atoms in their original order. -/
theorem daiLiGreedyAtomicSubdivision_join (d : Nat) (bands : List DaiLiAtomicCounter) :
    (daiLiGreedyAtomicSubdivision d bands).flatten = bands := by
  simpa [daiLiGreedyAtomicSubdivision] using daiLiGreedyScan_join d bands [] []

/-- Every concrete greedy piece is a nonempty low-counter or short atomic band. -/
theorem daiLiGreedyAtomicSubdivision_admissible (d : Nat)
    (bands : List DaiLiAtomicCounter) (piece : List DaiLiAtomicCounter)
    (hPiece : piece ∈ daiLiGreedyAtomicSubdivision d bands) :
    DaiLiAtomicPieceAdmissible d piece := by
  exact daiLiGreedyScan_admissible d bands [] [] (Or.inl rfl) (by simp) piece hPiece

/-- The corrected single-square Nat count: `m * d <= 20 * F + d`. -/
theorem daiLiGreedyAtomicSubdivision_count (d : Nat) (bands : List DaiLiAtomicCounter) :
    (daiLiGreedyAtomicSubdivision d bands).length * d ≤
      20 * daiLiAtomicMass bands + d := by
  simpa [daiLiGreedyAtomicSubdivision, daiLiAtomicMass, daiLiAtomicPiecesMass] using
    daiLiGreedyScan_count d bands [] [] (by simp)

/--
The corrected finite-family count.  Each bad square supplies `d <= 10 * F_i`,
which absorbs the one additive `d` from every single-square construction.
-/
theorem daiLiGreedyAtomicSubdivision_family_count
    {α : Type*} [DecidableEq α] (d : Nat)
    (bands : α → List DaiLiAtomicCounter) (squares : Finset α)
    (hBad : ∀ square ∈ squares, d ≤ 10 * daiLiAtomicMass (bands square)) :
    (∑ square ∈ squares, (daiLiGreedyAtomicSubdivision d (bands square)).length) * d ≤
      30 * ∑ square ∈ squares, daiLiAtomicMass (bands square) := by
  have hSingle : ∀ square ∈ squares,
      (daiLiGreedyAtomicSubdivision d (bands square)).length * d ≤
        20 * daiLiAtomicMass (bands square) + d := by
    intro square hSquare
    exact daiLiGreedyAtomicSubdivision_count d (bands square)
  have hSummed :
      ∑ square ∈ squares,
          (daiLiGreedyAtomicSubdivision d (bands square)).length * d ≤
        ∑ square ∈ squares, (20 * daiLiAtomicMass (bands square) + d) := by
    exact Finset.sum_le_sum fun square hSquare => hSingle square hSquare
  have hBadSummed : squares.card * d ≤
      10 * ∑ square ∈ squares, daiLiAtomicMass (bands square) := by
    calc
      squares.card * d = ∑ _square ∈ squares, d := by simp [Finset.sum_const_zero]
      _ ≤ ∑ square ∈ squares, 10 * daiLiAtomicMass (bands square) := by
        exact Finset.sum_le_sum fun square hSquare => hBad square hSquare
      _ = 10 * ∑ square ∈ squares, daiLiAtomicMass (bands square) := by
        rw [Finset.mul_sum]
  calc
    _ = ∑ square ∈ squares,
        (daiLiGreedyAtomicSubdivision d (bands square)).length * d := by
      rw [Finset.sum_mul]
    _ ≤ ∑ square ∈ squares, (20 * daiLiAtomicMass (bands square) + d) := hSummed
    _ = 20 * (∑ square ∈ squares, daiLiAtomicMass (bands square)) + squares.card * d := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const_zero]
    _ ≤ 30 * ∑ square ∈ squares, daiLiAtomicMass (bands square) := by
      omega

/--
The greedy scan with payload keeps the physical atoms that carry each counter.
Its branch condition is the same finite Nat condition as the counter-only
kernel, but it never has to recover atom identities from equal counter values.
-/
def daiLiGreedyScanWith {α : Type*} (weight : α → Nat) (d : Nat) : List α →
    List α → List (List α) → List (List α)
  | [], pending, emitted =>
      if pending = [] then emitted.reverse else (pending :: emitted).reverse
  | a :: rest, pending, emitted =>
      if hLow : 10 * ((pending.map weight).sum + weight a) ≤ d then
        daiLiGreedyScanWith weight d rest (pending ++ [a]) emitted
      else if hPending : pending = [] then
        daiLiGreedyScanWith weight d rest [] ([a] :: emitted)
      else
        daiLiGreedyScanWith weight d rest [] ([a] :: pending :: emitted)

/-- The payload-preserving concrete greedy subdivision. -/
def daiLiGreedySubdivisionWith {α : Type*} (weight : α → Nat) (d : Nat)
    (bands : List α) : List (List α) :=
  daiLiGreedyScanWith weight d bands [] []

/-- The payload scan has exactly the same counter trace as the Nat kernel. -/
theorem daiLiGreedyScanWith_map {α : Type*} (weight : α → Nat) (d : Nat) :
    ∀ (remaining pending : List α) (emitted : List (List α)),
      (daiLiGreedyScanWith weight d remaining pending emitted).map (List.map weight) =
        daiLiGreedyScan d (remaining.map weight) (pending.map weight)
          (emitted.map (List.map weight)) := by
  intro remaining
  induction remaining with
  | nil =>
      intro pending emitted
      by_cases hPending : pending = []
      · subst pending
        simp [daiLiGreedyScanWith, daiLiGreedyScan]
      · simp [daiLiGreedyScanWith, daiLiGreedyScan, hPending]
  | cons a remaining ih =>
      intro pending emitted
      by_cases hLow : 10 * ((pending.map weight).sum + weight a) ≤ d
      · have hNatLow : 10 * (daiLiAtomicMass (pending.map weight) + weight a) ≤ d := by
          simpa [daiLiAtomicMass] using hLow
        rw [daiLiGreedyScanWith, dif_pos hLow]
        simp only [List.map_cons]
        rw [daiLiGreedyScan, dif_pos hNatLow]
        simpa [List.map_append] using ih (pending ++ [a]) emitted
      · have hNatLow : ¬ 10 * (daiLiAtomicMass (pending.map weight) + weight a) ≤ d := by
          simpa [daiLiAtomicMass] using hLow
        by_cases hPending : pending = []
        · subst pending
          rw [daiLiGreedyScanWith, dif_neg hLow, dif_pos rfl]
          simp only [List.map_cons, List.map_nil]
          have hNatSingleLow : ¬ 10 * (daiLiAtomicMass [] + weight a) ≤ d := by
            simpa using hNatLow
          simp only [daiLiGreedyScan, dif_neg hNatSingleLow, dif_pos rfl,
            List.nil_append]
          simpa using ih [] ([a] :: emitted)
        · have hMappedPending : pending.map weight ≠ [] := by
            simpa using hPending
          rw [daiLiGreedyScanWith, dif_neg hLow, dif_neg hPending]
          simp only [List.map_cons]
          rw [daiLiGreedyScan, dif_neg hNatLow, dif_neg hMappedPending]
          simpa using ih [] ([a] :: pending :: emitted)

/-- The payload subdivision maps exactly to the established Nat subdivision. -/
theorem daiLiGreedySubdivisionWith_map {α : Type*} (weight : α → Nat) (d : Nat)
    (bands : List α) :
    (daiLiGreedySubdivisionWith weight d bands).map (List.map weight) =
      daiLiGreedyAtomicSubdivision d (bands.map weight) := by
  simpa [daiLiGreedySubdivisionWith, daiLiGreedyAtomicSubdivision] using
    daiLiGreedyScanWith_map weight d bands [] []

/-- The payload scan preserves the finite atom order exactly. -/
theorem daiLiGreedyScanWith_join {α : Type*} (weight : α → Nat) (d : Nat) :
    ∀ (remaining pending : List α) (emitted : List (List α)),
      (daiLiGreedyScanWith weight d remaining pending emitted).flatten =
        emitted.reverse.flatten ++ pending ++ remaining := by
  intro remaining
  induction remaining with
  | nil =>
      intro pending emitted
      by_cases hPending : pending = []
      · simp [daiLiGreedyScanWith, hPending]
      · simp [daiLiGreedyScanWith, hPending, List.append_assoc]
  | cons a remaining ih =>
      intro pending emitted
      by_cases hLow : 10 * ((pending.map weight).sum + weight a) ≤ d
      · simpa [daiLiGreedyScanWith, hLow, List.append_assoc] using
          ih (pending ++ [a]) emitted
      · by_cases hPending : pending = []
        · subst pending
          have hSingleLow : ¬ 10 * weight a ≤ d := by
            simpa using hLow
          simpa [daiLiGreedyScanWith, hLow, hSingleLow, List.append_assoc] using
            ih [] ([a] :: emitted)
        · simpa [daiLiGreedyScanWith, hLow, hPending, List.append_assoc] using
            ih [] ([a] :: pending :: emitted)

/-- The payload subdivision covers its atoms in their original finite order. -/
theorem daiLiGreedySubdivisionWith_join {α : Type*} (weight : α → Nat) (d : Nat)
    (bands : List α) :
    (daiLiGreedySubdivisionWith weight d bands).flatten = bands := by
  simpa [daiLiGreedySubdivisionWith] using daiLiGreedyScanWith_join weight d bands [] []

/--
The actual greedy subdivision retains the geometric horizontal atoms.  The
counter-only list is used only to choose branches, never to reconstruct a
physical atom from its numerical value.
-/
def daiLiPhysicalGreedySubdivision
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) : List (List (ℝ × ℝ)) :=
  daiLiGreedySubdivisionWith
    (fun atom => regionInteractionCounter P embedding threshold
      (daiLiAtomQubits embedding left right atom)) d atoms

/-- The retained physical groups map exactly to the established Nat groups. -/
theorem daiLiPhysicalGreedySubdivision_counters
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).map
        (daiLiAtomCounters P embedding threshold left right) =
      daiLiGreedyAtomicSubdivision d
        (daiLiAtomCounters P embedding threshold left right atoms) := by
  exact daiLiGreedyScanWith_map
        (fun atom => regionInteractionCounter P embedding threshold
          (daiLiAtomQubits embedding left right atom)) d atoms [] []

/-- The physical greedy groups cover every input atom in original order. -/
theorem daiLiPhysicalGreedySubdivision_join
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).flatten = atoms := by
  exact daiLiGreedySubdivisionWith_join
    (fun atom => regionInteractionCounter P embedding threshold
      (daiLiAtomQubits embedding left right atom)) d atoms

/-- Every retained physical group is nonempty and low-counter or one short atom. -/
theorem daiLiPhysicalGreedySubdivision_admissible
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms piece : List (ℝ × ℝ))
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    piece ≠ [] ∧
      (10 * (daiLiAtomCounters P embedding threshold left right piece).sum ≤ d ∨
        piece.length ≤ 1) := by
  have hImage : daiLiAtomCounters P embedding threshold left right piece ∈
      (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).map
        (daiLiAtomCounters P embedding threshold left right) :=
    List.mem_map_of_mem hPiece
  rw [daiLiPhysicalGreedySubdivision_counters] at hImage
  have hCounter := daiLiGreedyAtomicSubdivision_admissible d
    (daiLiAtomCounters P embedding threshold left right atoms)
    (daiLiAtomCounters P embedding threshold left right piece) hImage
  simpa [DaiLiAtomicPieceAdmissible, DaiLiLowCounter, DaiLiShortAtomicBand,
    daiLiAtomicMass, daiLiAtomCounters] using hCounter

/-- The physical greedy group's count is the corrected exact Nat bound. -/
theorem daiLiPhysicalGreedySubdivision_count
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).length * d ≤
      20 * (daiLiAtomCounters P embedding threshold left right atoms).sum + d := by
  have hLengths := congrArg List.length
    (daiLiPhysicalGreedySubdivision_counters P embedding threshold left right d atoms)
  have hLength : (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).length =
      (daiLiGreedyAtomicSubdivision d
        (daiLiAtomCounters P embedding threshold left right atoms)).length := by
    simpa using hLengths
  rw [hLength]
  simpa [daiLiAtomicMass] using
    daiLiGreedyAtomicSubdivision_count d
      (daiLiAtomCounters P embedding threshold left right atoms)

/-- A member of a list of lists is a contiguous infix of its flattening. -/
theorem daiLiGroup_infix_flatten {α : Type*}
    (groups : List (List α)) (piece : List α) (hPiece : piece ∈ groups) :
    piece <:+: groups.flatten := by
  induction groups with
  | nil => simp at hPiece
  | cons first groups ih =>
      simp only [List.mem_cons] at hPiece
      rcases hPiece with rfl | hPiece
      · exact ⟨[], groups.flatten, rfl⟩
      · rcases ih hPiece with ⟨before, after, hInfix⟩
        exact ⟨first ++ before, after, by simp [hInfix, List.append_assoc]⟩

/-- A physical greedy group is a contiguous infix of the original atom list. -/
theorem daiLiPhysicalGreedySubdivision_infix
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms piece : List (ℝ × ℝ))
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    piece <:+: atoms := by
  rw [← daiLiPhysicalGreedySubdivision_join P embedding threshold left right d atoms]
  exact daiLiGroup_infix_flatten
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) piece hPiece

/-- The lower endpoint of a nonempty contiguous atom group. -/
def daiLiAtomGroupLower : List (ℝ × ℝ) → ℝ
  | [] => 0
  | atom :: _ => atom.1

/-- The upper endpoint of a nonempty contiguous atom group. -/
def daiLiAtomGroupUpper : List (ℝ × ℝ) → ℝ
  | [] => 0
  | [atom] => atom.2
  | _ :: tail => daiLiAtomGroupUpper tail

/-- Collapse an ordered nonempty atom group to its horizontal rectangle. -/
def daiLiAtomGroupRectangle (left right : ℝ) (group : List (ℝ × ℝ)) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  ((left, daiLiAtomGroupLower group), (right, daiLiAtomGroupUpper group))

theorem daiLiAtomGroupLower_eq_head
    (group : List (ℝ × ℝ)) (hGroup : group ≠ []) :
    daiLiAtomGroupLower group = (group.head hGroup).1 := by
  cases group with
  | nil => exact False.elim (hGroup rfl)
  | cons atom tail => rfl

theorem daiLiAtomGroupUpper_eq_getLast
    (group : List (ℝ × ℝ)) (hGroup : group ≠ []) :
    daiLiAtomGroupUpper group = (group.getLast hGroup).2 := by
  induction group with
  | nil => exact False.elim (hGroup rfl)
  | cons atom tail ih =>
      cases tail with
      | nil => simp [daiLiAtomGroupUpper]
      | cons next tail =>
          have hTail : (next :: tail) ≠ [] := by simp
          simpa [daiLiAtomGroupUpper] using ih hTail

theorem daiLiAtomGroups_adjacent
    (first second : List (ℝ × ℝ)) (hFirst : first ≠ []) (hSecond : second ≠ [])
    (hAdjacent : ∀ firstAtom ∈ first.getLast?, ∀ secondAtom ∈ second.head?,
      DaiLiAtomAdjacent firstAtom secondAtom) :
    daiLiAtomGroupUpper first = daiLiAtomGroupLower second := by
  have hLastMem : first.getLast hFirst ∈ first.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hFirst]
    simp
  have hHeadMem : second.head hSecond ∈ second.head? := by
    rw [List.head?_eq_some_head hSecond]
    simp
  have hRelation := hAdjacent (first.getLast hFirst) hLastMem (second.head hSecond) hHeadMem
  rw [daiLiAtomGroupUpper_eq_getLast first hFirst,
    daiLiAtomGroupLower_eq_head second hSecond]
  exact hRelation

/-- A nonempty prefix of an atomization is itself an atomization. -/
theorem DaiLiHorizontalAtomization.prefix_atomization
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms) :
    ∀ {initial suffix : List (ℝ × ℝ)}, atoms = initial ++ suffix → initial ≠ [] →
      DaiLiHorizontalAtomization support ell lower (daiLiAtomGroupUpper initial) initial := by
  induction hAtoms with
  | @single actualLower actualUpper hHeight =>
      intro initial suffix hEq hInitial
      have hPrefixIn : initial <+: [(actualLower, actualUpper)] := ⟨suffix, hEq.symm⟩
      have hLength : initial.length ≤ 1 := by
        simpa using hPrefixIn.length_le
      cases initial with
      | nil => exact False.elim (hInitial rfl)
      | cons first rest =>
          cases rest with
          | nil =>
              cases suffix with
              | nil =>
                  simp only [List.append_nil, List.cons.injEq] at hEq
                  rcases hEq with ⟨hFirst, _⟩
                  cases hFirst
                  simpa [daiLiAtomGroupUpper] using
                    (DaiLiHorizontalAtomization.single hHeight)
              | cons next suffix =>
                  simp at hEq
          | cons next rest =>
              simp at hLength
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      intro initial suffix hEq hInitial
      cases initial with
      | nil => exact False.elim (hInitial rfl)
      | cons first initialTail =>
          simp only [List.cons_append, List.cons.injEq] at hEq
          rcases hEq with ⟨rfl, hTailEq⟩
          cases initialTail with
          | nil =>
              simpa [daiLiAtomGroupUpper] using
                (DaiLiHorizontalAtomization.single hHeight)
          | cons next rest =>
              have hTailAtomization := ih (initial := next :: rest) (suffix := suffix)
                hTailEq (by simp)
              simpa [daiLiAtomGroupUpper] using
                (DaiLiHorizontalAtomization.cons hCutFree hHeight hTailAtomization)

/-- Every nonempty contiguous infix of an atomization is a valid atomization. -/
theorem DaiLiHorizontalAtomization.infix_atomization
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms group : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hGroup : group <:+: atoms) (hGroupNe : group ≠ []) :
    DaiLiHorizontalAtomization support ell (daiLiAtomGroupLower group)
      (daiLiAtomGroupUpper group) group := by
  induction hAtoms generalizing group with
  | single hHeight =>
      rw [List.infix_singleton_iff] at hGroup
      rcases hGroup with hEmpty | hSingle
      · exact False.elim (hGroupNe hEmpty)
      · subst group
        simpa [daiLiAtomGroupLower, daiLiAtomGroupUpper] using
          (DaiLiHorizontalAtomization.single hHeight)
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      rcases hGroup with ⟨before, after, hGroupEq⟩
      cases before with
      | nil =>
          have hPrefix := DaiLiHorizontalAtomization.prefix_atomization
            (DaiLiHorizontalAtomization.cons hCutFree hHeight hTail)
            hGroupEq.symm hGroupNe
          rcases hPrefix.starts_at with ⟨firstUpper, rest, hStarts⟩
          have hStarts' : group = (lower, firstUpper) :: rest := by
            simpa using hStarts
          rw [hStarts'] at hPrefix ⊢
          simpa [daiLiAtomGroupLower] using hPrefix
      | cons first beforeTail =>
          simp only [List.cons_append, List.cons.injEq] at hGroupEq
          rcases hGroupEq with ⟨_, hTailGroupEq⟩
          exact ih ⟨beforeTail, after, hTailGroupEq⟩ hGroupNe

/-- Every nonempty atomization inherits the minimum physical height. -/
theorem DaiLiHorizontalAtomization.minimum_height
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) :
    5 * ell ≤ upper - lower := by
  induction hAtoms with
  | single hHeight => exact hHeight.1
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      have hTailPositive : cut < upper := hTail.lower_lt_upper hEll
      exact hHeight.1.trans (by linarith)

/-- A one-atom group inherits the exact Dai--Li short-height cap. -/
theorem daiLiAtomGroup_short_height {ell : ℝ} :
    ∀ (group : List (ℝ × ℝ)), group ≠ [] → group.length ≤ 1 →
      (∀ atom ∈ group, DaiLiShortHeight ell atom.1 atom.2) →
        daiLiAtomGroupUpper group - daiLiAtomGroupLower group ≤ 10 * ell := by
  intro group
  cases group with
  | nil =>
      intro hNe _ _
      exact False.elim (hNe rfl)
  | cons atom tail =>
      cases tail with
      | nil =>
          intro _ _ hShort
          simpa [daiLiAtomGroupLower, daiLiAtomGroupUpper] using
            (hShort atom (by simp)).2
      | cons next tail =>
          intro _ hLength _
          simp at hLength

/-- Each physical greedy group remains an adjacent chain of source atoms. -/
theorem daiLiPhysicalGreedySubdivision_group_chain
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    {ell lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    piece.IsChain DaiLiAtomAdjacent := by
  exact hAtoms.atom_chain.infix
    (daiLiPhysicalGreedySubdivision_infix P embedding threshold left right d atoms piece hPiece)

/-- Every physical greedy group retains the physical short-height facts of its atoms. -/
theorem daiLiPhysicalGreedySubdivision_group_atoms_short
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    {ell lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms)
    (atom : ℝ × ℝ) (hAtom : atom ∈ piece) :
    DaiLiShortHeight ell atom.1 atom.2 := by
  rcases daiLiPhysicalGreedySubdivision_infix P embedding threshold left right d atoms piece hPiece with
    ⟨before, after, hInfix⟩
  apply hAtoms.atom_short atom
  rw [← hInfix]
  simp [hAtom]

/-- The collapsed rectangle of every physical greedy group has the required minimum height. -/
theorem daiLiPhysicalGreedySubdivision_group_min_height
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    5 * ell ≤ (daiLiAtomGroupRectangle left right piece).2.2 -
      (daiLiAtomGroupRectangle left right piece).1.2 := by
  have hAdmissible := daiLiPhysicalGreedySubdivision_admissible
    P embedding threshold left right d atoms piece hPiece
  have hPieceAtoms := hAtoms.infix_atomization
    (daiLiPhysicalGreedySubdivision_infix P embedding threshold left right d atoms piece hPiece)
    hAdmissible.1
  simpa [daiLiAtomGroupRectangle] using hPieceAtoms.minimum_height hEll

/-- The short branch becomes the exact short-height alternative after collapsing. -/
theorem daiLiPhysicalGreedySubdivision_group_short_height
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms)
    (hShort : piece.length ≤ 1) :
    (daiLiAtomGroupRectangle left right piece).2.2 -
      (daiLiAtomGroupRectangle left right piece).1.2 ≤ 10 * ell := by
  have hAdmissible := daiLiPhysicalGreedySubdivision_admissible
    P embedding threshold left right d atoms piece hPiece
  simpa [daiLiAtomGroupRectangle] using daiLiAtomGroup_short_height piece hAdmissible.1 hShort
    (fun atom hAtom => daiLiPhysicalGreedySubdivision_group_atoms_short
      P embedding threshold left right hAtoms d hPiece atom hAtom)

/--
The counter carried by a physical greedy group is exactly the actual counter
of its collapsed rectangle, not merely a sum supplied as a hypothesis.
-/
theorem daiLiPhysicalGreedySubdivision_group_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    (daiLiAtomCounters P embedding threshold left right piece).sum =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle
          (daiLiAtomGroupRectangle left right piece).1
          (daiLiAtomGroupRectangle left right piece).2) := by
  have hAdmissible := daiLiPhysicalGreedySubdivision_admissible
    P embedding threshold left right d atoms piece hPiece
  have hPieceAtoms := hAtoms.infix_atomization
    (daiLiPhysicalGreedySubdivision_infix P embedding threshold left right d atoms piece hPiece)
    hAdmissible.1
  simpa [daiLiAtomGroupRectangle] using
    hPieceAtoms.atomCounters_sum P embedding threshold left right hEll

/-- Every collapsed physical group has the corrected low-counter or short-height alternative. -/
theorem daiLiPhysicalGreedySubdivision_group_alternative
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    10 * regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle
          (daiLiAtomGroupRectangle left right piece).1
          (daiLiAtomGroupRectangle left right piece).2) ≤ d ∨
      (daiLiAtomGroupRectangle left right piece).2.2 -
        (daiLiAtomGroupRectangle left right piece).1.2 ≤ 10 * ell := by
  rcases daiLiPhysicalGreedySubdivision_admissible
      P embedding threshold left right d atoms piece hPiece with
    ⟨_, hLow | hShort⟩
  · left
    rw [← daiLiPhysicalGreedySubdivision_group_counter
      P embedding threshold left right ell hEll hAtoms d hPiece]
    exact hLow
  · right
    exact daiLiPhysicalGreedySubdivision_group_short_height
      P embedding threshold left right ell hAtoms d hPiece hShort

/-- The concrete rectangle list obtained by collapsing each retained atom group. -/
def daiLiPhysicalGreedyRectangles
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) : List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).map
    (daiLiAtomGroupRectangle left right)

/-- The actual qubits covered by a finite list of collapsed rectangles. -/
def daiLiRectangleQubitsCover
    (embedding : UnitSeparatedEmbedding2D ι)
    (rectangles : List ((ℝ × ℝ) × (ℝ × ℝ))) : Finset ι :=
  rectangles.foldr (fun rectangle covered =>
    embedding.qubitsInRectangle rectangle.1 rectangle.2 ∪ covered) ∅

/-- Replacing atom groups by their equal collapsed rectangle covers commutes with folding. -/
theorem daiLiRectangleQubitsCover_groups
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (groups : List (List (ℝ × ℝ)))
    (hGroups : ∀ group ∈ groups,
      embedding.qubitsInRectangle (daiLiAtomGroupRectangle left right group).1
          (daiLiAtomGroupRectangle left right group).2 =
        daiLiAtomQubitsCover embedding left right group) :
    daiLiRectangleQubitsCover embedding
        (groups.map (daiLiAtomGroupRectangle left right)) =
      daiLiAtomQubitsCover embedding left right groups.flatten := by
  induction groups with
  | nil => simp [daiLiRectangleQubitsCover, daiLiAtomQubitsCover]
  | cons group groups ih =>
      have hGroup := hGroups group (by simp)
      have hTail : ∀ candidate ∈ groups,
          embedding.qubitsInRectangle (daiLiAtomGroupRectangle left right candidate).1
              (daiLiAtomGroupRectangle left right candidate).2 =
            daiLiAtomQubitsCover embedding left right candidate := by
        intro candidate hCandidate
        exact hGroups candidate (by simp [hCandidate])
      change daiLiRectangleQubitsCover embedding
          (daiLiAtomGroupRectangle left right group ::
            groups.map (daiLiAtomGroupRectangle left right)) =
        daiLiAtomQubitsCover embedding left right (group ++ groups.flatten)
      simp only [daiLiRectangleQubitsCover, List.foldr_cons,
        daiLiAtomQubitsCover_append]
      have hTailFold :
          List.foldr (fun rectangle covered =>
              embedding.qubitsInRectangle rectangle.1 rectangle.2 ∪ covered) ∅
              (groups.map (daiLiAtomGroupRectangle left right)) =
            daiLiAtomQubitsCover embedding left right groups.flatten := by
        simpa [daiLiRectangleQubitsCover] using ih hTail
      rw [hGroup, hTailFold]

/--
The collapsed physical greedy rectangles cover exactly the actual qubits of
their parent rectangle.  This is a finite half-open assignment cover: all
internal cuts are globally support-free.
-/
theorem daiLiPhysicalGreedyRectangles_cover
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) :
    daiLiRectangleQubitsCover embedding
        (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms) =
      embedding.qubitsInRectangle (left, lower) (right, upper) := by
  let groups := daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms
  have hGroups : ∀ group ∈ groups,
      embedding.qubitsInRectangle (daiLiAtomGroupRectangle left right group).1
          (daiLiAtomGroupRectangle left right group).2 =
        daiLiAtomQubitsCover embedding left right group := by
    intro group hGroup
    have hAdmissible := daiLiPhysicalGreedySubdivision_admissible
      P embedding threshold left right d atoms group hGroup
    have hGroupAtoms := hAtoms.infix_atomization
      (daiLiPhysicalGreedySubdivision_infix P embedding threshold left right d atoms group hGroup)
      hAdmissible.1
    exact (hGroupAtoms.atomQubitsCover embedding left right hEll).symm
  change daiLiRectangleQubitsCover embedding
      (groups.map (daiLiAtomGroupRectangle left right)) = _
  calc
    _ = daiLiAtomQubitsCover embedding left right groups.flatten :=
      daiLiRectangleQubitsCover_groups embedding left right groups hGroups
    _ = daiLiAtomQubitsCover embedding left right atoms := by
      rw [daiLiPhysicalGreedySubdivision_join P embedding threshold left right d atoms]
    _ = _ := hAtoms.atomQubitsCover embedding left right hEll

theorem daiLiAtomQubitsCover_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (first second : List (ℝ × ℝ))
    (hDisjoint : ∀ firstAtom ∈ first, ∀ secondAtom ∈ second,
      Disjoint (daiLiAtomQubits embedding left right firstAtom)
        (daiLiAtomQubits embedding left right secondAtom)) :
    Disjoint (daiLiAtomQubitsCover embedding left right first)
      (daiLiAtomQubitsCover embedding left right second) := by
  apply Finset.disjoint_left.mpr
  intro q hFirst hSecond
  rcases (mem_daiLiAtomQubitsCover embedding left right first q).1 hFirst with
    ⟨firstAtom, hFirstAtom, hqFirst⟩
  rcases (mem_daiLiAtomQubitsCover embedding left right second q).1 hSecond with
    ⟨secondAtom, hSecondAtom, hqSecond⟩
  exact (Finset.disjoint_left.mp (hDisjoint firstAtom hFirstAtom secondAtom hSecondAtom))
    hqFirst hqSecond

/-- Pairwise atom disjointness lifts to the finite covers of contiguous atom groups. -/
theorem daiLiAtomGroupsCover_pairwise
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (groups : List (List (ℝ × ℝ)))
    (hPairwise : (groups.flatten.map (daiLiAtomQubits embedding left right)).Pairwise Disjoint) :
    (groups.map (daiLiAtomQubitsCover embedding left right)).Pairwise Disjoint := by
  have hFlattened :
      ((groups.map (List.map (daiLiAtomQubits embedding left right))).flatten).Pairwise
        Disjoint := by
    simpa using hPairwise
  have hAcrossMapped := (List.pairwise_flatten.mp hFlattened).2
  have hAcross' : groups.Pairwise (fun first second =>
      ∀ firstQubits ∈ first.map (daiLiAtomQubits embedding left right),
        ∀ secondQubits ∈ second.map (daiLiAtomQubits embedding left right),
          Disjoint firstQubits secondQubits) := by
    simpa only [List.pairwise_map] using hAcrossMapped
  have hAcross : groups.Pairwise (fun first second =>
      ∀ firstAtom ∈ first, ∀ secondAtom ∈ second,
        Disjoint (daiLiAtomQubits embedding left right firstAtom)
          (daiLiAtomQubits embedding left right secondAtom)) := by
    refine hAcross'.imp ?_
    intro first second hMapped firstAtom hFirst secondAtom hSecond
    exact hMapped _ (List.mem_map_of_mem hFirst) _ (List.mem_map_of_mem hSecond)
  have hCovers : groups.Pairwise (fun first second =>
      Disjoint (daiLiAtomQubitsCover embedding left right first)
        (daiLiAtomQubitsCover embedding left right second)) :=
    hAcross.imp (by
      intro first second hDisjoint
      exact daiLiAtomQubitsCover_disjoint embedding left right first second hDisjoint)
  simpa only [List.pairwise_map] using hCovers

/-- Pairwise-disjointness of the finite qubit assignments of collapsed rectangles. -/
def DaiLiPairwiseDisjointQubitRectangles
    (embedding : UnitSeparatedEmbedding2D ι)
    (rectangles : List ((ℝ × ℝ) × (ℝ × ℝ))) : Prop :=
  (rectangles.map fun rectangle =>
    embedding.qubitsInRectangle rectangle.1 rectangle.2).Pairwise Disjoint

/-- The collapsed physical greedy rectangles have pairwise-disjoint half-open qubit assignments. -/
theorem daiLiPhysicalGreedyRectangles_pairwise
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) :
    DaiLiPairwiseDisjointQubitRectangles embedding
      (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms) := by
  let groups := daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms
  have hGroups : ∀ group ∈ groups,
      embedding.qubitsInRectangle (daiLiAtomGroupRectangle left right group).1
          (daiLiAtomGroupRectangle left right group).2 =
        daiLiAtomQubitsCover embedding left right group := by
    intro group hGroup
    have hAdmissible := daiLiPhysicalGreedySubdivision_admissible
      P embedding threshold left right d atoms group hGroup
    have hGroupAtoms := hAtoms.infix_atomization
      (daiLiPhysicalGreedySubdivision_infix P embedding threshold left right d atoms group hGroup)
      hAdmissible.1
    exact (hGroupAtoms.atomQubitsCover embedding left right hEll).symm
  have hAtomicPairwise :
      (groups.flatten.map (daiLiAtomQubits embedding left right)).Pairwise Disjoint := by
    rw [daiLiPhysicalGreedySubdivision_join P embedding threshold left right d atoms]
    exact hAtoms.atomQubits_pairwise embedding left right hEll
  have hGroupPairwise := daiLiAtomGroupsCover_pairwise embedding left right groups hAtomicPairwise
  have hMap :
      (groups.map (daiLiAtomGroupRectangle left right)).map (fun rectangle =>
        embedding.qubitsInRectangle rectangle.1 rectangle.2) =
      groups.map (daiLiAtomQubitsCover embedding left right) := by
    simpa [Function.comp_apply] using
      List.map_congr_left (fun group hGroup => hGroups group hGroup)
  change ((groups.map (daiLiAtomGroupRectangle left right)).map (fun rectangle =>
    embedding.qubitsInRectangle rectangle.1 rectangle.2)).Pairwise Disjoint
  rw [hMap]
  exact hGroupPairwise

/-- The collapsed rectangles remain ordered by their common horizontal endpoints. -/
theorem daiLiPhysicalGreedyRectangles_ordered
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) :
    (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).IsChain
      (fun first second => first.2.2 = second.1.2) := by
  let groups := daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms
  have hNoEmpty : [] ∉ groups := by
    intro hEmpty
    exact (daiLiPhysicalGreedySubdivision_admissible
      P embedding threshold left right d atoms [] hEmpty).1 rfl
  have hFlattened : groups.flatten.IsChain DaiLiAtomAdjacent := by
    rw [daiLiPhysicalGreedySubdivision_join P embedding threshold left right d atoms]
    exact hAtoms.atom_chain
  have hAcross := (List.isChain_flatten hNoEmpty).mp hFlattened |>.2
  have hOrderedGroups : groups.IsChain (fun first second =>
      daiLiAtomGroupUpper first = daiLiAtomGroupLower second) :=
    hAcross.imp_of_mem_imp (by
      intro first second hFirst hSecond hAdjacent
      have hFirstNe : first ≠ [] := fun hEmpty => hNoEmpty (hEmpty ▸ hFirst)
      have hSecondNe : second ≠ [] := fun hEmpty => hNoEmpty (hEmpty ▸ hSecond)
      exact daiLiAtomGroups_adjacent first second hFirstNe hSecondNe hAdjacent)
  change (groups.map (daiLiAtomGroupRectangle left right)).IsChain _
  rw [List.isChain_map]
  simpa [daiLiAtomGroupRectangle] using hOrderedGroups

/-- Every output rectangle has the exact minimum-height and low-counter/short alternatives. -/
theorem daiLiPhysicalGreedyRectangles_piece_properties
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) (rectangle : (ℝ × ℝ) × (ℝ × ℝ))
    (hRectangle : rectangle ∈ daiLiPhysicalGreedyRectangles
      P embedding threshold left right d atoms) :
    5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
      (10 * regionInteractionCounter P embedding threshold
          (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
        rectangle.2.2 - rectangle.1.2 ≤ 10 * ell) := by
  rcases List.mem_map.mp hRectangle with ⟨piece, hPiece, rfl⟩
  constructor
  · exact daiLiPhysicalGreedySubdivision_group_min_height
      P embedding threshold left right ell hEll hAtoms d hPiece
  · exact daiLiPhysicalGreedySubdivision_group_alternative
      P embedding threshold left right ell hEll hAtoms d hPiece

/-- The collapsed rectangle count retains the corrected single-rectangle bound. -/
theorem daiLiPhysicalGreedyRectangles_count
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).length * d ≤
      20 * (daiLiAtomCounters P embedding threshold left right atoms).sum + d := by
  simpa [daiLiPhysicalGreedyRectangles] using
    daiLiPhysicalGreedySubdivision_count P embedding threshold left right d atoms

/--
Arithmetic handoff for #386.  Under its still-required global incidence
budget `50 * totalF <= budget`, `d <= budget`, and the actual nonempty-bad
alternative, the corrected factor-30 subdivision count still gives the strict
rectangle budget `M < budget / d`.  The alternative is essential because Nat
division rounds down: either no rectangle was produced, or a bad square gives
`d <= 10 * totalF`.  For the Dai--Li application, `budget` is `max(k, d)`.
-/
theorem daiLiCorrectedFamilyCount_lt_budget_div
    (M totalF d budget : Nat) (hD : 0 < d) (hDLeBudget : d ≤ budget)
    (hCount : M * d ≤ 30 * totalF) (hTotal : 50 * totalF ≤ budget)
    (hEmptyOrBad : M = 0 ∨ d ≤ 10 * totalF) :
    M < budget / d := by
  apply Nat.lt_of_succ_le
  rw [Nat.le_div_iff_mul_le hD]
  rcases hEmptyOrBad with hEmpty | hBad
  · simpa [hEmpty] using hDLeBudget
  · calc
      M.succ * d = M * d + d := Nat.succ_mul M d
      _ ≤ 30 * totalF + 10 * totalF := Nat.add_le_add hCount hBad
      _ ≤ 50 * totalF := by omega
      _ ≤ budget := hTotal

/-!
The source's later `C` estimate charges four vertices per bad rectangle and at
most `6 * (4 * ell)^2 = 96 * ell^2` qubits per vertex.  Thus its exact packing
term is `384 * ell^2 * M`, which the paper relaxes to
`400 * ell^2 * budget / d`.  The next lemma verifies that the corrected
factor-30 count is still strong enough for that relaxation; it does not reuse
the false source rectangle-count bound.
-/
theorem daiLiCorrectedFamilyCount_badRectangleVertexTerm_le
    (M totalF d budget : Nat) (ell : ℝ) (hD : 0 < d)
    (hCount : M * d ≤ 30 * totalF) (hTotal : 50 * totalF ≤ budget) :
    384 * ell ^ 2 * (M : ℝ) ≤
      400 * ell ^ 2 * (budget : ℝ) / (d : ℝ) := by
  have hDReal : (0 : ℝ) < d := by exact_mod_cast hD
  have hCountReal : (M : ℝ) * d ≤ 30 * totalF := by exact_mod_cast hCount
  have hTotalReal : (50 : ℝ) * totalF ≤ budget := by exact_mod_cast hTotal
  have hScaled : (384 : ℝ) * M * d ≤ 400 * budget := by
    nlinarith
  have hBase : (384 : ℝ) * M ≤ 400 * budget / d := by
    exact (le_div_iff₀ hDReal).2 (by simpa [mul_assoc] using hScaled)
  have hEllSq : 0 ≤ ell ^ 2 := sq_nonneg ell
  calc
    384 * ell ^ 2 * (M : ℝ) = ell ^ 2 * (384 * M) := by ring
    _ ≤ ell ^ 2 * (400 * budget / d) :=
      mul_le_mul_of_nonneg_left hBase hEllSq
    _ = 400 * ell ^ 2 * (budget : ℝ) / (d : ℝ) := by ring

/-!
Exact arithmetic assembly for the later #386 `C` estimate.  The geometric
geometric proof still has to establish the three component-cardinality bounds and the two
scale inequalities.  This lemma only certifies that, once those concrete
obligations are available, the corrected bad-rectangle term preserves the
source's strict `|C| < k` conclusion.
-/
theorem daiLiCorrectedCComponentEstimate_lt
    (M totalF d k n : Nat) (ell w badQubits badRectangleVertexQubits
      gridVertexQubits : ℝ)
    (hD : 0 < d) (hK : 0 < k)
    (hCount : M * d ≤ 30 * totalF) (hTotal : 50 * totalF ≤ k)
    (hBadQubits : badQubits ≤ (k : ℝ) / 50)
    (hBadRectangleVertices :
      badRectangleVertexQubits ≤ 384 * ell ^ 2 * (M : ℝ))
    (hGridVertices :
      gridVertexQubits ≤ 16 * ell ^ 2 * (n : ℝ) / w ^ 2)
    (hBadRectangleScale :
      400 * ell ^ 2 * (k : ℝ) / (d : ℝ) ≤ (k : ℝ) / 25)
    (hGridScale : 16 * ell ^ 2 * (n : ℝ) / w ^ 2 ≤ (k : ℝ) / 100) :
    badQubits + badRectangleVertexQubits + gridVertexQubits < (k : ℝ) := by
  have hRectangleTerm := daiLiCorrectedFamilyCount_badRectangleVertexTerm_le
    M totalF d k ell hD hCount hTotal
  have hKReal : (0 : ℝ) < k := by exact_mod_cast hK
  have hBadRectangleFinal : badRectangleVertexQubits ≤ (k : ℝ) / 25 :=
    hBadRectangleVertices.trans (hRectangleTerm.trans hBadRectangleScale)
  have hGridFinal : gridVertexQubits ≤ (k : ℝ) / 100 :=
    hGridVertices.trans hGridScale
  calc
    badQubits + badRectangleVertexQubits + gridVertexQubits ≤
        (k : ℝ) / 50 + (k : ℝ) / 25 + (k : ℝ) / 100 := by
      linarith
    _ < (k : ℝ) := by linarith

/--
Every actual bad square of sufficient height has a constructed corrected
subdivision.  The returned atomization carries the support-free cuts and its
termination proof; the returned rectangle list is its greedy physical image.
-/
theorem exists_daiLiBadInteractionSquareSubdivision
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold ell : ℝ) (d : Nat)
    (center : ℝ × ℝ) (radius : ℝ)
    (hEll : 0 < ell) (hHeight : 5 * ell ≤ 2 * radius)
    (hBad : IsBadInteractionSquare P embedding threshold d center radius) :
    ∃ atoms rectangles,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        (center.2 - radius) (center.2 + radius) atoms ∧
      rectangles = daiLiPhysicalGreedyRectangles P embedding threshold
        (center.1 - radius) (center.1 + radius) d atoms ∧
      rectangles.IsChain (fun first second => first.2.2 = second.1.2) ∧
      DaiLiPairwiseDisjointQubitRectangles embedding rectangles ∧
      daiLiRectangleQubitsCover embedding rectangles =
        squareQubits embedding center radius ∧
      (∀ rectangle ∈ rectangles,
        5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
          (10 * regionInteractionCounter P embedding threshold
              (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
            rectangle.2.2 - rectangle.1.2 ≤ 10 * ell)) ∧
      rectangles.length * d ≤
        20 * regionInteractionCounter P embedding threshold
          (squareQubits embedding center radius) + d ∧
      d ≤ 10 * regionInteractionCounter P embedding threshold
        (squareQubits embedding center radius) := by
  have hRectangleHeight : 5 * ell ≤
      (center.2 + radius) - (center.2 - radius) := by
    linarith
  rcases exists_daiLiRectangleAtomization_globalSupport embedding
      (center.1 - radius, center.2 - radius)
      (center.1 + radius, center.2 + radius) ell hEll hRectangleHeight with
    ⟨atoms, hAtoms⟩
  let rectangles := daiLiPhysicalGreedyRectangles P embedding threshold
    (center.1 - radius) (center.1 + radius) d atoms
  refine ⟨atoms, rectangles, hAtoms, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [rectangles] using daiLiPhysicalGreedyRectangles_ordered
      P embedding threshold (center.1 - radius) (center.1 + radius) hAtoms d
  · simpa [rectangles] using daiLiPhysicalGreedyRectangles_pairwise
      P embedding threshold (center.1 - radius) (center.1 + radius) ell hEll hAtoms d
  · simpa [rectangles, squareQubits] using daiLiPhysicalGreedyRectangles_cover
      P embedding threshold (center.1 - radius) (center.1 + radius) ell hEll hAtoms d
  · intro rectangle hRectangle
    simpa [rectangles] using daiLiPhysicalGreedyRectangles_piece_properties
      P embedding threshold (center.1 - radius) (center.1 + radius) ell hEll hAtoms d
        rectangle hRectangle
  · calc
      rectangles.length * d ≤ 20 *
          (daiLiAtomCounters P embedding threshold
            (center.1 - radius) (center.1 + radius) atoms).sum + d := by
        simpa [rectangles] using daiLiPhysicalGreedyRectangles_count
          P embedding threshold (center.1 - radius) (center.1 + radius) d atoms
      _ = 20 * regionInteractionCounter P embedding threshold
          (squareQubits embedding center radius) + d := by
        rw [hAtoms.atomCounters_sum P embedding threshold
          (center.1 - radius) (center.1 + radius) hEll]
        rfl
  · simpa [IsBadInteractionSquare, IsBadInteractionRegion] using hBad

/--
A finite family of actual bad squares admits constructed physical subdivisions
whose total rectangle count satisfies the project-owned corrected factor-30
bound.  The internal choice is only over the explicitly proved terminating
atomization construction; each selected atom list is returned with its proof.
-/
theorem exists_daiLiBadInteractionSquareFamilySubdivision
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold ell : ℝ) (d : Nat)
    (squares : Finset α) (center : α → ℝ × ℝ) (radius : α → ℝ)
    (hEll : 0 < ell)
    (hHeight : ∀ square ∈ squares, 5 * ell ≤ 2 * radius square)
    (hBad : ∀ square ∈ squares,
      IsBadInteractionSquare P embedding threshold d (center square) (radius square)) :
    ∃ (atoms : α → List (ℝ × ℝ))
      (rectangles : α → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ square ∈ squares,
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((center square).2 - radius square) ((center square).2 + radius square)
          (atoms square)) ∧
      (∀ square ∈ squares,
        rectangles square = daiLiPhysicalGreedyRectangles P embedding threshold
          ((center square).1 - radius square) ((center square).1 + radius square)
          d (atoms square)) ∧
      (∀ square ∈ squares,
        (rectangles square).IsChain (fun first second => first.2.2 = second.1.2)) ∧
      (∀ square ∈ squares,
        DaiLiPairwiseDisjointQubitRectangles embedding (rectangles square)) ∧
      (∀ square ∈ squares,
        daiLiRectangleQubitsCover embedding (rectangles square) =
          squareQubits embedding (center square) (radius square)) ∧
      (∀ square ∈ squares, ∀ rectangle ∈ rectangles square,
        5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
          (10 * regionInteractionCounter P embedding threshold
              (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
            rectangle.2.2 - rectangle.1.2 ≤ 10 * ell)) ∧
      (∑ square ∈ squares, (rectangles square).length) * d ≤
        30 * ∑ square ∈ squares,
          regionInteractionCounter P embedding threshold
            (squareQubits embedding (center square) (radius square)) := by
  let atomWitness : ∀ square (hSquare : square ∈ squares),
      ∃ atoms, DaiLiHorizontalAtomization
        (daiLiGlobalVerticalQubitSupport embedding) ell
        ((center square).2 - radius square) ((center square).2 + radius square) atoms :=
    fun square hSquare =>
      exists_daiLiRectangleAtomization_globalSupport embedding
        ((center square).1 - radius square, (center square).2 - radius square)
        ((center square).1 + radius square, (center square).2 + radius square)
        ell hEll (by linarith [hHeight square hSquare])
  let atoms : α → List (ℝ × ℝ) := fun square =>
    if hSquare : square ∈ squares then Classical.choose (atomWitness square hSquare) else []
  have hAtoms : ∀ square ∈ squares,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((center square).2 - radius square) ((center square).2 + radius square)
        (atoms square) := by
    intro square hSquare
    simp only [atoms, dif_pos hSquare]
    exact Classical.choose_spec (atomWitness square hSquare)
  let rectangles : α → List ((ℝ × ℝ) × (ℝ × ℝ)) := fun square =>
    daiLiPhysicalGreedyRectangles P embedding threshold
      ((center square).1 - radius square) ((center square).1 + radius square)
      d (atoms square)
  refine ⟨atoms, rectangles, hAtoms, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro square hSquare
    rfl
  · intro square hSquare
    simpa [rectangles] using daiLiPhysicalGreedyRectangles_ordered
      P embedding threshold ((center square).1 - radius square)
        ((center square).1 + radius square) (hAtoms square hSquare) d
  · intro square hSquare
    simpa [rectangles] using daiLiPhysicalGreedyRectangles_pairwise
      P embedding threshold ((center square).1 - radius square)
        ((center square).1 + radius square) ell hEll (hAtoms square hSquare) d
  · intro square hSquare
    simpa [rectangles, squareQubits] using daiLiPhysicalGreedyRectangles_cover
      P embedding threshold ((center square).1 - radius square)
        ((center square).1 + radius square) ell hEll (hAtoms square hSquare) d
  · intro square hSquare rectangle hRectangle
    simpa [rectangles] using daiLiPhysicalGreedyRectangles_piece_properties
      P embedding threshold ((center square).1 - radius square)
        ((center square).1 + radius square) ell hEll (hAtoms square hSquare) d
        rectangle hRectangle
  · have hBadAtoms : ∀ square ∈ squares,
      d ≤ 10 * (daiLiAtomCounters P embedding threshold
        ((center square).1 - radius square) ((center square).1 + radius square)
        (atoms square)).sum := by
      intro square hSquare
      rw [(hAtoms square hSquare).atomCounters_sum P embedding threshold
        ((center square).1 - radius square) ((center square).1 + radius square) hEll]
      exact hBad square hSquare
    have hLengths : ∀ square ∈ squares,
        (rectangles square).length =
          (daiLiGreedyAtomicSubdivision d
            (daiLiAtomCounters P embedding threshold
              ((center square).1 - radius square) ((center square).1 + radius square)
              (atoms square))).length := by
      intro square hSquare
      have hLengths := congrArg List.length
        (daiLiPhysicalGreedySubdivision_counters P embedding threshold
          ((center square).1 - radius square) ((center square).1 + radius square)
          d (atoms square))
      simpa [rectangles, daiLiPhysicalGreedyRectangles] using hLengths
    calc
      (∑ square ∈ squares, (rectangles square).length) * d =
          (∑ square ∈ squares, (daiLiGreedyAtomicSubdivision d
            (daiLiAtomCounters P embedding threshold
              ((center square).1 - radius square) ((center square).1 + radius square)
              (atoms square))).length) * d := by
        apply congrArg (fun count : Nat => count * d)
        apply Finset.sum_congr rfl
        intro square hSquare
        exact hLengths square hSquare
      _ ≤
          30 * ∑ square ∈ squares,
            (daiLiAtomCounters P embedding threshold
              ((center square).1 - radius square) ((center square).1 + radius square)
              (atoms square)).sum := by
        exact daiLiGreedyAtomicSubdivision_family_count d
          (fun square => daiLiAtomCounters P embedding threshold
            ((center square).1 - radius square) ((center square).1 + radius square)
            (atoms square)) squares hBadAtoms
      _ = 30 * ∑ square ∈ squares,
          regionInteractionCounter P embedding threshold
            (squareQubits embedding (center square) (radius square)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro square hSquare
        rw [(hAtoms square hSquare).atomCounters_sum P embedding threshold
          ((center square).1 - radius square) ((center square).1 + radius square) hEll]
        rfl

/-!
The actual-family handoff used by the later recursive partition.  This keeps
the geometric witnesses and corrected count in the same existential package
as the `400 * ell^2 * k / d` vertex term, so callers cannot substitute a bare
rectangle-count hypothesis for the constructed subdivision.
-/
theorem exists_daiLiBadInteractionSquareFamilySubdivision_with_vertexTerm
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold ell : ℝ) (d k : Nat)
    (squares : Finset α) (center : α → ℝ × ℝ) (radius : α → ℝ)
    (hEll : 0 < ell) (hD : 0 < d)
    (hHeight : ∀ square ∈ squares, 5 * ell ≤ 2 * radius square)
    (hBad : ∀ square ∈ squares,
      IsBadInteractionSquare P embedding threshold d (center square) (radius square))
    (hGlobal : 50 * ∑ square ∈ squares,
      regionInteractionCounter P embedding threshold
        (squareQubits embedding (center square) (radius square)) ≤ k) :
    ∃ (atoms : α → List (ℝ × ℝ))
      (rectangles : α → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ square ∈ squares,
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((center square).2 - radius square) ((center square).2 + radius square)
          (atoms square)) ∧
      (∀ square ∈ squares,
        rectangles square = daiLiPhysicalGreedyRectangles P embedding threshold
          ((center square).1 - radius square) ((center square).1 + radius square)
          d (atoms square)) ∧
      (∀ square ∈ squares,
        (rectangles square).IsChain (fun first second => first.2.2 = second.1.2)) ∧
      (∀ square ∈ squares,
        DaiLiPairwiseDisjointQubitRectangles embedding (rectangles square)) ∧
      (∀ square ∈ squares,
        daiLiRectangleQubitsCover embedding (rectangles square) =
          squareQubits embedding (center square) (radius square)) ∧
      (∀ square ∈ squares, ∀ rectangle ∈ rectangles square,
        5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
          (10 * regionInteractionCounter P embedding threshold
              (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
            rectangle.2.2 - rectangle.1.2 ≤ 10 * ell)) ∧
      (∑ square ∈ squares, (rectangles square).length) * d ≤
        30 * ∑ square ∈ squares,
          regionInteractionCounter P embedding threshold
            (squareQubits embedding (center square) (radius square)) ∧
      384 * ell ^ 2 *
          ((∑ square ∈ squares, (rectangles square).length : Nat) : ℝ) ≤
        400 * ell ^ 2 * (k : ℝ) / (d : ℝ) := by
  rcases exists_daiLiBadInteractionSquareFamilySubdivision P embedding threshold ell d
      squares center radius hEll hHeight hBad with
    ⟨atoms, rectangles, hAtoms, hRectangles, hOrdered, hPairwise, hCover,
      hPieces, hCount⟩
  refine ⟨atoms, rectangles, hAtoms, hRectangles, hOrdered, hPairwise, hCover,
    hPieces, hCount, ?_⟩
  exact daiLiCorrectedFamilyCount_badRectangleVertexTerm_le
    (∑ square ∈ squares, (rectangles square).length)
    (∑ square ∈ squares,
      regionInteractionCounter P embedding threshold
        (squareQubits embedding (center square) (radius square)))
    d k ell hD hCount hGlobal

/--
The exact nonempty-bad alternative needed by the #386 integer-count handoff.
For an empty family the total output count is zero; otherwise any selected bad
square contributes enough actual counter mass to give `d <= 10 * totalF`.
-/
theorem daiLiBadInteractionSquareFamily_empty_or_total_lower
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (squares : Finset α) (center : α → ℝ × ℝ) (radius : α → ℝ)
    (rectangles : α → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hBad : ∀ square ∈ squares,
      IsBadInteractionSquare P embedding threshold d (center square) (radius square)) :
    (∑ square ∈ squares, (rectangles square).length) = 0 ∨
      d ≤ 10 * ∑ square ∈ squares,
        regionInteractionCounter P embedding threshold
          (squareQubits embedding (center square) (radius square)) := by
  by_cases hEmpty : squares = ∅
  · left
    simp [hEmpty]
  · right
    rcases Finset.nonempty_iff_ne_empty.mpr hEmpty with ⟨square, hSquare⟩
    have hSquareBad : d ≤ 10 * regionInteractionCounter P embedding threshold
        (squareQubits embedding (center square) (radius square)) := by
      simpa [IsBadInteractionSquare, IsBadInteractionRegion] using hBad square hSquare
    exact hSquareBad.trans (Nat.mul_le_mul_left 10
      (Finset.single_le_sum
        (f := fun candidate => regionInteractionCounter P embedding threshold
          (squareQubits embedding (center candidate) (radius candidate)))
        (fun _ _ => Nat.zero_le _) hSquare))

end QEC.Locality
