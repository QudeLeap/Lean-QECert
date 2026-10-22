import QEC.Locality.CorrectablePartition.SmallBoundary
import QEC.Locality.OptimalTradeoff.BadSquareSubdivision
/-!
# Dai--Li finite correctable-region partition

This internal module closes the finite geometric bookkeeping between the
translated grid and the semantic correctability calculus used by the
Dai--Li long-interaction argument.  A concrete floor-indexed grid owns each
qubit exactly once.  Correctability witnesses may use the corresponding
closed square, so boundary qubits are never silently discarded; the resulting
finite overlap is charged explicitly in the global incidence estimate.
-/

noncomputable section

open MeasureTheory Set Metric

namespace QEC.Locality

open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

local instance instClassicalDecidableCorrectable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Center of the closed witness square associated with one floor-indexed grid
cell.  The cell itself owns qubits half-openly, while this square retains the
boundary qubits needed by the physical subdivision theorem. -/
def daiLiGridCellCenter (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : ℝ × ℝ :=
  (origin.1 + ((cell.1 : ℝ) + 1 / 2) * w,
    origin.2 + ((cell.2 : ℝ) + 1 / 2) * w)

/-- The closed physical square used to certify one finite grid cell. -/
def daiLiGridCellClosedQubits (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : Finset ι :=
  squareQubits embedding (daiLiGridCellCenter w origin cell) (w / 2)

/-- The actual finite subsystem of one closed grid witness cell. -/
def daiLiGridCellClosedSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : FiniteSubsystem ι :=
  ⟨daiLiGridCellClosedQubits embedding w origin cell⟩

/-- The closed witness square is exactly the expected closed rectangle. -/
theorem daiLiGridCellClosedQubits_eq_rectangle
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (cell : ℤ × ℤ) :
    daiLiGridCellClosedQubits embedding w origin cell =
      embedding.qubitsInRectangle (gridCellLower w origin cell)
        (gridCellUpper w origin cell) := by
  ext q
  simp only [daiLiGridCellClosedQubits, squareQubits,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
  constructor <;> intro hq
  · rcases hq with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    constructor <;> constructor
    · dsimp [daiLiGridCellCenter, gridCellLower] at hxl ⊢
      ring_nf at hxl ⊢
      linarith
    · dsimp [daiLiGridCellCenter, gridCellUpper] at hxu ⊢
      ring_nf at hxu ⊢
      linarith
    · dsimp [daiLiGridCellCenter, gridCellLower] at hyl ⊢
      ring_nf at hyl ⊢
      linarith
    · dsimp [daiLiGridCellCenter, gridCellUpper] at hyu ⊢
      ring_nf at hyu ⊢
      linarith
  · rcases hq with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
    constructor <;> constructor
    · dsimp [daiLiGridCellCenter, gridCellLower] at hxl ⊢
      ring_nf at hxl ⊢
      linarith
    · dsimp [daiLiGridCellCenter, gridCellUpper] at hxu ⊢
      ring_nf at hxu ⊢
      linarith
    · dsimp [daiLiGridCellCenter, gridCellLower] at hyl ⊢
      ring_nf at hyl ⊢
      linarith
    · dsimp [daiLiGridCellCenter, gridCellUpper] at hyu ⊢
      ring_nf at hyu ⊢
      linarith

/-- Half-open ownership is contained in the closed physical witness square. -/
theorem gridCellQubits_subset_daiLiGridCellClosedQubits
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    embedding.gridCellQubits w origin cell ⊆
      daiLiGridCellClosedQubits embedding w origin cell := by
  rw [daiLiGridCellClosedQubits_eq_rectangle]
  exact embedding.gridCellQubits_subset_qubitsInRectangle hw origin cell

/-- The finite family of closed witness cells containing one actual qubit. -/
def daiLiGridClosedCellsContaining (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (q : ι) : Finset (ℤ × ℤ) :=
  (embedding.gridOccupiedCells w origin).filter fun cell =>
    q ∈ daiLiGridCellClosedQubits embedding w origin cell

/-- A qubit can lie in a closed cell only in one of the two adjacent integer
positions in each coordinate relative to its half-open owner. -/
theorem gridCellIndex_coordinate_eq_or_succ_of_mem_closed
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) (q : ι)
    (hq : q ∈ daiLiGridCellClosedQubits embedding w origin cell) :
    (gridCellIndex w origin (embedding.point q)).1 = cell.1 ∨
      (gridCellIndex w origin (embedding.point q)).1 = cell.1 + 1 := by
  rw [daiLiGridCellClosedQubits_eq_rectangle,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
  have hxLower : (cell.1 : ℝ) ≤ ((embedding.point q).1 - origin.1) / w := by
    apply (le_div_iff₀ hw).2
    dsimp [gridCellLower] at hq
    nlinarith [hq.1.1]
  have hxUpper : ((embedding.point q).1 - origin.1) / w ≤ (cell.1 : ℝ) + 1 := by
    apply (div_le_iff₀ hw).2
    dsimp [gridCellUpper] at hq
    nlinarith [hq.1.2]
  have hFloorLower : cell.1 ≤ ⌊((embedding.point q).1 - origin.1) / w⌋ :=
    (Int.le_floor).2 hxLower
  have hFloorUpper : ⌊((embedding.point q).1 - origin.1) / w⌋ ≤ cell.1 + 1 := by
    apply (Int.floor_le_iff).2
    push_cast
    linarith
  change ⌊((embedding.point q).1 - origin.1) / w⌋ = cell.1 ∨
    ⌊((embedding.point q).1 - origin.1) / w⌋ = cell.1 + 1
  omega

theorem gridCellIndex_coordinate_eq_or_succ_of_mem_closed_y
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) (q : ι)
    (hq : q ∈ daiLiGridCellClosedQubits embedding w origin cell) :
    (gridCellIndex w origin (embedding.point q)).2 = cell.2 ∨
      (gridCellIndex w origin (embedding.point q)).2 = cell.2 + 1 := by
  rw [daiLiGridCellClosedQubits_eq_rectangle,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
  have hyLower : (cell.2 : ℝ) ≤ ((embedding.point q).2 - origin.2) / w := by
    apply (le_div_iff₀ hw).2
    dsimp [gridCellLower] at hq
    nlinarith [hq.2.1]
  have hyUpper : ((embedding.point q).2 - origin.2) / w ≤ (cell.2 : ℝ) + 1 := by
    apply (div_le_iff₀ hw).2
    dsimp [gridCellUpper] at hq
    nlinarith [hq.2.2]
  have hFloorLower : cell.2 ≤ ⌊((embedding.point q).2 - origin.2) / w⌋ :=
    (Int.le_floor).2 hyLower
  have hFloorUpper : ⌊((embedding.point q).2 - origin.2) / w⌋ ≤ cell.2 + 1 := by
    apply (Int.floor_le_iff).2
    push_cast
    linarith
  change ⌊((embedding.point q).2 - origin.2) / w⌋ = cell.2 ∨
    ⌊((embedding.point q).2 - origin.2) / w⌋ = cell.2 + 1
  omega

/-- Closed witness squares overlap at most four times.  This is the explicit
boundary charge replacing the paper's informal generic perturbation. -/
theorem card_daiLiGridClosedCellsContaining_le_four
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (q : ι) :
    (daiLiGridClosedCellsContaining embedding w origin q).card ≤ 4 := by
  let owner := gridCellIndex w origin (embedding.point q)
  let candidates : Finset (ℤ × ℤ) :=
    ({owner.1, owner.1 - 1} : Finset ℤ).product
      ({owner.2, owner.2 - 1} : Finset ℤ)
  have hsubset : daiLiGridClosedCellsContaining embedding w origin q ⊆ candidates := by
    intro cell hcell
    have hq : q ∈ daiLiGridCellClosedQubits embedding w origin cell :=
      Finset.mem_filter.mp hcell |>.2
    rcases gridCellIndex_coordinate_eq_or_succ_of_mem_closed embedding hw origin cell q hq with
      hx | hx <;>
      rcases gridCellIndex_coordinate_eq_or_succ_of_mem_closed_y embedding hw origin cell q hq with
        hy | hy
    · apply Finset.mem_product.mpr
      constructor
      · change owner.1 = cell.1 at hx
        simp [hx]
      · change owner.2 = cell.2 at hy
        simp [hy]
    · apply Finset.mem_product.mpr
      constructor
      · change owner.1 = cell.1 at hx
        simp [hx]
      · change owner.2 = cell.2 + 1 at hy
        have hcell : cell.2 = owner.2 - 1 := by omega
        simp [hcell]
    · apply Finset.mem_product.mpr
      constructor
      · change owner.1 = cell.1 + 1 at hx
        have hcell : cell.1 = owner.1 - 1 := by omega
        simp [hcell]
      · change owner.2 = cell.2 at hy
        simp [hy]
    · apply Finset.mem_product.mpr
      constructor
      · change owner.1 = cell.1 + 1 at hx
        have hcell : cell.1 = owner.1 - 1 := by omega
        simp [hcell]
      · change owner.2 = cell.2 + 1 at hy
        have hcell : cell.2 = owner.2 - 1 := by omega
        simp [hcell]
  have hxcard : ({owner.1, owner.1 - 1} : Finset ℤ).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp
      omega
  have hycard : ({owner.2, owner.2 - 1} : Finset ℤ).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp
      omega
  calc
    _ ≤ candidates.card := Finset.card_le_card hsubset
    _ = ({owner.1, owner.1 - 1} : Finset ℤ).card *
        ({owner.2, owner.2 - 1} : Finset ℤ).card := by
      simp [candidates]
    _ ≤ 4 := by
      rw [hxcard, hycard]

/-- The actual finite set of owned grid cells classified as bad by the
closed-square Dai--Li interaction counter. -/
def daiLiBadGridCells
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) : Finset (ℤ × ℤ) :=
  (embedding.gridOccupiedCells w origin).filter fun cell =>
    IsBadInteractionSquare P embedding threshold d
      (daiLiGridCellCenter w origin cell) (w / 2)

@[simp]
theorem mem_daiLiBadGridCells_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    cell ∈ daiLiBadGridCells P embedding threshold d w origin ↔
      cell ∈ embedding.gridOccupiedCells w origin ∧
        IsBadInteractionSquare P embedding threshold d
          (daiLiGridCellCenter w origin cell) (w / 2) := by
  simp [daiLiBadGridCells]

/-- The concrete finite total of long-interaction incidences over all closed
grid-square witnesses. -/
def daiLiGridClosedTotalF
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w : ℝ)
    (origin : ℝ × ℝ) : Nat :=
  ∑ cell ∈ embedding.gridOccupiedCells w origin,
    regionInteractionCounter P embedding threshold
      (daiLiGridCellClosedQubits embedding w origin cell)

/-- The corresponding finite total restricted to actually bad grid cells. -/
def daiLiBadGridTotalF
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) : Nat :=
  ∑ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
    regionInteractionCounter P embedding threshold
      (daiLiGridCellClosedQubits embedding w origin cell)

theorem daiLiBadGridTotalF_le_daiLiGridClosedTotalF
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) :
    daiLiBadGridTotalF P embedding threshold d w origin ≤
      daiLiGridClosedTotalF P embedding threshold w origin := by
  unfold daiLiBadGridTotalF daiLiGridClosedTotalF
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro cell hcell
    exact (mem_daiLiBadGridCells_iff P embedding threshold d w origin cell).1 hcell |>.1
  · intro _ _ _
    exact Nat.zero_le _

/-- The closed-cell incidence total is at most four times the actual global
long-incidence total.  The factor is an exact finite boundary-overlap charge,
not an assumption that a periodic tiling has no boundary qubits. -/
theorem daiLiGridClosedTotalF_le_four_mul_globalCounter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) {w : ℝ}
    (hw : 0 < w) (origin : ℝ × ℝ) :
    daiLiGridClosedTotalF P embedding threshold w origin ≤
      4 * ∑ q : ι, P.daiLiInteractionCounter embedding threshold q := by
  classical
  let occupied := embedding.gridOccupiedCells w origin
  let counter := fun q : ι => P.daiLiInteractionCounter embedding threshold q
  have hswap :
      (∑ cell ∈ occupied,
        ∑ q ∈ daiLiGridCellClosedQubits embedding w origin cell, counter q) =
        ∑ q : ι, ∑ cell ∈ occupied,
          if q ∈ daiLiGridCellClosedQubits embedding w origin cell then counter q else 0 := by
    calc
      _ = ∑ cell ∈ occupied, ∑ q : ι,
          if q ∈ daiLiGridCellClosedQubits embedding w origin cell then counter q else 0 := by
        apply Finset.sum_congr rfl
        intro cell hcell
        rw [← Finset.sum_filter]
        simp
      _ = _ := Finset.sum_comm
  have hpoint : ∀ q : ι,
      (∑ cell ∈ occupied,
        if q ∈ daiLiGridCellClosedQubits embedding w origin cell then counter q else 0) ≤
          4 * counter q := by
    intro q
    have hcard :
        (daiLiGridClosedCellsContaining embedding w origin q).card ≤ 4 :=
      card_daiLiGridClosedCellsContaining_le_four embedding hw origin q
    calc
      _ = (daiLiGridClosedCellsContaining embedding w origin q).card * counter q := by
        rw [← Finset.sum_filter]
        simp [daiLiGridClosedCellsContaining, occupied]
      _ ≤ 4 * counter q := Nat.mul_le_mul_right _ hcard
  unfold daiLiGridClosedTotalF regionInteractionCounter
  change (∑ cell ∈ occupied,
    ∑ q ∈ daiLiGridCellClosedQubits embedding w origin cell, counter q) ≤ _
  rw [hswap, Finset.mul_sum]
  exact Finset.sum_le_sum fun q _ => hpoint q

/-- The bad-cell total inherits the same concrete global long-incidence bound. -/
theorem daiLiBadGridTotalF_le_four_mul_globalCounter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    {w : ℝ} (hw : 0 < w) (origin : ℝ × ℝ) :
    daiLiBadGridTotalF P embedding threshold d w origin ≤
      4 * ∑ q : ι, P.daiLiInteractionCounter embedding threshold q := by
  exact (daiLiBadGridTotalF_le_daiLiGridClosedTotalF
    P embedding threshold d w origin).trans
      (daiLiGridClosedTotalF_le_four_mul_globalCounter P embedding threshold hw origin)

/-- Every finite bad grid-cell family has the project-owned corrected
support-free subdivision.  The returned rectangle family is constructed by
#496; its factor-30 count is deliberately not attributed to DL24. -/
theorem exists_daiLiBadGridCellSubdivision
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold ell : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) (hEll : 0 < ell) (hHeight : 5 * ell ≤ w) :
    ∃ (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w origin cell).2 - w / 2)
          ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell)) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
          ((daiLiGridCellCenter w origin cell).1 - w / 2)
          ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell)) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        (rectangles cell).IsChain (fun first second => first.2.2 = second.1.2)) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        DaiLiPairwiseDisjointQubitRectangles embedding (rectangles cell)) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        daiLiRectangleQubitsCover embedding (rectangles cell) =
          daiLiGridCellClosedQubits embedding w origin cell) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        ∀ rectangle ∈ rectangles cell,
          5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
            (10 * regionInteractionCounter P embedding threshold
                (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
              rectangle.2.2 - rectangle.1.2 ≤ 10 * ell)) ∧
      (∑ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        (rectangles cell).length) * d ≤
          30 * daiLiBadGridTotalF P embedding threshold d w origin := by
  have hSquareHeight : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      5 * ell ≤ 2 * (w / 2) := by
    intro _ _
    linarith
  have hBad : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      IsBadInteractionSquare P embedding threshold d
        (daiLiGridCellCenter w origin cell) (w / 2) := by
    intro cell hcell
    exact (mem_daiLiBadGridCells_iff P embedding threshold d w origin cell).1 hcell |>.2
  rcases exists_daiLiBadInteractionSquareFamilySubdivision P embedding threshold ell d
      (daiLiBadGridCells P embedding threshold d w origin)
      (daiLiGridCellCenter w origin) (fun _ => w / 2) hEll hSquareHeight hBad with
    ⟨atoms, rectangles, hAtoms, hRectangles, hOrdered, hPairwise, hCover,
      hPieces, hCount⟩
  refine ⟨atoms, rectangles, hAtoms, hRectangles, hOrdered, hPairwise, ?_, hPieces, ?_⟩
  · intro cell hcell
    simpa [daiLiGridCellClosedQubits] using hCover cell hcell
  · simpa [daiLiBadGridTotalF, daiLiGridCellClosedQubits] using hCount

/-- Every #496 rectangle for a bad grid cell retains the exact horizontal
span of its parent grid square.  This is the width fact used by both the
short-rectangle packing recovery and its finite side-strip estimates. -/
theorem daiLiBadGridRectangle_horizontalSpan
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d
        (atoms cell))
    (cell : ℤ × ℤ) (hcell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (rectangle : (ℝ × ℝ) × (ℝ × ℝ)) (hrectangle : rectangle ∈ rectangles cell) :
    rectangle.2.1 - rectangle.1.1 = w := by
  rw [hRectangles cell hcell] at hrectangle
  rcases List.mem_map.mp hrectangle with ⟨piece, hpiece, rfl⟩
  simp [daiLiAtomGroupRectangle, daiLiGridCellCenter]

/-- Every atom of a finite Dai--Li atomization remains inside its declared
parent interval. -/
theorem DaiLiHorizontalAtomization.atom_bounds
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) (atom : ℝ × ℝ) (hAtom : atom ∈ atoms) :
    lower ≤ atom.1 ∧ atom.2 ≤ upper := by
  induction hAtoms generalizing atom with
  | single hHeight =>
      simp only [List.mem_singleton] at hAtom
      subst atom
      exact ⟨le_rfl, le_rfl⟩
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      simp only [List.mem_cons] at hAtom
      rcases hAtom with rfl | hAtom
      · have hCutUpper : cut ≤ upper := (hTail.lower_lt_upper hEll).le
        exact ⟨le_rfl, hCutUpper⟩
      · have hTailBounds := ih atom hAtom
        have hLowerCut : lower ≤ cut := by
          rcases hHeight with ⟨hMin, _⟩
          nlinarith
        exact ⟨hLowerCut.trans hTailBounds.1, hTailBounds.2⟩

/-- The span of any nonempty contiguous greedy atom group is bounded by the
span of its original atomized parent interval. -/
theorem DaiLiHorizontalAtomization.infix_span_le
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms group : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) (hGroup : group <:+: atoms) (hGroupNe : group ≠ []) :
    daiLiAtomGroupUpper group - daiLiAtomGroupLower group ≤ upper - lower := by
  have hHeadMem : group.head hGroupNe ∈ atoms := by
    rcases hGroup with ⟨before, after, hEq⟩
    rw [← hEq]
    simp
  have hLastMem : group.getLast hGroupNe ∈ atoms := by
    rcases hGroup with ⟨before, after, hEq⟩
    rw [← hEq]
    simp
  have hHeadBounds := hAtoms.atom_bounds hEll (group.head hGroupNe) hHeadMem
  have hLastBounds := hAtoms.atom_bounds hEll (group.getLast hGroupNe) hLastMem
  rw [daiLiAtomGroupLower_eq_head group hGroupNe,
    daiLiAtomGroupUpper_eq_getLast group hGroupNe]
  linarith

/-- The lower and upper coordinates of a nonempty contiguous atom group stay
inside the original atomized interval. -/
theorem DaiLiHorizontalAtomization.infix_bounds
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms group : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) (hGroup : group <:+: atoms) (hGroupNe : group ≠ []) :
    lower ≤ daiLiAtomGroupLower group ∧ daiLiAtomGroupUpper group ≤ upper := by
  have hHeadMem : group.head hGroupNe ∈ atoms := by
    rcases hGroup with ⟨before, after, hEq⟩
    rw [← hEq]
    simp
  have hLastMem : group.getLast hGroupNe ∈ atoms := by
    rcases hGroup with ⟨before, after, hEq⟩
    rw [← hEq]
    simp
  have hHeadBounds := hAtoms.atom_bounds hEll (group.head hGroupNe) hHeadMem
  have hLastBounds := hAtoms.atom_bounds hEll (group.getLast hGroupNe) hLastMem
  rw [daiLiAtomGroupLower_eq_head group hGroupNe,
    daiLiAtomGroupUpper_eq_getLast group hGroupNe]
  exact ⟨hHeadBounds.1, hLastBounds.2⟩

/-- Every actual greedy rectangle remains vertically inside its parent grid
cell.  This is the finite atom-chain fact needed to use one box-scale growth
and strip budget for all bad rectangles. -/
theorem daiLiBadGridRectangle_verticalSpan_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hcell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (rectangle : (ℝ × ℝ) × (ℝ × ℝ)) (hrectangle : rectangle ∈ rectangles cell) :
    rectangle.2.2 - rectangle.1.2 ≤ w := by
  rw [hRectangles cell hcell] at hrectangle
  rcases List.mem_map.mp hrectangle with ⟨piece, hpiece, rfl⟩
  have hAdmissible := daiLiPhysicalGreedySubdivision_admissible
    P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell) piece hpiece
  have hInfix := daiLiPhysicalGreedySubdivision_infix
    P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell) piece hpiece
  have hSpan := (hAtoms cell hcell).infix_span_le hEll hInfix hAdmissible.1
  simpa [daiLiAtomGroupRectangle, daiLiGridCellCenter] using hSpan

/-- The actual rectangle endpoints lie on or inside the endpoints of their
parent grid cell.  Horizontal endpoints agree exactly; vertical endpoints are
bounded by the atomized parent interval. -/
theorem daiLiBadGridRectangle_parentBounds
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hcell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (rectangle : (ℝ × ℝ) × (ℝ × ℝ)) (hrectangle : rectangle ∈ rectangles cell) :
    (gridCellLower w origin cell).1 = rectangle.1.1 ∧
      rectangle.2.1 = (gridCellUpper w origin cell).1 ∧
        (gridCellLower w origin cell).2 ≤ rectangle.1.2 ∧
          rectangle.2.2 ≤ (gridCellUpper w origin cell).2 := by
  rw [hRectangles cell hcell] at hrectangle
  rcases List.mem_map.mp hrectangle with ⟨piece, hpiece, rfl⟩
  have hAdmissible := daiLiPhysicalGreedySubdivision_admissible
    P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell) piece hpiece
  have hInfix := daiLiPhysicalGreedySubdivision_infix
    P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell) piece hpiece
  have hBounds := (hAtoms cell hcell).infix_bounds hEll hInfix hAdmissible.1
  constructor
  · simp [daiLiAtomGroupRectangle, gridCellLower, daiLiGridCellCenter]
    ring
  constructor
  · simp [daiLiAtomGroupRectangle, gridCellUpper, daiLiGridCellCenter]
    ring
  · constructor
    · change origin.2 + (cell.2 : ℝ) * w ≤ daiLiAtomGroupLower piece
      have hLower := hBounds.1
      simp [daiLiGridCellCenter] at hLower
      linarith
    · change daiLiAtomGroupUpper piece ≤ origin.2 + ((cell.2 : ℝ) + 1) * w
      have hUpper := hBounds.2
      simp [daiLiGridCellCenter] at hUpper
      linarith

/-- An ordered vertical rectangle chain becomes pairwise ordered once every
member has nonnegative height.  This is the list-level geometry behind the
strict `ell` cores of a bad-cell subdivision. -/
theorem daiLiRectangleList_pairwise_verticalOrder
    (rectangles : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hChain : rectangles.IsChain (fun first second => first.2.2 = second.1.2))
    (hNonnegative : ∀ rectangle ∈ rectangles,
      0 ≤ rectangle.2.2 - rectangle.1.2) :
    rectangles.Pairwise (fun first second => first.2.2 ≤ second.1.2) := by
  induction rectangles with
  | nil => simp
  | cons first rest ih =>
      cases rest with
      | nil => simp
      | cons second tail =>
          have hChainParts := List.isChain_cons_cons.mp hChain
          have hAdjacent : first.2.2 ≤ second.1.2 := hChainParts.1.le
          have hTailNonnegative : ∀ rectangle ∈ second :: tail,
              0 ≤ rectangle.2.2 - rectangle.1.2 := by
            intro rectangle hRectangle
            exact hNonnegative rectangle (by simp [hRectangle])
          have hTailPairwise := ih hChainParts.2 hTailNonnegative
          rw [List.pairwise_cons]
          constructor
          · intro rectangle hRectangle
            rcases List.mem_cons.mp hRectangle with rfl | hTailMember
            · exact hAdjacent
            · have hSecondHeight : 0 ≤ second.2.2 - second.1.2 :=
                hNonnegative second (by simp)
              have hSecondBefore : second.2.2 ≤ rectangle.1.2 :=
                (List.pairwise_cons.mp hTailPairwise).1 rectangle hTailMember
              linarith
          · exact hTailPairwise

/-- Earlier and later concrete #496 rectangle entries have vertically ordered
endpoints.  The statement uses natural list positions so it can be applied
directly to the finite `k >= d` region index. -/
theorem daiLiBadGridRectangle_get_verticalOrder
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hcell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (first second : ℕ) (hFirst : first < (rectangles cell).length)
    (hSecond : second < (rectangles cell).length) (hOrder : first < second) :
    ((rectangles cell).get ⟨first, hFirst⟩).2.2 ≤
      ((rectangles cell).get ⟨second, hSecond⟩).1.2 := by
  have hChain : (rectangles cell).IsChain (fun left right => left.2.2 = right.1.2) := by
    rw [hRectangles cell hcell]
    exact daiLiPhysicalGreedyRectangles_ordered P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) (hAtoms cell hcell) d
  have hNonnegative : ∀ rectangle ∈ rectangles cell,
      0 ≤ rectangle.2.2 - rectangle.1.2 := by
    intro rectangle hRectangle
    have hPhysical := hRectangle
    rw [hRectangles cell hcell] at hPhysical
    have hProperties := daiLiPhysicalGreedyRectangles_piece_properties P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) ell hEll
      (hAtoms cell hcell) d rectangle hPhysical
    linarith [hProperties.1]
  have hPairwise := daiLiRectangleList_pairwise_verticalOrder
    (rectangles cell) hChain hNonnegative
  exact hPairwise.rel_get_of_lt (show
    (⟨first, hFirst⟩ : Fin (rectangles cell).length) < ⟨second, hSecond⟩ from hOrder)

/-- A bad grid cell has at least one actual greedy rectangle. -/
theorem daiLiBadGridRectangle_length_pos
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (cell : ℤ × ℤ) (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w origin) :
    0 < (rectangles cell).length := by
  have hAtomsNonempty : atoms cell ≠ [] := by
    rcases (hAtoms cell hCell).starts_at with ⟨firstUpper, tail, hStarts⟩
    simp [hStarts]
  have hPhysicalNonempty : daiLiPhysicalGreedyRectangles P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell) ≠ [] := by
    intro hEmpty
    have hGroupsEmpty : daiLiPhysicalGreedySubdivision P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell) = [] := by
      simpa [daiLiPhysicalGreedyRectangles] using hEmpty
    have hJoin := daiLiPhysicalGreedySubdivision_join P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell)
    apply hAtomsNonempty
    simpa [hGroupsEmpty] using hJoin.symm
  by_contra hNotPositive
  have hLengthZero : (rectangles cell).length = 0 :=
    Nat.eq_zero_of_not_pos hNotPositive
  have hEmpty : rectangles cell = [] := by
    cases hList : rectangles cell with
    | nil => rfl
    | cons rectangle tail => simp [hList] at hLengthZero
  apply hPhysicalNonempty
  rw [← hRectangles cell hCell]
  exact hEmpty

/-- The first rectangle of a nonempty greedy subdivision starts at the
declared lower atomization endpoint. -/
theorem daiLiPhysicalGreedyRectangles_first_lower
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell lower upper : ℝ) (d : Nat)
    (atoms : List (ℝ × ℝ))
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hLength : 0 < (daiLiPhysicalGreedyRectangles P embedding threshold left right
      d atoms).length) :
    ((daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).get
      ⟨0, hLength⟩).1.2 = lower := by
  let groups := daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms
  have hGroupsNonempty : groups ≠ [] := by
    intro hEmpty
    have hRectanglesEmpty : daiLiPhysicalGreedyRectangles P embedding threshold left right
        d atoms = [] := by
      simp [daiLiPhysicalGreedyRectangles, groups, hEmpty]
    have hLengthZero : (daiLiPhysicalGreedyRectangles P embedding threshold left right
        d atoms).length = 0 := by simp [hRectanglesEmpty]
    exact (Nat.ne_of_gt hLength) hLengthZero
  cases hGroups : groups with
  | nil => exact (hGroupsNonempty hGroups).elim
  | cons first rest =>
      have hGroupValue : daiLiPhysicalGreedySubdivision P embedding threshold left right
          d atoms = first :: rest := by
        simpa [groups] using hGroups
      have hFirstNonempty : first ≠ [] := by
        exact (daiLiPhysicalGreedySubdivision_admissible P embedding threshold left right
          d atoms first (by rw [hGroupValue]; simp)).1
      cases hFirst : first with
      | nil => exact (hFirstNonempty hFirst).elim
      | cons head tail =>
          rcases hAtoms.starts_at with ⟨firstUpper, atomTail, hStarts⟩
          have hJoin := daiLiPhysicalGreedySubdivision_join P embedding threshold left right
            d atoms
          rw [hGroupValue] at hJoin
          have hHead : head = (lower, firstUpper) := by
            simpa [hFirst, hStarts] using congrArg List.head? hJoin
          simp [daiLiPhysicalGreedyRectangles, hGroupValue, hFirst,
            daiLiAtomGroupRectangle, daiLiAtomGroupLower, hHead]

/-- An atomization reaches its declared upper endpoint. -/
theorem daiLiHorizontalAtomization_last_upper
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hNonempty : atoms ≠ []) :
    (atoms.getLast hNonempty).2 = upper := by
  induction hAtoms with
  | single hHeight => simp
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      have hTailNonempty : tail ≠ [] := by
        rcases hTail.starts_at with ⟨firstUpper, rest, hStarts⟩
        simp [hStarts]
      simpa [List.getLast_cons hTailNonempty] using ih hTailNonempty

/-- The last rectangle of a nonempty greedy subdivision ends at the declared
upper atomization endpoint. -/
theorem daiLiPhysicalGreedyRectangles_last_upper
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell lower upper : ℝ) (d : Nat)
    (atoms : List (ℝ × ℝ))
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hNonempty : daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms ≠ []) :
    (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).getLast
      hNonempty |>.2.2 = upper := by
  let groups := daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms
  have hGroupsNonempty : groups ≠ [] := by
    intro hEmpty
    apply hNonempty
    simp [daiLiPhysicalGreedyRectangles, groups, hEmpty]
  have hAtomsNonempty : atoms ≠ [] := by
    rcases hAtoms.starts_at with ⟨firstUpper, tail, hStarts⟩
    simp [hStarts]
  have hFlattenNonempty : groups.flatten ≠ [] := by
    intro hEmpty
    apply hAtomsNonempty
    have hJoin := daiLiPhysicalGreedySubdivision_join P embedding threshold left right d atoms
    simpa [groups, hEmpty] using hJoin.symm
  have hLastGroupNonempty : groups.getLast hGroupsNonempty ≠ [] := by
    exact (daiLiPhysicalGreedySubdivision_admissible P embedding threshold left right d atoms
      (groups.getLast hGroupsNonempty) (List.getLast_mem hGroupsNonempty)).1
  have hLastAtom : (groups.getLast hGroupsNonempty).getLast hLastGroupNonempty =
      atoms.getLast hAtomsNonempty := by
    calc
      (groups.getLast hGroupsNonempty).getLast hLastGroupNonempty =
          groups.flatten.getLast hFlattenNonempty := by
            symm
            exact List.getLast_flatten_eq_getLast_getLast hFlattenNonempty hLastGroupNonempty
      _ = atoms.getLast hAtomsNonempty := by
        have hJoin := daiLiPhysicalGreedySubdivision_join P embedding threshold left right d atoms
        have hLastQuestion : groups.flatten.getLast? = atoms.getLast? := by
          simpa [groups] using congrArg List.getLast? hJoin
        simpa [List.getLast?_eq_getLast_of_ne_nil hFlattenNonempty,
          List.getLast?_eq_getLast_of_ne_nil hAtomsNonempty] using hLastQuestion
  have hLastGroupUpper : daiLiAtomGroupUpper (groups.getLast hGroupsNonempty) = upper := by
    rw [daiLiAtomGroupUpper_eq_getLast _ hLastGroupNonempty, hLastAtom]
    exact daiLiHorizontalAtomization_last_upper hAtoms hAtomsNonempty
  have hLastRectangle :
      (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).getLast
          hNonempty = daiLiAtomGroupRectangle left right (groups.getLast hGroupsNonempty) := by
    simp [daiLiPhysicalGreedyRectangles, groups]
  rw [hLastRectangle]
  simpa [daiLiAtomGroupRectangle] using hLastGroupUpper

/-- The first actual rectangle in a bad grid cell starts on that cell's lower
grid boundary. -/
theorem daiLiBadGridRectangle_first_lower_eq_parent
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (cell : ℤ × ℤ) (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (hLength : 0 < (rectangles cell).length) :
    ((rectangles cell).get ⟨0, hLength⟩).1.2 = (gridCellLower w origin cell).2 := by
  have hPhysicalLength : 0 < (daiLiPhysicalGreedyRectangles P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell)).length := by
    simpa [hRectangles cell hCell] using hLength
  have hFirst := daiLiPhysicalGreedyRectangles_first_lower P embedding threshold
    ((daiLiGridCellCenter w origin cell).1 - w / 2)
    ((daiLiGridCellCenter w origin cell).1 + w / 2) ell
    ((daiLiGridCellCenter w origin cell).2 - w / 2)
    ((daiLiGridCellCenter w origin cell).2 + w / 2) d (atoms cell)
    (hAtoms cell hCell) hPhysicalLength
  have hGetQuestion := congrArg (fun list => list[0]?) (hRectangles cell hCell)
  have hGet : (rectangles cell).get ⟨0, hLength⟩ =
      (daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell)).get
          ⟨0, hPhysicalLength⟩ := by
    apply Option.some.inj
    calc
      some ((rectangles cell).get ⟨0, hLength⟩) = (rectangles cell)[0]? := by
        symm
        exact List.getElem?_eq_getElem hLength
      _ = (daiLiPhysicalGreedyRectangles P embedding threshold
          ((daiLiGridCellCenter w origin cell).1 - w / 2)
          ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))[0]? :=
        hGetQuestion
      _ = some ((daiLiPhysicalGreedyRectangles P embedding threshold
          ((daiLiGridCellCenter w origin cell).1 - w / 2)
          ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell)).get
            ⟨0, hPhysicalLength⟩) :=
        List.getElem?_eq_getElem hPhysicalLength
  have hFirst' : ((rectangles cell).get ⟨0, hLength⟩).1.2 =
      (daiLiGridCellCenter w origin cell).2 - w / 2 := by
    rw [hGet]
    exact hFirst
  calc
    _ = (daiLiGridCellCenter w origin cell).2 - w / 2 := hFirst'
    _ = (gridCellLower w origin cell).2 := by
      simp [gridCellLower, daiLiGridCellCenter]
      ring

/-- The final actual rectangle in a bad grid cell ends on that cell's upper
grid boundary. -/
theorem daiLiBadGridRectangle_last_upper_eq_parent
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (cell : ℤ × ℤ) (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (slot : ℕ) (hSlot : slot < (rectangles cell).length)
    (hLast : slot + 1 = (rectangles cell).length) :
    ((rectangles cell).get ⟨slot, hSlot⟩).2.2 = (gridCellUpper w origin cell).2 := by
  let physical := daiLiPhysicalGreedyRectangles P embedding threshold
    ((daiLiGridCellCenter w origin cell).1 - w / 2)
    ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell)
  have hPhysicalSlot : slot < physical.length := by
    simpa [physical, hRectangles cell hCell] using hSlot
  have hPhysicalLast : slot + 1 = physical.length := by
    simpa [physical, hRectangles cell hCell] using hLast
  have hPhysicalNonempty : physical ≠ [] := by
    intro hEmpty
    have hLengthZero : physical.length = 0 := by simp [hEmpty]
    omega
  have hLastPhysical := daiLiPhysicalGreedyRectangles_last_upper P embedding threshold
    ((daiLiGridCellCenter w origin cell).1 - w / 2)
    ((daiLiGridCellCenter w origin cell).1 + w / 2) ell
    ((daiLiGridCellCenter w origin cell).2 - w / 2)
    ((daiLiGridCellCenter w origin cell).2 + w / 2) d (atoms cell)
    (hAtoms cell hCell) hPhysicalNonempty
  have hSlotSub : slot = physical.length - 1 := by omega
  have hMinus : physical.length - 1 < physical.length := by
    have : 0 < physical.length := Nat.zero_lt_of_lt hPhysicalSlot
    omega
  have hGetLast : physical.get ⟨slot, hPhysicalSlot⟩ = physical.getLast hPhysicalNonempty := by
    simpa [hSlotSub] using List.get_length_sub_one (l := physical) hMinus
  have hGetQuestion := congrArg (fun list => list[slot]?) (hRectangles cell hCell)
  have hGet : (rectangles cell).get ⟨slot, hSlot⟩ =
      physical.get ⟨slot, hPhysicalSlot⟩ := by
    apply Option.some.inj
    calc
      some ((rectangles cell).get ⟨slot, hSlot⟩) = (rectangles cell)[slot]? := by
        symm
        exact List.getElem?_eq_getElem hSlot
      _ = physical[slot]? := by simpa [physical] using hGetQuestion
      _ = some (physical.get ⟨slot, hPhysicalSlot⟩) :=
        List.getElem?_eq_getElem hPhysicalSlot
  calc
    ((rectangles cell).get ⟨slot, hSlot⟩).2.2 =
        (physical.get ⟨slot, hPhysicalSlot⟩).2.2 := by rw [hGet]
    _ = (physical.getLast hPhysicalNonempty).2.2 := by rw [hGetLast]
    _ = (daiLiGridCellCenter w origin cell).2 + w / 2 := hLastPhysical
    _ = (gridCellUpper w origin cell).2 := by
      simp [gridCellUpper, daiLiGridCellCenter]
      ring

/-- Consecutive actual bad-rectangle entries meet exactly at their shared
horizontal cut. -/
theorem daiLiBadGridRectangle_adjacent_verticalBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (cell : ℤ × ℤ) (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (slot : ℕ) (hSlot : slot < (rectangles cell).length)
    (hNext : slot + 1 < (rectangles cell).length) :
    ((rectangles cell).get ⟨slot, hSlot⟩).2.2 =
      ((rectangles cell).get ⟨slot + 1, hNext⟩).1.2 := by
  have hChain : (rectangles cell).IsChain (fun first second => first.2.2 = second.1.2) := by
    rw [hRectangles cell hCell]
    exact daiLiPhysicalGreedyRectangles_ordered P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) (hAtoms cell hCell) d
  rw [List.isChain_iff_getElem] at hChain
  simpa using hChain slot hNext

/-- A nonempty constructed bad-grid subdivision carries the exact bad-square
counter lower bound needed for its integer count handoff. -/
theorem daiLiBadGridCellSubdivision_empty_or_total_lower
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    (∑ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      (rectangles cell).length) = 0 ∨
      d ≤ 10 * daiLiBadGridTotalF P embedding threshold d w origin := by
  apply daiLiBadInteractionSquareFamily_empty_or_total_lower P embedding threshold d
    (daiLiBadGridCells P embedding threshold d w origin)
    (daiLiGridCellCenter w origin) (fun _ => w / 2) rectangles
  intro cell hcell
  exact (mem_daiLiBadGridCells_iff P embedding threshold d w origin cell).1 hcell |>.2

/-- The four geometric corners of one actual horizontal Dai--Li rectangle. -/
def daiLiRectangleVertex (rectangle : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 4 → ℝ × ℝ
  | 0 => rectangle.1
  | 1 => (rectangle.1.1, rectangle.2.2)
  | 2 => (rectangle.2.1, rectangle.1.2)
  | 3 => rectangle.2

/-- A finite index for every vertex of every constructed bad rectangle. -/
abbrev DaiLiBadGridRectangleVertexIndex
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :=
  Σ cell : {cell // cell ∈ cells}, Σ _ : Fin (rectangles cell).length, Fin 4

/-- The actual vertex point carried by a finite bad-rectangle vertex index. -/
def daiLiBadGridRectangleVertexPoint
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    DaiLiBadGridRectangleVertexIndex cells rectangles → ℝ × ℝ
  | ⟨cell, rectangle, vertex⟩ =>
      daiLiRectangleVertex (rectangles cell.1)[rectangle] vertex

/-- Actual qubits in the closed `2 * ell` square around a constructed
bad-rectangle vertex. -/
def daiLiVertexNeighborhoodQubits (embedding : UnitSeparatedEmbedding2D ι)
    (ell : ℝ) (vertex : ℝ × ℝ) : Finset ι :=
  embedding.qubitsInRectangle (vertex.1 - 2 * ell, vertex.2 - 2 * ell)
    (vertex.1 + 2 * ell, vertex.2 + 2 * ell)

/-- The finite, concrete bad-rectangle vertex component of the Dai--Li
separator. -/
def daiLiBadGridRectangleVertexBuffer
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ)
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : Finset ι :=
  Finset.univ.biUnion fun vertex : DaiLiBadGridRectangleVertexIndex cells rectangles =>
    daiLiVertexNeighborhoodQubits embedding ell
      (daiLiBadGridRectangleVertexPoint cells rectangles vertex)

/-- Every vertex neighborhood of an actual indexed bad-grid rectangle occurs
in the concrete finite rectangle-vertex component of the source separator. -/
theorem daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ)
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (hCell : cell ∈ cells) (slot : ℕ)
    (hSlot : slot < (rectangles cell).length) (vertex : Fin 4) :
    daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex ((rectangles cell).get ⟨slot, hSlot⟩) vertex) ⊆
      daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles := by
  intro q hq
  unfold daiLiBadGridRectangleVertexBuffer
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨⟨cell, hCell⟩, ⟨⟨slot, hSlot⟩, vertex⟩⟩, Finset.mem_univ _, ?_⟩
  simpa [daiLiBadGridRectangleVertexPoint] using hq

/-- Membership in the finite cover of actual rectangles has a concrete
rectangle-list witness. -/
theorem mem_daiLiRectangleQubitsCover_iff
    (embedding : UnitSeparatedEmbedding2D ι)
    (rectangles : List ((ℝ × ℝ) × (ℝ × ℝ))) (q : ι) :
    q ∈ daiLiRectangleQubitsCover embedding rectangles ↔
      ∃ rectangle ∈ rectangles,
        q ∈ embedding.qubitsInRectangle rectangle.1 rectangle.2 := by
  induction rectangles with
  | nil => simp [daiLiRectangleQubitsCover]
  | cons rectangle rectangles ih =>
      constructor
      · intro hq
        simp only [daiLiRectangleQubitsCover, List.foldr_cons, Finset.mem_union] at hq
        rcases hq with hq | hq
        · exact ⟨rectangle, by simp, hq⟩
        · rcases ih.mp hq with ⟨other, hOther, hqOther⟩
          exact ⟨other, by simp [hOther], hqOther⟩
      · rintro ⟨other, hOther, hqOther⟩
        simp only [daiLiRectangleQubitsCover, List.foldr_cons, Finset.mem_union]
        rcases List.mem_cons.mp hOther with rfl | hOther
        · exact Or.inl hqOther
        · exact Or.inr (ih.mpr ⟨other, hOther, hqOther⟩)

/-- A point of one actual rectangle which avoids all four `2 * ell` vertex
neighborhoods lies either in its strict core or in one of the four concrete
source side strips.  This is the local geometric assignment used for the
finite `k >= d` partition. -/
theorem daiLiRectanglePoint_vertex_or_strictCore_or_side
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (hEll : 0 < ell)
    (lower upper : ℝ × ℝ) (q : ι)
    (hq : q ∈ embedding.qubitsInRectangle lower upper) :
    (∃ vertex : Fin 4,
      q ∈ daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex (lower, upper) vertex)) ∨
      (lower.1 + ell < (embedding.point q).1 ∧
        (embedding.point q).1 < upper.1 - ell ∧
          lower.2 + ell < (embedding.point q).2 ∧
            (embedding.point q).2 < upper.2 - ell) ∨
      ∃ side : Fin 4,
        q ∈ daiLiRectangleSideStripQubits embedding ell lower upper side := by
  by_cases hVertex : ∃ vertex : Fin 4,
      q ∈ daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex (lower, upper) vertex)
  · exact Or.inl hVertex
  apply Or.inr
  have hNoVertex : ∀ vertex : Fin 4,
      q ∉ daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex (lower, upper) vertex) := by
    intro vertex hqVertex
    exact hVertex ⟨vertex, hqVertex⟩
  rw [UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
  by_cases hxLower : (embedding.point q).1 ≤ lower.1 + ell
  · apply Or.inr
    refine ⟨0, ?_⟩
    have hyLower : lower.2 + 2 * ell ≤ (embedding.point q).2 := by
      by_contra hnot
      have hy : (embedding.point q).2 < lower.2 + 2 * ell := lt_of_not_ge hnot
      apply hNoVertex 0
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hq.1.1], by nlinarith [hxLower]⟩,
        ⟨by nlinarith [hq.2.1], by nlinarith⟩⟩
    have hyUpper : (embedding.point q).2 ≤ upper.2 - 2 * ell := by
      by_contra hnot
      have hy : upper.2 - 2 * ell < (embedding.point q).2 := lt_of_not_ge hnot
      apply hNoVertex 1
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hq.1.1], by nlinarith [hxLower]⟩,
        ⟨by nlinarith, by nlinarith [hq.2.2]⟩⟩
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨by nlinarith [hq.1.1], hxLower⟩, ⟨hyLower, hyUpper⟩⟩
  have hxLower' : lower.1 + ell < (embedding.point q).1 := lt_of_not_ge hxLower
  by_cases hxUpper : upper.1 - ell ≤ (embedding.point q).1
  · apply Or.inr
    refine ⟨1, ?_⟩
    have hyLower : lower.2 + 2 * ell ≤ (embedding.point q).2 := by
      by_contra hnot
      have hy : (embedding.point q).2 < lower.2 + 2 * ell := lt_of_not_ge hnot
      apply hNoVertex 2
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hxUpper], by nlinarith [hq.1.2]⟩,
        ⟨by nlinarith [hq.2.1], by nlinarith⟩⟩
    have hyUpper : (embedding.point q).2 ≤ upper.2 - 2 * ell := by
      by_contra hnot
      have hy : upper.2 - 2 * ell < (embedding.point q).2 := lt_of_not_ge hnot
      apply hNoVertex 3
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hxUpper], by nlinarith [hq.1.2]⟩,
        ⟨by nlinarith, by nlinarith [hq.2.2]⟩⟩
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxUpper, by nlinarith [hq.1.2]⟩, ⟨hyLower, hyUpper⟩⟩
  have hxUpper' : (embedding.point q).1 < upper.1 - ell := lt_of_not_ge hxUpper
  by_cases hyLower : (embedding.point q).2 ≤ lower.2 + ell
  · apply Or.inr
    refine ⟨2, ?_⟩
    have hxLeft : lower.1 + 2 * ell ≤ (embedding.point q).1 := by
      by_contra hnot
      have hx : (embedding.point q).1 < lower.1 + 2 * ell := lt_of_not_ge hnot
      apply hNoVertex 0
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hq.1.1], by nlinarith⟩,
        ⟨by nlinarith [hq.2.1], by nlinarith [hyLower]⟩⟩
    have hxRight : (embedding.point q).1 ≤ upper.1 - 2 * ell := by
      by_contra hnot
      have hx : upper.1 - 2 * ell < (embedding.point q).1 := lt_of_not_ge hnot
      apply hNoVertex 2
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith, by nlinarith [hq.1.2]⟩,
        ⟨by nlinarith [hq.2.1], by nlinarith [hyLower]⟩⟩
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxLeft, hxRight⟩, ⟨by nlinarith [hq.2.1], hyLower⟩⟩
  have hyLower' : lower.2 + ell < (embedding.point q).2 := lt_of_not_ge hyLower
  by_cases hyUpper : upper.2 - ell ≤ (embedding.point q).2
  · apply Or.inr
    refine ⟨3, ?_⟩
    have hxLeft : lower.1 + 2 * ell ≤ (embedding.point q).1 := by
      by_contra hnot
      have hx : (embedding.point q).1 < lower.1 + 2 * ell := lt_of_not_ge hnot
      apply hNoVertex 1
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hq.1.1], by nlinarith⟩,
        ⟨by nlinarith [hyUpper], by nlinarith [hq.2.2]⟩⟩
    have hxRight : (embedding.point q).1 ≤ upper.1 - 2 * ell := by
      by_contra hnot
      have hx : upper.1 - 2 * ell < (embedding.point q).1 := lt_of_not_ge hnot
      apply hNoVertex 3
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith, by nlinarith [hq.1.2]⟩,
        ⟨by nlinarith [hyUpper], by nlinarith [hq.2.2]⟩⟩
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxLeft, hxRight⟩, ⟨hyUpper, by nlinarith [hq.2.2]⟩⟩
  exact Or.inl ⟨hxLower', hxUpper', hyLower', lt_of_not_ge hyUpper⟩

/-- An atomization reaches its declared upper endpoint. -/
theorem DaiLiHorizontalAtomization.ends_at
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hNonempty : atoms ≠ []) :
    (atoms.getLast hNonempty).2 = upper := by
  induction hAtoms with
  | single hHeight => simp
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      have hTailNonempty : tail ≠ [] := by
        rcases hTail.starts_at with ⟨firstUpper, rest, hStarts⟩
        simp [hStarts]
      simpa [List.getLast_cons hTailNonempty] using ih hTailNonempty

theorem card_daiLiBadGridRectangleVertexIndex
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Fintype.card (DaiLiBadGridRectangleVertexIndex cells rectangles) =
      4 * ∑ cell ∈ cells, (rectangles cell).length := by
  calc
    Fintype.card (DaiLiBadGridRectangleVertexIndex cells rectangles) =
        ∑ cell : {cell // cell ∈ cells}, (rectangles cell).length * 4 := by
      simp [Fintype.card_sigma]
    _ = ∑ cell ∈ cells, (rectangles cell).length * 4 := by
      symm
      exact Finset.sum_subtype cells (fun _ => Iff.rfl) _
    _ = 4 * ∑ cell ∈ cells, (rectangles cell).length := by
      rw [← Finset.sum_mul]
      ring

/-- Packing controls each actual `2 * ell` vertex neighborhood by the
source's `96 * ell^2` local term. -/
theorem card_daiLiVertexNeighborhoodQubits_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (hEll : 1 ≤ ell)
    (vertex : ℝ × ℝ) :
    ((daiLiVertexNeighborhoodQubits embedding ell vertex).card : ℝ) ≤
      96 * ell ^ 2 := by
  have hwidth : 1 ≤ (vertex.1 + 2 * ell) - (vertex.1 - 2 * ell) := by
    linarith
  have hheight : 1 ≤ (vertex.2 + 2 * ell) - (vertex.2 - 2 * ell) := by
    linarith
  have hPacking := embedding.card_qubitsInRectangle_le_six_mul_area
    (vertex.1 - 2 * ell, vertex.2 - 2 * ell)
    (vertex.1 + 2 * ell, vertex.2 + 2 * ell) hwidth hheight
  simpa [daiLiVertexNeighborhoodQubits] using (hPacking.trans_eq (by ring))

/-- The explicit finite bad-rectangle vertex buffer obeys the exact
`384 * ell^2 * M` packing charge. -/
theorem card_daiLiBadGridRectangleVertexBuffer_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (hEll : 1 ≤ ell)
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) ≤
      384 * ell ^ 2 *
        ((∑ cell ∈ cells, (rectangles cell).length : Nat) : ℝ) := by
  have hUnion :
      (daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card ≤
        ∑ vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
          (daiLiVertexNeighborhoodQubits embedding ell
            (daiLiBadGridRectangleVertexPoint cells rectangles vertex)).card := by
    exact Finset.card_biUnion_le
  have hEach : ∀ vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
      ((daiLiVertexNeighborhoodQubits embedding ell
        (daiLiBadGridRectangleVertexPoint cells rectangles vertex)).card : ℝ) ≤
        96 * ell ^ 2 := by
    intro vertex
    exact card_daiLiVertexNeighborhoodQubits_le embedding ell hEll _
  have hUnionReal :
      ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) ≤
        ∑ vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
          ((daiLiVertexNeighborhoodQubits embedding ell
            (daiLiBadGridRectangleVertexPoint cells rectangles vertex)).card : ℝ) := by
    exact_mod_cast hUnion
  calc
    _ ≤ ∑ vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
        ((daiLiVertexNeighborhoodQubits embedding ell
          (daiLiBadGridRectangleVertexPoint cells rectangles vertex)).card : ℝ) := hUnionReal
    _ ≤ ∑ _vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
        96 * ell ^ 2 := by
      apply Finset.sum_le_sum
      intro vertex _
      exact hEach vertex
    _ = 96 * ell ^ 2 *
        Fintype.card (DaiLiBadGridRectangleVertexIndex cells rectangles) := by
      rw [Finset.sum_const, Finset.card_univ]
      ring
    _ = 384 * ell ^ 2 *
        ((∑ cell ∈ cells, (rectangles cell).length : Nat) : ℝ) := by
      rw [card_daiLiBadGridRectangleVertexIndex]
      norm_num
      ring

/-- The concrete `C` region in the `k >= d` branch: selected grid vertices,
all actual long-interaction endpoints, and the vertices created by the
project-owned bad-square subdivision. -/
def daiLiKGeDSeparator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : Finset ι :=
  gridVertexBufferQubits embedding w ell t ∪
    longInteractionEndpointQubits P embedding threshold ∪
      daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles

/-- The `k >= d` separator has a concrete componentwise cardinality estimate.
The first term is exactly the selected grid-vertex count, the second is the
actual global long-endpoint count, and the third is the constructed rectangle
vertex charge. -/
theorem card_daiLiKGeDSeparator_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ((daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
          ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) := by
  have hUnion :
      (daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card ≤
        (gridVertexBufferQubits embedding w ell t).card +
          (longInteractionEndpointQubits P embedding threshold).card +
            (daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card := by
    unfold daiLiKGeDSeparator
    calc
      _ ≤ (gridVertexBufferQubits embedding w ell t ∪
          longInteractionEndpointQubits P embedding threshold).card +
            (daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card :=
        Finset.card_union_le _ _
      _ ≤ ((gridVertexBufferQubits embedding w ell t).card +
          (longInteractionEndpointQubits P embedding threshold).card) +
            (daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by omega
  have hEndpoints := card_longInteractionEndpointQubits_le_sum_counter
    P embedding threshold
  have hVertex :
      (gridVertexBufferQubits embedding w ell t).card =
        vertexBadCount w (2 * ell) embedding.point t := by
    rfl
  have hUnionReal :
      ((daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card : ℝ) ≤
        ((gridVertexBufferQubits embedding w ell t).card : ℝ) +
          ((longInteractionEndpointQubits P embedding threshold).card : ℝ) +
            ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) := by
    exact_mod_cast hUnion
  calc
    _ ≤ ((gridVertexBufferQubits embedding w ell t).card : ℝ) +
          ((longInteractionEndpointQubits P embedding threshold).card : ℝ) +
            ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) :=
      hUnionReal
    _ ≤ (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
          (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
            ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) := by
      have hEndpointsReal :
          ((longInteractionEndpointQubits P embedding threshold).card : ℝ) ≤
            ∑ q : ι, P.daiLiInteractionCounter embedding threshold q := by
        exact_mod_cast hEndpoints
      rw [hVertex]
      linarith

/-- The finite fourfold closed-cell boundary charge preserves a quantitative
bad-rectangle vertex estimate.  `960` is a Lean-QEC conservative witness:
it comes from the proved factor-30 subdivision and the explicit overlap
factor four, not from a constant asserted in DL24. -/
theorem daiLiFourOverlapBadRectangleVertexTerm_le
    (M badTotalF globalTotalF d k : Nat) (ell : ℝ)
    (hD : 0 < d) (hCount : M * d ≤ 30 * badTotalF)
    (hOverlap : badTotalF ≤ 4 * globalTotalF)
    (hGlobal : 50 * globalTotalF ≤ k) :
    384 * ell ^ 2 * (M : ℝ) ≤ 960 * ell ^ 2 * (k : ℝ) / (d : ℝ) := by
  have hDReal : (0 : ℝ) < d := by exact_mod_cast hD
  have hCountReal : (M : ℝ) * d ≤ 30 * badTotalF := by exact_mod_cast hCount
  have hOverlapReal : (badTotalF : ℝ) ≤ 4 * globalTotalF := by exact_mod_cast hOverlap
  have hGlobalReal : (50 : ℝ) * globalTotalF ≤ k := by exact_mod_cast hGlobal
  have hScaled : (384 : ℝ) * M * d ≤ 960 * k := by
    nlinarith
  have hBase : (384 : ℝ) * M ≤ 960 * k / d := by
    exact (le_div_iff₀ hDReal).2 (by simpa [mul_assoc] using hScaled)
  have hEllSq : 0 ≤ ell ^ 2 := sq_nonneg ell
  calc
    384 * ell ^ 2 * (M : ℝ) = ell ^ 2 * (384 * M) := by ring
    _ ≤ ell ^ 2 * (960 * k / d) := mul_le_mul_of_nonneg_left hBase hEllSq
    _ = 960 * ell ^ 2 * (k : ℝ) / (d : ℝ) := by ring

/-- Combining the actual separator components with the constructed subdivision
gives a source-routed `C` estimate.  The only long-interaction input is the
actual global endpoint-incidence total; no interaction lower bound is assumed. -/
theorem card_daiLiKGeDSeparator_le_conservative
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (d k : Nat) (hEll : 1 ≤ ell) (hD : 0 < d)
    (hCount : (∑ cell ∈ cells, (rectangles cell).length) * d ≤
      30 * daiLiBadGridTotalF P embedding threshold d w (gridOrigin w t))
    (hOverlap : daiLiBadGridTotalF P embedding threshold d w (gridOrigin w t) ≤
      4 * ∑ q : ι, P.daiLiInteractionCounter embedding threshold q)
    (hGlobal : 50 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) ≤ k) :
    ((daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
          960 * ell ^ 2 * (k : ℝ) / (d : ℝ) := by
  let M : Nat := ∑ cell ∈ cells, (rectangles cell).length
  let globalTotalF : Nat := ∑ q : ι, P.daiLiInteractionCounter embedding threshold q
  have hBuffer := card_daiLiBadGridRectangleVertexBuffer_le embedding ell hEll
    cells rectangles
  have hBuffer' :
      ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) ≤
        384 * ell ^ 2 * (M : ℝ) := by
    simpa [M] using hBuffer
  have hRectangleTerm :
      384 * ell ^ 2 * (M : ℝ) ≤ 960 * ell ^ 2 * (k : ℝ) / (d : ℝ) := by
    apply daiLiFourOverlapBadRectangleVertexTerm_le M
      (daiLiBadGridTotalF P embedding threshold d w (gridOrigin w t)) globalTotalF d k ell hD
    · simpa [M] using hCount
    · simpa [globalTotalF] using hOverlap
    · simpa [globalTotalF] using hGlobal
  calc
    _ ≤ (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
          ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) :=
      card_daiLiKGeDSeparator_le P embedding threshold w ell t cells rectangles
    _ ≤ (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
          384 * ell ^ 2 * (M : ℝ) := by
      linarith
    _ ≤ _ := by gcongr

/-! ## Finite grid-side and vertex geometry

The periodic translation is used only to obtain small averaged counts.  The
partition itself is indexed by concrete integer grid lines around the finitely
many occupied cells.  This avoids treating the torus quotient as a physical
partition of the plane.
-/

/-- A finite grid-side index.  `true` denotes a vertical grid-line segment
and `false` a horizontal segment.  The two integer coordinates name the
supporting line and the unit-length grid interval along it. -/
abbrev DaiLiGridSideIndex := ℤ × ℤ × Bool

/-- The concrete rectangular strip around a finite segment of a vertical or
horizontal grid line.  The two endpoint vertex neighborhoods have width
`2 * vertexRadius` independently of the edge half-width. -/
def daiLiGridSideStripQubits (embedding : UnitSeparatedEmbedding2D ι)
    (w edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ)
    (side : DaiLiGridSideIndex) : Finset ι :=
  if side.2.2 then
    embedding.qubitsInRectangle
      (origin.1 + (side.1 : ℝ) * w - edgeRadius,
        origin.2 + (side.2.1 : ℝ) * w + vertexRadius)
      (origin.1 + (side.1 : ℝ) * w + edgeRadius,
        origin.2 + ((side.2.1 : ℝ) + 1) * w - vertexRadius)
  else
    embedding.qubitsInRectangle
      (origin.1 + (side.1 : ℝ) * w + vertexRadius,
        origin.2 + (side.2.1 : ℝ) * w - edgeRadius)
      (origin.1 + ((side.1 : ℝ) + 1) * w - vertexRadius,
        origin.2 + (side.2.1 : ℝ) * w + edgeRadius)

def daiLiGridSideStripSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (w edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ)
    (side : DaiLiGridSideIndex) : FiniteSubsystem ι :=
  ⟨daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side⟩

/-- The finite candidate side family generated by each occupied cell's four
grid-line sides.  A physical line segment has a canonical integer index, so
shared cell sides do not duplicate a component. -/
def daiLiGridSideCandidates (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) : Finset DaiLiGridSideIndex := by
  classical
  exact (embedding.gridOccupiedCells w origin).biUnion fun cell =>
    {(cell.1, cell.2, true), (cell.1 + 1, cell.2, true),
      (cell.1, cell.2, false), (cell.1, cell.2 + 1, false)}

/-- The finite candidate vertices generated by the corners of occupied cells. -/
def daiLiGridVertexCandidates (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (embedding.gridOccupiedCells w origin).biUnion fun cell =>
    {(cell.1, cell.2), (cell.1 + 1, cell.2),
      (cell.1, cell.2 + 1), (cell.1 + 1, cell.2 + 1)}

/-- The actual finite vertex buffer used by the concrete grid partition. -/
def daiLiFiniteGridVertexBuffer (embedding : UnitSeparatedEmbedding2D ι)
    (w ell : ℝ) (origin : ℝ × ℝ) : Finset ι :=
  (daiLiGridVertexCandidates embedding w origin).biUnion fun vertex =>
    daiLiVertexNeighborhoodQubits embedding ell
      (origin.1 + (vertex.1 : ℝ) * w, origin.2 + (vertex.2 : ℝ) * w)

/-- A finite Euclidean vertex neighborhood is contained in the periodic
vertex event for the same translated grid.  Thus the actual partition can use
the #385 averaged count without quotient-space boundary assumptions. -/
theorem daiLiVertexNeighborhood_subset_gridVertexBuffer
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (ell : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) (vertex : ℤ × ℤ) :
    daiLiVertexNeighborhoodQubits embedding ell
      (origin.1 + (vertex.1 : ℝ) * w, origin.2 + (vertex.2 : ℝ) * w) ⊆
      gridVertexBufferQubits embedding w ell t := by
  intro q hq
  rw [daiLiVertexNeighborhoodQubits,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
  have htX : t.1 = (origin.1 : AddCircle w) := by
    have := congrArg Prod.fst ht
    simpa [phase] using this.symm
  have htY : t.2 = (origin.2 : AddCircle w) := by
    have := congrArg Prod.snd ht
    simpa [phase] using this.symm
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold vertexBad
  constructor
  · rw [htX]
    have hperiod :
        ((origin.1 + (vertex.1 : ℝ) * w : ℝ) : AddCircle w) =
          (origin.1 : AddCircle w) :=
      addCircle_coe_add_int_mul_period w origin.1 vertex.1
    calc
      dist (origin.1 : AddCircle w) (phase w (embedding.point q)).1 ≤
          |(embedding.point q).1 - origin.1 - (vertex.1 : ℝ) * w| := by
        have hdist := addCircle_dist_le_abs_sub w
          (origin.1 + (vertex.1 : ℝ) * w) (embedding.point q).1 hw
        rw [hperiod] at hdist
        simp only [sub_add_eq_sub_sub] at hdist
        exact hdist
      _ ≤ 2 * ell := by
        rw [abs_le]
        constructor <;> nlinarith [hq.1.1, hq.1.2]
  · rw [htY]
    have hperiod :
        ((origin.2 + (vertex.2 : ℝ) * w : ℝ) : AddCircle w) =
          (origin.2 : AddCircle w) :=
      addCircle_coe_add_int_mul_period w origin.2 vertex.2
    calc
      dist (origin.2 : AddCircle w) (phase w (embedding.point q)).2 ≤
          |(embedding.point q).2 - origin.2 - (vertex.2 : ℝ) * w| := by
        have hdist := addCircle_dist_le_abs_sub w
          (origin.2 + (vertex.2 : ℝ) * w) (embedding.point q).2 hw
        rw [hperiod] at hdist
        simp only [sub_add_eq_sub_sub] at hdist
        exact hdist
      _ ≤ 2 * ell := by
        rw [abs_le]
        constructor <;> nlinarith [hq.2.1, hq.2.2]

/-- The full finite vertex buffer is counted by the selected periodic vertex
event. -/
theorem daiLiFiniteGridVertexBuffer_subset_gridVertexBuffer
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (ell : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) :
    daiLiFiniteGridVertexBuffer embedding w ell origin ⊆
      gridVertexBufferQubits embedding w ell t := by
  intro q hq
  rcases Finset.mem_biUnion.mp hq with ⟨vertex, hvertex, hqVertex⟩
  exact daiLiVertexNeighborhood_subset_gridVertexBuffer embedding hw ell origin t ht
    vertex hqVertex

/-- The finite union of actual side-strip rectangles around occupied cells. -/
def daiLiFiniteGridSideBuffer (embedding : UnitSeparatedEmbedding2D ι)
    (w edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ) : Finset ι :=
  (daiLiGridSideCandidates embedding w origin).biUnion fun side =>
    daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side

/-- Every concrete vertical or horizontal grid-side strip has the expected
area packing estimate. -/
theorem card_daiLiGridSideStrip_le
    (embedding : UnitSeparatedEmbedding2D ι) (w edgeRadius vertexRadius : ℝ)
    (origin : ℝ × ℝ) (side : DaiLiGridSideIndex)
    (hEdge : 1 ≤ 2 * edgeRadius) (hLong : 1 ≤ w - 2 * vertexRadius) :
    ((daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side).card : ℝ) ≤
      12 * edgeRadius * (w - 2 * vertexRadius) := by
  by_cases hVertical : side.2.2
  · rw [daiLiGridSideStripQubits, if_pos hVertical]
    have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (origin.1 + (side.1 : ℝ) * w - edgeRadius,
        origin.2 + (side.2.1 : ℝ) * w + vertexRadius)
      (origin.1 + (side.1 : ℝ) * w + edgeRadius,
        origin.2 + ((side.2.1 : ℝ) + 1) * w - vertexRadius)
      (by linarith) (by linarith)
    calc
      _ ≤ 6 * ((2 * edgeRadius) * (w - 2 * vertexRadius)) := by
        convert h using 1 <;> norm_num <;> ring
      _ = _ := by ring
  · rw [daiLiGridSideStripQubits, if_neg hVertical]
    have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (origin.1 + (side.1 : ℝ) * w + vertexRadius,
        origin.2 + (side.2.1 : ℝ) * w - edgeRadius)
      (origin.1 + ((side.1 : ℝ) + 1) * w - vertexRadius,
        origin.2 + (side.2.1 : ℝ) * w + edgeRadius)
      (by linarith) (by linarith)
    calc
      _ ≤ 6 * ((w - 2 * vertexRadius) * (2 * edgeRadius)) := by
        convert h using 1 <;> norm_num <;> ring
      _ = _ := by ring

/-- Every actual finite side strip lies in the corresponding periodic edge
event for the same translation.  Only this inclusion, not an identification
of a quotient cell with a physical region, is used for the #385 count. -/
theorem daiLiGridSideStrip_subset_gridEdgeBuffer
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) (side : DaiLiGridSideIndex) :
    daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side ⊆
      Finset.univ.filter fun q => edgeBad w edgeRadius t (embedding.point q) := by
  intro q hq
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have htX : t.1 = (origin.1 : AddCircle w) := by
    have := congrArg Prod.fst ht
    simpa [phase] using this.symm
  have htY : t.2 = (origin.2 : AddCircle w) := by
    have := congrArg Prod.snd ht
    simpa [phase] using this.symm
  by_cases hVertical : side.2.2
  · rw [daiLiGridSideStripQubits, if_pos hVertical,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
    unfold edgeBad
    left
    rw [htX]
    have hperiod :
        ((origin.1 + (side.1 : ℝ) * w : ℝ) : AddCircle w) =
          (origin.1 : AddCircle w) :=
      addCircle_coe_add_int_mul_period w origin.1 side.1
    have hdist := addCircle_dist_le_abs_sub w
      (origin.1 + (side.1 : ℝ) * w) (embedding.point q).1 hw
    rw [hperiod] at hdist
    calc
      dist (origin.1 : AddCircle w) (phase w (embedding.point q)).1 ≤
          |(embedding.point q).1 - origin.1 - (side.1 : ℝ) * w| := by
        simp only [sub_add_eq_sub_sub] at hdist
        exact hdist
      _ ≤ edgeRadius := by
        rw [abs_le]
        constructor <;> nlinarith [hq.1.1, hq.1.2]
  · rw [daiLiGridSideStripQubits, if_neg hVertical,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
    unfold edgeBad
    right
    rw [htY]
    have hperiod :
        ((origin.2 + (side.2.1 : ℝ) * w : ℝ) : AddCircle w) =
          (origin.2 : AddCircle w) :=
      addCircle_coe_add_int_mul_period w origin.2 side.2.1
    have hdist := addCircle_dist_le_abs_sub w
      (origin.2 + (side.2.1 : ℝ) * w) (embedding.point q).2 hw
    rw [hperiod] at hdist
    calc
      dist (origin.2 : AddCircle w) (phase w (embedding.point q)).2 ≤
          |(embedding.point q).2 - origin.2 - (side.2.1 : ℝ) * w| := by
        simp only [sub_add_eq_sub_sub] at hdist
        exact hdist
      _ ≤ edgeRadius := by
        rw [abs_le]
        constructor <;> nlinarith [hq.2.1, hq.2.2]

/-- The entire finite physical side buffer is counted by the matching periodic
edge event selected by the averaging theorem. -/
theorem daiLiFiniteGridSideBuffer_subset_gridEdgeBuffer
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) :
    daiLiFiniteGridSideBuffer embedding w edgeRadius vertexRadius origin ⊆
      Finset.univ.filter fun q => edgeBad w edgeRadius t (embedding.point q) := by
  intro q hq
  rcases Finset.mem_biUnion.mp hq with ⟨side, hside, hqSide⟩
  exact daiLiGridSideStrip_subset_gridEdgeBuffer embedding hw edgeRadius vertexRadius
    origin t ht side hqSide

/-- A coordinate lower bound gives the corresponding Euclidean lower bound
for the concrete embedding. -/
theorem le_distance_of_le_abs_coordinate_x
    (embedding : UnitSeparatedEmbedding2D ι) {p q : ι} {r : ℝ}
    (h : r ≤ |(embedding.point p).1 - (embedding.point q).1|) :
    r ≤ embedding.distance p q := by
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  have hSq : ((embedding.point p).1 - (embedding.point q).1) ^ 2 ≤
      ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
    nlinarith [sq_nonneg ((embedding.point p).2 - (embedding.point q).2)]
  exact h.trans (Real.abs_le_sqrt hSq)

theorem le_distance_of_le_abs_coordinate_y
    (embedding : UnitSeparatedEmbedding2D ι) {p q : ι} {r : ℝ}
    (h : r ≤ |(embedding.point p).2 - (embedding.point q).2|) :
    r ≤ embedding.distance p q := by
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  have hSq : ((embedding.point p).2 - (embedding.point q).2) ^ 2 ≤
      ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
    nlinarith [sq_nonneg ((embedding.point p).1 - (embedding.point q).1)]
  exact h.trans (Real.abs_le_sqrt hSq)

/-- Strict `ell` interiors of two distinct physical grid cells are separated
by at least `ell`.  This is stated directly on coordinates so both good cells
and bad-cell subdivision rectangles can share it. -/
theorem daiLiStrictGridCellInteriors_separated
    (embedding : UnitSeparatedEmbedding2D ι) {w ell : ℝ}
    (hEll : 0 ≤ ell) (hWidth : 0 ≤ w) (origin : ℝ × ℝ)
    (cell other : ℤ × ℤ) (hne : cell ≠ other) {p q : ι}
    (hp : origin.1 + (cell.1 : ℝ) * w + ell < (embedding.point p).1 ∧
      (embedding.point p).1 < origin.1 + ((cell.1 : ℝ) + 1) * w - ell ∧
        origin.2 + (cell.2 : ℝ) * w + ell < (embedding.point p).2 ∧
          (embedding.point p).2 < origin.2 + ((cell.2 : ℝ) + 1) * w - ell)
    (hq : origin.1 + (other.1 : ℝ) * w + ell < (embedding.point q).1 ∧
      (embedding.point q).1 < origin.1 + ((other.1 : ℝ) + 1) * w - ell ∧
        origin.2 + (other.2 : ℝ) * w + ell < (embedding.point q).2 ∧
          (embedding.point q).2 < origin.2 + ((other.2 : ℝ) + 1) * w - ell) :
    ell ≤ embedding.distance p q := by
  by_cases hx : cell.1 = other.1
  · have hy : cell.2 ≠ other.2 := by
      intro hy
      apply hne
      exact Prod.ext hx hy
    rcases lt_or_gt_of_ne hy with hylt | hygt
    · have hInt : cell.2 + 1 ≤ other.2 := by omega
      have hReal : (cell.2 : ℝ) + 1 ≤ other.2 := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hWidth
      apply le_distance_of_le_abs_coordinate_y embedding
      rw [le_abs]
      right
      nlinarith [hp.2.2.2, hq.2.2.1, hMul]
    · have hInt : other.2 + 1 ≤ cell.2 := by omega
      have hReal : (other.2 : ℝ) + 1 ≤ cell.2 := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hWidth
      apply le_distance_of_le_abs_coordinate_y embedding
      rw [le_abs]
      left
      nlinarith [hp.2.2.1, hq.2.2.2, hMul]
  · rcases lt_or_gt_of_ne hx with hxlt | hxgt
    · have hInt : cell.1 + 1 ≤ other.1 := by omega
      have hReal : (cell.1 : ℝ) + 1 ≤ other.1 := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hWidth
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      right
      nlinarith [hp.2.1, hq.1, hMul]
    · have hInt : other.1 + 1 ≤ cell.1 := by omega
      have hReal : (other.1 : ℝ) + 1 ≤ cell.1 := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hWidth
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      left
      nlinarith [hp.1, hq.2.1, hMul]

/-- Distinct canonical grid-side strips are physically separated by at least
`ell`.  This is the finite replacement for the former periodic `AddCircle`
gap: same-orientation strips are separated by their vertex buffers, while a
vertical and a horizontal strip are separated in the horizontal coordinate. -/
theorem daiLiGridSideStrips_separated
    (embedding : UnitSeparatedEmbedding2D ι) {w ell : ℝ}
    (hEll : 0 ≤ ell) (hWidth : 4 * ell ≤ w) (origin : ℝ × ℝ)
    (side other : DaiLiGridSideIndex) (hne : side ≠ other)
    {p q : ι}
    (hp : p ∈ daiLiGridSideStripQubits embedding w ell (2 * ell) origin side)
    (hq : q ∈ daiLiGridSideStripQubits embedding w ell (2 * ell) origin other) :
    ell ≤ embedding.distance p q := by
  rcases side with ⟨i, j, b⟩
  rcases other with ⟨i', j', b'⟩
  have hw0 : 0 ≤ w := by nlinarith
  cases b <;> cases b'
  · -- horizontal / horizontal
    simp [daiLiGridSideStripQubits] at hp hq
    by_cases hj : j = j'
    · subst j'
      have hi : i ≠ i' := by
        intro hi
        apply hne
        simp [hi]
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hInt : i + 1 ≤ i' := by omega
        have hReal : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_x embedding
        rw [le_abs]
        right
        nlinarith [hp.1.2, hq.1.1, hMul]
      · have hInt : i' + 1 ≤ i := by omega
        have hReal : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_x embedding
        rw [le_abs]
        left
        nlinarith [hp.1.1, hq.1.2, hMul]

    · rcases lt_or_gt_of_ne hj with hlt | hgt
      · have hInt : j + 1 ≤ j' := by omega
        have hReal : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_y embedding
        rw [le_abs]
        right
        nlinarith [hp.2.2, hq.2.1, hMul]
      · have hInt : j' + 1 ≤ j := by omega
        have hReal : (j' : ℝ) + 1 ≤ j := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_y embedding
        rw [le_abs]
        left
        nlinarith [hp.2.1, hq.2.2, hMul]
  · -- horizontal / vertical
    simp [daiLiGridSideStripQubits] at hp hq
    by_cases hi : i ≤ i'
    · by_cases hiEq : i = i'
      · subst i'
        apply le_distance_of_le_abs_coordinate_x embedding
        rw [le_abs]
        left
        nlinarith [hp.1.1, hq.1.2]
      · have hInt : i + 1 ≤ i' := by omega
        have hReal : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_x embedding
        rw [le_abs]
        right
        nlinarith [hp.1.2, hq.1.1, hMul]
    · have hInt : i' + 1 ≤ i := by omega
      have hReal : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      left
      nlinarith [hp.1.1, hq.1.2, hMul]
  · -- vertical / horizontal
    simp [daiLiGridSideStripQubits] at hp hq
    by_cases hi : i ≤ i'
    · have hReal : (i : ℝ) ≤ i' := by exact_mod_cast hi
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      right
      nlinarith [hp.1.2, hq.1.1, hMul]
    · have hInt : i' + 1 ≤ i := by omega
      have hReal : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      left
      nlinarith [hp.1.1, hq.1.2, hMul]
  · -- vertical / vertical
    simp [daiLiGridSideStripQubits] at hp hq
    by_cases hi : i = i'
    · subst i'
      have hj : j ≠ j' := by
        intro hj
        apply hne
        simp [hj]
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have hInt : j + 1 ≤ j' := by omega
        have hReal : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_y embedding
        rw [le_abs]
        right
        nlinarith [hp.2.2, hq.2.1, hMul]
      · have hInt : j' + 1 ≤ j := by omega
        have hReal : (j' : ℝ) + 1 ≤ j := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_y embedding
        rw [le_abs]
        left
        nlinarith [hp.2.1, hq.2.2, hMul]
    · rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hInt : i + 1 ≤ i' := by omega
        have hReal : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_x embedding
        rw [le_abs]
        right
        nlinarith [hp.1.2, hq.1.1, hMul]
      · have hInt : i' + 1 ≤ i := by omega
        have hReal : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hInt
        have hMul := mul_le_mul_of_nonneg_right hReal hw0
        apply le_distance_of_le_abs_coordinate_x embedding
        rw [le_abs]
        left
        nlinarith [hp.1.1, hq.1.2, hMul]

/-- A finite physical grid side after deleting every endpoint of a long
interaction.  These are the mutually decoupled ``good'' side components used
in the Dai--Li partition; the deletion is semantic, not an assumption. -/
def daiLiGridSideGoodQubits
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (origin : ℝ × ℝ) (side : DaiLiGridSideIndex) : Finset ι :=
  daiLiGridSideStripQubits embedding w ell (2 * ell) origin side \
    longInteractionEndpointQubits P embedding threshold

def daiLiGridSideGoodSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (origin : ℝ × ℝ) (side : DaiLiGridSideIndex) : FiniteSubsystem ι :=
  ⟨daiLiGridSideGoodQubits P embedding threshold w ell origin side⟩

/-- Distinct good finite side strips have no shared qubits: geometrically they
are at least `ell` apart, and the code's separation threshold is positive. -/
theorem daiLiGridSideGood_disjoint
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {w ell : ℝ}
    (threshold : ℝ) (hEll : 0 < ell) (hWidth : 4 * ell ≤ w) (origin : ℝ × ℝ)
    (side other : DaiLiGridSideIndex) (hne : side ≠ other) :
    Disjoint
      (daiLiGridSideGoodQubits P embedding threshold w ell origin side)
      (daiLiGridSideGoodQubits P embedding threshold w ell origin other) := by
  apply Finset.disjoint_left.mpr
  intro q hqSide hqOther
  have hDistance := daiLiGridSideStrips_separated embedding hEll.le hWidth origin
    side other hne
    (Finset.mem_sdiff.mp hqSide).1 (Finset.mem_sdiff.mp hqOther).1
  have hZero : ell ≤ 0 := by
    simpa [UnitSeparatedEmbedding2D.distance, euclideanDistance2D] using hDistance
  exact (not_le_of_gt hEll) hZero

/-- The concrete finite good strips are pairwise fixed-generator decoupled.
This is the exact bridge from the proved coordinate separation to the CPTP
union closure, with long endpoints removed from both components. -/
theorem daiLiGridSideGood_fixedGeneratorDecoupled
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {w ell : ℝ}
    (hEll : 0 < ell) (hWidth : 4 * ell ≤ w) (threshold : ℝ)
    (hThreshold : threshold ≤ ell)
    (origin : ℝ × ℝ) (side other : DaiLiGridSideIndex) (hne : side ≠ other) :
    P.fixedGeneratorDecoupled
      ((daiLiGridSideGoodQubits P embedding threshold w ell origin side : Finset ι) : Set ι)
      ((daiLiGridSideGoodQubits P embedding threshold w ell origin other : Finset ι) : Set ι) := by
  apply fixedGeneratorDecoupled_of_separated_outside_longEndpoints P embedding threshold
  · exact daiLiGridSideGood_disjoint P embedding threshold hEll hWidth origin side other hne
  · intro q hq
    simpa using (Finset.mem_sdiff.mp hq).2
  · intro q hq
    simpa using (Finset.mem_sdiff.mp hq).2
  · intro p hp q hq
    exact hThreshold.trans (daiLiGridSideStrips_separated embedding hEll.le hWidth origin
      side other hne (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1)

/-- The same packing estimate holds after removing long-interaction endpoints.
The hypotheses state the actual positive dimensions of the side rectangle. -/
theorem card_daiLiGridSideGood_lt_distance
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold : ℝ)
    {w ell : ℝ} (origin : ℝ × ℝ) (side : DaiLiGridSideIndex)
    (hEdge : 1 ≤ 2 * ell) (hLong : 1 ≤ w - 4 * ell)
    (hSmall : 12 * ell * (w - 4 * ell) < d) :
    (daiLiGridSideGoodQubits P embedding threshold w ell origin side).card < d := by
  have hLong' : 1 ≤ w - 2 * (2 * ell) := by linarith
  have hPacking := card_daiLiGridSideStrip_le embedding w ell (2 * ell) origin side
    hEdge hLong'
  have hPacking' :
      ((daiLiGridSideStripQubits embedding w ell (2 * ell) origin side).card : ℝ) ≤
        12 * ell * (w - 4 * ell) := by
    convert hPacking using 1 <;> ring
  have hSubset : daiLiGridSideGoodQubits P embedding threshold w ell origin side ⊆
      daiLiGridSideStripQubits embedding w ell (2 * ell) origin side :=
    Finset.sdiff_subset
  have hCard :
      ((daiLiGridSideGoodQubits P embedding threshold w ell origin side).card : ℝ) ≤
        ((daiLiGridSideStripQubits embedding w ell (2 * ell) origin side).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSubset
  have hCardReal :
      ((daiLiGridSideGoodQubits P embedding threshold w ell origin side).card : ℝ) < d :=
    lt_of_le_of_lt (hCard.trans hPacking') hSmall
  exact_mod_cast hCardReal

/-- The finite family of all actual good grid-side components. -/
def daiLiGridSideGoodFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (origin : ℝ × ℝ) : DaiLiGridSideIndex → FiniteSubsystem ι :=
  daiLiGridSideGoodSubsystem P embedding threshold w ell origin

/-- A typed CPTP erasure recovery for the union of any finite family of good
grid sides.  Each component is recovered from semantic distance and the union
is recovered through actual fixed-generator decoupling. -/
theorem exists_erasureRecovery_daiLiGridSideGoodFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    {w ell : ℝ} (hEll : 0 < ell) (hWidth : 4 * ell ≤ w)
    (threshold : ℝ) (hThreshold : threshold ≤ ell)
    (origin : ℝ × ℝ) (s : Finset DaiLiGridSideIndex)
    (hEdge : 1 ≤ 2 * ell) (hLong : 1 ≤ w - 4 * ell)
    (hSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem (daiLiGridSideGoodFamily P embedding threshold w ell origin) s).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem (daiLiGridSideGoodFamily P embedding threshold w ell origin) s).complementSystem
        P.semanticCode
        (familyUnionSubsystem (daiLiGridSideGoodFamily P embedding threshold w ell origin) s).erasureChannelFromRegister
        recovery := by
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
    (daiLiGridSideGoodFamily P embedding threshold w ell origin) s
  · intro side hside
    exact semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance
      (daiLiGridSideGoodFamily P embedding threshold w ell origin side)
      (by
        simpa [daiLiGridSideGoodFamily, daiLiGridSideGoodSubsystem] using
          card_daiLiGridSideGood_lt_distance P embedding d threshold origin side
            hEdge hLong hSmall)
  · intro side hside other hother hne
    simpa [daiLiGridSideGoodFamily, daiLiGridSideGoodSubsystem] using
      daiLiGridSideGood_fixedGeneratorDecoupled P embedding hEll hWidth threshold hThreshold
        origin side other hne

/-- Every source-good closed grid cell has an actual CPTP recovery through the
clipped rectangle-growth construction.  The inputs are only finite geometric
and numerical checks; the proof does not accept a cell recovery witness. -/
theorem exists_erasureRecovery_daiLiGridCell_of_good_clipped_growth
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVertical : baseVerticalRadius ≤ w / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVertical : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding (daiLiGridCellCenter w origin cell)
      baseHorizontalRadius baseVerticalRadius).card < d)
    (hGood : IsGoodInteractionSquare P embedding threshold d
      (daiLiGridCellCenter w origin cell) (w / 2))
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d) :
    ∃ recovery : QuantumChannel
        (daiLiGridCellClosedSubsystem embedding w origin cell).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiGridCellClosedSubsystem embedding w origin cell).complementSystem
        P.semanticCode
        (daiLiGridCellClosedSubsystem embedding w origin cell).erasureChannelFromRegister
          recovery := by
  have hCounter : 10 * regionInteractionCounter P embedding threshold
      (centeredRectangleQubits embedding (daiLiGridCellCenter w origin cell)
        (w / 2) (w / 2)) ≤ d := by
    apply Nat.le_of_lt
    simpa [IsGoodInteractionSquare, IsGoodInteractionRegion,
      daiLiGridCellClosedQubits, squareQubits, centeredRectangleQubits] using hGood
  exact
    exists_erasureRecovery_centeredRectangle_of_good_clipped_growth
      P embedding d hDistance (daiLiGridCellCenter w origin cell)
      baseHorizontalRadius baseVerticalRadius (w / 2) (w / 2) threshold steps
      hThreshold hBaseHorizontal hBaseVertical hBaseHorizontalDiameter
      hBaseVerticalDiameter hReachHorizontal hReachVertical hBaseCard hCounter
      hBoundaryBudget

/-- The center of an explicit axis-parallel rectangle. -/
def daiLiRectangleCenter (lower upper : ℝ × ℝ) : ℝ × ℝ :=
  ((lower.1 + upper.1) / 2, (lower.2 + upper.2) / 2)

def daiLiRectangleHorizontalRadius (lower upper : ℝ × ℝ) : ℝ :=
  (upper.1 - lower.1) / 2

def daiLiRectangleVerticalRadius (lower upper : ℝ × ℝ) : ℝ :=
  (upper.2 - lower.2) / 2

def daiLiRectangleSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (lower upper : ℝ × ℝ) : FiniteSubsystem ι :=
  ⟨embedding.qubitsInRectangle lower upper⟩

/-- The rectangle representation used by #496 agrees exactly with the
center-and-half-side representation used by actual growth. -/
theorem daiLiRectangleQubits_eq_centeredRectangleQubits
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ) :
    embedding.qubitsInRectangle lower upper =
      centeredRectangleQubits embedding (daiLiRectangleCenter lower upper)
        (daiLiRectangleHorizontalRadius lower upper)
        (daiLiRectangleVerticalRadius lower upper) := by
  have hLowerX : (daiLiRectangleCenter lower upper).1 -
      daiLiRectangleHorizontalRadius lower upper = lower.1 := by
    simp [daiLiRectangleCenter, daiLiRectangleHorizontalRadius]
    ring
  have hUpperX : (daiLiRectangleCenter lower upper).1 +
      daiLiRectangleHorizontalRadius lower upper = upper.1 := by
    simp [daiLiRectangleCenter, daiLiRectangleHorizontalRadius]
    ring
  have hLowerY : (daiLiRectangleCenter lower upper).2 -
      daiLiRectangleVerticalRadius lower upper = lower.2 := by
    simp [daiLiRectangleCenter, daiLiRectangleVerticalRadius]
    ring
  have hUpperY : (daiLiRectangleCenter lower upper).2 +
      daiLiRectangleVerticalRadius lower upper = upper.2 := by
    simp [daiLiRectangleCenter, daiLiRectangleVerticalRadius]
    ring
  rw [centeredRectangleQubits, hLowerX, hUpperX, hLowerY, hUpperY]

/-- The concrete #496 rectangle and the centered-growth rectangle are the
same finite subsystem, including all dependent erasure data. -/
theorem daiLiRectangleSubsystem_eq_centeredRectangleSubsystem
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ) :
    daiLiRectangleSubsystem embedding lower upper =
      centeredRectangleSubsystem embedding (daiLiRectangleCenter lower upper)
        (daiLiRectangleHorizontalRadius lower upper)
        (daiLiRectangleVerticalRadius lower upper) := by
  simp only [daiLiRectangleSubsystem, centeredRectangleSubsystem]
  rw [daiLiRectangleQubits_eq_centeredRectangleQubits]

/-- A low-interaction #496 rectangle has an actual CPTP recovery through the
same clipped rectangle-growth construction. -/
theorem exists_erasureRecovery_daiLiRectangle_of_low_counter_clipped_growth
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold : ℝ) (lower upper : ℝ × ℝ)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤
      daiLiRectangleHorizontalRadius lower upper)
    (hBaseVertical : baseVerticalRadius ≤ daiLiRectangleVerticalRadius lower upper)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : daiLiRectangleHorizontalRadius lower upper ≤
      baseHorizontalRadius + steps * threshold)
    (hReachVertical : daiLiRectangleVerticalRadius lower upper ≤
      baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
      (daiLiRectangleCenter lower upper) baseHorizontalRadius
      baseVerticalRadius).card < d)
    (hLowCounter : 10 * regionInteractionCounter P embedding threshold
      (embedding.qubitsInRectangle lower upper) ≤ d)
    (hBoundaryBudget :
      48 * (daiLiRectangleHorizontalRadius lower upper +
        daiLiRectangleVerticalRadius lower upper + threshold) * threshold +
        (d : ℝ) / 10 < d) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        P.semanticCode
        (daiLiRectangleSubsystem embedding lower upper).erasureChannelFromRegister
          recovery := by
  have hCounter : 10 * regionInteractionCounter P embedding threshold
      (centeredRectangleQubits embedding (daiLiRectangleCenter lower upper)
        (daiLiRectangleHorizontalRadius lower upper)
        (daiLiRectangleVerticalRadius lower upper)) ≤ d := by
    simpa [daiLiRectangleQubits_eq_centeredRectangleQubits] using hLowCounter
  rw [daiLiRectangleSubsystem_eq_centeredRectangleSubsystem]
  exact exists_erasureRecovery_centeredRectangle_of_good_clipped_growth
    P embedding d hDistance (daiLiRectangleCenter lower upper)
    baseHorizontalRadius baseVerticalRadius
    (daiLiRectangleHorizontalRadius lower upper)
    (daiLiRectangleVerticalRadius lower upper) threshold steps
    hThreshold hBaseHorizontal hBaseVertical hBaseHorizontalDiameter
    hBaseVerticalDiameter hReachHorizontal hReachVertical hBaseCard hCounter
    hBoundaryBudget

/-- A geometrically short #496 rectangle is recovered directly from semantic
distance using the exact two-dimensional packing bound. -/
theorem exists_erasureRecovery_daiLiRectangle_of_packing_lt_distance
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (lower upper : ℝ × ℝ)
    (hWidth : 1 ≤ upper.1 - lower.1) (hHeight : 1 ≤ upper.2 - lower.2)
    (hPackingSmall : 6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) < d) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        P.semanticCode
        (daiLiRectangleSubsystem embedding lower upper).erasureChannelFromRegister
          recovery := by
  have hPacking := embedding.card_qubitsInRectangle_le_six_mul_area lower upper
    hWidth hHeight
  have hCardReal : ((embedding.qubitsInRectangle lower upper).card : ℝ) < d :=
    lt_of_le_of_lt hPacking hPackingSmall
  have hCard : (embedding.qubitsInRectangle lower upper).card < d := by
    exact_mod_cast hCardReal
  exact semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
    (daiLiRectangleSubsystem embedding lower upper)
    (by simpa [daiLiRectangleSubsystem] using hCard)

/-- A true #496 subdivision rectangle is correctable in either branch of its
proved local contract: low interaction count uses clipped growth, while a
short horizontal band uses the packing-to-distance route. -/
theorem exists_erasureRecovery_daiLiRectangle_of_piece_alternative
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold ell w : ℝ) (lower upper : ℝ × ℝ)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ daiLiRectangleHorizontalRadius lower upper)
    (hBaseVertical : baseVerticalRadius ≤ daiLiRectangleVerticalRadius lower upper)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : daiLiRectangleHorizontalRadius lower upper ≤
      baseHorizontalRadius + steps * threshold)
    (hReachVertical : daiLiRectangleVerticalRadius lower upper ≤
      baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
      (daiLiRectangleCenter lower upper) baseHorizontalRadius
      baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (daiLiRectangleHorizontalRadius lower upper +
        daiLiRectangleVerticalRadius lower upper + threshold) * threshold +
        (d : ℝ) / 10 < d)
    (hSpan : upper.1 - lower.1 = w) (hWidth : 1 ≤ w) (hEll : 1 ≤ ell)
    (hMinimumHeight : 5 * ell ≤ upper.2 - lower.2)
    (hShortPackingScale : 60 * w * ell < d)
    (hPiece : 10 * regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle lower upper) ≤ d ∨
      upper.2 - lower.2 ≤ 10 * ell) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        P.semanticCode
        (daiLiRectangleSubsystem embedding lower upper).erasureChannelFromRegister recovery := by
  rcases hPiece with hLow | hShort
  · exact exists_erasureRecovery_daiLiRectangle_of_low_counter_clipped_growth
      P embedding d hDistance threshold lower upper baseHorizontalRadius
      baseVerticalRadius steps hThreshold hBaseHorizontal hBaseVertical
      hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal hReachVertical
      hBaseCard hLow hBoundaryBudget
  · apply exists_erasureRecovery_daiLiRectangle_of_packing_lt_distance
      P embedding d hDistance lower upper
    · linarith
    · nlinarith
    · have hArea : 6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) ≤
          60 * w * ell := by
        have hHeightScaled : w * (upper.2 - lower.2) ≤ w * (10 * ell) :=
          mul_le_mul_of_nonneg_left hShort (by linarith)
        calc
          6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) =
              6 * (w * (upper.2 - lower.2)) := by rw [hSpan]
          _ ≤ 6 * (w * (10 * ell)) :=
            mul_le_mul_of_nonneg_left hHeightScaled (by norm_num)
          _ = 60 * w * ell := by ring
      exact lt_of_le_of_lt hArea hShortPackingScale

/-- Under the Dai--Li box scale, every one of the four finite edge strips of
a subdivision rectangle has cardinality strictly below the distance.  This is
the local `B` recovery budget; it is proved from packing rather than supplied
as a per-strip cardinality witness. -/
theorem card_daiLiRectangleSideStrip_lt_distance_of_box_scale
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (ell w : ℝ)
    (lower upper : ℝ × ℝ) (hEll : 1 ≤ ell) (hCellWidth : 5 * ell ≤ w)
    (hSpan : upper.1 - lower.1 = w)
    (hMinimumHeight : 5 * ell ≤ upper.2 - lower.2)
    (hMaximumHeight : upper.2 - lower.2 ≤ w)
    (hSideScale : 12 * ell * w < d) (side : Fin 4) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper side).card : ℝ) < d := by
  have hVerticalLong : 1 ≤ upper.2 - lower.2 - 4 * ell := by
    nlinarith
  have hHorizontalLong : 1 ≤ upper.1 - lower.1 - 4 * ell := by
    rw [hSpan]
    nlinarith
  have hFactor : 0 ≤ 12 * ell := by nlinarith
  have hCases : side.val = 0 ∨ side.val = 1 ∨ side.val = 2 ∨ side.val = 3 := by
    omega
  rcases hCases with hZero | hOne | hTwo | hThree
  · have hSide : side = (0 : Fin 4) := Fin.ext hZero
    subst side
    have hCard := card_daiLiRectangleSideStrip_zero_le embedding ell lower upper
      (by nlinarith : 1 ≤ 2 * ell) hVerticalLong
    have hLength : upper.2 - lower.2 - 4 * ell ≤ w := by linarith
    exact lt_of_le_of_lt hCard
      ((mul_le_mul_of_nonneg_left hLength hFactor).trans_lt hSideScale)
  · have hSide : side = (1 : Fin 4) := Fin.ext hOne
    subst side
    have hCard := card_daiLiRectangleSideStrip_one_le embedding ell lower upper
      (by nlinarith : 1 ≤ 2 * ell) hVerticalLong
    have hLength : upper.2 - lower.2 - 4 * ell ≤ w := by linarith
    exact lt_of_le_of_lt hCard
      ((mul_le_mul_of_nonneg_left hLength hFactor).trans_lt hSideScale)
  · have hSide : side = (2 : Fin 4) := Fin.ext hTwo
    subst side
    have hCard := card_daiLiRectangleSideStrip_two_le embedding ell lower upper
      (by nlinarith : 1 ≤ 2 * ell) hHorizontalLong
    have hLength : upper.1 - lower.1 - 4 * ell ≤ w := by rw [hSpan]; linarith
    exact lt_of_le_of_lt hCard
      ((mul_le_mul_of_nonneg_left hLength hFactor).trans_lt hSideScale)
  · have hSide : side = (3 : Fin 4) := Fin.ext hThree
    subst side
    have hCard := card_daiLiRectangleSideStrip_three_le embedding ell lower upper
      (by nlinarith : 1 ≤ 2 * ell) hHorizontalLong
    have hLength : upper.1 - lower.1 - 4 * ell ≤ w := by rw [hSpan]; linarith
    exact lt_of_le_of_lt hCard
      ((mul_le_mul_of_nonneg_left hLength hFactor).trans_lt hSideScale)

/-- Each box-scale subdivision side strip therefore obtains its CPTP erasure
recovery directly from the semantic distance API. -/
theorem exists_erasureRecovery_daiLiRectangleSideStrip_of_box_scale
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ) (lower upper : ℝ × ℝ) (hEll : 1 ≤ ell)
    (hCellWidth : 5 * ell ≤ w) (hSpan : upper.1 - lower.1 = w)
    (hMinimumHeight : 5 * ell ≤ upper.2 - lower.2)
    (hMaximumHeight : upper.2 - lower.2 ≤ w)
    (hSideScale : 12 * ell * w < d) (side : Fin 4) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        P.semanticCode
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).erasureChannelFromRegister
          recovery := by
  have hCardReal := card_daiLiRectangleSideStrip_lt_distance_of_box_scale
    embedding d ell w lower upper hEll hCellWidth hSpan hMinimumHeight hMaximumHeight
      hSideScale side
  have hCard : (daiLiRectangleSideStripQubits embedding ell lower upper side).card < d := by
    exact_mod_cast hCardReal
  exact exists_erasureRecovery_daiLiRectangleSideStrip_of_card_lt P embedding d hDistance ell
    lower upper side hCard

/-! ## Finite `k >= d` region indexing

The source partition has one region for each good grid square and one region
for each actual greedy rectangle inside a bad square.  The finite index below
keeps those two cases distinct.  In particular, a bad rectangle is not an
arbitrary rectangle supplied by a caller: its natural-number coordinate is
admitted only when it is in range for the concrete #496 list of its bad cell.
-/

/-- A good grid cell, or a position in the actual rectangle list of a bad
grid cell. -/
abbrev DaiLiKGeDRegionIndex :=
  Sum (ℤ × ℤ) ((ℤ × ℤ) × ℕ)

/-- The finite source region family around the occupied cells.  Good cells
occur once; bad cells contribute exactly their #496 greedy rectangles. -/
def daiLiKGeDRegionCandidates
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Finset DaiLiKGeDRegionIndex := by
  classical
  let bad := daiLiBadGridCells P embedding threshold d w origin
  exact ((embedding.gridOccupiedCells w origin \ bad).image (fun cell => Sum.inl cell)) ∪
    bad.biUnion fun cell =>
      (Finset.range (rectangles cell).length).image
        (fun slot => Sum.inr (cell, slot))

/-- The physical rectangle named by a finite `k >= d` source-region index. -/
def daiLiKGeDRegionRectangle
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) : (ℝ × ℝ) × (ℝ × ℝ) :=
  match region with
  | Sum.inl cell => (gridCellLower w origin cell, gridCellUpper w origin cell)
  | Sum.inr (cell, slot) => (rectangles cell).getD slot ((0, 0), (0, 0))

/-- The unique grid cell that contains a source region. -/
def daiLiKGeDRegionHostCell : DaiLiKGeDRegionIndex → ℤ × ℤ
  | Sum.inl cell => cell
  | Sum.inr (cell, _) => cell

/-- A grid-cell index is present exactly when that occupied cell is not
classified bad. -/
theorem mem_daiLiKGeDRegionCandidates_good_iff
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) (cell : ℤ × ℤ) :
    Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d w origin rectangles ↔
      cell ∈ embedding.gridOccupiedCells w origin ∧
        cell ∉ daiLiBadGridCells P embedding threshold d w origin := by
  classical
  simp [daiLiKGeDRegionCandidates]

/-- A rectangle index is present exactly when it names a position of the
concrete list belonging to an actual bad grid cell. -/
theorem mem_daiLiKGeDRegionCandidates_bad_iff
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) :
    Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d w origin rectangles ↔
      cell ∈ daiLiBadGridCells P embedding threshold d w origin ∧
        slot < (rectangles cell).length := by
  classical
  simp [daiLiKGeDRegionCandidates]

/-- On an in-range bad index, the total lookup used by the region definition
reduces to the corresponding concrete list entry. -/
theorem daiLiKGeDRegionRectangle_bad_eq_get
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) (hSlot : slot < (rectangles cell).length) :
    daiLiKGeDRegionRectangle embedding w origin rectangles (Sum.inr (cell, slot)) =
      (rectangles cell).get ⟨slot, hSlot⟩ := by
  change (rectangles cell).getD slot ((0, 0), (0, 0)) = _
  simpa using List.getD_eq_get (rectangles cell) ((0, 0), (0, 0)) ⟨slot, hSlot⟩

/-- Every in-range bad-region index denotes an actual member of its cell's
#496 rectangle list. -/
theorem daiLiKGeDRegionRectangle_bad_mem
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) (hSlot : slot < (rectangles cell).length) :
    daiLiKGeDRegionRectangle embedding w origin rectangles (Sum.inr (cell, slot)) ∈
      rectangles cell := by
  rw [daiLiKGeDRegionRectangle_bad_eq_get embedding w origin rectangles cell slot hSlot]
  exact List.get_mem _ _

/-- Every finite source-region candidate is rooted in an occupied physical
grid cell. -/
theorem daiLiKGeDRegionCandidate_host_occupied
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d w origin rectangles) :
    daiLiKGeDRegionHostCell region ∈ embedding.gridOccupiedCells w origin := by
  cases region with
  | inl cell =>
      exact (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w origin
        rectangles cell).1 hRegion |>.1
  | inr pair =>
      rcases pair with ⟨cell, slot⟩
      have hBad := (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w origin
        rectangles cell slot).1 hRegion |>.1
      exact (mem_daiLiBadGridCells_iff P embedding threshold d w origin cell).1 hBad |>.1

/-- The exact source `A` contribution of one physical region: the strict
interior left after the counted `C` region and its width-`ell` boundary belt
are removed. -/
def daiLiKGeDRegionCoreQubits
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) : Finset ι :=
  let rectangle := daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region
  (embedding.qubitsInRectangle rectangle.1 rectangle.2).filter fun q =>
    q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles ∧
      rectangle.1.1 + ell < (embedding.point q).1 ∧
        (embedding.point q).1 < rectangle.2.1 - ell ∧
          rectangle.1.2 + ell < (embedding.point q).2 ∧
            (embedding.point q).2 < rectangle.2.2 - ell

def daiLiKGeDRegionCoreSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) : FiniteSubsystem ι :=
  ⟨daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region⟩

def daiLiKGeDRegionCoreFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    DaiLiKGeDRegionIndex → FiniteSubsystem ι :=
  daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t cells rectangles

/-- Each strict core is a genuine subset of the closed source region from
which its CPTP recovery will be inherited. -/
theorem daiLiKGeDRegionCore_subset_rectangle
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) :
    daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region ⊆
      embedding.qubitsInRectangle
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).1
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).2 := by
  exact Finset.filter_subset _ _

/-- Each selected core point is strictly inside all four sides of its own
physical source rectangle. -/
theorem mem_daiLiKGeDRegionCore_strict_rectangleBounds
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) (p : ι)
    (hp : p ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region) :
    (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).1.1 + ell <
        (embedding.point p).1 ∧
      (embedding.point p).1 <
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).2.1 - ell ∧
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).1.2 + ell <
          (embedding.point p).2 ∧
          (embedding.point p).2 <
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).2.2 - ell := by
  dsimp [daiLiKGeDRegionCoreQubits] at hp
  exact ⟨(Finset.mem_filter.mp hp).2.2.1, (Finset.mem_filter.mp hp).2.2.2.1,
    (Finset.mem_filter.mp hp).2.2.2.2.1, (Finset.mem_filter.mp hp).2.2.2.2.2⟩

/-- Membership in a finite `k >= d` core gives strict `ell` bounds in the
host grid cell.  For a bad region those bounds pass through the concrete
#496 rectangle-to-parent endpoint theorem. -/
theorem mem_daiLiKGeDRegionCore_strict_hostBounds
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (region : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (p : ι)
    (hp : p ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles region) :
    (gridOrigin w t).1 + (daiLiKGeDRegionHostCell region).1 * w + ell <
        (embedding.point p).1 ∧
      (embedding.point p).1 < (gridOrigin w t).1 +
        ((daiLiKGeDRegionHostCell region).1 + 1) * w - ell ∧
        (gridOrigin w t).2 + (daiLiKGeDRegionHostCell region).2 * w + ell <
          (embedding.point p).2 ∧
          (embedding.point p).2 < (gridOrigin w t).2 +
            ((daiLiKGeDRegionHostCell region).2 + 1) * w - ell := by
  dsimp [daiLiKGeDRegionCoreQubits] at hp
  have hData := (Finset.mem_filter.mp hp).2
  cases region with
  | inl cell =>
      simpa [daiLiKGeDRegionHostCell, daiLiKGeDRegionRectangle] using
        ⟨hData.2.1, hData.2.2.1, hData.2.2.2.1, hData.2.2.2.2⟩
  | inr pair =>
      rcases pair with ⟨cell, slot⟩
      rcases (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
        (gridOrigin w t) rectangles cell slot).1 hRegion with ⟨hBad, hSlot⟩
      let rectangle := daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
        (Sum.inr (cell, slot))
      have hRectangle : rectangle ∈ rectangles cell := by
        dsimp [rectangle]
        exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
          rectangles cell slot hSlot
      have hParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell
        (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad rectangle hRectangle
      simp only [gridCellLower, gridCellUpper] at hParent
      change p ∈ (embedding.qubitsInRectangle rectangle.1 rectangle.2).filter _ at hp
      have hRectangleData := (Finset.mem_filter.mp hp).2
      change p ∉ daiLiKGeDSeparator P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles ∧
        rectangle.1.1 + ell < (embedding.point p).1 ∧
          (embedding.point p).1 < rectangle.2.1 - ell ∧
            rectangle.1.2 + ell < (embedding.point p).2 ∧
              (embedding.point p).2 < rectangle.2.2 - ell at hRectangleData
      dsimp [daiLiKGeDRegionHostCell]
      refine ⟨?_, ?_, ?_, ?_⟩
      · nlinarith [hParent.1, hRectangleData.2.1]
      · nlinarith [hParent.2.1, hRectangleData.2.2.1]
      · nlinarith [hParent.2.2.1, hRectangleData.2.2.2.1]
      · nlinarith [hParent.2.2.2, hRectangleData.2.2.2.2]

/-- Distinct finite `k >= d` source-region cores are geometrically separated.
Different host cells use strict grid interiors; two entries in one bad cell use
the proved order of the actual greedy rectangle list. -/
theorem daiLiKGeDRegionCores_separated
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (hWidth : 0 < w)
    (region other : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOther : other ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hne : region ≠ other) {p q : ι}
    (hp : p ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles region)
    (hq : q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles other) :
    ell ≤ embedding.distance p q := by
  have hpHost := mem_daiLiKGeDRegionCore_strict_hostBounds P embedding d threshold w ell t
    atoms rectangles hAtoms hRectangles hEll region hRegion p hp
  have hqHost := mem_daiLiKGeDRegionCore_strict_hostBounds P embedding d threshold w ell t
    atoms rectangles hAtoms hRectangles hEll other hOther q hq
  by_cases hHost : daiLiKGeDRegionHostCell region = daiLiKGeDRegionHostCell other
  · cases region with
    | inl cell =>
        cases other with
        | inl other =>
            simp only [daiLiKGeDRegionHostCell] at hHost
            subst other
            exact (hne rfl).elim
        | inr pair =>
            rcases pair with ⟨other, slot⟩
            simp only [daiLiKGeDRegionHostCell] at hHost
            subst other
            have hNotBad := (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell).1 hRegion |>.2
            have hBad := (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell slot).1 hOther |>.1
            exact (hNotBad hBad).elim
    | inr pair =>
        rcases pair with ⟨cell, slot⟩
        cases other with
        | inl other =>
            simp only [daiLiKGeDRegionHostCell] at hHost
            subst other
            have hBad := (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell slot).1 hRegion |>.1
            have hNotBad := (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell).1 hOther |>.2
            exact (hNotBad hBad).elim
        | inr otherPair =>
            rcases otherPair with ⟨other, otherSlot⟩
            simp only [daiLiKGeDRegionHostCell] at hHost
            subst other
            rcases (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell slot).1 hRegion with ⟨hBad, hSlot⟩
            rcases (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell otherSlot).1 hOther with ⟨_, hOtherSlot⟩
            have hSlotNe : slot ≠ otherSlot := by
              intro hEqual
              apply hne
              simp [hEqual]
            have hpRectangle := mem_daiLiKGeDRegionCore_strict_rectangleBounds
              P embedding threshold w ell t
              (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
              (Sum.inr (cell, slot)) p hp
            have hqRectangle := mem_daiLiKGeDRegionCore_strict_rectangleBounds
              P embedding threshold w ell t
              (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
              (Sum.inr (cell, otherSlot)) q hq
            rcases lt_or_gt_of_ne hSlotNe with hForward | hBackward
            · have hOrder := daiLiBadGridRectangle_get_verticalOrder P embedding threshold d w ell
                (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad
                slot otherSlot hSlot hOtherSlot hForward
              have hFirstEq := daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
                rectangles cell slot hSlot
              have hSecondEq := daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
                rectangles cell otherSlot hOtherSlot
              have hOrder' :
                  (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
                    (Sum.inr (cell, slot))).2.2 ≤
                    (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
                      (Sum.inr (cell, otherSlot))).1.2 := by
                rw [hFirstEq, hSecondEq]
                exact hOrder
              apply le_distance_of_le_abs_coordinate_y embedding
              rw [le_abs]
              right
              nlinarith [hpRectangle.2.2.2, hqRectangle.2.2.1, hOrder']
            · have hOrder := daiLiBadGridRectangle_get_verticalOrder P embedding threshold d w ell
                (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad
                otherSlot slot hOtherSlot hSlot hBackward
              have hFirstEq := daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
                rectangles cell otherSlot hOtherSlot
              have hSecondEq := daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
                rectangles cell slot hSlot
              have hOrder' :
                  (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
                    (Sum.inr (cell, otherSlot))).2.2 ≤
                    (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
                      (Sum.inr (cell, slot))).1.2 := by
                rw [hFirstEq, hSecondEq]
                exact hOrder
              apply le_distance_of_le_abs_coordinate_y embedding
              rw [le_abs]
              left
              nlinarith [hpRectangle.2.2.1, hqRectangle.2.2.2, hOrder']
  · exact daiLiStrictGridCellInteriors_separated embedding hEll.le hWidth.le (gridOrigin w t)
      (daiLiKGeDRegionHostCell region) (daiLiKGeDRegionHostCell other) hHost hpHost hqHost

/-- A good-cell member of the finite `k >= d` family has an actual CPTP
recovery.  The source-good classification is recovered from the candidate
index itself, and the strict core inherits the closed-cell recovery by subset
closure. -/
theorem exists_erasureRecovery_daiLiKGeDGoodRegionCore
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ)
    (hCandidate : Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVertical : baseVerticalRadius ≤ w / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVertical : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
      (daiLiGridCellCenter w (gridOrigin w t) cell)
      baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).complementSystem
        P.semanticCode
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).erasureChannelFromRegister recovery := by
  rcases (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w
    (gridOrigin w t) rectangles cell).1 hCandidate with ⟨hOccupied, hNotBad⟩
  have hNotBadSquare : ¬ IsBadInteractionSquare P embedding threshold d
      (daiLiGridCellCenter w (gridOrigin w t) cell) (w / 2) := by
    intro hBad
    apply hNotBad
    exact (mem_daiLiBadGridCells_iff P embedding threshold d w (gridOrigin w t) cell).2
      ⟨hOccupied, hBad⟩
  have hGood : IsGoodInteractionSquare P embedding threshold d
      (daiLiGridCellCenter w (gridOrigin w t) cell) (w / 2) := by
    by_contra hNotGood
    apply hNotBadSquare
    change IsBadInteractionRegion P embedding threshold d
      (squareQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell) (w / 2))
    apply (isBadInteractionRegion_iff_not_isGoodInteractionRegion P embedding threshold d
      (squareQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell) (w / 2))).2
    simpa [IsGoodInteractionSquare] using hNotGood
  apply exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (Sum.inl cell))
    (daiLiGridCellClosedSubsystem embedding w (gridOrigin w t) cell)
  · change daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (Sum.inl cell) ⊆ daiLiGridCellClosedQubits embedding w (gridOrigin w t) cell
    rw [daiLiGridCellClosedQubits_eq_rectangle]
    simpa [daiLiKGeDRegionRectangle] using
      (daiLiKGeDRegionCore_subset_rectangle P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
        (Sum.inl cell))
  · exact exists_erasureRecovery_daiLiGridCell_of_good_clipped_growth
      P embedding d hDistance threshold w (gridOrigin w t) cell
      baseHorizontalRadius baseVerticalRadius steps hThreshold hBaseHorizontal hBaseVertical
      hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal hReachVertical
      hBaseCard hGood hBoundaryBudget

/-- A bad-rectangle member of the finite `k >= d` family has an actual CPTP
recovery.  Its source is the in-range #496 list entry, whose proved
low-counter/short-height alternative selects the growth or packing route. -/
theorem exists_erasureRecovery_daiLiKGeDBadRegionCore
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (cell : ℤ × ℤ) (slot : ℕ)
    (hCandidate : Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold) (hWidth : 1 ≤ w) (hEll : 1 ≤ ell)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVertical : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVertical : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
      (daiLiRectangleCenter
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
          (Sum.inr (cell, slot))).1
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
          (Sum.inr (cell, slot))).2)
      baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inr (cell, slot))).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inr (cell, slot))).complementSystem
        P.semanticCode
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inr (cell, slot))).erasureChannelFromRegister recovery := by
  rcases (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
    (gridOrigin w t) rectangles cell slot).1 hCandidate with ⟨hBad, hSlot⟩
  let rectangle := daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
    (Sum.inr (cell, slot))
  have hRectangle : rectangle ∈ rectangles cell := by
    dsimp [rectangle]
    exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
      rectangles cell slot hSlot
  have hRectanglePhysical := hRectangle
  rw [hRectangles cell hBad] at hRectanglePhysical
  have hProperties := daiLiPhysicalGreedyRectangles_piece_properties
    P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell
      (by linarith : 0 < ell) (hAtoms cell hBad) d rectangle hRectanglePhysical
  have hSpan := daiLiBadGridRectangle_horizontalSpan P embedding threshold d w
    (gridOrigin w t) atoms rectangles hRectangles cell hBad rectangle hRectangle
  have hVerticalSpan := daiLiBadGridRectangle_verticalSpan_le P embedding threshold d w ell
    (gridOrigin w t) atoms rectangles hAtoms hRectangles (by linarith : 0 < ell)
    cell hBad rectangle hRectangle
  have hHorizontalRadius : daiLiRectangleHorizontalRadius rectangle.1 rectangle.2 = w / 2 := by
    unfold daiLiRectangleHorizontalRadius
    linarith
  have hVerticalRadius : daiLiRectangleVerticalRadius rectangle.1 rectangle.2 ≤ w / 2 := by
    unfold daiLiRectangleVerticalRadius
    linarith
  have hBaseHorizontal' : baseHorizontalRadius ≤
      daiLiRectangleHorizontalRadius rectangle.1 rectangle.2 := by
    rw [hHorizontalRadius]
    exact hBaseHorizontal
  have hBaseVertical' : baseVerticalRadius ≤
      daiLiRectangleVerticalRadius rectangle.1 rectangle.2 := by
    unfold daiLiRectangleVerticalRadius
    linarith [hProperties.1]
  have hReachHorizontal' : daiLiRectangleHorizontalRadius rectangle.1 rectangle.2 ≤
      baseHorizontalRadius + steps * threshold := by
    rw [hHorizontalRadius]
    exact hReachHorizontal
  have hReachVertical' : daiLiRectangleVerticalRadius rectangle.1 rectangle.2 ≤
      baseVerticalRadius + steps * threshold :=
    hVerticalRadius.trans hReachVertical
  have hBoundaryBudget' :
      48 * (daiLiRectangleHorizontalRadius rectangle.1 rectangle.2 +
        daiLiRectangleVerticalRadius rectangle.1 rectangle.2 + threshold) * threshold +
        (d : ℝ) / 10 < d := by
    have hSum : daiLiRectangleHorizontalRadius rectangle.1 rectangle.2 +
        daiLiRectangleVerticalRadius rectangle.1 rectangle.2 + threshold ≤
        w / 2 + w / 2 + threshold := by
      rw [hHorizontalRadius]
      linarith
    have hScale : 0 ≤ 48 * threshold := by nlinarith
    have hScaled := mul_le_mul_of_nonneg_left hSum hScale
    nlinarith
  apply exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (Sum.inr (cell, slot)))
    (daiLiRectangleSubsystem embedding rectangle.1 rectangle.2)
  · change daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (Sum.inr (cell, slot)) ⊆ (daiLiRectangleSubsystem embedding rectangle.1 rectangle.2).selected
    simpa [daiLiRectangleSubsystem, rectangle] using
      (daiLiKGeDRegionCore_subset_rectangle P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
        (Sum.inr (cell, slot)))
  · simpa [rectangle] using
      (exists_erasureRecovery_daiLiRectangle_of_piece_alternative
        P embedding d hDistance threshold ell w rectangle.1 rectangle.2
        baseHorizontalRadius baseVerticalRadius steps hThreshold hBaseHorizontal'
        hBaseVertical' hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal'
        hReachVertical' hBaseCard hBoundaryBudget' hSpan hWidth hEll hProperties.1
        hShortPackingScale hProperties.2)

/-- Distinct finite source-region cores are fixed-generator decoupled.  This
uses the actual long-endpoint component of `C`, rather than treating
source-goodness as an ambient graph hypothesis. -/
theorem daiLiKGeDRegionCores_fixedGeneratorDecoupled
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell)
    (region other : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOther : other ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hne : region ≠ other) :
    P.fixedGeneratorDecoupled
      ((daiLiKGeDRegionCoreQubits P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles region : Finset ι) : Set ι)
      ((daiLiKGeDRegionCoreQubits P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles other : Finset ι) : Set ι) := by
  apply fixedGeneratorDecoupled_of_separated_outside_longEndpoints P embedding threshold
  · apply Finset.disjoint_left.mpr
    intro q hqRegion hqOther
    have hSeparation := daiLiKGeDRegionCores_separated P embedding d threshold w ell t
      atoms rectangles hAtoms hRectangles hEll hWidth region other hRegion hOther hne
      hqRegion hqOther
    have hZero : ell ≤ 0 := by
      simpa [UnitSeparatedEmbedding2D.distance, euclideanDistance2D] using hSeparation
    exact (not_le_of_gt hEll) hZero
  · intro q hq
    change q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles region at hq
    apply Finset.mem_compl.mpr
    intro hEndpoint
    exact (Finset.mem_filter.mp hq).2.1
      (Finset.mem_union_left _ (Finset.mem_union_right _ hEndpoint))
  · intro q hq
    change q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles other at hq
    apply Finset.mem_compl.mpr
    intro hEndpoint
    exact (Finset.mem_filter.mp hq).2.1
      (Finset.mem_union_left _ (Finset.mem_union_right _ hEndpoint))
  · intro p hp q hq
    exact hThresholdEll.trans
      (daiLiKGeDRegionCores_separated P embedding d threshold w ell t
        atoms rectangles hAtoms hRectangles hEll hWidth region other hRegion hOther hne hp hq)

/-- The finite union of all source-region cores has an actual CPTP erasure
recovery.  Each branch is discharged by its local construction, and the
family closure receives the proved geometric decoupling above. -/
theorem exists_erasureRecovery_daiLiKGeDRegionCoreFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ cell,
      Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBadBaseCard : ∀ cell slot,
      Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding
        (daiLiRectangleCenter
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).1
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).2)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem
          (daiLiKGeDRegionCoreFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem
          (daiLiKGeDRegionCoreFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)).complementSystem
        P.semanticCode
        (familyUnionSubsystem
          (daiLiKGeDRegionCoreFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)).erasureChannelFromRegister
        recovery := by
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
    (daiLiKGeDRegionCoreFamily P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
    (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)
  · intro region hRegion
    cases region with
    | inl cell =>
        exact
          (exists_erasureRecovery_daiLiKGeDGoodRegionCore P embedding d hDistance threshold w ell t
            rectangles cell hRegion baseHorizontalRadius baseVerticalRadius steps hThreshold
            hBaseHorizontal hBaseVerticalGood hBaseHorizontalDiameter hBaseVerticalDiameter
            hReachHorizontal hReachVerticalGood (hGoodBaseCard cell hRegion) hBoundaryBudget)
    | inr pair =>
        rcases pair with ⟨cell, slot⟩
        exact
          (exists_erasureRecovery_daiLiKGeDBadRegionCore P embedding d hDistance threshold w ell t
            atoms rectangles hAtoms hRectangles cell slot hRegion baseHorizontalRadius
            baseVerticalRadius steps hThreshold hWidthNat hEllNat hBaseHorizontal hBaseVerticalBad
            hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal hReachVerticalBad
            (hBadBaseCard cell slot hRegion) hBoundaryBudget hShortPackingScale)
  · intro region hRegion other hOther hne
    simpa [daiLiKGeDRegionCoreFamily, daiLiKGeDRegionCoreSubsystem] using
      (daiLiKGeDRegionCores_fixedGeneratorDecoupled P embedding d threshold w ell t
        atoms rectangles hAtoms hRectangles hEll hWidth hThresholdEll region other
        hRegion hOther hne)

/-! ## Canonical internal bad-rectangle sides

The outer sides of a bad-cell rectangle are already represented by the finite
grid-side family.  Each internal horizontal cut is therefore represented once,
by the upper side of its lower rectangle.  This prevents both a duplicate
component and an uncharged overlap in the source `B` region. -/

abbrev DaiLiKGeDInternalSideIndex := (ℤ × ℤ) × ℕ

/-- The finite canonical family of internal horizontal bad-rectangle cuts. -/
def daiLiKGeDInternalSideCandidates
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Finset DaiLiKGeDInternalSideIndex := by
  classical
  exact (daiLiBadGridCells P embedding threshold d w origin).biUnion fun cell =>
    ((Finset.range (rectangles cell).length).filter fun slot =>
      slot + 1 < (rectangles cell).length).image fun slot => (cell, slot)

/-- Candidate membership says exactly that the cut belongs to a bad cell and
has a following rectangle; it is not an arbitrary list coordinate. -/
theorem mem_daiLiKGeDInternalSideCandidates_iff
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) :
    (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d w origin rectangles ↔
      cell ∈ daiLiBadGridCells P embedding threshold d w origin ∧
        slot + 1 < (rectangles cell).length := by
  constructor
  · intro hMember
    rcases Finset.mem_biUnion.mp hMember with ⟨owner, hOwner, hImage⟩
    rcases Finset.mem_image.mp hImage with ⟨found, hFound, hEqual⟩
    have hOwnerEq : owner = cell := by
      exact congrArg Prod.fst hEqual
    have hFoundEq : found = slot := by
      exact congrArg Prod.snd hEqual
    subst owner
    subst found
    exact ⟨hOwner, (Finset.mem_filter.mp hFound).2⟩
  · rintro ⟨hBad, hNext⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨cell, hBad, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨slot, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · simpa using Nat.lt_trans (Nat.lt_succ_self slot) hNext
    · exact hNext

def daiLiKGeDInternalSideRectangle
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) : (ℝ × ℝ) × (ℝ × ℝ) :=
  daiLiKGeDRegionRectangle embedding w origin rectangles (Sum.inr side)

/-- One canonical internal cut, with the full source `C` removed. -/
def daiLiKGeDInternalSideQubits
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) : Finset ι :=
  daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles side).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles side).2 3 \
    daiLiKGeDSeparator P embedding threshold w ell t cells rectangles

def daiLiKGeDInternalSideSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) : FiniteSubsystem ι :=
  ⟨daiLiKGeDInternalSideQubits P embedding threshold w ell t cells rectangles side⟩

def daiLiKGeDInternalSideFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    DaiLiKGeDInternalSideIndex → FiniteSubsystem ι :=
  daiLiKGeDInternalSideSubsystem P embedding threshold w ell t cells rectangles

/-- A canonical internal bad-rectangle side has a direct CPTP recovery through
the local box-scale packing proof, then subset closure after the separator is
removed. -/
theorem exists_erasureRecovery_daiLiKGeDInternalSide
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEllNat : 1 ≤ ell) (hCellWidth : 5 * ell ≤ w)
    (hSideScale : 12 * ell * w < d)
    (side : DaiLiKGeDInternalSideIndex)
    (hCandidate : side ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDInternalSideSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDInternalSideSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).complementSystem
        P.semanticCode
        (daiLiKGeDInternalSideSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).erasureChannelFromRegister
        recovery := by
  rcases side with ⟨cell, slot⟩
  rcases (mem_daiLiKGeDInternalSideCandidates_iff P embedding threshold d w
    (gridOrigin w t) rectangles cell slot).1 hCandidate with ⟨hBad, hNext⟩
  have hSlot : slot < (rectangles cell).length := by omega
  let rectangle := daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles
    (cell, slot)
  have hRectangle : rectangle ∈ rectangles cell := by
    dsimp [rectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
      rectangles cell slot hSlot
  have hPhysical := hRectangle
  rw [hRectangles cell hBad] at hPhysical
  have hEll : 0 < ell := by linarith
  have hProperties := daiLiPhysicalGreedyRectangles_piece_properties
    P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell hEll
      (hAtoms cell hBad) d rectangle hPhysical
  have hSpan := daiLiBadGridRectangle_horizontalSpan P embedding threshold d w
    (gridOrigin w t) atoms rectangles hRectangles cell hBad rectangle hRectangle
  have hVerticalSpan := daiLiBadGridRectangle_verticalSpan_le P embedding threshold d w ell
    (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad rectangle hRectangle
  apply exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiKGeDInternalSideSubsystem P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles (cell, slot))
    (daiLiRectangleSideStripSubsystem embedding ell rectangle.1 rectangle.2 3)
  · exact Finset.sdiff_subset
  · simpa [daiLiKGeDInternalSideSubsystem, daiLiKGeDInternalSideQubits,
      daiLiKGeDInternalSideRectangle, rectangle] using
      (exists_erasureRecovery_daiLiRectangleSideStrip_of_box_scale P embedding d hDistance ell w
        rectangle.1 rectangle.2 hEllNat hCellWidth hSpan hProperties.1 hVerticalSpan
        hSideScale 3)

/-- Exact coordinate bounds for the raw upper-side strip of one canonical
internal cut.  The later pairwise proof uses these bounds before subtracting
the separator, so no geometric gap is hidden in a set-level wrapper. -/
theorem mem_daiLiKGeDInternalSideRawBounds
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).1
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2 3) :
    (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).1.1 + 2 * ell ≤
        (embedding.point q).1 ∧
      (embedding.point q).1 ≤
        (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.1 - 2 * ell ∧
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.2 - ell ≤
        (embedding.point q).2 ∧
      (embedding.point q).2 ≤
        (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.2 + ell := by
  rw [daiLiRectangleSideStripQubits,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
  refine ⟨hq.1.1, hq.1.2, ?_, hq.2.2⟩
  linarith [hq.2.1]

/-- Every canonical internal cut lies in the `4 * ell`-trimmed host cell.
The upper trimming uses the actual next list element, so it holds even when
the rectangle list has an arbitrary finite length. -/
theorem mem_daiLiKGeDInternalSide_strict_hostBounds
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ) (slot : ℕ)
    (hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (p : ι)
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3) :
    (gridOrigin w t).1 + (cell.1 : ℝ) * w + 2 * ell ≤ (embedding.point p).1 ∧
      (embedding.point p).1 ≤ (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - 2 * ell ∧
      (gridOrigin w t).2 + (cell.2 : ℝ) * w + 4 * ell ≤ (embedding.point p).2 ∧
      (embedding.point p).2 ≤ (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - 4 * ell := by
  rcases (mem_daiLiKGeDInternalSideCandidates_iff P embedding threshold d w
    (gridOrigin w t) rectangles cell slot).1 hCandidate with ⟨hBad, hNext⟩
  have hSlot : slot < (rectangles cell).length :=
    Nat.lt_trans (Nat.lt_succ_self slot) hNext
  let rectangle := daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles
    (cell, slot)
  let nextRectangle := daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles
    (cell, slot + 1)
  have hRectangle : rectangle ∈ rectangles cell := by
    dsimp [rectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
      rectangles cell slot hSlot
  have hNextRectangle : nextRectangle ∈ rectangles cell := by
    dsimp [nextRectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
      rectangles cell (slot + 1) hNext
  have hPhysical := hRectangle
  have hNextPhysical := hNextRectangle
  rw [hRectangles cell hBad] at hPhysical hNextPhysical
  have hProperties := daiLiPhysicalGreedyRectangles_piece_properties
    P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell hEll
      (hAtoms cell hBad) d rectangle hPhysical
  have hNextProperties := daiLiPhysicalGreedyRectangles_piece_properties
    P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell hEll
      (hAtoms cell hBad) d nextRectangle hNextPhysical
  have hParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell
    (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad rectangle hRectangle
  have hNextParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell
    (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad nextRectangle
      hNextRectangle
  have hOrder := daiLiBadGridRectangle_get_verticalOrder P embedding threshold d w ell
    (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad slot (slot + 1)
    hSlot hNext (Nat.lt_succ_self slot)
  have hRectangleEq : rectangle = (rectangles cell).get ⟨slot, hSlot⟩ := by
    dsimp [rectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
      rectangles cell slot hSlot
  have hNextRectangleEq : nextRectangle = (rectangles cell).get ⟨slot + 1, hNext⟩ := by
    dsimp [nextRectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
      rectangles cell (slot + 1) hNext
  have hOrder' : rectangle.2.2 ≤ nextRectangle.1.2 := by
    rw [hRectangleEq, hNextRectangleEq]
    exact hOrder
  have hpBounds := mem_daiLiKGeDInternalSideRawBounds embedding w ell (gridOrigin w t)
    rectangles (cell, slot) p hp
  simp only [gridCellLower, gridCellUpper] at hParent hNextParent
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hParent.1, hpBounds.1]
  · nlinarith [hParent.2.1, hpBounds.2.1]
  · nlinarith [hParent.2.2.1, hProperties.1, hpBounds.2.2.1]
  · nlinarith [hOrder', hNextProperties.1, hNextParent.2.2.2, hpBounds.2.2.2]

/-- Two distinct internal cuts in one actual bad-rectangle list are separated
by at least `ell`.  This is the list-order branch of the finite `B` geometry. -/
theorem daiLiKGeDInternalSides_sameHost_separated
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ) (slot otherSlot : ℕ)
    (hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOtherCandidate : (cell, otherSlot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hne : slot ≠ otherSlot) {p q : ι}
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, otherSlot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, otherSlot)).2 3) :
    ell ≤ embedding.distance p q := by
  rcases (mem_daiLiKGeDInternalSideCandidates_iff P embedding threshold d w
    (gridOrigin w t) rectangles cell slot).1 hCandidate with ⟨hBad, hNext⟩
  rcases (mem_daiLiKGeDInternalSideCandidates_iff P embedding threshold d w
    (gridOrigin w t) rectangles cell otherSlot).1 hOtherCandidate with ⟨_, hOtherNext⟩
  have hSlot : slot < (rectangles cell).length :=
    Nat.lt_trans (Nat.lt_succ_self slot) hNext
  have hOtherSlot : otherSlot < (rectangles cell).length :=
    Nat.lt_trans (Nat.lt_succ_self otherSlot) hOtherNext
  let rectangle := daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles
    (cell, slot)
  let otherRectangle := daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles
    (cell, otherSlot)
  have hRectangle : rectangle ∈ rectangles cell := by
    dsimp [rectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
      rectangles cell slot hSlot
  have hOtherRectangle : otherRectangle ∈ rectangles cell := by
    dsimp [otherRectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
      rectangles cell otherSlot hOtherSlot
  have hPhysical := hRectangle
  have hOtherPhysical := hOtherRectangle
  rw [hRectangles cell hBad] at hPhysical hOtherPhysical
  have hProperties := daiLiPhysicalGreedyRectangles_piece_properties
    P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell hEll
      (hAtoms cell hBad) d rectangle hPhysical
  have hOtherProperties := daiLiPhysicalGreedyRectangles_piece_properties
    P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell hEll
      (hAtoms cell hBad) d otherRectangle hOtherPhysical
  have hpBounds := mem_daiLiKGeDInternalSideRawBounds embedding w ell (gridOrigin w t)
    rectangles (cell, slot) p hp
  have hqBounds := mem_daiLiKGeDInternalSideRawBounds embedding w ell (gridOrigin w t)
    rectangles (cell, otherSlot) q hq
  rcases lt_or_gt_of_ne hne with hForward | hBackward
  · have hOrder := daiLiBadGridRectangle_get_verticalOrder P embedding threshold d w ell
      (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad slot otherSlot
      hSlot hOtherSlot hForward
    have hRectangleEq : rectangle = (rectangles cell).get ⟨slot, hSlot⟩ := by
      dsimp [rectangle, daiLiKGeDInternalSideRectangle]
      exact daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
        rectangles cell slot hSlot
    have hOtherRectangleEq : otherRectangle = (rectangles cell).get ⟨otherSlot, hOtherSlot⟩ := by
      dsimp [otherRectangle, daiLiKGeDInternalSideRectangle]
      exact daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
        rectangles cell otherSlot hOtherSlot
    have hOrder' : rectangle.2.2 ≤ otherRectangle.1.2 := by
      rw [hRectangleEq, hOtherRectangleEq]
      exact hOrder
    apply le_distance_of_le_abs_coordinate_y embedding
    rw [le_abs]
    right
    nlinarith [hpBounds.2.2.2, hqBounds.2.2.1, hOrder', hOtherProperties.1]
  · have hOrder := daiLiBadGridRectangle_get_verticalOrder P embedding threshold d w ell
      (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad otherSlot slot
      hOtherSlot hSlot hBackward
    have hRectangleEq : rectangle = (rectangles cell).get ⟨slot, hSlot⟩ := by
      dsimp [rectangle, daiLiKGeDInternalSideRectangle]
      exact daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
        rectangles cell slot hSlot
    have hOtherRectangleEq : otherRectangle = (rectangles cell).get ⟨otherSlot, hOtherSlot⟩ := by
      dsimp [otherRectangle, daiLiKGeDInternalSideRectangle]
      exact daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
        rectangles cell otherSlot hOtherSlot
    have hOrder' : otherRectangle.2.2 ≤ rectangle.1.2 := by
      rw [hRectangleEq, hOtherRectangleEq]
      exact hOrder
    apply le_distance_of_le_abs_coordinate_y embedding
    rw [le_abs]
    left
    nlinarith [hpBounds.2.2.1, hqBounds.2.2.2, hOrder', hProperties.1]

/-- Canonical internal cuts in different grid cells are separated by their
trimmed host-cell boxes. -/
theorem daiLiKGeDInternalSides_differentHost_separated
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (hWidth : 0 < w)
    (cell other : ℤ × ℤ) (slot otherSlot : ℕ)
    (hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOtherCandidate : (other, otherSlot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hCellNe : cell ≠ other) {p q : ι}
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (other, otherSlot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (other, otherSlot)).2 3) :
    ell ≤ embedding.distance p q := by
  have hpBounds := mem_daiLiKGeDInternalSide_strict_hostBounds P embedding d threshold w ell t
    atoms rectangles hAtoms hRectangles hEll cell slot hCandidate p hp
  have hqBounds := mem_daiLiKGeDInternalSide_strict_hostBounds P embedding d threshold w ell t
    atoms rectangles hAtoms hRectangles hEll other otherSlot hOtherCandidate q hq
  have hw0 : 0 ≤ w := hWidth.le
  by_cases hx : cell.1 = other.1
  · have hy : cell.2 ≠ other.2 := by
      intro hy
      apply hCellNe
      exact Prod.ext hx hy
    rcases lt_or_gt_of_ne hy with hForward | hBackward
    · have hInt : cell.2 + 1 ≤ other.2 := by omega
      have hReal : (cell.2 : ℝ) + 1 ≤ other.2 := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_y embedding
      rw [le_abs]
      right
      nlinarith [hpBounds.2.2.2, hqBounds.2.2.1, hMul]
    · have hInt : other.2 + 1 ≤ cell.2 := by omega
      have hReal : (other.2 : ℝ) + 1 ≤ cell.2 := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_y embedding
      rw [le_abs]
      left
      nlinarith [hpBounds.2.2.1, hqBounds.2.2.2, hMul]
  · rcases lt_or_gt_of_ne hx with hForward | hBackward
    · have hInt : cell.1 + 1 ≤ other.1 := by omega
      have hReal : (cell.1 : ℝ) + 1 ≤ other.1 := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      right
      nlinarith [hpBounds.2.1, hqBounds.1, hMul]
    · have hInt : other.1 + 1 ≤ cell.1 := by omega
      have hReal : (other.1 : ℝ) + 1 ≤ cell.1 := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      left
      nlinarith [hpBounds.1, hqBounds.2.1, hMul]

/-- Every pair of distinct canonical internal cuts is geometrically separated. -/
theorem daiLiKGeDInternalSides_separated
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (hWidth : 0 < w)
    (side other : DaiLiKGeDInternalSideIndex)
    (hCandidate : side ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOtherCandidate : other ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hne : side ≠ other) {p q : ι}
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles side).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles side).2 3)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles other).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles other).2 3) :
    ell ≤ embedding.distance p q := by
  rcases side with ⟨cell, slot⟩
  rcases other with ⟨other, otherSlot⟩
  by_cases hCell : cell = other
  · subst other
    have hSlot : slot ≠ otherSlot := by
      intro hEqual
      apply hne
      simp [hEqual]
    exact daiLiKGeDInternalSides_sameHost_separated P embedding d threshold w ell t
      atoms rectangles hAtoms hRectangles hEll cell slot otherSlot hCandidate hOtherCandidate
      hSlot hp hq
  · exact daiLiKGeDInternalSides_differentHost_separated P embedding d threshold w ell t
      atoms rectangles hAtoms hRectangles hEll hWidth cell other slot otherSlot hCandidate
      hOtherCandidate hCell hp hq

/-- The internal bad-rectangle side family is pairwise fixed-generator
decoupled after the concrete separator removes all long endpoints. -/
theorem daiLiKGeDInternalSides_fixedGeneratorDecoupled
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell)
    (side other : DaiLiKGeDInternalSideIndex)
    (hCandidate : side ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOtherCandidate : other ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hne : side ≠ other) :
    P.fixedGeneratorDecoupled
      ((daiLiKGeDInternalSideQubits P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side : Finset ι) : Set ι)
      ((daiLiKGeDInternalSideQubits P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles other : Finset ι) : Set ι) := by
  apply fixedGeneratorDecoupled_of_separated_outside_longEndpoints P embedding threshold
  · apply Finset.disjoint_left.mpr
    intro q hqSide hqOther
    have hSeparation := daiLiKGeDInternalSides_separated P embedding d threshold w ell t
      atoms rectangles hAtoms hRectangles hEll hWidth side other hCandidate hOtherCandidate hne
      (Finset.mem_sdiff.mp hqSide).1 (Finset.mem_sdiff.mp hqOther).1
    have hZero : ell ≤ 0 := by
      simpa [UnitSeparatedEmbedding2D.distance, euclideanDistance2D] using hSeparation
    exact (not_le_of_gt hEll) hZero
  · intro q hq
    apply Finset.mem_compl.mpr
    intro hEndpoint
    exact (Finset.mem_sdiff.mp hq).2
      (Finset.mem_union_left _ (Finset.mem_union_right _ hEndpoint))
  · intro q hq
    apply Finset.mem_compl.mpr
    intro hEndpoint
    exact (Finset.mem_sdiff.mp hq).2
      (Finset.mem_union_left _ (Finset.mem_union_right _ hEndpoint))
  · intro p hp q hq
    exact hThresholdEll.trans
      (daiLiKGeDInternalSides_separated P embedding d threshold w ell t
        atoms rectangles hAtoms hRectangles hEll hWidth side other hCandidate hOtherCandidate hne
        (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1)

/-- The finite union of canonical internal bad-rectangle sides has an actual
CPTP erasure recovery. -/
theorem exists_erasureRecovery_daiLiKGeDInternalSideFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEllNat : 1 ≤ ell) (hCellWidth : 5 * ell ≤ w)
    (hSideScale : 12 * ell * w < d)
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem
          (daiLiKGeDInternalSideFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem
          (daiLiKGeDInternalSideFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)).complementSystem
        P.semanticCode
        (familyUnionSubsystem
          (daiLiKGeDInternalSideFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)).erasureChannelFromRegister
        recovery := by
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
    (daiLiKGeDInternalSideFamily P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
    (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)
  · intro side hside
    exact
      (exists_erasureRecovery_daiLiKGeDInternalSide P embedding d hDistance threshold w ell t
        atoms rectangles hAtoms hRectangles hEllNat hCellWidth hSideScale side hside)
  · intro side hside other hother hne
    simpa [daiLiKGeDInternalSideFamily, daiLiKGeDInternalSideSubsystem] using
      (daiLiKGeDInternalSides_fixedGeneratorDecoupled P embedding d threshold w ell t
        atoms rectangles hAtoms hRectangles hEll hWidth hThresholdEll side other hside hother hne)

/-- A canonical internal bad-rectangle cut is separated from every finite
grid-side component.  The proof uses the explicit host-cell trimming instead
of an implicit periodic-space convention. -/
theorem daiLiKGeDInternalSide_gridSide_separated
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (hWidth : 0 < w)
    (cell : ℤ × ℤ) (slot : ℕ)
    (hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (gridSide : DaiLiGridSideIndex) {p q : ι}
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3)
    (hq : q ∈ daiLiGridSideStripQubits embedding w ell (2 * ell) (gridOrigin w t) gridSide) :
    ell ≤ embedding.distance p q := by
  have hpBounds := mem_daiLiKGeDInternalSide_strict_hostBounds P embedding d threshold w ell t
    atoms rectangles hAtoms hRectangles hEll cell slot hCandidate p hp
  have hw0 : 0 ≤ w := hWidth.le
  rcases gridSide with ⟨i, j, vertical⟩
  cases vertical
  · -- horizontal grid side
    simp [daiLiGridSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
    by_cases hBelow : j ≤ cell.2
    · have hReal : (j : ℝ) ≤ cell.2 := by exact_mod_cast hBelow
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_y embedding
      rw [le_abs]
      left
      nlinarith [hpBounds.2.2.1, hq.2.2, hMul]
    · have hInt : cell.2 + 1 ≤ j := by omega
      have hReal : (cell.2 : ℝ) + 1 ≤ j := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_y embedding
      rw [le_abs]
      right
      nlinarith [hpBounds.2.2.2, hq.2.1, hMul]
  · -- vertical grid side
    simp [daiLiGridSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
    by_cases hLeft : i ≤ cell.1
    · have hReal : (i : ℝ) ≤ cell.1 := by exact_mod_cast hLeft
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      left
      nlinarith [hpBounds.1, hq.1.2, hMul]
    · have hInt : cell.1 + 1 ≤ i := by omega
      have hReal : (cell.1 : ℝ) + 1 ≤ i := by exact_mod_cast hInt
      have hMul := mul_le_mul_of_nonneg_right hReal hw0
      apply le_distance_of_le_abs_coordinate_x embedding
      rw [le_abs]
      right
      nlinarith [hpBounds.2.1, hq.1.1, hMul]

/-- A canonical grid side for the `k >= d` partition, with every component
of the concrete source separator removed. -/
def daiLiKGeDGridSideQubits
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiGridSideIndex) : Finset ι :=
  daiLiGridSideStripQubits embedding w ell (2 * ell) (gridOrigin w t) side \
    daiLiKGeDSeparator P embedding threshold w ell t cells rectangles

def daiLiKGeDGridSideSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiGridSideIndex) : FiniteSubsystem ι :=
  ⟨daiLiKGeDGridSideQubits P embedding threshold w ell t cells rectangles side⟩

def daiLiKGeDGridSideFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    DaiLiGridSideIndex → FiniteSubsystem ι :=
  daiLiKGeDGridSideSubsystem P embedding threshold w ell t cells rectangles

def daiLiKGeDGridSideUnionSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  familyUnionSubsystem (daiLiKGeDGridSideFamily P embedding threshold w ell t cells rectangles)
    (daiLiGridSideCandidates embedding w (gridOrigin w t))

def daiLiKGeDInternalSideUnionSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  familyUnionSubsystem (daiLiKGeDInternalSideFamily P embedding threshold w ell t cells rectangles)
    (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)

/-- The concrete `k >= d` grid-side union inherits an actual CPTP recovery
from the established good grid-side family by selected-subsystem closure. -/
theorem exists_erasureRecovery_daiLiKGeDGridSideUnion
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    {w ell : ℝ} (hEll : 0 < ell) (hWidth : 4 * ell ≤ w)
    (threshold : ℝ) (hThresholdEll : threshold ≤ ell)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hEdge : 1 ≤ 2 * ell) (hLong : 1 ≤ w - 4 * ell)
    (hSideSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).complementSystem
        P.semanticCode
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).erasureChannelFromRegister
        recovery := by
  obtain ⟨recovery, hRecovery⟩ := exists_erasureRecovery_daiLiGridSideGoodFamily
    P embedding d hDistance hEll hWidth threshold hThresholdEll (gridOrigin w t)
    (daiLiGridSideCandidates embedding w (gridOrigin w t)) hEdge hLong hSideSmall
  apply exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles)
    (familyUnionSubsystem (daiLiGridSideGoodFamily P embedding threshold w ell (gridOrigin w t))
      (daiLiGridSideCandidates embedding w (gridOrigin w t)))
  · intro q hq
    change q ∈ (daiLiGridSideCandidates embedding w (gridOrigin w t)).biUnion
      (fun side => (daiLiKGeDGridSideFamily P embedding threshold w ell t cells rectangles side).selected) at hq
    rcases Finset.mem_biUnion.mp hq with ⟨side, hside, hqSide⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨side, hside, ?_⟩
    change q ∈ daiLiGridSideGoodQubits P embedding threshold w ell (gridOrigin w t) side
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp hqSide).1, ?_⟩
    intro hEndpoint
    exact (Finset.mem_sdiff.mp hqSide).2
      (Finset.mem_union_left _ (Finset.mem_union_right _ hEndpoint))
  · exact ⟨recovery, hRecovery⟩

/-- The two finite `k >= d` side unions are fixed-generator decoupled.  This
is the cross-family Union-Lemma contract for `B`. -/
theorem daiLiKGeDGridSideUnion_fixedGeneratorDecoupled_internal
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell) :
    P.fixedGeneratorDecoupled
      ((daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected : Set ι)
      ((daiLiKGeDInternalSideUnionSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected : Set ι) := by
  apply fixedGeneratorDecoupled_of_separated_outside_longEndpoints P embedding threshold
  · apply Finset.disjoint_left.mpr
    intro q hqGrid hqInternal
    change q ∈ (daiLiGridSideCandidates embedding w (gridOrigin w t)).biUnion
      (fun side => (daiLiKGeDGridSideFamily P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).selected) at hqGrid
    change q ∈ (daiLiKGeDInternalSideCandidates P embedding threshold d w
      (gridOrigin w t) rectangles).biUnion
      (fun side => (daiLiKGeDInternalSideFamily P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).selected) at hqInternal
    rcases Finset.mem_biUnion.mp hqGrid with ⟨gridSide, _, hqGridSide⟩
    rcases Finset.mem_biUnion.mp hqInternal with ⟨internalSide, hInternalSide, hqInternalSide⟩
    rcases internalSide with ⟨cell, slot⟩
    have hSeparation := daiLiKGeDInternalSide_gridSide_separated P embedding d threshold w ell t
      atoms rectangles hAtoms hRectangles hEll hWidth cell slot hInternalSide gridSide
      (Finset.mem_sdiff.mp hqInternalSide).1 (Finset.mem_sdiff.mp hqGridSide).1
    have hZero : ell ≤ 0 := by
      simpa [UnitSeparatedEmbedding2D.distance, euclideanDistance2D] using hSeparation
    exact (not_le_of_gt hEll) hZero
  · intro q hq
    change q ∈ (daiLiGridSideCandidates embedding w (gridOrigin w t)).biUnion
      (fun side => (daiLiKGeDGridSideFamily P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).selected) at hq
    rcases Finset.mem_biUnion.mp hq with ⟨side, _, hqSide⟩
    apply Finset.mem_compl.mpr
    intro hEndpoint
    exact (Finset.mem_sdiff.mp hqSide).2
      (Finset.mem_union_left _ (Finset.mem_union_right _ hEndpoint))
  · intro q hq
    change q ∈ (daiLiKGeDInternalSideCandidates P embedding threshold d w
      (gridOrigin w t) rectangles).biUnion
      (fun side => (daiLiKGeDInternalSideFamily P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).selected) at hq
    rcases Finset.mem_biUnion.mp hq with ⟨side, _, hqSide⟩
    apply Finset.mem_compl.mpr
    intro hEndpoint
    exact (Finset.mem_sdiff.mp hqSide).2
      (Finset.mem_union_left _ (Finset.mem_union_right _ hEndpoint))
  · intro p hp q hq
    change p ∈ (daiLiGridSideCandidates embedding w (gridOrigin w t)).biUnion
      (fun side => (daiLiKGeDGridSideFamily P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).selected) at hp
    change q ∈ (daiLiKGeDInternalSideCandidates P embedding threshold d w
      (gridOrigin w t) rectangles).biUnion
      (fun side => (daiLiKGeDInternalSideFamily P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).selected) at hq
    rcases Finset.mem_biUnion.mp hp with ⟨gridSide, _, hpGridSide⟩
    rcases Finset.mem_biUnion.mp hq with ⟨internalSide, hInternalSide, hqInternalSide⟩
    rcases internalSide with ⟨cell, slot⟩
    have hSeparation := daiLiKGeDInternalSide_gridSide_separated P embedding d threshold w ell t
      atoms rectangles hAtoms hRectangles hEll hWidth cell slot hInternalSide gridSide
      (Finset.mem_sdiff.mp hqInternalSide).1 (Finset.mem_sdiff.mp hpGridSide).1
    rw [embedding.distance_comm q p] at hSeparation
    exact hThresholdEll.trans hSeparation

/-- The source `B` region in the finite `k >= d` partition: all canonical
grid sides and all canonical internal bad-rectangle cuts, both with `C`
removed. -/
def daiLiKGeDBSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  unionSubsystem
    (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles)
    (daiLiKGeDInternalSideUnionSubsystem P embedding d threshold w ell t cells rectangles)

/-- The complete finite `k >= d` source-side region `B` has an actual CPTP
erasure recovery. -/
theorem exists_erasureRecovery_daiLiKGeDB
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEllNat : 1 ≤ ell) (hCellWidth : 5 * ell ≤ w)
    (hInternalSideScale : 12 * ell * w < d)
    (hEll : 0 < ell) (hGridWidth : 4 * ell ≤ w)
    (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        P.semanticCode
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).erasureChannelFromRegister
        recovery := by
  have hWidth : 0 < w := by nlinarith
  obtain ⟨gridRecovery, hGridRecovery⟩ := exists_erasureRecovery_daiLiKGeDGridSideUnion
    P embedding d hDistance hEll hGridWidth threshold hThresholdEll t
    (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
    hEdge hGridLong hGridSideSmall
  obtain ⟨internalRecovery, hInternalRecovery⟩ :=
    exists_erasureRecovery_daiLiKGeDInternalSideFamily P embedding d hDistance threshold w ell t
      atoms rectangles hAtoms hRectangles hEllNat hCellWidth hInternalSideScale hEll hWidth
      hThresholdEll
  exact
    (exists_erasureRecovery_of_fixedGeneratorDecoupled P
      (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      (daiLiKGeDInternalSideUnionSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      gridRecovery internalRecovery hGridRecovery hInternalRecovery
      (daiLiKGeDGridSideUnion_fixedGeneratorDecoupled_internal P embedding d threshold w ell t
        atoms rectangles hAtoms hRectangles hEll hWidth hThresholdEll))

/-- The source `A` region in the finite `k >= d` branch: the union of strict
good-cell and actual bad-rectangle cores. -/
def daiLiKGeDASubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  familyUnionSubsystem
    (daiLiKGeDRegionCoreFamily P embedding threshold w ell t cells rectangles)
    (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)

/-- The two-region dimension lemma receives `B` after removing any point also
assigned to `A`; its recovery is later inherited from the concrete source-side
construction above. -/
def daiLiKGeDTrimmedBSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  ⟨(daiLiKGeDBSubsystem P embedding d threshold w ell t cells rectangles).selected \
    (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected⟩

/-- The third region in the finite `k >= d` partition.  The geometric
assignment below proves that it is a subset of the concrete source `C`. -/
def daiLiKGeDResidualSubsystem
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) : FiniteSubsystem ι :=
  ⟨Finset.univ \
    ((daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected ∪
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected)⟩

/-- The finite `k >= d` partition components are pairwise disjoint by the
chosen trimming and residual construction. -/
theorem daiLiKGeD_partition_pairwise
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Disjoint (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected ∧
    Disjoint (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t cells rectangles).selected ∧
    Disjoint (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t cells rectangles).selected := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hA hB
    exact (Finset.mem_sdiff.mp hB).2 hA
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hA hC
    exact (Finset.mem_sdiff.mp hC).2 (Finset.mem_union_left _ hA)
  · apply Finset.disjoint_left.mpr
    intro q hB hC
    exact (Finset.mem_sdiff.mp hC).2 (Finset.mem_union_right _ hB)

/-- The selected `A`, trimmed `B`, and residual regions cover all finite
physical qubits. -/
theorem daiLiKGeD_partition_cover
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected ∪
        (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected ∪
          (daiLiKGeDResidualSubsystem P embedding d threshold w ell t cells rectangles).selected =
      Finset.univ := by
  ext q
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    by_cases hq : q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected ∪
        (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected
    · rcases Finset.mem_union.mp hq with hA | hB
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union_left _ hA))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union_right _ hB))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq⟩))

/-- One selected finite source-region core belongs to the assembled `A`
subsystem. -/
theorem mem_daiLiKGeDRegionCore_into_A
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hq : q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region) :
    q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected := by
  change q ∈ (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles).biUnion
    (fun index => (daiLiKGeDRegionCoreFamily P embedding threshold w ell t cells rectangles
      index).selected)
  apply Finset.mem_biUnion.mpr
  refine ⟨region, hRegion, ?_⟩
  simpa [daiLiKGeDRegionCoreFamily, daiLiKGeDRegionCoreSubsystem] using hq

/-- One selected canonical grid side belongs to the assembled untrimmed `B`
subsystem. -/
theorem mem_daiLiKGeDGridSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiGridSideIndex)
    (hSide : side ∈ daiLiGridSideCandidates embedding w (gridOrigin w t)) (q : ι)
    (hq : q ∈ daiLiKGeDGridSideQubits P embedding threshold w ell t cells rectangles side) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t cells rectangles).selected := by
  apply Finset.mem_union_left
  change q ∈ (daiLiGridSideCandidates embedding w (gridOrigin w t)).biUnion
    (fun index => (daiLiKGeDGridSideFamily P embedding threshold w ell t cells rectangles
      index).selected)
  apply Finset.mem_biUnion.mpr
  refine ⟨side, hSide, ?_⟩
  simpa [daiLiKGeDGridSideFamily, daiLiKGeDGridSideSubsystem] using hq

/-- One selected internal bad-rectangle cut belongs to the assembled
untrimmed `B` subsystem. -/
theorem mem_daiLiKGeDInternalSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex)
    (hSide : side ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hq : q ∈ daiLiKGeDInternalSideQubits P embedding threshold w ell t cells rectangles side) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t cells rectangles).selected := by
  apply Finset.mem_union_right
  change q ∈ (daiLiKGeDInternalSideCandidates P embedding threshold d w
      (gridOrigin w t) rectangles).biUnion
    (fun index => (daiLiKGeDInternalSideFamily P embedding threshold w ell t cells rectangles
      index).selected)
  apply Finset.mem_biUnion.mpr
  refine ⟨side, hSide, ?_⟩
  simpa [daiLiKGeDInternalSideFamily, daiLiKGeDInternalSideSubsystem] using hq

/-- Avoiding the concrete `k >= d` separator excludes every vertex
neighborhood of every actual indexed bad rectangle. -/
theorem not_mem_daiLiKGeDSeparator_not_badRectangleVertex
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (q : ι) (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (cell : ℤ × ℤ) (hCell : cell ∈ cells) (slot : ℕ)
    (hSlot : slot < (rectangles cell).length) (vertex : Fin 4) :
    q ∉ daiLiVertexNeighborhoodQubits embedding ell
      (daiLiRectangleVertex ((rectangles cell).get ⟨slot, hSlot⟩) vertex) := by
  intro hVertex
  apply hNotSeparator
  apply Finset.mem_union_right
  exact daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer
    embedding ell cells rectangles cell hCell slot hSlot vertex hVertex

/-- A strict, separator-free point of one indexed actual bad rectangle is
assigned to the concrete `A` subsystem. -/
theorem mem_daiLiKGeDBadRectangleCore_into_A
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) (hSlot : slot < (rectangles cell).length)
    (hCandidate : Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hRect : q ∈ embedding.qubitsInRectangle
      ((rectangles cell).get ⟨slot, hSlot⟩).1 ((rectangles cell).get ⟨slot, hSlot⟩).2)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (hStrict : ((rectangles cell).get ⟨slot, hSlot⟩).1.1 + ell < (embedding.point q).1 ∧
      (embedding.point q).1 < ((rectangles cell).get ⟨slot, hSlot⟩).2.1 - ell ∧
        ((rectangles cell).get ⟨slot, hSlot⟩).1.2 + ell < (embedding.point q).2 ∧
          (embedding.point q).2 < ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - ell) :
    q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected := by
  have hCore : q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles
      (Sum.inr (cell, slot)) := by
    change q ∈ (embedding.qubitsInRectangle
      (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
        (Sum.inr (cell, slot))).1
      (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
        (Sum.inr (cell, slot))).2).filter _
    rw [daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
      rectangles cell slot hSlot]
    exact Finset.mem_filter.mpr ⟨hRect, ⟨hNotSeparator, hStrict⟩⟩
  exact mem_daiLiKGeDRegionCore_into_A P embedding d threshold w ell t cells rectangles
    (Sum.inr (cell, slot)) hCandidate q hCore

/-- The left edge strip of an actual bad-cell rectangle is contained in the
canonical left grid-side component. -/
theorem mem_daiLiKGeDBadRectangle_leftSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
    (slot : ℕ) (hSlot : slot < (rectangles cell).length) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      ((rectangles cell).get ⟨slot, hSlot⟩).1 ((rectangles cell).get ⟨slot, hSlot⟩).2 0)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
  have hOccupied : cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) :=
    (mem_daiLiBadGridCells_iff P embedding threshold d w (gridOrigin w t) cell).1 hCell |>.1
  have hSide : (cell.1, cell.2, true) ∈ daiLiGridSideCandidates embedding w (gridOrigin w t) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨cell, hOccupied, ?_⟩
    simp
  apply mem_daiLiKGeDGridSide_into_B P embedding d threshold w ell t
    (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
    (cell.1, cell.2, true) hSide q
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, hNotSeparator⟩
  have hParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell (gridOrigin w t)
    atoms rectangles hAtoms hRectangles hEll cell hCell
    ((rectangles cell).get ⟨slot, hSlot⟩) (List.get_mem _ _)
  have hXLower : (gridOrigin w t).1 + (cell.1 : ℝ) * w =
      ((rectangles cell).get ⟨slot, hSlot⟩).1.1 := by
    simpa [gridCellLower] using hParent.1
  have hXUpper : ((rectangles cell).get ⟨slot, hSlot⟩).2.1 =
      (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w := by
    simpa [gridCellUpper] using hParent.2.1
  have hYLower : (gridOrigin w t).2 + (cell.2 : ℝ) * w ≤
      ((rectangles cell).get ⟨slot, hSlot⟩).1.2 := by
    simpa [gridCellLower] using hParent.2.2.1
  have hYUpper : ((rectangles cell).get ⟨slot, hSlot⟩).2.2 ≤
      (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w := by
    simpa [gridCellUpper] using hParent.2.2.2
  simp [daiLiRectangleSideStripQubits,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff, rectangle] at hq
  change
    (((rectangles cell).get ⟨slot, hSlot⟩).1.1 - ell ≤ (embedding.point q).1 ∧
      ((rectangles cell).get ⟨slot, hSlot⟩).1.2 + 2 * ell ≤ (embedding.point q).2) ∧
      ((embedding.point q).1 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).1.1 + ell ∧
        (embedding.point q).2 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - 2 * ell) at hq
  simp [daiLiGridSideStripQubits,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff, rectangle]
  change
    ((gridOrigin w t).1 + (cell.1 : ℝ) * w - ell ≤ (embedding.point q).1 ∧
      (gridOrigin w t).2 + (cell.2 : ℝ) * w + 2 * ell ≤ (embedding.point q).2) ∧
      ((embedding.point q).1 ≤ (gridOrigin w t).1 + (cell.1 : ℝ) * w + ell ∧
        (embedding.point q).2 ≤ (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - 2 * ell)
  rcases hq with ⟨⟨hxLower, hyLower⟩, ⟨hxUpper, hyUpper⟩⟩
  exact ⟨⟨by
      calc
        (gridOrigin w t).1 + (cell.1 : ℝ) * w - ell =
            ((rectangles cell).get ⟨slot, hSlot⟩).1.1 - ell := by rw [hXLower]
        _ ≤ (embedding.point q).1 := hxLower,
      by
      calc
        (gridOrigin w t).2 + (cell.2 : ℝ) * w + 2 * ell ≤
            ((rectangles cell).get ⟨slot, hSlot⟩).1.2 + 2 * ell := by
              linarith [hYLower]
        _ ≤ (embedding.point q).2 := hyLower⟩,
    ⟨by
      calc
        (embedding.point q).1 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).1.1 + ell := hxUpper
        _ = (gridOrigin w t).1 + (cell.1 : ℝ) * w + ell := by rw [← hXLower],
      by
      calc
        (embedding.point q).2 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - 2 * ell := hyUpper
        _ ≤ (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - 2 * ell := by
          linarith [hYUpper]⟩⟩

/-- The right edge strip of an actual bad-cell rectangle is contained in the
canonical right grid-side component. -/
theorem mem_daiLiKGeDBadRectangle_rightSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
    (slot : ℕ) (hSlot : slot < (rectangles cell).length) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      ((rectangles cell).get ⟨slot, hSlot⟩).1 ((rectangles cell).get ⟨slot, hSlot⟩).2 1)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
  have hOccupied : cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) :=
    (mem_daiLiBadGridCells_iff P embedding threshold d w (gridOrigin w t) cell).1 hCell |>.1
  have hSide : (cell.1 + 1, cell.2, true) ∈
      daiLiGridSideCandidates embedding w (gridOrigin w t) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨cell, hOccupied, ?_⟩
    simp
  apply mem_daiLiKGeDGridSide_into_B P embedding d threshold w ell t
    (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
    (cell.1 + 1, cell.2, true) hSide q
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, hNotSeparator⟩
  have hParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell (gridOrigin w t)
    atoms rectangles hAtoms hRectangles hEll cell hCell
    ((rectangles cell).get ⟨slot, hSlot⟩) (List.get_mem _ _)
  have hXUpper : ((rectangles cell).get ⟨slot, hSlot⟩).2.1 =
      (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w := by
    simpa [gridCellUpper] using hParent.2.1
  have hYLower : (gridOrigin w t).2 + (cell.2 : ℝ) * w ≤
      ((rectangles cell).get ⟨slot, hSlot⟩).1.2 := by
    simpa [gridCellLower] using hParent.2.2.1
  have hYUpper : ((rectangles cell).get ⟨slot, hSlot⟩).2.2 ≤
      (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w := by
    simpa [gridCellUpper] using hParent.2.2.2
  simp [daiLiRectangleSideStripQubits,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff, rectangle] at hq
  change
    (((rectangles cell).get ⟨slot, hSlot⟩).2.1 - ell ≤ (embedding.point q).1 ∧
      ((rectangles cell).get ⟨slot, hSlot⟩).1.2 + 2 * ell ≤ (embedding.point q).2) ∧
      ((embedding.point q).1 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.1 + ell ∧
        (embedding.point q).2 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - 2 * ell) at hq
  simp [daiLiGridSideStripQubits,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff, rectangle]
  change
    ((gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - ell ≤ (embedding.point q).1 ∧
      (gridOrigin w t).2 + (cell.2 : ℝ) * w + 2 * ell ≤ (embedding.point q).2) ∧
      ((embedding.point q).1 ≤ (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w + ell ∧
        (embedding.point q).2 ≤ (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - 2 * ell)
  rcases hq with ⟨⟨hxLower, hyLower⟩, ⟨hxUpper, hyUpper⟩⟩
  exact ⟨⟨by
      calc
        (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - ell =
            ((rectangles cell).get ⟨slot, hSlot⟩).2.1 - ell := by rw [hXUpper]
        _ ≤ (embedding.point q).1 := hxLower,
      by
      calc
        (gridOrigin w t).2 + (cell.2 : ℝ) * w + 2 * ell ≤
            ((rectangles cell).get ⟨slot, hSlot⟩).1.2 + 2 * ell := by
              linarith [hYLower]
        _ ≤ (embedding.point q).2 := hyLower⟩,
    ⟨by
      calc
        (embedding.point q).1 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.1 + ell := hxUpper
        _ = (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w + ell := by rw [hXUpper],
      by
      calc
        (embedding.point q).2 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - 2 * ell := hyUpper
        _ ≤ (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - 2 * ell := by
          linarith [hYUpper]⟩⟩

/-- The upper strip of an actual bad-cell rectangle is assigned either to its
unique following-cut component or, for the final rectangle, to the upper grid
boundary component. -/
theorem mem_daiLiKGeDBadRectangle_topSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
    (slot : ℕ) (hSlot : slot < (rectangles cell).length) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      ((rectangles cell).get ⟨slot, hSlot⟩).1 ((rectangles cell).get ⟨slot, hSlot⟩).2 3)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
  by_cases hNext : slot + 1 < (rectangles cell).length
  · have hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
        w (gridOrigin w t) rectangles :=
      (mem_daiLiKGeDInternalSideCandidates_iff P embedding threshold d w
        (gridOrigin w t) rectangles cell slot).2 ⟨hCell, hNext⟩
    apply mem_daiLiKGeDInternalSide_into_B P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (cell, slot) hCandidate q
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hNotSeparator⟩
    change q ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3
    rw [daiLiKGeDInternalSideRectangle,
      daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
        rectangles cell slot hSlot]
    exact hq
  · have hLast : slot + 1 = (rectangles cell).length := by omega
    have hOccupied : cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) :=
      (mem_daiLiBadGridCells_iff P embedding threshold d w (gridOrigin w t) cell).1 hCell |>.1
    have hSide : (cell.1, cell.2 + 1, false) ∈
        daiLiGridSideCandidates embedding w (gridOrigin w t) := by
      apply Finset.mem_biUnion.mpr
      refine ⟨cell, hOccupied, ?_⟩
      simp
    apply mem_daiLiKGeDGridSide_into_B P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (cell.1, cell.2 + 1, false) hSide q
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hNotSeparator⟩
    have hParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell (gridOrigin w t)
      atoms rectangles hAtoms hRectangles hEll cell hCell
      ((rectangles cell).get ⟨slot, hSlot⟩) (List.get_mem _ _)
    have hXLower : (gridOrigin w t).1 + (cell.1 : ℝ) * w =
        ((rectangles cell).get ⟨slot, hSlot⟩).1.1 := by
      simpa [gridCellLower] using hParent.1
    have hXUpper : ((rectangles cell).get ⟨slot, hSlot⟩).2.1 =
        (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w := by
      simpa [gridCellUpper] using hParent.2.1
    have hTop : ((rectangles cell).get ⟨slot, hSlot⟩).2.2 =
        (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w := by
      simpa [gridCellUpper] using
        (daiLiBadGridRectangle_last_upper_eq_parent P embedding threshold d w ell (gridOrigin w t)
          atoms rectangles hAtoms hRectangles cell hCell slot hSlot hLast)
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff, rectangle] at hq
    change
      (((rectangles cell).get ⟨slot, hSlot⟩).1.1 + 2 * ell ≤ (embedding.point q).1 ∧
        ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - ell ≤ (embedding.point q).2) ∧
        ((embedding.point q).1 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.1 - 2 * ell ∧
          (embedding.point q).2 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.2 + ell) at hq
    simp [daiLiGridSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff, rectangle]
    change
      ((gridOrigin w t).1 + (cell.1 : ℝ) * w + 2 * ell ≤ (embedding.point q).1 ∧
        (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - ell ≤ (embedding.point q).2) ∧
        ((embedding.point q).1 ≤ (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - 2 * ell ∧
          (embedding.point q).2 ≤ (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w + ell)
    rcases hq with ⟨⟨hxLower, hyLower⟩, ⟨hxUpper, hyUpper⟩⟩
    exact ⟨⟨by
        calc
          (gridOrigin w t).1 + (cell.1 : ℝ) * w + 2 * ell =
              ((rectangles cell).get ⟨slot, hSlot⟩).1.1 + 2 * ell := by rw [hXLower]
          _ ≤ (embedding.point q).1 := hxLower,
        by
        calc
          (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - ell =
              ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - ell := by rw [hTop]
          _ ≤ (embedding.point q).2 := hyLower⟩,
      ⟨by
        calc
          (embedding.point q).1 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.1 - 2 * ell := hxUpper
          _ = (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - 2 * ell := by rw [hXUpper],
        by
        calc
          (embedding.point q).2 ≤ ((rectangles cell).get ⟨slot, hSlot⟩).2.2 + ell := hyUpper
          _ = (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w + ell := by rw [hTop]⟩⟩

/-- The lower strip of an actual bad-cell rectangle is assigned to the lower
grid boundary only for the first rectangle; otherwise it is the preceding
rectangle's already-canonical upper cut. -/
theorem mem_daiLiKGeDBadRectangle_bottomSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
    (slot : ℕ) (hSlot : slot < (rectangles cell).length) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      ((rectangles cell).get ⟨slot, hSlot⟩).1 ((rectangles cell).get ⟨slot, hSlot⟩).2 2)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
  by_cases hZero : slot = 0
  · subst slot
    have hOccupied : cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) :=
      (mem_daiLiBadGridCells_iff P embedding threshold d w (gridOrigin w t) cell).1 hCell |>.1
    have hSide : (cell.1, cell.2, false) ∈
        daiLiGridSideCandidates embedding w (gridOrigin w t) := by
      apply Finset.mem_biUnion.mpr
      refine ⟨cell, hOccupied, ?_⟩
      simp
    apply mem_daiLiKGeDGridSide_into_B P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (cell.1, cell.2, false) hSide q
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hNotSeparator⟩
    have hParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell (gridOrigin w t)
      atoms rectangles hAtoms hRectangles hEll cell hCell
      ((rectangles cell).get ⟨0, hSlot⟩) (List.get_mem _ _)
    have hXLower : (gridOrigin w t).1 + (cell.1 : ℝ) * w =
        ((rectangles cell).get ⟨0, hSlot⟩).1.1 := by
      simpa [gridCellLower] using hParent.1
    have hXUpper : ((rectangles cell).get ⟨0, hSlot⟩).2.1 =
        (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w := by
      simpa [gridCellUpper] using hParent.2.1
    have hBottom : ((rectangles cell).get ⟨0, hSlot⟩).1.2 =
        (gridOrigin w t).2 + (cell.2 : ℝ) * w := by
      simpa [gridCellLower] using
        (daiLiBadGridRectangle_first_lower_eq_parent P embedding threshold d w ell (gridOrigin w t)
          atoms rectangles hAtoms hRectangles cell hCell hSlot)
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff, rectangle] at hq
    change
      (((rectangles cell).get ⟨0, hSlot⟩).1.1 + 2 * ell ≤ (embedding.point q).1 ∧
        ((rectangles cell).get ⟨0, hSlot⟩).1.2 - ell ≤ (embedding.point q).2) ∧
        ((embedding.point q).1 ≤ ((rectangles cell).get ⟨0, hSlot⟩).2.1 - 2 * ell ∧
          (embedding.point q).2 ≤ ((rectangles cell).get ⟨0, hSlot⟩).1.2 + ell) at hq
    simp [daiLiGridSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff, rectangle]
    change
      ((gridOrigin w t).1 + (cell.1 : ℝ) * w + 2 * ell ≤ (embedding.point q).1 ∧
        (gridOrigin w t).2 + (cell.2 : ℝ) * w - ell ≤ (embedding.point q).2) ∧
        ((embedding.point q).1 ≤ (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - 2 * ell ∧
          (embedding.point q).2 ≤ (gridOrigin w t).2 + (cell.2 : ℝ) * w + ell)
    rcases hq with ⟨⟨hxLower, hyLower⟩, ⟨hxUpper, hyUpper⟩⟩
    exact ⟨⟨by
        calc
          (gridOrigin w t).1 + (cell.1 : ℝ) * w + 2 * ell =
              ((rectangles cell).get ⟨0, hSlot⟩).1.1 + 2 * ell := by rw [hXLower]
          _ ≤ (embedding.point q).1 := hxLower,
        by
        calc
          (gridOrigin w t).2 + (cell.2 : ℝ) * w - ell =
              ((rectangles cell).get ⟨0, hSlot⟩).1.2 - ell := by rw [hBottom]
          _ ≤ (embedding.point q).2 := hyLower⟩,
      ⟨by
        calc
          (embedding.point q).1 ≤ ((rectangles cell).get ⟨0, hSlot⟩).2.1 - 2 * ell := hxUpper
          _ = (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - 2 * ell := by rw [hXUpper],
        by
        calc
          (embedding.point q).2 ≤ ((rectangles cell).get ⟨0, hSlot⟩).1.2 + ell := hyUpper
          _ = (gridOrigin w t).2 + (cell.2 : ℝ) * w + ell := by rw [hBottom]⟩⟩
  · have hPrev : slot - 1 < (rectangles cell).length := by omega
    have hNext : slot - 1 + 1 < (rectangles cell).length := by omega
    have hPrevSucc : slot - 1 + 1 = slot := by omega
    have hAdjacent := daiLiBadGridRectangle_adjacent_verticalBoundary P embedding threshold d w ell
      (gridOrigin w t) atoms rectangles hAtoms hRectangles cell hCell (slot - 1) hPrev hNext
    have hCut : ((rectangles cell).get ⟨slot - 1, hPrev⟩).2.2 =
        ((rectangles cell).get ⟨slot, hSlot⟩).1.2 := by
      simpa [hPrevSucc] using hAdjacent
    have hParentPrev := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell
      (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hCell
      ((rectangles cell).get ⟨slot - 1, hPrev⟩) (List.get_mem _ _)
    have hParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell (gridOrigin w t)
      atoms rectangles hAtoms hRectangles hEll cell hCell
      ((rectangles cell).get ⟨slot, hSlot⟩) (List.get_mem _ _)
    have hLeft : ((rectangles cell).get ⟨slot - 1, hPrev⟩).1.1 =
        ((rectangles cell).get ⟨slot, hSlot⟩).1.1 :=
      hParentPrev.1.symm.trans hParent.1
    have hRight : ((rectangles cell).get ⟨slot - 1, hPrev⟩).2.1 =
        ((rectangles cell).get ⟨slot, hSlot⟩).2.1 :=
      hParentPrev.2.1.trans hParent.2.1.symm
    have hLeftElem : (rectangles cell)[slot - 1].1.1 = (rectangles cell)[slot].1.1 := by
      simpa using hLeft
    have hRightElem : (rectangles cell)[slot - 1].2.1 = (rectangles cell)[slot].2.1 := by
      simpa using hRight
    have hCutElem : (rectangles cell)[slot - 1].2.2 = (rectangles cell)[slot].1.2 := by
      simpa using hCut
    have hqTop : q ∈ daiLiRectangleSideStripQubits embedding ell
        ((rectangles cell).get ⟨slot - 1, hPrev⟩).1
        ((rectangles cell).get ⟨slot - 1, hPrev⟩).2 3 := by
      simpa [daiLiRectangleSideStripQubits, hLeftElem, hRightElem, hCutElem] using hq
    exact mem_daiLiKGeDBadRectangle_topSide_into_B P embedding d threshold w ell t atoms rectangles
      hAtoms hRectangles hEll cell hCell (slot - 1) hPrev q hqTop hNotSeparator

/-- Every source side strip of a good grid cell is one of the canonical grid
side components of the assembled `k >= d` region `B`. -/
theorem mem_daiLiKGeDGoodCellSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (hOccupied : cell ∈ embedding.gridOccupiedCells w (gridOrigin w t))
    (side : Fin 4) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell) side)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t cells rectangles).selected := by
  fin_cases side
  · have hSide : (cell.1, cell.2, true) ∈
        daiLiGridSideCandidates embedding w (gridOrigin w t) := by
      apply Finset.mem_biUnion.mpr
      refine ⟨cell, hOccupied, by simp⟩
    apply mem_daiLiKGeDGridSide_into_B P embedding d threshold w ell t cells rectangles
      (cell.1, cell.2, true) hSide q
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hNotSeparator⟩
    simpa [daiLiKGeDGridSideQubits, daiLiGridSideStripQubits,
      daiLiRectangleSideStripQubits, gridCellLower, gridCellUpper] using hq
  · have hSide : (cell.1 + 1, cell.2, true) ∈
        daiLiGridSideCandidates embedding w (gridOrigin w t) := by
      apply Finset.mem_biUnion.mpr
      refine ⟨cell, hOccupied, by simp⟩
    apply mem_daiLiKGeDGridSide_into_B P embedding d threshold w ell t cells rectangles
      (cell.1 + 1, cell.2, true) hSide q
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hNotSeparator⟩
    simpa [daiLiKGeDGridSideQubits, daiLiGridSideStripQubits,
      daiLiRectangleSideStripQubits, gridCellLower, gridCellUpper] using hq
  · have hSide : (cell.1, cell.2, false) ∈
        daiLiGridSideCandidates embedding w (gridOrigin w t) := by
      apply Finset.mem_biUnion.mpr
      refine ⟨cell, hOccupied, by simp⟩
    apply mem_daiLiKGeDGridSide_into_B P embedding d threshold w ell t cells rectangles
      (cell.1, cell.2, false) hSide q
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hNotSeparator⟩
    simpa [daiLiKGeDGridSideQubits, daiLiGridSideStripQubits,
      daiLiRectangleSideStripQubits, gridCellLower, gridCellUpper] using hq
  · have hSide : (cell.1, cell.2 + 1, false) ∈
        daiLiGridSideCandidates embedding w (gridOrigin w t) := by
      apply Finset.mem_biUnion.mpr
      refine ⟨cell, hOccupied, by simp⟩
    apply mem_daiLiKGeDGridSide_into_B P embedding d threshold w ell t cells rectangles
      (cell.1, cell.2 + 1, false) hSide q
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hNotSeparator⟩
    simpa [daiLiKGeDGridSideQubits, daiLiGridSideStripQubits,
      daiLiRectangleSideStripQubits, gridCellLower, gridCellUpper] using hq

/-- The #496 rectangle list of a bad grid cell gives every owned qubit a
concrete, in-range actual rectangle witness. -/
theorem exists_daiLiBadGridRectangle_covering_qubit
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hw : 0 < w) (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
    (q : ι) (hq : q ∈ embedding.gridCellQubits w (gridOrigin w t) cell) :
    ∃ slot : Fin (rectangles cell).length,
      q ∈ embedding.qubitsInRectangle ((rectangles cell).get slot).1
        ((rectangles cell).get slot).2 := by
  have hClosed : q ∈ embedding.qubitsInRectangle
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell) := by
    rw [← daiLiGridCellClosedQubits_eq_rectangle]
    exact gridCellQubits_subset_daiLiGridCellClosedQubits embedding hw (gridOrigin w t) cell hq
  have hPhysical : q ∈ embedding.qubitsInRectangle
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2,
        (daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2,
        (daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) := by
    convert hClosed using 1 <;> simp [gridCellLower, gridCellUpper, daiLiGridCellCenter] <;> ring
  have hCover : q ∈ daiLiRectangleQubitsCover embedding (rectangles cell) := by
    rw [hRectangles cell hCell]
    rw [daiLiPhysicalGreedyRectangles_cover P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell hEll
      (hAtoms cell hCell) d]
    exact hPhysical
  rcases (mem_daiLiRectangleQubitsCover_iff embedding (rectangles cell) q).1 hCover with
    ⟨rectangle, hRectangle, hqRectangle⟩
  rcases List.mem_iff_get.mp hRectangle with ⟨slot, hSlot⟩
  refine ⟨slot, ?_⟩
  simpa [← hSlot] using hqRectangle

/-- A strict, separator-free point of a good grid cell is selected by the
actual good-cell member of the finite `A` family. -/
theorem mem_daiLiKGeDGoodCellCore_into_A
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ)
    (hCandidate : Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hRect : q ∈ embedding.qubitsInRectangle
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell))
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (hStrict : (gridCellLower w (gridOrigin w t) cell).1 + ell < (embedding.point q).1 ∧
      (embedding.point q).1 < (gridCellUpper w (gridOrigin w t) cell).1 - ell ∧
        (gridCellLower w (gridOrigin w t) cell).2 + ell < (embedding.point q).2 ∧
          (embedding.point q).2 < (gridCellUpper w (gridOrigin w t) cell).2 - ell) :
    q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected := by
  apply mem_daiLiKGeDRegionCore_into_A P embedding d threshold w ell t cells rectangles
    (Sum.inl cell) hCandidate q
  change q ∈ (embedding.qubitsInRectangle
    (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell)).filter
      (fun q =>
        q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles ∧
          (gridCellLower w (gridOrigin w t) cell).1 + ell < (embedding.point q).1 ∧
            (embedding.point q).1 < (gridCellUpper w (gridOrigin w t) cell).1 - ell ∧
              (gridCellLower w (gridOrigin w t) cell).2 + ell < (embedding.point q).2 ∧
                (embedding.point q).2 < (gridCellUpper w (gridOrigin w t) cell).2 - ell)
  exact Finset.mem_filter.mpr ⟨hRect, ⟨hNotSeparator, hStrict⟩⟩

/-- A vertex neighborhood of a good grid cell belongs to the periodic vertex
component of the concrete `k >= d` separator. -/
theorem mem_daiLiKGeDGoodCellVertex_into_separator
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (threshold ell : ℝ) (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (vertex : Fin 4) (q : ι)
    (hq : q ∈ daiLiVertexNeighborhoodQubits embedding ell
      (daiLiRectangleVertex
        (gridCellLower w (gridOrigin w t) cell, gridCellUpper w (gridOrigin w t) cell) vertex)) :
    q ∈ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  fin_cases vertex
  · apply daiLiVertexNeighborhood_subset_gridVertexBuffer embedding hw ell (gridOrigin w t) t
      (phase_gridOrigin w t) (cell.1, cell.2)
    convert hq using 1 <;>
      simp [daiLiRectangleVertex, gridCellLower, gridCellUpper] <;> ring
  · apply daiLiVertexNeighborhood_subset_gridVertexBuffer embedding hw ell (gridOrigin w t) t
      (phase_gridOrigin w t) (cell.1, cell.2 + 1)
    convert hq using 1 <;>
      simp [daiLiRectangleVertex, gridCellLower, gridCellUpper] <;> ring
  · apply daiLiVertexNeighborhood_subset_gridVertexBuffer embedding hw ell (gridOrigin w t) t
      (phase_gridOrigin w t) (cell.1 + 1, cell.2)
    convert hq using 1 <;>
      simp [daiLiRectangleVertex, gridCellLower, gridCellUpper] <;> ring
  · apply daiLiVertexNeighborhood_subset_gridVertexBuffer embedding hw ell (gridOrigin w t) t
      (phase_gridOrigin w t) (cell.1 + 1, cell.2 + 1)
    convert hq using 1 <;>
      simp [daiLiRectangleVertex, gridCellLower, gridCellUpper] <;> ring

/-- Every owned physical qubit is assigned to the concrete `k >= d` source
separator, a strict `A` core, or an actual recoverable `B` strip.  Bad cells
are routed through their finite #496 rectangle list, while good cells use the
underlying grid rectangle directly. -/
theorem daiLiKGeD_cell_assignment
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hw : 0 < w) (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ embedding.gridOccupiedCells w (gridOrigin w t)) (q : ι)
    (hq : q ∈ embedding.gridCellQubits w (gridOrigin w t) cell) :
    q ∈ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles ∨
      q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected ∨
        q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
  by_cases hSeparator : q ∈ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
  · exact Or.inl hSeparator
  have hRect : q ∈ embedding.qubitsInRectangle
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell) := by
    rw [← daiLiGridCellClosedQubits_eq_rectangle]
    exact gridCellQubits_subset_daiLiGridCellClosedQubits embedding hw (gridOrigin w t) cell hq
  by_cases hBad : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t)
  · rcases exists_daiLiBadGridRectangle_covering_qubit P embedding d threshold w ell t atoms
      rectangles hAtoms hRectangles hw hEll cell hBad q hq with ⟨slot, hqRectangle⟩
    rcases daiLiRectanglePoint_vertex_or_strictCore_or_side embedding ell hEll
      ((rectangles cell).get slot).1 ((rectangles cell).get slot).2 q hqRectangle with
        hVertex | hStrict | ⟨side, hSide⟩
    · rcases hVertex with ⟨vertex, hVertex⟩
      apply Or.inl
      apply Finset.mem_union_right
      exact daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer embedding ell
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell hBad
        slot.1 slot.2 vertex hVertex
    · apply Or.inr
      apply Or.inl
      have hCandidate : Sum.inr (cell, slot.1) ∈ daiLiKGeDRegionCandidates P embedding threshold d
          w (gridOrigin w t) rectangles :=
        (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
          (gridOrigin w t) rectangles cell slot.1).2 ⟨hBad, slot.2⟩
      exact mem_daiLiKGeDBadRectangleCore_into_A P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell slot.1
        slot.2 hCandidate q hqRectangle hSeparator hStrict
    · apply Or.inr
      apply Or.inr
      fin_cases side
      · exact mem_daiLiKGeDBadRectangle_leftSide_into_B P embedding d threshold w ell t atoms
          rectangles hAtoms hRectangles hEll cell hBad slot.1 slot.2 q hSide hSeparator
      · exact mem_daiLiKGeDBadRectangle_rightSide_into_B P embedding d threshold w ell t atoms
          rectangles hAtoms hRectangles hEll cell hBad slot.1 slot.2 q hSide hSeparator
      · exact mem_daiLiKGeDBadRectangle_bottomSide_into_B P embedding d threshold w ell t atoms
          rectangles hAtoms hRectangles hEll cell hBad slot.1 slot.2 q hSide hSeparator
      · exact mem_daiLiKGeDBadRectangle_topSide_into_B P embedding d threshold w ell t atoms
          rectangles hAtoms hRectangles hEll cell hBad slot.1 slot.2 q hSide hSeparator
  · have hCandidate : Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles :=
      (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w
        (gridOrigin w t) rectangles cell).2 ⟨hCell, hBad⟩
    rcases daiLiRectanglePoint_vertex_or_strictCore_or_side embedding ell hEll
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell) q hRect with
        hVertex | hStrict | ⟨side, hSide⟩
    · rcases hVertex with ⟨vertex, hVertex⟩
      exact Or.inl (mem_daiLiKGeDGoodCellVertex_into_separator P embedding hw threshold ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell vertex q hVertex)
    · exact Or.inr (Or.inl (mem_daiLiKGeDGoodCellCore_into_A P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell hCandidate q
        hRect hSeparator hStrict))
    · exact Or.inr (Or.inr (mem_daiLiKGeDGoodCellSide_into_B P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell hCell side q
        hSide hSeparator))

/-- The residual of the finite `k >= d` partition is contained in the actual
source separator.  This is the exact bridge from the physical grid-and-
rectangle construction to the #368 dimension lemma. -/
theorem daiLiKGeDResidual_subset_separator
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hw : 0 < w) (hEll : 0 < ell) :
    (daiLiKGeDResidualSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected ⊆
      daiLiKGeDSeparator P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles := by
  intro q hq
  have hOutside : q ∉
      (daiLiKGeDASubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected ∪
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected :=
    (Finset.mem_sdiff.mp hq).2
  have hNotA : q ∉ (daiLiKGeDASubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
    intro hA
    exact hOutside (Finset.mem_union_left _ hA)
  have hNotTrimmedB : q ∉ (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
    intro hB
    exact hOutside (Finset.mem_union_right _ hB)
  have hCellCover : q ∈ (embedding.gridOccupiedCells w (gridOrigin w t)).biUnion
      (embedding.gridCellQubits w (gridOrigin w t)) := by
    rw [embedding.gridCellQubits_cover w (gridOrigin w t)]
    exact Finset.mem_univ _
  rcases Finset.mem_biUnion.mp hCellCover with ⟨cell, hCell, hqCell⟩
  rcases daiLiKGeD_cell_assignment P embedding d threshold w ell t atoms rectangles
      hAtoms hRectangles hw hEll cell hCell q hqCell with hSeparator | hA | hB
  · exact hSeparator
  · exact False.elim (hNotA hA)
  · exfalso
    apply hNotTrimmedB
    apply Finset.mem_sdiff.mpr
    exact ⟨hB, hNotA⟩

/-- The residual cardinality inherits the concrete source-separator bound. -/
theorem card_daiLiKGeDResidual_le_separator
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hw : 0 < w) (hEll : 0 < ell) :
    (daiLiKGeDResidualSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected.card ≤
      (daiLiKGeDSeparator P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).card :=
  Finset.card_le_card
    (daiLiKGeDResidual_subset_separator P embedding d threshold w ell t atoms rectangles
      hAtoms hRectangles hw hEll)

/-- The assembled finite `A` family inherits the actual CPTP recovery built
for the source-region core family. -/
theorem exists_erasureRecovery_daiLiKGeDA
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ cell,
      Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBadBaseCard : ∀ cell slot,
      Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding
        (daiLiRectangleCenter
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).1
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).2)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDASubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDASubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        P.semanticCode
        (daiLiKGeDASubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).erasureChannelFromRegister
          recovery := by
  exact
    (exists_erasureRecovery_daiLiKGeDRegionCoreFamily P embedding d hDistance threshold w ell t
      atoms rectangles hAtoms hRectangles hThreshold hWidthNat hEllNat hEll hWidth hThresholdEll
      baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood hBaseVerticalBad
      hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal hReachVerticalGood hReachVerticalBad
      hGoodBaseCard hBadBaseCard hBoundaryBudget hShortPackingScale)

/-- The trimmed `B` component inherits the CPTP recovery of the fully
constructed source-side `B` by finite-subsystem inclusion. -/
theorem exists_erasureRecovery_daiLiKGeDTrimmedB
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEllNat : 1 ≤ ell) (hCellWidth : 5 * ell ≤ w)
    (hInternalSideScale : 12 * ell * w < d)
    (hEll : 0 < ell) (hGridWidth : 4 * ell ≤ w)
    (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        P.semanticCode
        (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).erasureChannelFromRegister
          recovery := by
  obtain ⟨recovery, hRecovery⟩ := exists_erasureRecovery_daiLiKGeDB P embedding d hDistance
    threshold w ell t atoms rectangles hAtoms hRectangles hEllNat hCellWidth hInternalSideScale
    hEll hGridWidth hThresholdEll hEdge hGridLong hGridSideSmall
  apply exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
    (daiLiKGeDBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
  · exact Finset.sdiff_subset
  · exact ⟨recovery, hRecovery⟩

/-- The completed finite `k >= d` Dai--Li partition supplies both actual CPTP
recoveries required by #368, so the encoded dimension is bounded by the
concrete physical separator rather than by an assumed interaction cut. -/
theorem daiLiKGeD_encodedQubits_le_separator_card
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hWidth : 0 < w) (hEll : 0 < ell) (hThresholdEll : threshold ≤ ell)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ cell,
      Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBadBaseCard : ∀ cell slot,
      Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding
        (daiLiRectangleCenter
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).1
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).2)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hCellWidth : 5 * ell ≤ w) (hInternalSideScale : 12 * ell * w < d)
    (hGridWidth : 4 * ell ≤ w) (hEdge : 1 ≤ 2 * ell)
    (hGridLong : 1 ≤ w - 4 * ell) (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    P.encodedQubits ≤
      (daiLiKGeDSeparator P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).card := by
  obtain ⟨recoveryA, hRecoveryA⟩ := exists_erasureRecovery_daiLiKGeDA P embedding d hDistance
    threshold w ell t atoms rectangles hAtoms hRectangles hThreshold hWidthNat hEllNat hEll hWidth
    hThresholdEll baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
    hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
    hReachVerticalGood hReachVerticalBad hGoodBaseCard hBadBaseCard hBoundaryBudget
    hShortPackingScale
  obtain ⟨recoveryB, hRecoveryB⟩ := exists_erasureRecovery_daiLiKGeDTrimmedB P embedding d
    hDistance threshold w ell t atoms rectangles hAtoms hRectangles hEllNat hCellWidth
    hInternalSideScale hEll hGridWidth hThresholdEll hEdge hGridLong hGridSideSmall
  have hPairwise := daiLiKGeD_partition_pairwise P embedding d threshold w ell t
    (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
  have hDimension : P.encodedQubits ≤
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected.card :=
    two_correctable_regions_encodedQubits_le_separator_card P
      (daiLiKGeDASubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      hPairwise.1 hPairwise.2.1 hPairwise.2.2
      (daiLiKGeD_partition_cover P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      recoveryA hRecoveryA recoveryB hRecoveryB
  exact hDimension.trans
    (card_daiLiKGeDResidual_le_separator P embedding d threshold w ell t atoms rectangles
      hAtoms hRectangles hWidth hEll)

end QEC.Locality
