import QEC.Bounds.GeometricLocalityTradeoff.BlockRecursion
import QEC.Bounds.BPTSeparatedUnion

/-!
# Finite BPT square-partition geometry

This module begins the source-faithful finite `A`/`B`/`C` square partition
from BPT10.  It deliberately keeps the lattice coordinates and the BPT
measurement-distance convention visible: a region is recoverable only by
passing through the finite-qudit no-information-to-CPTP-recovery bridge.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open Semantics

universe u v

namespace BPTSquareLattice

/-- The square-lattice tile containing a site at a positive block scale. -/
def tileIndex (L : BPTSquareLattice) (blockWidth : Nat) (site : L.Site) : Nat × Nat :=
  (site.1.val / blockWidth, site.2.val / blockWidth)

/-- The square block with the given tile index and source block width. -/
def tile (L : BPTSquareLattice) (blockWidth : Nat) (index : Nat × Nat) :
    Finset L.Site :=
  L.square (index.1 * blockWidth, index.2 * blockWidth) blockWidth

/-- The finite open-boundary tile enlarged by a visible local interaction margin. -/
def expandedTile (L : BPTSquareLattice) (blockWidth margin : Nat) (index : Nat × Nat) :
    Finset L.Site :=
  L.square (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
    (blockWidth + margin + margin)

/--
The strictly interior square left after removing a source-width boundary layer
from all four sides of a square.  It is intentionally an open-boundary finite
set, so the definition also applies to squares meeting the physical boundary.
-/
def squareInnerCore (L : BPTSquareLattice) (origin : Nat × Nat) (width margin : Nat) :
    Finset L.Site :=
  L.square (origin.1 + margin, origin.2 + margin) (width - margin - margin)

/--
The finite thin frame around a source square: an outer layer of width
`margin` on both sides, with the square's deep interior removed.  This is the
literal `B union C` boundary cover from the BPT growth argument, rather than
the entire enlarged square used by the earlier local adapter.
-/
def squareBoundaryFrame (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.square (origin.1 - margin, origin.2 - margin) (width + margin + margin) \
    L.squareInnerCore origin width margin

/-- An open-boundary coordinate rectangle with independently visible side lengths. -/
def rectangle (L : BPTSquareLattice) (origin : Nat × Nat)
    (rowWidth columnWidth : Nat) : Finset L.Site :=
  Finset.univ.filter fun site =>
    origin.1 ≤ site.1.val ∧ site.1.val < origin.1 + rowWidth ∧
      origin.2 ≤ site.2.val ∧ site.2.val < origin.2 + columnWidth

@[simp]
theorem mem_rectangle_iff (L : BPTSquareLattice) (origin : Nat × Nat)
    (rowWidth columnWidth : Nat) (site : L.Site) :
    site ∈ L.rectangle origin rowWidth columnWidth ↔
      origin.1 ≤ site.1.val ∧ site.1.val < origin.1 + rowWidth ∧
        origin.2 ≤ site.2.val ∧ site.2.val < origin.2 + columnWidth := by
  simp [rectangle]

/-- An open-boundary coordinate rectangle has no more sites than its area. -/
theorem rectangle_card_le_area (L : BPTSquareLattice) (origin : Nat × Nat)
    (rowWidth columnWidth : Nat) :
    (L.rectangle origin rowWidth columnWidth).card ≤ rowWidth * columnWidth := by
  let f : {site : L.Site // site ∈ L.rectangle origin rowWidth columnWidth} →
      Fin rowWidth × Fin columnWidth :=
    fun site =>
      (⟨site.1.1.val - origin.1, by
        have h := (L.mem_rectangle_iff origin rowWidth columnWidth site.1).mp site.2
        omega⟩,
      ⟨site.1.2.val - origin.2, by
        have h := (L.mem_rectangle_iff origin rowWidth columnWidth site.1).mp site.2
        omega⟩)
  have hinjective : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hs := (L.mem_rectangle_iff origin rowWidth columnWidth s.1).mp s.2
      have ht := (L.mem_rectangle_iff origin rowWidth columnWidth t.1).mp t.2
      have hrow : s.1.1.val - origin.1 = t.1.1.val - origin.1 := by
        exact congrArg (fun pair => pair.1.val) h
      calc
        s.1.1.val = origin.1 + (s.1.1.val - origin.1) := (Nat.add_sub_of_le hs.1).symm
        _ = origin.1 + (t.1.1.val - origin.1) := by rw [hrow]
        _ = t.1.1.val := Nat.add_sub_of_le ht.1
    · apply Fin.ext
      have hs := (L.mem_rectangle_iff origin rowWidth columnWidth s.1).mp s.2
      have ht := (L.mem_rectangle_iff origin rowWidth columnWidth t.1).mp t.2
      have hcolumn : s.1.2.val - origin.2 = t.1.2.val - origin.2 := by
        exact congrArg (fun pair => pair.2.val) h
      calc
        s.1.2.val = origin.2 + (s.1.2.val - origin.2) :=
          (Nat.add_sub_of_le hs.2.2.1).symm
        _ = origin.2 + (t.1.2.val - origin.2) := by rw [hcolumn]
        _ = t.1.2.val := Nat.add_sub_of_le ht.2.2.1
  have hcard := Fintype.card_le_of_injective f hinjective
  calc
    (L.rectangle origin rowWidth columnWidth).card =
        Fintype.card {site : L.Site // site ∈ L.rectangle origin rowWidth columnWidth} :=
      (Fintype.card_coe (L.rectangle origin rowWidth columnWidth)).symm
    _ ≤ rowWidth * columnWidth := by simpa using hcard

/-- The lower horizontal strip of the source-thickness square frame. -/
def squareBoundaryFrameLowerRow (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.rectangle (origin.1 - margin, origin.2 - margin) (margin + margin)
    (width + margin + margin)

/-- The upper horizontal strip of the source-thickness square frame. -/
def squareBoundaryFrameUpperRow (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.rectangle (origin.1 + width - margin, origin.2 - margin) (margin + margin)
    (width + margin + margin)

/-- The left vertical strip of the source-thickness square frame. -/
def squareBoundaryFrameLowerColumn (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.rectangle (origin.1 - margin, origin.2 - margin) (width + margin + margin)
    (margin + margin)

/-- The right vertical strip of the source-thickness square frame. -/
def squareBoundaryFrameUpperColumn (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.rectangle (origin.1 - margin, origin.2 + width - margin) (width + margin + margin)
    (margin + margin)

/-- The four explicit strips that cover the finite BPT square frame. -/
def squareBoundaryFrameStripCover (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.squareBoundaryFrameLowerRow origin width margin ∪
    L.squareBoundaryFrameUpperRow origin width margin ∪
      L.squareBoundaryFrameLowerColumn origin width margin ∪
        L.squareBoundaryFrameUpperColumn origin width margin

/-- The inner `B` layer obtained by restricting the finite strip cover to its square. -/
def squareGrowthInside (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.square origin width ∩ L.squareBoundaryFrameStripCover origin width margin

/-- The outer `C` layer obtained from the same finite strip cover. -/
def squareGrowthOutside (L : BPTSquareLattice) (origin : Nat × Nat)
    (width margin : Nat) : Finset L.Site :=
  L.squareBoundaryFrameStripCover origin width margin \ L.square origin width

/-- A coordinate square is fully present in the finite open-boundary lattice. -/
def squareFits (L : BPTSquareLattice) (origin : Nat × Nat) (width : Nat) : Prop :=
  origin.1 + width ≤ L.rows ∧ origin.2 + width ≤ L.columns

/-- The deep core is contained in the visible outer square whenever it is nonempty. -/
theorem squareInnerCore_subset_outerSquare (L : BPTSquareLattice)
    (origin : Nat × Nat) (width margin : Nat) (hwidth : margin + margin ≤ width) :
    L.squareInnerCore origin width margin ⊆
      L.square (origin.1 - margin, origin.2 - margin) (width + margin + margin) := by
  intro site hsite
  simp only [squareInnerCore, mem_square_iff] at hsite
  simp only [mem_square_iff]
  have hrowOrigin : origin.1 - margin ≤ site.1.val := by omega
  have hcolumnOrigin : origin.2 - margin ≤ site.2.val := by omega
  constructor
  · exact hrowOrigin
  constructor
  · omega
  constructor
  · exact hcolumnOrigin
  · omega

/--
The four source-width strips have at most `16 * w * R` sites when `R >= 2w`.
This is an open-boundary estimate: clipped strips only lose sites, and no
periodic or implicit infinite-lattice convention is used.
-/
theorem squareBoundaryFrameStripCover_card_le_sixteen_mul (L : BPTSquareLattice)
    (origin : Nat × Nat) (width margin : Nat) (hwidth : margin + margin ≤ width) :
    (L.squareBoundaryFrameStripCover origin width margin).card ≤ 16 * margin * width := by
  let bound := (margin + margin) * (width + margin + margin)
  have hLowerRow : (L.squareBoundaryFrameLowerRow origin width margin).card ≤ bound := by
    simpa [bound, squareBoundaryFrameLowerRow] using
      L.rectangle_card_le_area (origin.1 - margin, origin.2 - margin)
        (margin + margin) (width + margin + margin)
  have hUpperRow : (L.squareBoundaryFrameUpperRow origin width margin).card ≤ bound := by
    simpa [bound, squareBoundaryFrameUpperRow] using
      L.rectangle_card_le_area (origin.1 + width - margin, origin.2 - margin)
        (margin + margin) (width + margin + margin)
  have hLowerColumn : (L.squareBoundaryFrameLowerColumn origin width margin).card ≤ bound := by
    simpa [bound, squareBoundaryFrameLowerColumn, Nat.mul_comm] using
      L.rectangle_card_le_area (origin.1 - margin, origin.2 - margin)
        (width + margin + margin) (margin + margin)
  have hUpperColumn : (L.squareBoundaryFrameUpperColumn origin width margin).card ≤ bound := by
    simpa [bound, squareBoundaryFrameUpperColumn, Nat.mul_comm] using
      L.rectangle_card_le_area (origin.1 - margin, origin.2 + width - margin)
        (width + margin + margin) (margin + margin)
  have hcoverCard : (L.squareBoundaryFrameStripCover origin width margin).card ≤
      (L.squareBoundaryFrameLowerRow origin width margin).card +
        (L.squareBoundaryFrameUpperRow origin width margin).card +
          (L.squareBoundaryFrameLowerColumn origin width margin).card +
            (L.squareBoundaryFrameUpperColumn origin width margin).card := by
    calc
      (L.squareBoundaryFrameStripCover origin width margin).card =
          (((L.squareBoundaryFrameLowerRow origin width margin ∪
            L.squareBoundaryFrameUpperRow origin width margin) ∪
              L.squareBoundaryFrameLowerColumn origin width margin) ∪
                L.squareBoundaryFrameUpperColumn origin width margin).card := rfl
      _ ≤ ((L.squareBoundaryFrameLowerRow origin width margin ∪
          L.squareBoundaryFrameUpperRow origin width margin) ∪
            L.squareBoundaryFrameLowerColumn origin width margin).card +
              (L.squareBoundaryFrameUpperColumn origin width margin).card :=
        Finset.card_union_le _ _
      _ ≤ ((L.squareBoundaryFrameLowerRow origin width margin ∪
          L.squareBoundaryFrameUpperRow origin width margin).card +
            (L.squareBoundaryFrameLowerColumn origin width margin).card) +
              (L.squareBoundaryFrameUpperColumn origin width margin).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ ((L.squareBoundaryFrameLowerRow origin width margin).card +
          (L.squareBoundaryFrameUpperRow origin width margin).card +
            (L.squareBoundaryFrameLowerColumn origin width margin).card) +
              (L.squareBoundaryFrameUpperColumn origin width margin).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ = (L.squareBoundaryFrameLowerRow origin width margin).card +
          (L.squareBoundaryFrameUpperRow origin width margin).card +
            (L.squareBoundaryFrameLowerColumn origin width margin).card +
              (L.squareBoundaryFrameUpperColumn origin width margin).card := by omega
  have hlinear : (L.squareBoundaryFrameStripCover origin width margin).card ≤
      bound + bound + bound + bound := by omega
  have hside : width + margin + margin ≤ width + width := by omega
  have hbound : bound ≤ (margin + margin) * (width + width) := by
    exact Nat.mul_le_mul_left _ hside
  calc
    (L.squareBoundaryFrameStripCover origin width margin).card ≤
        bound + bound + bound + bound := hlinear
    _ ≤ 4 * bound := by omega
    _ ≤ 4 * ((margin + margin) * (width + width)) := Nat.mul_le_mul_left _ hbound
    _ = 16 * margin * width := by ring

/-- The finite `B` and `C` layers reconstruct their common strip cover exactly. -/
theorem squareGrowthInside_union_outside_eq_stripCover (L : BPTSquareLattice)
    (origin : Nat × Nat) (width margin : Nat) :
    L.squareGrowthInside origin width margin ∪ L.squareGrowthOutside origin width margin =
      L.squareBoundaryFrameStripCover origin width margin := by
  change (L.square origin width ∩ L.squareBoundaryFrameStripCover origin width margin) ∪
      (L.squareBoundaryFrameStripCover origin width margin \ L.square origin width) =
        L.squareBoundaryFrameStripCover origin width margin
  rw [Finset.inter_comm, Finset.union_comm]
  exact Finset.sdiff_union_inter _ _

/-- The source growth layers around the inner square reconstruct the larger square. -/
theorem square_union_squareGrowthOutside_eq_grownSquare (L : BPTSquareLattice)
    (origin : Nat × Nat) (width margin : Nat) (hwidth : margin + margin ≤ width)
    (hmarginOrigin : margin ≤ origin.1 ∧ margin ≤ origin.2) :
    L.square origin width ∪ L.squareGrowthOutside origin width margin =
      L.square (origin.1 - margin, origin.2 - margin) (width + margin + margin) := by
  ext site
  simp only [squareGrowthOutside, squareBoundaryFrameStripCover,
    squareBoundaryFrameLowerRow, squareBoundaryFrameUpperRow,
    squareBoundaryFrameLowerColumn, squareBoundaryFrameUpperColumn,
    Finset.mem_union, Finset.mem_sdiff, mem_square_iff, mem_rectangle_iff]
  rcases hmarginOrigin with ⟨hrowMargin, hcolumnMargin⟩
  omega

/-- The source's checkerboard color of the block containing a lattice site. -/
def checkerboardEven (L : BPTSquareLattice) (blockWidth : Nat) (site : L.Site) : Prop :=
  Even (site.1.val / blockWidth + site.2.val / blockWidth)

/--
Two lattice regions have the coordinate separation needed for a source
projector of the given square range to meet at most one of them.  This is a
coordinate criterion, not a replacement interaction graph.
-/
def CoordinateRangeSeparated (L : BPTSquareLattice) (range : Nat)
    (left right : Finset L.Site) : Prop :=
  ∀ leftSite ∈ left, ∀ rightSite ∈ right,
    range ≤ leftSite.1.val - rightSite.1.val ∨
      range ≤ rightSite.1.val - leftSite.1.val ∨
        range ≤ leftSite.2.val - rightSite.2.val ∨
          range ≤ rightSite.2.val - leftSite.2.val

/--
The corner cutouts in the BPT `A`/`B`/`C` picture.  The two-sided residue
window retains a margin around every grid-line intersection, including the
open-boundary truncations of those intersections.
-/
def cornerCutout (L : BPTSquareLattice) (blockWidth margin : Nat) (site : L.Site) : Prop :=
  (site.1.val % blockWidth < margin ∨ blockWidth - margin ≤ site.1.val % blockWidth) ∧
    (site.2.val % blockWidth < margin ∨ blockWidth - margin ≤ site.2.val % blockWidth)

/-- The explicit finite `C` corner region of the BPT checkerboard partition. -/
def squarePartitionC (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset L.Site :=
  Finset.univ.filter (cornerCutout L blockWidth margin)

/-- Four finite `margin`-by-`margin` rectangles covering one tile's C cutouts. -/
def cornerCutoutTileCover (L : BPTSquareLattice) (blockWidth margin : Nat)
    (index : Nat × Nat) : Finset L.Site :=
  L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin ∪
    L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
      margin margin ∪
      L.rectangle (index.1 * blockWidth + blockWidth - margin, index.2 * blockWidth)
        margin margin ∪
        L.rectangle (index.1 * blockWidth + blockWidth - margin,
          index.2 * blockWidth + blockWidth - margin) margin margin

/--
Four `3 * margin` squares covering every range-`margin` enlargement of a
tile's four C corner cutouts.  The lower origins use natural subtraction, so
open-boundary clipping can only reduce the actual finite cover.
-/
def cornerCutoutTileExpandedCover (L : BPTSquareLattice) (blockWidth margin : Nat)
    (index : Nat × Nat) : Finset L.Site :=
  L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
    (margin + margin + margin) (margin + margin + margin) ∪
    L.rectangle (index.1 * blockWidth - margin,
      index.2 * blockWidth + blockWidth - margin - margin)
      (margin + margin + margin) (margin + margin + margin) ∪
      L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
        index.2 * blockWidth - margin)
        (margin + margin + margin) (margin + margin + margin) ∪
        L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
          index.2 * blockWidth + blockWidth - margin - margin)
          (margin + margin + margin) (margin + margin + margin)

/-- The explicit finite `A` region of the BPT checkerboard partition. -/
def squarePartitionA (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset L.Site :=
  Finset.univ.filter fun site =>
    ¬ cornerCutout L blockWidth margin site ∧ checkerboardEven L blockWidth site

/-- The explicit finite `B` region of the BPT checkerboard partition. -/
def squarePartitionB (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset L.Site :=
  Finset.univ.filter fun site =>
    ¬ cornerCutout L blockWidth margin site ∧ ¬ checkerboardEven L blockWidth site

/-- All source tile indices that occur on the finite open lattice. -/
def occupiedTileIndices (L : BPTSquareLattice) (blockWidth : Nat) :
    Finset (Nat × Nat) :=
  Finset.univ.image (L.tileIndex blockWidth)

/-- The `A` portion of one explicitly indexed source square block. -/
def squarePartitionAComponent (L : BPTSquareLattice) (blockWidth margin : Nat)
    (index : Nat × Nat) : Finset L.Site :=
  L.tile blockWidth index ∩ L.squarePartitionA blockWidth margin

/-- The `B` portion of one explicitly indexed source square block. -/
def squarePartitionBComponent (L : BPTSquareLattice) (blockWidth margin : Nat)
    (index : Nat × Nat) : Finset L.Site :=
  L.tile blockWidth index ∩ L.squarePartitionB blockWidth margin

/-- The explicit finite square blocks whose union is the source `A` region. -/
def squarePartitionAComponents (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset (Finset L.Site) :=
  (((L.occupiedTileIndices blockWidth).filter fun index => Even (index.1 + index.2)).image
    fun index => L.squarePartitionAComponent blockWidth margin index).filter
      Finset.Nonempty

/-- The explicit finite square blocks whose union is the source `B` region. -/
def squarePartitionBComponents (L : BPTSquareLattice) (blockWidth margin : Nat) :
    Finset (Finset L.Site) :=
  (((L.occupiedTileIndices blockWidth).filter fun index => ¬ Even (index.1 + index.2)).image
    fun index => L.squarePartitionBComponent blockWidth margin index).filter
      Finset.Nonempty

/-- Every site belongs to its explicitly indexed source square block. -/
theorem mem_tile_of_pos (L : BPTSquareLattice) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (site : L.Site) :
    site ∈ L.tile blockWidth (L.tileIndex blockWidth site) := by
  simp only [tile, tileIndex, mem_square_iff]
  constructor
  · simpa [Nat.mul_comm] using Nat.mul_div_le site.1.val blockWidth
  constructor
  · calc
      site.1.val = blockWidth * (site.1.val / blockWidth) + site.1.val % blockWidth :=
        (Nat.div_add_mod site.1.val blockWidth).symm
      _ < blockWidth * (site.1.val / blockWidth) + blockWidth :=
        Nat.add_lt_add_left (Nat.mod_lt site.1.val hblockWidth) _
      _ = (site.1.val / blockWidth) * blockWidth + blockWidth := by
        rw [Nat.mul_comm]
  constructor
  · simpa [Nat.mul_comm] using Nat.mul_div_le site.2.val blockWidth
  calc
    site.2.val = blockWidth * (site.2.val / blockWidth) + site.2.val % blockWidth :=
      (Nat.div_add_mod site.2.val blockWidth).symm
    _ < blockWidth * (site.2.val / blockWidth) + blockWidth :=
      Nat.add_lt_add_left (Nat.mod_lt site.2.val hblockWidth) _
    _ = (site.2.val / blockWidth) * blockWidth + blockWidth := by
      rw [Nat.mul_comm]

/-- A site in an explicitly indexed tile has exactly that quotient pair. -/
theorem tileIndex_eq_of_mem_tile (L : BPTSquareLattice) {blockWidth : Nat}
    (_hblockWidth : 0 < blockWidth) {index : Nat × Nat} {site : L.Site}
    (hsite : site ∈ L.tile blockWidth index) :
    L.tileIndex blockWidth site = index := by
  simp only [tile, mem_square_iff] at hsite
  apply Prod.ext
  · exact Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using hsite.1)
      (by simpa [Nat.succ_mul] using hsite.2.1)
  · exact Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using hsite.2.2.1)
      (by simpa [Nat.succ_mul] using hsite.2.2.2)

/-- Membership in an indexed `A` block exposes both its tile and source color. -/
theorem mem_squarePartitionAComponent_iff (L : BPTSquareLattice)
    (blockWidth margin : Nat) (index : Nat × Nat) (site : L.Site) :
    site ∈ L.squarePartitionAComponent blockWidth margin index ↔
      site ∈ L.tile blockWidth index ∧ ¬ L.cornerCutout blockWidth margin site ∧
        L.checkerboardEven blockWidth site := by
  simp [squarePartitionAComponent, squarePartitionA]

/-- Membership in an indexed `B` block exposes both its tile and source color. -/
theorem mem_squarePartitionBComponent_iff (L : BPTSquareLattice)
    (blockWidth margin : Nat) (index : Nat × Nat) (site : L.Site) :
    site ∈ L.squarePartitionBComponent blockWidth margin index ↔
      site ∈ L.tile blockWidth index ∧ ¬ L.cornerCutout blockWidth margin site ∧
        ¬ L.checkerboardEven blockWidth site := by
  simp [squarePartitionBComponent, squarePartitionB]

/-- An even tile's A component is exactly that tile with its C corners removed. -/
theorem squarePartitionAComponent_eq_tile_sdiff_C_of_even (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    (index : Nat × Nat) (heven : Even (index.1 + index.2)) :
    L.squarePartitionAComponent blockWidth margin index =
      L.tile blockWidth index \ L.squarePartitionC blockWidth margin := by
  ext site
  constructor
  · intro hsite
    rcases (L.mem_squarePartitionAComponent_iff blockWidth margin index site).mp hsite with
      ⟨htile, hnotCorner, _⟩
    exact Finset.mem_sdiff.mpr ⟨htile, by simpa [squarePartitionC] using hnotCorner⟩
  · intro hsite
    rcases Finset.mem_sdiff.mp hsite with ⟨htile, hnotC⟩
    have hindex : L.tileIndex blockWidth site = index :=
      L.tileIndex_eq_of_mem_tile hblockWidth htile
    have hchecker : L.checkerboardEven blockWidth site := by
      have hrow : site.1.val / blockWidth = index.1 := by
        simpa [tileIndex] using congrArg Prod.fst hindex
      have hcolumn : site.2.val / blockWidth = index.2 := by
        simpa [tileIndex] using congrArg Prod.snd hindex
      simp only [checkerboardEven]
      rw [hrow, hcolumn]
      exact heven
    exact (L.mem_squarePartitionAComponent_iff blockWidth margin index site).mpr
      ⟨htile, by simpa [squarePartitionC] using hnotC, hchecker⟩

/-- An odd tile's B component is exactly that tile with its C corners removed. -/
theorem squarePartitionBComponent_eq_tile_sdiff_C_of_odd (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    (index : Nat × Nat) (hodd : ¬ Even (index.1 + index.2)) :
    L.squarePartitionBComponent blockWidth margin index =
      L.tile blockWidth index \ L.squarePartitionC blockWidth margin := by
  ext site
  constructor
  · intro hsite
    rcases (L.mem_squarePartitionBComponent_iff blockWidth margin index site).mp hsite with
      ⟨htile, hnotCorner, _⟩
    exact Finset.mem_sdiff.mpr ⟨htile, by simpa [squarePartitionC] using hnotCorner⟩
  · intro hsite
    rcases Finset.mem_sdiff.mp hsite with ⟨htile, hnotC⟩
    have hindex : L.tileIndex blockWidth site = index :=
      L.tileIndex_eq_of_mem_tile hblockWidth htile
    have hchecker : ¬ L.checkerboardEven blockWidth site := by
      have hrow : site.1.val / blockWidth = index.1 := by
        simpa [tileIndex] using congrArg Prod.fst hindex
      have hcolumn : site.2.val / blockWidth = index.2 := by
        simpa [tileIndex] using congrArg Prod.snd hindex
      simp only [checkerboardEven]
      rw [hrow, hcolumn]
      exact hodd
    exact (L.mem_squarePartitionBComponent_iff blockWidth margin index site).mpr
      ⟨htile, by simpa [squarePartitionC] using hnotC, hchecker⟩

/-- A point in an indexed `A` component carries that component's exact tile index. -/
theorem tileIndex_eq_of_mem_squarePartitionAComponent (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    {index : Nat × Nat} {site : L.Site}
    (hsite : site ∈ L.squarePartitionAComponent blockWidth margin index) :
    L.tileIndex blockWidth site = index :=
  L.tileIndex_eq_of_mem_tile hblockWidth (L.mem_squarePartitionAComponent_iff
    blockWidth margin index site |>.mp hsite).1

/-- A point in an indexed `B` component carries that component's exact tile index. -/
theorem tileIndex_eq_of_mem_squarePartitionBComponent (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    {index : Nat × Nat} {site : L.Site}
    (hsite : site ∈ L.squarePartitionBComponent blockWidth margin index) :
    L.tileIndex blockWidth site = index :=
  L.tileIndex_eq_of_mem_tile hblockWidth (L.mem_squarePartitionBComponent_iff
    blockWidth margin index site |>.mp hsite).1

/-- Coordinate separation is preserved when either region is shrunk. -/
theorem CoordinateRangeSeparated.mono (L : BPTSquareLattice) {range : Nat}
    {left' left right' right : Finset L.Site}
    (hgap : L.CoordinateRangeSeparated range left right) (hleft : left' ⊆ left)
    (hright : right' ⊆ right) :
    L.CoordinateRangeSeparated range left' right' := by
  intro leftSite hleftSite rightSite hrightSite
  exact hgap leftSite (hleft hleftSite) rightSite (hright hrightSite)

/-- Coordinate-range separation is symmetric in its two finite regions. -/
theorem CoordinateRangeSeparated.symm (L : BPTSquareLattice) {range : Nat}
    {left right : Finset L.Site}
    (hgap : L.CoordinateRangeSeparated range left right) :
    L.CoordinateRangeSeparated range right left := by
  intro rightSite hrightSite leftSite hleftSite
  rcases hgap leftSite hleftSite rightSite hrightSite with hrow | hrow | hcolumn | hcolumn
  · exact Or.inr (Or.inl hrow)
  · exact Or.inl hrow
  · exact Or.inr (Or.inr (Or.inr hcolumn))
  · exact Or.inr (Or.inr (Or.inl hcolumn))

/-- Tiles with a full tile between them in the row direction have the requested gap. -/
theorem coordinateRangeSeparated_tile_of_row_gap (L : BPTSquareLattice)
    {blockWidth range : Nat} (hrange : range ≤ blockWidth)
    (leftIndex rightIndex : Nat × Nat) (hrow : leftIndex.1 + 1 < rightIndex.1) :
    L.CoordinateRangeSeparated range (L.tile blockWidth leftIndex)
      (L.tile blockWidth rightIndex) := by
  intro leftSite hleftSite rightSite hrightSite
  simp only [tile, mem_square_iff] at hleftSite hrightSite
  refine Or.inr (Or.inl ?_)
  have htileGap : leftIndex.1 * blockWidth + blockWidth + blockWidth ≤
      rightIndex.1 * blockWidth := by
    calc
      leftIndex.1 * blockWidth + blockWidth + blockWidth =
          (leftIndex.1 + 2) * blockWidth := by ring
      _ ≤ rightIndex.1 * blockWidth :=
        Nat.mul_le_mul_right blockWidth (by omega)
  have horder : leftSite.1.val ≤ rightSite.1.val := by omega
  rw [Nat.le_sub_iff_add_le horder]
  omega

/-- Tiles with a full tile between them in the column direction have the requested gap. -/
theorem coordinateRangeSeparated_tile_of_column_gap (L : BPTSquareLattice)
    {blockWidth range : Nat} (hrange : range ≤ blockWidth)
    (leftIndex rightIndex : Nat × Nat) (hcolumn : leftIndex.2 + 1 < rightIndex.2) :
    L.CoordinateRangeSeparated range (L.tile blockWidth leftIndex)
      (L.tile blockWidth rightIndex) := by
  intro leftSite hleftSite rightSite hrightSite
  simp only [tile, mem_square_iff] at hleftSite hrightSite
  refine Or.inr (Or.inr (Or.inr ?_))
  have htileGap : leftIndex.2 * blockWidth + blockWidth + blockWidth ≤
      rightIndex.2 * blockWidth := by
    calc
      leftIndex.2 * blockWidth + blockWidth + blockWidth =
          (leftIndex.2 + 2) * blockWidth := by ring
      _ ≤ rightIndex.2 * blockWidth :=
        Nat.mul_le_mul_right blockWidth (by omega)
  have horder : leftSite.2.val ≤ rightSite.2.val := by omega
  rw [Nat.le_sub_iff_add_le horder]
  omega

/--
The source corner cutout separates a tile from the diagonally next tile.  If
both coordinate gaps were smaller than `range`, the point in the lower-left
tile would lie in its removed corner window.
-/
theorem coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) (left right : Finset L.Site)
    (hleftTile : left ⊆ L.tile blockWidth index)
    (hleftNotCorner : ∀ site ∈ left, ¬ L.cornerCutout blockWidth margin site)
    (hrightTile : right ⊆ L.tile blockWidth (index.1 + 1, index.2 + 1)) :
    L.CoordinateRangeSeparated range left right := by
  intro leftSite hleftSite rightSite hrightSite
  have hleftTileSite := hleftTile hleftSite
  have hrightTileSite := hrightTile hrightSite
  have hleftIndex : L.tileIndex blockWidth leftSite = index :=
    L.tileIndex_eq_of_mem_tile hblockWidth hleftTileSite
  have hrowIndex : leftSite.1.val / blockWidth = index.1 :=
    congrArg Prod.fst hleftIndex
  have hcolumnIndex : leftSite.2.val / blockWidth = index.2 :=
    congrArg Prod.snd hleftIndex
  have hrowDecomposition : leftSite.1.val =
      index.1 * blockWidth + leftSite.1.val % blockWidth := by
    calc
      leftSite.1.val = blockWidth * (leftSite.1.val / blockWidth) +
          leftSite.1.val % blockWidth :=
        (Nat.div_add_mod leftSite.1.val blockWidth).symm
      _ = index.1 * blockWidth + leftSite.1.val % blockWidth := by
        rw [hrowIndex, Nat.mul_comm]
  have hcolumnDecomposition : leftSite.2.val =
      index.2 * blockWidth + leftSite.2.val % blockWidth := by
    calc
      leftSite.2.val = blockWidth * (leftSite.2.val / blockWidth) +
          leftSite.2.val % blockWidth :=
        (Nat.div_add_mod leftSite.2.val blockWidth).symm
      _ = index.2 * blockWidth + leftSite.2.val % blockWidth := by
        rw [hcolumnIndex, Nat.mul_comm]
  have hleftBounds := (L.mem_square_iff (index.1 * blockWidth,
    index.2 * blockWidth) blockWidth leftSite).mp hleftTileSite
  have hrightBounds := (L.mem_square_iff ((index.1 + 1) * blockWidth,
    (index.2 + 1) * blockWidth) blockWidth rightSite).mp hrightTileSite
  by_cases hrowGap : range ≤ rightSite.1.val - leftSite.1.val
  · exact Or.inr (Or.inl hrowGap)
  by_cases hcolumnGap : range ≤ rightSite.2.val - leftSite.2.val
  · exact Or.inr (Or.inr (Or.inr hcolumnGap))
  exfalso
  apply hleftNotCorner leftSite hleftSite
  have hrightRowLower : index.1 * blockWidth + blockWidth ≤ rightSite.1.val := by
    simpa [Nat.add_mul] using hrightBounds.1
  have hrightColumnLower : index.2 * blockWidth + blockWidth ≤ rightSite.2.val := by
    simpa [Nat.add_mul] using hrightBounds.2.2.1
  have hrowOrder : leftSite.1.val ≤ rightSite.1.val := by
    have hrowTileEdge : index.1 * blockWidth + blockWidth ≤
        (index.1 + 1) * blockWidth := by simp [Nat.add_mul]
    omega
  have hcolumnOrder : leftSite.2.val ≤ rightSite.2.val := by
    have hcolumnTileEdge : index.2 * blockWidth + blockWidth ≤
        (index.2 + 1) * blockWidth := by simp [Nat.add_mul]
    omega
  have hrowGapLt : rightSite.1.val - leftSite.1.val < range :=
    Nat.lt_of_not_ge hrowGap
  have hcolumnGapLt : rightSite.2.val - leftSite.2.val < range :=
    Nat.lt_of_not_ge hcolumnGap
  constructor
  · right
    omega
  · right
    omega

/--
The other diagonal orientation is separated by the same corner cutout.  Here
the left region is in the upper-left tile and the right region in the
lower-right tile, so the two failed gaps force the upper-left point into its
lower-right removed corner.
-/
theorem coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) (left right : Finset L.Site)
    (hleftTile : left ⊆ L.tile blockWidth (index.1, index.2 + 1))
    (hleftNotCorner : ∀ site ∈ left, ¬ L.cornerCutout blockWidth margin site)
    (hrightTile : right ⊆ L.tile blockWidth (index.1 + 1, index.2)) :
    L.CoordinateRangeSeparated range left right := by
  intro leftSite hleftSite rightSite hrightSite
  have hleftTileSite := hleftTile hleftSite
  have hrightTileSite := hrightTile hrightSite
  have hleftIndex : L.tileIndex blockWidth leftSite = (index.1, index.2 + 1) :=
    L.tileIndex_eq_of_mem_tile hblockWidth hleftTileSite
  have hrowIndex : leftSite.1.val / blockWidth = index.1 :=
    congrArg Prod.fst hleftIndex
  have hcolumnIndex : leftSite.2.val / blockWidth = index.2 + 1 :=
    congrArg Prod.snd hleftIndex
  have hrowDecomposition : leftSite.1.val =
      index.1 * blockWidth + leftSite.1.val % blockWidth := by
    calc
      leftSite.1.val = blockWidth * (leftSite.1.val / blockWidth) +
          leftSite.1.val % blockWidth :=
        (Nat.div_add_mod leftSite.1.val blockWidth).symm
      _ = index.1 * blockWidth + leftSite.1.val % blockWidth := by
        rw [hrowIndex, Nat.mul_comm]
  have hcolumnDecomposition : leftSite.2.val = index.2 * blockWidth + blockWidth +
      leftSite.2.val % blockWidth := by
    calc
      leftSite.2.val = blockWidth * (leftSite.2.val / blockWidth) +
          leftSite.2.val % blockWidth :=
        (Nat.div_add_mod leftSite.2.val blockWidth).symm
      _ = (index.2 + 1) * blockWidth + leftSite.2.val % blockWidth := by
        rw [hcolumnIndex, Nat.mul_comm]
      _ = index.2 * blockWidth + blockWidth + leftSite.2.val % blockWidth := by
        simp [Nat.add_mul]
  have hleftBounds := (L.mem_square_iff (index.1 * blockWidth,
    (index.2 + 1) * blockWidth) blockWidth leftSite).mp hleftTileSite
  have hrightBounds := (L.mem_square_iff ((index.1 + 1) * blockWidth,
    index.2 * blockWidth) blockWidth rightSite).mp hrightTileSite
  by_cases hrowGap : range ≤ rightSite.1.val - leftSite.1.val
  · exact Or.inr (Or.inl hrowGap)
  by_cases hcolumnGap : range ≤ leftSite.2.val - rightSite.2.val
  · exact Or.inr (Or.inr (Or.inl hcolumnGap))
  exfalso
  apply hleftNotCorner leftSite hleftSite
  have hrightRowLower : index.1 * blockWidth + blockWidth ≤ rightSite.1.val := by
    simpa [Nat.add_mul] using hrightBounds.1
  have hrightColumnUpper : rightSite.2.val < index.2 * blockWidth + blockWidth := by
    exact hrightBounds.2.2.2
  have hrowOrder : leftSite.1.val ≤ rightSite.1.val := by
    have hrowTileEdge : index.1 * blockWidth + blockWidth ≤
        (index.1 + 1) * blockWidth := by simp [Nat.add_mul]
    omega
  have hcolumnOrder : rightSite.2.val ≤ leftSite.2.val := by
    have hcolumnTileEdge : index.2 * blockWidth + blockWidth ≤
        (index.2 + 1) * blockWidth := by simp [Nat.add_mul]
    omega
  have hrowGapLt : rightSite.1.val - leftSite.1.val < range :=
    Nat.lt_of_not_ge hrowGap
  have hcolumnGapLt : leftSite.2.val - rightSite.2.val < range :=
    Nat.lt_of_not_ge hcolumnGap
  constructor
  · right
    omega
  · left
    omega

/--
Two distinct checkerboard indices are either separated by a whole tile in one
coordinate or are diagonal neighbours.  The one-axis-neighbour cases are
excluded by the common parity.
-/
theorem sameColor_tileIndex_relation (parityOffset : Nat) (left right : Nat × Nat)
    (hevenLeft : Even (left.1 + left.2 + parityOffset))
    (hevenRight : Even (right.1 + right.2 + parityOffset))
    (hne : left ≠ right) :
    left.1 + 1 < right.1 ∨ right.1 + 1 < left.1 ∨
      left.2 + 1 < right.2 ∨ right.2 + 1 < left.2 ∨
        (right.1 = left.1 + 1 ∧ right.2 = left.2 + 1) ∨
          (right.1 = left.1 + 1 ∧ left.2 = right.2 + 1) ∨
            (left.1 = right.1 + 1 ∧ right.2 = left.2 + 1) ∨
              left.1 = right.1 + 1 ∧ left.2 = right.2 + 1 := by
  by_cases hrowForward : left.1 + 1 < right.1
  · exact Or.inl hrowForward
  by_cases hrowBackward : right.1 + 1 < left.1
  · exact Or.inr (Or.inl hrowBackward)
  by_cases hcolumnForward : left.2 + 1 < right.2
  · exact Or.inr (Or.inr (Or.inl hcolumnForward))
  by_cases hcolumnBackward : right.2 + 1 < left.2
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcolumnBackward)))
  have hrowClose : right.1 = left.1 ∨ right.1 = left.1 + 1 ∨
      left.1 = right.1 + 1 := by omega
  have hcolumnClose : right.2 = left.2 ∨ right.2 = left.2 + 1 ∨
      left.2 = right.2 + 1 := by omega
  rcases hevenLeft with ⟨leftHalf, hleftHalf⟩
  rcases hevenRight with ⟨rightHalf, hrightHalf⟩
  rcases hrowClose with hrow | hrow | hrow <;>
    rcases hcolumnClose with hcolumn | hcolumn | hcolumn
  · exact False.elim (hne (by ext <;> omega))
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hrow, hcolumn⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hrow, hcolumn⟩)))))
  · exfalso
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hrow, hcolumn⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hrow, hcolumn⟩))))))

/--
The full same-color separation proof for any family of corner-trimmed tile
components.  This combines the parity classification with the proven finite
row, column, and diagonal coordinate arguments.
-/
theorem coordinateRangeSeparated_of_even_cornerCutoutComponents
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : range ≤ blockWidth)
    (hrangeMargin : range ≤ margin) (component : Nat × Nat → Finset L.Site)
    (hcomponentTile : ∀ index, component index ⊆ L.tile blockWidth index)
    (hcomponentNotCorner : ∀ index site, site ∈ component index →
      ¬ L.cornerCutout blockWidth margin site)
    (parityOffset : Nat) (leftIndex rightIndex : Nat × Nat)
    (hevenLeft : Even (leftIndex.1 + leftIndex.2 + parityOffset))
    (hevenRight : Even (rightIndex.1 + rightIndex.2 + parityOffset))
    (hne : leftIndex ≠ rightIndex) :
    L.CoordinateRangeSeparated range (component leftIndex) (component rightIndex) := by
  rcases sameColor_tileIndex_relation parityOffset leftIndex rightIndex hevenLeft hevenRight hne with
      hrowForward | hrowBackward | hcolumnForward | hcolumnBackward |
        hdiagonalUp | hdiagonalDown | hdiagonalLeftUp | hdiagonalLeftDown
  · exact CoordinateRangeSeparated.mono L
      (L.coordinateRangeSeparated_tile_of_row_gap hrangeBlock leftIndex rightIndex hrowForward)
      (hcomponentTile leftIndex) (hcomponentTile rightIndex)
  · exact CoordinateRangeSeparated.symm L (CoordinateRangeSeparated.mono L
      (L.coordinateRangeSeparated_tile_of_row_gap hrangeBlock rightIndex leftIndex hrowBackward)
      (hcomponentTile rightIndex) (hcomponentTile leftIndex))
  · exact CoordinateRangeSeparated.mono L
      (L.coordinateRangeSeparated_tile_of_column_gap hrangeBlock leftIndex rightIndex
        hcolumnForward)
      (hcomponentTile leftIndex) (hcomponentTile rightIndex)
  · exact CoordinateRangeSeparated.symm L (CoordinateRangeSeparated.mono L
      (L.coordinateRangeSeparated_tile_of_column_gap hrangeBlock rightIndex leftIndex
        hcolumnBackward)
      (hcomponentTile rightIndex) (hcomponentTile leftIndex))
  · have hrightIndex : (leftIndex.1 + 1, leftIndex.2 + 1) = rightIndex := by
      apply Prod.ext <;> omega
    exact L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
      hblockWidth hrangeMargin leftIndex (component leftIndex) (component rightIndex)
      (hcomponentTile leftIndex)
      (fun site hsite => hcomponentNotCorner leftIndex site hsite)
      (by simpa only [hrightIndex] using hcomponentTile rightIndex)
  · have hleftIndex : (leftIndex.1, rightIndex.2 + 1) = leftIndex := by
      apply Prod.ext <;> omega
    have hrightIndex : (leftIndex.1 + 1, rightIndex.2) = rightIndex := by
      apply Prod.ext <;> omega
    exact L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
      hblockWidth hrangeMargin (leftIndex.1, rightIndex.2)
      (component leftIndex) (component rightIndex)
      (by simpa only [hleftIndex] using hcomponentTile leftIndex)
      (fun site hsite => hcomponentNotCorner leftIndex site hsite)
      (by simpa only [hrightIndex] using hcomponentTile rightIndex)
  · have hrightIndex : (rightIndex.1, leftIndex.2 + 1) = rightIndex := by
      apply Prod.ext <;> omega
    have hleftIndex : (rightIndex.1 + 1, leftIndex.2) = leftIndex := by
      apply Prod.ext <;> omega
    exact CoordinateRangeSeparated.symm L
      (L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
        hblockWidth hrangeMargin (rightIndex.1, leftIndex.2)
        (component rightIndex) (component leftIndex)
        (by simpa only [hrightIndex] using hcomponentTile rightIndex)
        (fun site hsite => hcomponentNotCorner rightIndex site hsite)
        (by simpa only [hleftIndex] using hcomponentTile leftIndex))
  · have hleftIndex : (rightIndex.1 + 1, rightIndex.2 + 1) = leftIndex := by
      apply Prod.ext <;> omega
    exact CoordinateRangeSeparated.symm L
      (L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
        hblockWidth hrangeMargin rightIndex (component rightIndex) (component leftIndex)
        (hcomponentTile rightIndex)
        (fun site hsite => hcomponentNotCorner rightIndex site hsite)
        (by simpa only [hleftIndex] using hcomponentTile leftIndex))

/-- Every two distinct even-colored indexed `A` components have the source gap. -/
theorem coordinateRangeSeparated_squarePartitionAComponent_of_even_distinct
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : range ≤ blockWidth)
    (hrangeMargin : range ≤ margin) (leftIndex rightIndex : Nat × Nat)
    (hevenLeft : Even (leftIndex.1 + leftIndex.2))
    (hevenRight : Even (rightIndex.1 + rightIndex.2))
    (hne : leftIndex ≠ rightIndex) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionAComponent blockWidth margin leftIndex)
      (L.squarePartitionAComponent blockWidth margin rightIndex) := by
  exact coordinateRangeSeparated_of_even_cornerCutoutComponents L hblockWidth hrangeBlock
    hrangeMargin (L.squarePartitionAComponent blockWidth margin)
    (fun _ => Finset.inter_subset_left)
    (fun index site hsite =>
      (L.mem_squarePartitionAComponent_iff blockWidth margin index site |>.mp hsite).2.1)
    0 leftIndex rightIndex (by simpa using hevenLeft) (by simpa using hevenRight) hne

/-- Every two distinct odd-colored indexed `B` components have the source gap. -/
theorem coordinateRangeSeparated_squarePartitionBComponent_of_odd_distinct
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : range ≤ blockWidth)
    (hrangeMargin : range ≤ margin) (leftIndex rightIndex : Nat × Nat)
    (hoddLeft : ¬ Even (leftIndex.1 + leftIndex.2))
    (hoddRight : ¬ Even (rightIndex.1 + rightIndex.2))
    (hne : leftIndex ≠ rightIndex) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionBComponent blockWidth margin leftIndex)
      (L.squarePartitionBComponent blockWidth margin rightIndex) := by
  have hevenLeft : Even (leftIndex.1 + leftIndex.2 + 1) := by
    rcases Nat.not_even_iff_odd.mp hoddLeft with ⟨half, hhalf⟩
    exact ⟨half + 1, by omega⟩
  have hevenRight : Even (rightIndex.1 + rightIndex.2 + 1) := by
    rcases Nat.not_even_iff_odd.mp hoddRight with ⟨half, hhalf⟩
    exact ⟨half + 1, by omega⟩
  exact coordinateRangeSeparated_of_even_cornerCutoutComponents L hblockWidth hrangeBlock
    hrangeMargin (L.squarePartitionBComponent blockWidth margin)
    (fun _ => Finset.inter_subset_left)
    (fun index site hsite =>
      (L.mem_squarePartitionBComponent_iff blockWidth margin index site |>.mp hsite).2.1)
    1 leftIndex rightIndex hevenLeft hevenRight hne
/-- The diagonal corner-cutout separation specialized to indexed `A` blocks. -/
theorem coordinateRangeSeparated_squarePartitionAComponent_diagonal_succ_succ
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionAComponent blockWidth margin index)
      (L.squarePartitionAComponent blockWidth margin (index.1 + 1, index.2 + 1)) := by
  apply L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
    hblockWidth hrange index
  · intro site hsite
    exact (L.mem_squarePartitionAComponent_iff blockWidth margin index site |>.mp hsite).1
  · intro site hsite
    exact (L.mem_squarePartitionAComponent_iff blockWidth margin index site |>.mp hsite).2.1
  · intro site hsite
    exact (L.mem_squarePartitionAComponent_iff blockWidth margin
      (index.1 + 1, index.2 + 1) site |>.mp hsite).1

/-- The diagonal corner-cutout separation specialized to indexed `B` blocks. -/
theorem coordinateRangeSeparated_squarePartitionBComponent_diagonal_succ_succ
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionBComponent blockWidth margin index)
      (L.squarePartitionBComponent blockWidth margin (index.1 + 1, index.2 + 1)) := by
  apply L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
    hblockWidth hrange index
  · intro site hsite
    exact (L.mem_squarePartitionBComponent_iff blockWidth margin index site |>.mp hsite).1
  · intro site hsite
    exact (L.mem_squarePartitionBComponent_iff blockWidth margin index site |>.mp hsite).2.1
  · intro site hsite
    exact (L.mem_squarePartitionBComponent_iff blockWidth margin
      (index.1 + 1, index.2 + 1) site |>.mp hsite).1

/-- The actual finite family of `A` blocks covers exactly the constructed `A` region. -/
theorem biUnion_squarePartitionAComponents_eq_squarePartitionA
    (L : BPTSquareLattice) {blockWidth : Nat} (hblockWidth : 0 < blockWidth)
    (margin : Nat) :
    (L.squarePartitionAComponents blockWidth margin).biUnion id =
      L.squarePartitionA blockWidth margin := by
  ext site
  constructor
  · intro hsite
    rcases Finset.mem_biUnion.mp hsite with ⟨block, hblock, hsiteBlock⟩
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, _, rfl⟩
    exact (Finset.mem_inter.mp hsiteBlock).2
  · intro hsite
    have htile : site ∈ L.tile blockWidth (L.tileIndex blockWidth site) :=
      L.mem_tile_of_pos hblockWidth site
    have hindex : L.tileIndex blockWidth site ∈ L.occupiedTileIndices blockWidth :=
      Finset.mem_image.mpr ⟨site, Finset.mem_univ _, rfl⟩
    have heven : Even ((L.tileIndex blockWidth site).1 + (L.tileIndex blockWidth site).2) := by
      simpa [checkerboardEven, tileIndex] using
        (show L.checkerboardEven blockWidth site from
          (Finset.mem_filter.mp hsite).2.2)
    have hcomponent : L.squarePartitionAComponent blockWidth margin
        (L.tileIndex blockWidth site) ∈
        L.squarePartitionAComponents blockWidth margin :=
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨L.tileIndex blockWidth site,
        Finset.mem_filter.mpr ⟨hindex, heven⟩, rfl⟩,
        ⟨site, Finset.mem_inter.mpr ⟨htile, hsite⟩⟩⟩
    exact Finset.mem_biUnion.mpr ⟨_, hcomponent,
      Finset.mem_inter.mpr ⟨htile, hsite⟩⟩

/-- The actual finite family of `B` blocks covers exactly the constructed `B` region. -/
theorem biUnion_squarePartitionBComponents_eq_squarePartitionB
    (L : BPTSquareLattice) {blockWidth : Nat} (hblockWidth : 0 < blockWidth)
    (margin : Nat) :
    (L.squarePartitionBComponents blockWidth margin).biUnion id =
      L.squarePartitionB blockWidth margin := by
  ext site
  constructor
  · intro hsite
    rcases Finset.mem_biUnion.mp hsite with ⟨block, hblock, hsiteBlock⟩
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, _, rfl⟩
    exact (Finset.mem_inter.mp hsiteBlock).2
  · intro hsite
    have htile : site ∈ L.tile blockWidth (L.tileIndex blockWidth site) :=
      L.mem_tile_of_pos hblockWidth site
    have hindex : L.tileIndex blockWidth site ∈ L.occupiedTileIndices blockWidth :=
      Finset.mem_image.mpr ⟨site, Finset.mem_univ _, rfl⟩
    have hodd : ¬ Even ((L.tileIndex blockWidth site).1 + (L.tileIndex blockWidth site).2) := by
      simpa [checkerboardEven, tileIndex] using
        (show ¬ L.checkerboardEven blockWidth site from
          (Finset.mem_filter.mp hsite).2.2)
    have hcomponent : L.squarePartitionBComponent blockWidth margin
        (L.tileIndex blockWidth site) ∈
        L.squarePartitionBComponents blockWidth margin :=
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨L.tileIndex blockWidth site,
        Finset.mem_filter.mpr ⟨hindex, hodd⟩, rfl⟩,
        ⟨site, Finset.mem_inter.mpr ⟨htile, hsite⟩⟩⟩
    exact Finset.mem_biUnion.mpr ⟨_, hcomponent,
      Finset.mem_inter.mpr ⟨htile, hsite⟩⟩

/-- The finite BPT regions are disjoint in the `A`, `B`, `C` source split. -/
theorem squarePartition_pairwise_disjoint (L : BPTSquareLattice)
    (blockWidth margin : Nat) :
    Disjoint (L.squarePartitionA blockWidth margin) (L.squarePartitionB blockWidth margin) ∧
      Disjoint (L.squarePartitionA blockWidth margin) (L.squarePartitionC blockWidth margin) ∧
        Disjoint (L.squarePartitionB blockWidth margin) (L.squarePartitionC blockWidth margin) := by
  constructor
  · rw [Finset.disjoint_left]
    intro site hA hB
    simp only [squarePartitionA, squarePartitionB, Finset.mem_filter,
      Finset.mem_univ, true_and] at hA hB
    exact hB.2 hA.2
  constructor <;> rw [Finset.disjoint_left] <;> intro site hleft hright
  · simp only [squarePartitionA, squarePartitionC, Finset.mem_filter,
      Finset.mem_univ, true_and] at hleft hright
    exact hleft.1 hright
  · simp only [squarePartitionB, squarePartitionC, Finset.mem_filter,
      Finset.mem_univ, true_and] at hleft hright
    exact hleft.1 hright

/-- The explicitly constructed `A`, `B`, and `C` regions cover the lattice. -/
theorem squarePartition_union_eq_univ (L : BPTSquareLattice)
    (blockWidth margin : Nat) :
    L.squarePartitionA blockWidth margin ∪ L.squarePartitionB blockWidth margin ∪
      L.squarePartitionC blockWidth margin = Finset.univ := by
  ext site
  simp only [Finset.mem_union, squarePartitionA, squarePartitionB, squarePartitionC,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hcorner : L.cornerCutout blockWidth margin site
  · tauto
  by_cases heven : L.checkerboardEven blockWidth site <;> tauto

/-- The source `C` region is exactly the complement of the two checkerboard regions. -/
theorem squarePartitionAB_eq_compl_C (L : BPTSquareLattice)
    (blockWidth margin : Nat) :
    L.squarePartitionA blockWidth margin ∪ L.squarePartitionB blockWidth margin =
      (L.squarePartitionC blockWidth margin)ᶜ := by
  ext site
  simp only [Finset.mem_union, Finset.mem_compl, squarePartitionA, squarePartitionB,
    squarePartitionC, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hcorner : L.cornerCutout blockWidth margin site
  · tauto
  by_cases heven : L.checkerboardEven blockWidth site <;> tauto

/-- A finite open-boundary source square has at most `width^2` sites. -/
theorem square_card_le_width_sq (L : BPTSquareLattice) (origin : Nat × Nat) (width : Nat) :
    (L.square origin width).card <= width * width := by
  let f : {site : L.Site // site ∈ L.square origin width} → Fin width × Fin width :=
    fun site =>
      (⟨site.1.1.val - origin.1, by
        have h := (L.mem_square_iff origin width site.1).mp site.2
        omega⟩,
      ⟨site.1.2.val - origin.2, by
        have h := (L.mem_square_iff origin width site.1).mp site.2
        omega⟩)
  have hinjective : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hs := (L.mem_square_iff origin width s.1).mp s.2
      have ht := (L.mem_square_iff origin width t.1).mp t.2
      have hrow : s.1.1.val - origin.1 = t.1.1.val - origin.1 := by
        exact congrArg (fun pair => pair.1.val) h
      calc
        s.1.1.val = origin.1 + (s.1.1.val - origin.1) := (Nat.add_sub_of_le hs.1).symm
        _ = origin.1 + (t.1.1.val - origin.1) := by rw [hrow]
        _ = t.1.1.val := Nat.add_sub_of_le ht.1
    · apply Fin.ext
      have hs := (L.mem_square_iff origin width s.1).mp s.2
      have ht := (L.mem_square_iff origin width t.1).mp t.2
      have hcolumn : s.1.2.val - origin.2 = t.1.2.val - origin.2 := by
        exact congrArg (fun pair => pair.2.val) h
      calc
        s.1.2.val = origin.2 + (s.1.2.val - origin.2) :=
          (Nat.add_sub_of_le hs.2.2.1).symm
        _ = origin.2 + (t.1.2.val - origin.2) := by rw [hcolumn]
        _ = t.1.2.val := Nat.add_sub_of_le ht.2.2.1
  have hcard := Fintype.card_le_of_injective f hinjective
  calc
    (L.square origin width).card =
        Fintype.card {site : L.Site // site ∈ L.square origin width} :=
      (Fintype.card_coe (L.square origin width)).symm
    _ ≤ width * width := by simpa using hcard

/-- Every `A` component is a finite source square truncated by the `C` cutout. -/
theorem squarePartitionAComponent_card_le_width_sq (L : BPTSquareLattice)
    (blockWidth margin : Nat) (block : Finset L.Site)
    (hblock : block ∈ L.squarePartitionAComponents blockWidth margin) :
    block.card <= blockWidth * blockWidth := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, _, rfl⟩
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (by simpa [tile] using
      L.square_card_le_width_sq (index.1 * blockWidth, index.2 * blockWidth) blockWidth)

/-- Every `B` component is a finite source square truncated by the `C` cutout. -/
theorem squarePartitionBComponent_card_le_width_sq (L : BPTSquareLattice)
    (blockWidth margin : Nat) (block : Finset L.Site)
    (hblock : block ∈ L.squarePartitionBComponents blockWidth margin) :
    block.card <= blockWidth * blockWidth := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, _, rfl⟩
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (by simpa [tile] using
      L.square_card_le_width_sq (index.1 * blockWidth, index.2 * blockWidth) blockWidth)

/-- Each tile's actual C residue lies in one of four explicit corner rectangles. -/
theorem tile_inter_squarePartitionC_subset_cornerCutoutTileCover (L : BPTSquareLattice)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth) (hmargin : margin ≤ blockWidth)
    (index : Nat × Nat) :
    L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin ⊆
      L.cornerCutoutTileCover blockWidth margin index := by
  intro site hsite
  rcases Finset.mem_inter.mp hsite with ⟨htile, hC⟩
  have hindex : L.tileIndex blockWidth site = index :=
    L.tileIndex_eq_of_mem_tile hblockWidth htile
  have hrowIndex : site.1.val / blockWidth = index.1 := congrArg Prod.fst hindex
  have hcolumnIndex : site.2.val / blockWidth = index.2 := congrArg Prod.snd hindex
  have hrowDecomposition : site.1.val =
      index.1 * blockWidth + site.1.val % blockWidth := by
    calc
      site.1.val = blockWidth * (site.1.val / blockWidth) + site.1.val % blockWidth :=
        (Nat.div_add_mod site.1.val blockWidth).symm
      _ = index.1 * blockWidth + site.1.val % blockWidth := by
        rw [hrowIndex, Nat.mul_comm]
  have hcolumnDecomposition : site.2.val =
      index.2 * blockWidth + site.2.val % blockWidth := by
    calc
      site.2.val = blockWidth * (site.2.val / blockWidth) + site.2.val % blockWidth :=
        (Nat.div_add_mod site.2.val blockWidth).symm
      _ = index.2 * blockWidth + site.2.val % blockWidth := by
        rw [hcolumnIndex, Nat.mul_comm]
  have hrowModLt : site.1.val % blockWidth < blockWidth :=
    Nat.mod_lt _ hblockWidth
  have hcolumnModLt : site.2.val % blockWidth < blockWidth :=
    Nat.mod_lt _ hblockWidth
  have hcorner : L.cornerCutout blockWidth margin site := by
    simpa [squarePartitionC] using hC
  rcases hcorner with ⟨hrowCorner, hcolumnCorner⟩
  rcases hrowCorner with hrowLower | hrowUpper <;>
    rcases hcolumnCorner with hcolumnLower | hcolumnUpper
  · simp only [cornerCutoutTileCover, Finset.mem_union,
      mem_rectangle_iff]
    omega
  · simp only [cornerCutoutTileCover, Finset.mem_union,
      mem_rectangle_iff]
    omega
  · simp only [cornerCutoutTileCover, Finset.mem_union,
      mem_rectangle_iff]
    omega
  · simp only [cornerCutoutTileCover, Finset.mem_union,
      mem_rectangle_iff]
    omega

/-- A single source tile contributes at most four `margin`-squared C sites. -/
theorem tile_inter_squarePartitionC_card_le_four_mul_sq (L : BPTSquareLattice)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth) (hmargin : margin ≤ blockWidth)
    (index : Nat × Nat) :
    (L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin).card ≤
      4 * margin * margin := by
  have hsubset := L.tile_inter_squarePartitionC_subset_cornerCutoutTileCover
    hblockWidth hmargin index
  have hLowerLower :
      (L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin).card ≤
        margin * margin :=
    L.rectangle_card_le_area _ _ _
  have hLowerUpper :
      (L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
        margin margin).card ≤ margin * margin :=
    L.rectangle_card_le_area _ _ _
  have hUpperLower :
      (L.rectangle (index.1 * blockWidth + blockWidth - margin, index.2 * blockWidth)
        margin margin).card ≤ margin * margin :=
    L.rectangle_card_le_area _ _ _
  have hUpperUpper :
      (L.rectangle (index.1 * blockWidth + blockWidth - margin,
        index.2 * blockWidth + blockWidth - margin) margin margin).card ≤ margin * margin :=
    L.rectangle_card_le_area _ _ _
  have hcover : (L.cornerCutoutTileCover blockWidth margin index).card ≤
      margin * margin + margin * margin + margin * margin + margin * margin := by
    calc
      (L.cornerCutoutTileCover blockWidth margin index).card =
          (((L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin ∪
            L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
              margin margin) ∪
              L.rectangle (index.1 * blockWidth + blockWidth - margin,
                index.2 * blockWidth) margin margin) ∪
                L.rectangle (index.1 * blockWidth + blockWidth - margin,
                  index.2 * blockWidth + blockWidth - margin) margin margin).card := rfl
      _ ≤ ((L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin ∪
          L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
            margin margin) ∪
            L.rectangle (index.1 * blockWidth + blockWidth - margin,
              index.2 * blockWidth) margin margin).card +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin,
                index.2 * blockWidth + blockWidth - margin) margin margin).card :=
        Finset.card_union_le _ _
      _ ≤ ((L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin ∪
          L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
            margin margin).card +
            (L.rectangle (index.1 * blockWidth + blockWidth - margin,
              index.2 * blockWidth) margin margin).card) +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin,
                index.2 * blockWidth + blockWidth - margin) margin margin).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ ((L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin).card +
          (L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
            margin margin).card +
            (L.rectangle (index.1 * blockWidth + blockWidth - margin,
              index.2 * blockWidth) margin margin).card) +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin,
                index.2 * blockWidth + blockWidth - margin) margin margin).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ (margin * margin + margin * margin + margin * margin) + margin * margin := by
        gcongr
      _ = margin * margin + margin * margin + margin * margin + margin * margin := by omega
  calc
    (L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin).card ≤
        (L.cornerCutoutTileCover blockWidth margin index).card := Finset.card_le_card hsubset
    _ ≤ margin * margin + margin * margin + margin * margin + margin * margin := hcover
    _ = 4 * margin * margin := by ring

/-- A finite regular `blockWidth` tiling has at most its declared grid many occupied tiles. -/
theorem occupiedTileIndices_card_le_grid (L : BPTSquareLattice)
    {blockWidth tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth) :
    (L.occupiedTileIndices blockWidth).card ≤ tileRows * tileColumns := by
  let f : {index : Nat × Nat // index ∈ L.occupiedTileIndices blockWidth} →
      Fin tileRows × Fin tileColumns :=
    fun index =>
      (⟨index.1.1, by
        rcases Finset.mem_image.mp index.2 with ⟨site, _, hindex⟩
        have hrowIndex : site.1.val / blockWidth = index.1.1 := congrArg Prod.fst hindex
        rw [← hrowIndex]
        apply (Nat.div_lt_iff_lt_mul hblockWidth).mpr
        simpa [hrows] using site.1.isLt⟩,
      ⟨index.1.2, by
        rcases Finset.mem_image.mp index.2 with ⟨site, _, hindex⟩
        have hcolumnIndex : site.2.val / blockWidth = index.1.2 := congrArg Prod.snd hindex
        rw [← hcolumnIndex]
        apply (Nat.div_lt_iff_lt_mul hblockWidth).mpr
        simpa [hcolumns] using site.2.isLt⟩)
  have hinjective : Function.Injective f := by
    intro left right h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Fin.val (congrArg Prod.fst h)
    · exact congrArg Fin.val (congrArg Prod.snd h)
  have hcard := Fintype.card_le_of_injective f hinjective
  calc
    (L.occupiedTileIndices blockWidth).card =
        Fintype.card {index : Nat × Nat // index ∈ L.occupiedTileIndices blockWidth} :=
      (Fintype.card_coe (L.occupiedTileIndices blockWidth)).symm
    _ ≤ tileRows * tileColumns := by simpa using hcard

/-- Every occupied regular-grid tile is a fully present source square. -/
theorem tile_fits_of_mem_occupiedTileIndices_grid (L : BPTSquareLattice)
    {blockWidth tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth)
    (index : Nat × Nat) (hindex : index ∈ L.occupiedTileIndices blockWidth) :
    L.squareFits (index.1 * blockWidth, index.2 * blockWidth) blockWidth := by
  rcases Finset.mem_image.mp hindex with ⟨site, _, hsite⟩
  have hrowIndex : site.1.val / blockWidth = index.1 := congrArg Prod.fst hsite
  have hcolumnIndex : site.2.val / blockWidth = index.2 := congrArg Prod.snd hsite
  have hrowLt : index.1 < tileRows := by
    rw [← hrowIndex]
    apply (Nat.div_lt_iff_lt_mul hblockWidth).mpr
    simpa [hrows] using site.1.isLt
  have hcolumnLt : index.2 < tileColumns := by
    rw [← hcolumnIndex]
    apply (Nat.div_lt_iff_lt_mul hblockWidth).mpr
    simpa [hcolumns] using site.2.isLt
  simp only [squareFits]
  constructor
  · calc
      index.1 * blockWidth + blockWidth = (index.1 + 1) * blockWidth := by ring
      _ ≤ tileRows * blockWidth := Nat.mul_le_mul_right blockWidth (by omega)
      _ = L.rows := hrows.symm
  · calc
      index.2 * blockWidth + blockWidth = (index.2 + 1) * blockWidth := by ring
      _ ≤ tileColumns * blockWidth := Nat.mul_le_mul_right blockWidth (by omega)
      _ = L.columns := hcolumns.symm

/--
The finite C corner region has the explicit regular-grid bound
`4 * margin^2` per tile.  There is no asymptotic remainder hidden at an open
boundary: the row and column grid equalities are stated as hypotheses.
-/
theorem squarePartitionC_card_le_grid_four_mul_sq (L : BPTSquareLattice)
    {blockWidth margin tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : margin ≤ blockWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth) :
    (L.squarePartitionC blockWidth margin).card ≤
      tileRows * tileColumns * (4 * margin * margin) := by
  have hsubset : L.squarePartitionC blockWidth margin ⊆
      (L.occupiedTileIndices blockWidth).biUnion
        (fun index => L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin) := by
    intro site hsite
    refine Finset.mem_biUnion.mpr ⟨L.tileIndex blockWidth site, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨site, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_inter.mpr ⟨L.mem_tile_of_pos hblockWidth site, hsite⟩
  have htiles := L.occupiedTileIndices_card_le_grid hblockWidth hrows hcolumns
  calc
    (L.squarePartitionC blockWidth margin).card ≤
        ((L.occupiedTileIndices blockWidth).biUnion
          (fun index => L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ index ∈ L.occupiedTileIndices blockWidth,
        (L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _index ∈ L.occupiedTileIndices blockWidth, 4 * margin * margin := by
      apply Finset.sum_le_sum
      intro index hindex
      exact L.tile_inter_squarePartitionC_card_le_four_mul_sq hblockWidth hmargin index
    _ = (L.occupiedTileIndices blockWidth).card * (4 * margin * margin) := by simp
    _ ≤ tileRows * tileColumns * (4 * margin * margin) :=
      Nat.mul_le_mul_right _ htiles

/--
The open-boundary grid needs no divisibility hypothesis: every occupied tile
index lies below the quotient count of the last lattice coordinate plus one.
The positive side-length assumptions on `BPTSquareLattice` make this the exact
finite ceiling count, including a clipped final row or column.
-/
theorem occupiedTileIndices_card_le_openGrid (L : BPTSquareLattice)
    (blockWidth : Nat) :
    (L.occupiedTileIndices blockWidth).card ≤
      ((L.rows - 1) / blockWidth + 1) * ((L.columns - 1) / blockWidth + 1) := by
  let rowTiles := (L.rows - 1) / blockWidth + 1
  let columnTiles := (L.columns - 1) / blockWidth + 1
  let f : {index : Nat × Nat // index ∈ L.occupiedTileIndices blockWidth} →
      Fin rowTiles × Fin columnTiles :=
    fun index =>
      (⟨index.1.1, by
        rcases Finset.mem_image.mp index.2 with ⟨site, _, hindex⟩
        have hrowIndex : site.1.val / blockWidth = index.1.1 := congrArg Prod.fst hindex
        have hsiteLe : site.1.val ≤ L.rows - 1 := by omega
        have hdivLe : site.1.val / blockWidth ≤ (L.rows - 1) / blockWidth :=
          Nat.div_le_div_right hsiteLe
        rw [← hrowIndex]
        dsimp [rowTiles]
        omega⟩,
      ⟨index.1.2, by
        rcases Finset.mem_image.mp index.2 with ⟨site, _, hindex⟩
        have hcolumnIndex : site.2.val / blockWidth = index.1.2 := congrArg Prod.snd hindex
        have hsiteLe : site.2.val ≤ L.columns - 1 := by omega
        have hdivLe : site.2.val / blockWidth ≤ (L.columns - 1) / blockWidth :=
          Nat.div_le_div_right hsiteLe
        rw [← hcolumnIndex]
        dsimp [columnTiles]
        omega⟩)
  have hinjective : Function.Injective f := by
    intro left right h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Fin.val (congrArg Prod.fst h)
    · exact congrArg Fin.val (congrArg Prod.snd h)
  have hcard := Fintype.card_le_of_injective f hinjective
  calc
    (L.occupiedTileIndices blockWidth).card =
        Fintype.card {index : Nat × Nat // index ∈ L.occupiedTileIndices blockWidth} :=
      (Fintype.card_coe (L.occupiedTileIndices blockWidth)).symm
    _ ≤ rowTiles * columnTiles := by simpa using hcard
    _ = ((L.rows - 1) / blockWidth + 1) * ((L.columns - 1) / blockWidth + 1) := rfl

/--
The finite `C` count for a clipped open-boundary grid.  Unlike the earlier
regular-grid lemma, it counts the partial final row and column explicitly.
-/
theorem squarePartitionC_card_le_openGrid_four_mul_sq (L : BPTSquareLattice)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : margin ≤ blockWidth) :
    (L.squarePartitionC blockWidth margin).card ≤
      (((L.rows - 1) / blockWidth + 1) * ((L.columns - 1) / blockWidth + 1)) *
        (4 * margin * margin) := by
  have hsubset : L.squarePartitionC blockWidth margin ⊆
      (L.occupiedTileIndices blockWidth).biUnion
        (fun index => L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin) := by
    intro site hsite
    refine Finset.mem_biUnion.mpr ⟨L.tileIndex blockWidth site, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨site, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_inter.mpr ⟨L.mem_tile_of_pos hblockWidth site, hsite⟩
  have htiles := L.occupiedTileIndices_card_le_openGrid blockWidth
  calc
    (L.squarePartitionC blockWidth margin).card ≤
        ((L.occupiedTileIndices blockWidth).biUnion
          (fun index => L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ index ∈ L.occupiedTileIndices blockWidth,
        (L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _index ∈ L.occupiedTileIndices blockWidth, 4 * margin * margin := by
      apply Finset.sum_le_sum
      intro index hindex
      exact L.tile_inter_squarePartitionC_card_le_four_mul_sq hblockWidth hmargin index
    _ = (L.occupiedTileIndices blockWidth).card * (4 * margin * margin) := by simp
    _ ≤ (((L.rows - 1) / blockWidth + 1) * ((L.columns - 1) / blockWidth + 1)) *
          (4 * margin * margin) :=
      Nat.mul_le_mul_right _ htiles

/-- The four enlarged C corner squares have at most `36 * margin^2` sites. -/
theorem cornerCutoutTileExpandedCover_card_le_thirtysix_mul_sq (L : BPTSquareLattice)
    (blockWidth margin : Nat) (index : Nat × Nat) :
    (L.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
      36 * margin * margin := by
  let side := margin + margin + margin
  have hLowerLower :
      (L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
        side side).card ≤ side * side :=
    L.rectangle_card_le_area _ _ _
  have hLowerUpper :
      (L.rectangle (index.1 * blockWidth - margin,
        index.2 * blockWidth + blockWidth - margin - margin) side side).card ≤ side * side :=
    L.rectangle_card_le_area _ _ _
  have hUpperLower :
      (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
        index.2 * blockWidth - margin) side side).card ≤ side * side :=
    L.rectangle_card_le_area _ _ _
  have hUpperUpper :
      (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
        index.2 * blockWidth + blockWidth - margin - margin) side side).card ≤ side * side :=
    L.rectangle_card_le_area _ _ _
  have hcover : (L.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
      side * side + side * side + side * side + side * side := by
    calc
      (L.cornerCutoutTileExpandedCover blockWidth margin index).card =
          (((L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
            side side ∪
            L.rectangle (index.1 * blockWidth - margin,
              index.2 * blockWidth + blockWidth - margin - margin) side side) ∪
              L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                index.2 * blockWidth - margin) side side) ∪
                L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                  index.2 * blockWidth + blockWidth - margin - margin) side side).card := rfl
      _ ≤ ((L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
          side side ∪
          L.rectangle (index.1 * blockWidth - margin,
            index.2 * blockWidth + blockWidth - margin - margin) side side) ∪
            L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
              index.2 * blockWidth - margin) side side).card +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                index.2 * blockWidth + blockWidth - margin - margin) side side).card :=
        Finset.card_union_le _ _
      _ ≤ ((L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
          side side ∪
          L.rectangle (index.1 * blockWidth - margin,
            index.2 * blockWidth + blockWidth - margin - margin) side side).card +
            (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
              index.2 * blockWidth - margin) side side).card) +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                index.2 * blockWidth + blockWidth - margin - margin) side side).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ ((L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
          side side).card +
          (L.rectangle (index.1 * blockWidth - margin,
            index.2 * blockWidth + blockWidth - margin - margin) side side).card +
            (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
              index.2 * blockWidth - margin) side side).card) +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                index.2 * blockWidth + blockWidth - margin - margin) side side).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ (side * side + side * side + side * side) + side * side := by
        gcongr
      _ = side * side + side * side + side * side + side * side := by omega
  calc
    (L.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
        side * side + side * side + side * side + side * side := hcover
    _ = 36 * margin * margin := by dsimp [side]; ring

/-- A square based at the open-boundary origin covers the finite lattice at any large enough side. -/
theorem square_zero_eq_univ_of_le (L : BPTSquareLattice) (width : Nat)
    (hrows : L.rows ≤ width) (hcolumns : L.columns ≤ width) :
    L.square (0, 0) width = Finset.univ := by
  ext site
  simp only [Finset.mem_univ, iff_true, mem_square_iff]
  omega

end BPTSquareLattice

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
The #378 support-square locality condition turns an explicit coordinate gap
into the actual-projector separation premise of #403.  No graph proxy or
assumed union recovery is involved.
-/
theorem actualProjectorSeparated_of_coordinateRangeSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hgap : L.lattice.CoordinateRangeSeparated M.interactionRange left right) :
    M.ActualProjectorSeparated left right := by
  intro check hboth
  rcases hboth.1 with ⟨leftSite, hleftSite⟩
  rcases hboth.2 with ⟨rightSite, hrightSite⟩
  rcases Finset.mem_inter.mp hleftSite with ⟨hleftSupport, hleft⟩
  rcases Finset.mem_inter.mp hrightSite with ⟨hrightSupport, hright⟩
  have hleftSquare := (M.projector_support_subset_square check) hleftSupport
  have hrightSquare := (M.projector_support_subset_square check) hrightSupport
  simp only [BPTSquareLattice.mem_square_iff] at hleftSquare hrightSquare
  rcases hgap leftSite hleft rightSite hright with hrow | hrow | hcolumn | hcolumn <;> omega

/--
The concrete finite `A` family satisfies #403's actual-support separation
premise.  This derives it from the source checkerboard and corner-cutout
geometry rather than accepting pairwise separation as a caller hypothesis.
-/
theorem actualProjectorSeparated_squarePartitionAComponents
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (left : Finset L.Site)
    (hleft : left ∈ L.lattice.squarePartitionAComponents blockWidth margin)
    (right : Finset L.Site)
    (hright : right ∈ L.lattice.squarePartitionAComponents blockWidth margin)
    (hne : left ≠ right) :
    M.ActualProjectorSeparated left right := by
  apply M.actualProjectorSeparated_of_coordinateRangeSeparated
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hleft).1 with ⟨leftIndex, hleftIndex, rfl⟩
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hright).1 with
    ⟨rightIndex, hrightIndex, rfl⟩
  have hevenLeft : Even (leftIndex.1 + leftIndex.2) :=
    (Finset.mem_filter.mp hleftIndex).2
  have hevenRight : Even (rightIndex.1 + rightIndex.2) :=
    (Finset.mem_filter.mp hrightIndex).2
  have hindexNe : leftIndex ≠ rightIndex := by
    intro heq
    subst rightIndex
    exact hne rfl
  exact L.lattice.coordinateRangeSeparated_squarePartitionAComponent_of_even_distinct
    hblockWidth hrangeBlock hrangeMargin leftIndex rightIndex hevenLeft hevenRight hindexNe

/-- The matching actual-support separation theorem for the finite `B` family. -/
theorem actualProjectorSeparated_squarePartitionBComponents
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (left : Finset L.Site)
    (hleft : left ∈ L.lattice.squarePartitionBComponents blockWidth margin)
    (right : Finset L.Site)
    (hright : right ∈ L.lattice.squarePartitionBComponents blockWidth margin)
    (hne : left ≠ right) :
    M.ActualProjectorSeparated left right := by
  apply M.actualProjectorSeparated_of_coordinateRangeSeparated
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hleft).1 with ⟨leftIndex, hleftIndex, rfl⟩
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hright).1 with
    ⟨rightIndex, hrightIndex, rfl⟩
  have hoddLeft : ¬ Even (leftIndex.1 + leftIndex.2) :=
    (Finset.mem_filter.mp hleftIndex).2
  have hoddRight : ¬ Even (rightIndex.1 + rightIndex.2) :=
    (Finset.mem_filter.mp hrightIndex).2
  have hindexNe : leftIndex ≠ rightIndex := by
    intro heq
    subst rightIndex
    exact hne rfl
  exact L.lattice.coordinateRangeSeparated_squarePartitionBComponent_of_odd_distinct
    hblockWidth hrangeBlock hrangeMargin leftIndex rightIndex hoddLeft hoddRight hindexNe

/--
Every actual external-boundary site of a region contained in one tile lies in
the explicitly enlarged tile.  The proof uses the concrete support-coupling
witness and #378 square-locality, not a graph-neighbourhood surrogate.
-/
theorem externalBoundary_subset_expandedTile_of_subset_tile
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin : Nat}
    (index : Nat × Nat) (block : Finset L.Site)
    (hblock : block ⊆ L.lattice.tile blockWidth index)
    (hrange : M.interactionRange ≤ margin) :
    M.externalBoundary block ⊆ L.lattice.expandedTile blockWidth margin index := by
  intro site hsite
  rcases (M.mem_externalBoundary_iff block site).mp hsite with
    ⟨_, check, hcouples, hsiteSupport⟩
  rcases hcouples.1 with ⟨insideSite, hinsideSite⟩
  rcases Finset.mem_inter.mp hinsideSite with ⟨hinsideSupport, hinsideBlock⟩
  have hinsideTile := hblock hinsideBlock
  have hinsideSupportSquare := (M.projector_support_subset_square check) hinsideSupport
  have hsiteSupportSquare := (M.projector_support_subset_square check) hsiteSupport
  simp only [BPTSquareLattice.tile, BPTSquareLattice.mem_square_iff] at hinsideTile hinsideSupportSquare hsiteSupportSquare
  simp only [BPTSquareLattice.expandedTile, BPTSquareLattice.mem_square_iff]
  constructor
  · have hsiteNearInside : insideSite.1.val < site.1.val + M.interactionRange := by
      omega
    have horiginLe : index.1 * blockWidth ≤ site.1.val + margin := by
      omega
    omega
  constructor
  · have hsiteNearInside : site.1.val < insideSite.1.val + M.interactionRange := by
      omega
    by_cases hmargin : margin ≤ index.1 * blockWidth
    · have hcancel : index.1 * blockWidth - margin + margin = index.1 * blockWidth :=
        Nat.sub_add_cancel hmargin
      omega
    · have horiginLt : index.1 * blockWidth < margin := Nat.lt_of_not_ge hmargin
      omega
  constructor
  · have hsiteNearInside : insideSite.2.val < site.2.val + M.interactionRange := by
      omega
    have horiginLe : index.2 * blockWidth ≤ site.2.val + margin := by
      omega
    omega
  · have hsiteNearInside : site.2.val < insideSite.2.val + M.interactionRange := by
      omega
    by_cases hmargin : margin ≤ index.2 * blockWidth
    · have hcancel : index.2 * blockWidth - margin + margin = index.2 * blockWidth :=
        Nat.sub_add_cancel hmargin
      omega
    · have horiginLt : index.2 * blockWidth < margin := Nat.lt_of_not_ge hmargin
      omega

/--
Every support participating in the actual boundary of a square lies in the
source-thickness frame around that square.  The argument keeps both witnesses
to coupling--one site inside and one outside--and uses their common #378
support square to rule out the deep interior.  Thus it proves the source's
thin-boundary geometry rather than covering the boundary by a whole expanded
square.
-/
theorem boundary_subset_squareBoundaryFrame
    (M : BPTCommutingProjectorModel L kappa) (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width) :
    M.boundary (L.lattice.square origin width) ⊆
      L.lattice.squareBoundaryFrame origin width M.interactionRange := by
  intro site hsite
  rcases (M.mem_boundary_iff (L.lattice.square origin width) site).mp hsite with
    ⟨check, hcouples, hsiteSupport⟩
  rcases hcouples.1 with ⟨insideSite, hinside⟩
  rcases hcouples.2 with ⟨outsideSite, houtside⟩
  rcases Finset.mem_inter.mp hinside with ⟨hinsideSupport, hinsideSquareRegion⟩
  rcases Finset.mem_sdiff.mp houtside with ⟨houtsideSupport, houtsideNotSquare⟩
  have hinsideSupportSquare := (M.projector_support_subset_square check) hinsideSupport
  have houtsideSupportSquare := (M.projector_support_subset_square check) houtsideSupport
  have hsiteSupportSquare := (M.projector_support_subset_square check) hsiteSupport
  simp only [BPTSquareLattice.mem_square_iff] at hinsideSquareRegion hinsideSupportSquare houtsideSupportSquare hsiteSupportSquare
  simp only [BPTSquareLattice.squareBoundaryFrame, Finset.mem_sdiff]
  constructor
  · simp only [BPTSquareLattice.mem_square_iff]
    constructor
    · have hsiteNearInside : insideSite.1.val < site.1.val + M.interactionRange := by
        omega
      omega
    constructor
    · have hsiteNearInside : site.1.val < insideSite.1.val + M.interactionRange := by
        omega
      omega
    constructor
    · have hsiteNearInside : insideSite.2.val < site.2.val + M.interactionRange := by
        omega
      omega
    · have hsiteNearInside : site.2.val < insideSite.2.val + M.interactionRange := by
        omega
      omega
  · intro hcore
    simp only [BPTSquareLattice.squareInnerCore, BPTSquareLattice.mem_square_iff] at hcore
    simp only [BPTSquareLattice.mem_square_iff] at houtsideNotSquare
    by_cases hrowLower : outsideSite.1.val < origin.1
    · omega
    by_cases hrowUpper : origin.1 + width ≤ outsideSite.1.val
    · omega
    by_cases hcolumnLower : outsideSite.2.val < origin.2
    · omega
    by_cases hcolumnUpper : origin.2 + width ≤ outsideSite.2.val
    · omega
    apply houtsideNotSquare
    omega

/--
The actual coupled-projector boundary of a square is covered by the four
finite source-thickness strips.  Unlike a naively translated enlarged square,
the strips do not shift clipped lower-boundary width to the opposite side of
an open lattice.
-/
theorem boundary_subset_squareBoundaryFrameStripCover
    (M : BPTCommutingProjectorModel L kappa) (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width) :
    M.boundary (L.lattice.square origin width) ⊆
      L.lattice.squareBoundaryFrameStripCover origin width M.interactionRange := by
  intro site hsite
  rcases (M.mem_boundary_iff (L.lattice.square origin width) site).mp hsite with
    ⟨check, hcouples, hsiteSupport⟩
  rcases hcouples.1 with ⟨insideSite, hinside⟩
  rcases hcouples.2 with ⟨outsideSite, houtside⟩
  rcases Finset.mem_inter.mp hinside with ⟨hinsideSupport, hinsideSquareRegion⟩
  rcases Finset.mem_sdiff.mp houtside with ⟨houtsideSupport, houtsideNotSquare⟩
  have hinsideSupportSquare := (M.projector_support_subset_square check) hinsideSupport
  have houtsideSupportSquare := (M.projector_support_subset_square check) houtsideSupport
  have hsiteSupportSquare := (M.projector_support_subset_square check) hsiteSupport
  simp only [BPTSquareLattice.mem_square_iff] at hinsideSquareRegion hinsideSupportSquare houtsideSupportSquare hsiteSupportSquare
  have hrowLower : origin.1 - M.interactionRange ≤ site.1.val := by
    have hsiteNearInside : insideSite.1.val < site.1.val + M.interactionRange := by omega
    omega
  have hrowUpper : site.1.val < origin.1 + width + M.interactionRange := by
    have hsiteNearInside : site.1.val < insideSite.1.val + M.interactionRange := by omega
    omega
  have hcolumnLower : origin.2 - M.interactionRange ≤ site.2.val := by
    have hsiteNearInside : insideSite.2.val < site.2.val + M.interactionRange := by omega
    omega
  have hcolumnUpper : site.2.val < origin.2 + width + M.interactionRange := by
    have hsiteNearInside : site.2.val < insideSite.2.val + M.interactionRange := by omega
    omega
  have hnotCore : ¬ (origin.1 + M.interactionRange ≤ site.1.val ∧
      site.1.val < origin.1 + M.interactionRange +
        (width - M.interactionRange - M.interactionRange) ∧
      origin.2 + M.interactionRange ≤ site.2.val ∧
        site.2.val < origin.2 + M.interactionRange +
          (width - M.interactionRange - M.interactionRange)) := by
    intro hcore
    simp only [BPTSquareLattice.mem_square_iff] at houtsideNotSquare
    by_cases hrowBelow : outsideSite.1.val < origin.1
    · omega
    by_cases hrowAbove : origin.1 + width ≤ outsideSite.1.val
    · omega
    by_cases hcolumnBelow : outsideSite.2.val < origin.2
    · omega
    by_cases hcolumnAbove : origin.2 + width ≤ outsideSite.2.val
    · omega
    apply houtsideNotSquare
    omega
  by_cases hrowNearLower : site.1.val < origin.1 + M.interactionRange
  · simp only [BPTSquareLattice.squareBoundaryFrameStripCover, Finset.mem_union,
      BPTSquareLattice.squareBoundaryFrameLowerRow, BPTSquareLattice.mem_rectangle_iff]
    omega
  by_cases hrowNearUpper : origin.1 + width - M.interactionRange ≤ site.1.val
  · have htop : origin.1 + width - M.interactionRange +
        (M.interactionRange + M.interactionRange) =
          origin.1 + width + M.interactionRange := by omega
    simp only [BPTSquareLattice.squareBoundaryFrameStripCover, Finset.mem_union,
      BPTSquareLattice.squareBoundaryFrameLowerRow,
      BPTSquareLattice.squareBoundaryFrameUpperRow, BPTSquareLattice.mem_rectangle_iff]
    omega
  by_cases hcolumnNearLower : site.2.val < origin.2 + M.interactionRange
  · simp only [BPTSquareLattice.squareBoundaryFrameStripCover, Finset.mem_union,
      BPTSquareLattice.squareBoundaryFrameLowerRow,
      BPTSquareLattice.squareBoundaryFrameUpperRow,
      BPTSquareLattice.squareBoundaryFrameLowerColumn, BPTSquareLattice.mem_rectangle_iff]
    omega
  by_cases hcolumnNearUpper : origin.2 + width - M.interactionRange ≤ site.2.val
  · have htop : origin.2 + width - M.interactionRange +
        (M.interactionRange + M.interactionRange) =
          origin.2 + width + M.interactionRange := by omega
    simp only [BPTSquareLattice.squareBoundaryFrameStripCover, Finset.mem_union,
      BPTSquareLattice.squareBoundaryFrameLowerRow,
      BPTSquareLattice.squareBoundaryFrameUpperRow,
      BPTSquareLattice.squareBoundaryFrameLowerColumn,
      BPTSquareLattice.squareBoundaryFrameUpperColumn, BPTSquareLattice.mem_rectangle_iff]
    omega
  exfalso
  apply hnotCore
  omega

/--
The source-thickness coupled-projector boundary has a finite linear bound
`|boundary(M)| <= 16 w R`; the proof composes actual-support coverage with the
open-boundary strip count, not an assumed entropy or recovery estimate.
-/
theorem boundary_card_le_sixteen_mul_interactionRange (M : BPTCommutingProjectorModel L kappa)
    (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width) :
    (M.boundary (L.lattice.square origin width)).card ≤
      16 * M.interactionRange * width := by
  calc
    (M.boundary (L.lattice.square origin width)).card ≤
        (L.lattice.squareBoundaryFrameStripCover origin width M.interactionRange).card :=
      Finset.card_le_card (M.boundary_subset_squareBoundaryFrameStripCover origin width hwidth)
    _ ≤ 16 * M.interactionRange * width :=
      L.lattice.squareBoundaryFrameStripCover_card_le_sixteen_mul origin width
        M.interactionRange hwidth

/--
Any site in the same actual local-projector support as a tile-C corner lies in
the corresponding finite `3w` corner enlargement.  This is a support witness
calculation, not a graph-neighborhood replacement.
-/
theorem site_mem_cornerCutoutTileExpandedCover_of_sameProjectorSupport
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin : Nat}
    (hblockWidth : 0 < blockWidth) (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth) (index : Nat × Nat) (check : kappa)
    (cornerSite site : L.Site)
    (hcorner : cornerSite ∈
      L.lattice.tile blockWidth index ∩ L.lattice.squarePartitionC blockWidth margin)
    (hcornerSupport : cornerSite ∈ M.support check) (hsiteSupport : site ∈ M.support check) :
    site ∈ L.lattice.cornerCutoutTileExpandedCover blockWidth margin index := by
  rcases Finset.mem_inter.mp hcorner with ⟨hcornerTile, hcornerC⟩
  have hindex : L.lattice.tileIndex blockWidth cornerSite = index :=
    L.lattice.tileIndex_eq_of_mem_tile hblockWidth hcornerTile
  have hrowIndex : cornerSite.1.val / blockWidth = index.1 := congrArg Prod.fst hindex
  have hcolumnIndex : cornerSite.2.val / blockWidth = index.2 := congrArg Prod.snd hindex
  have hrowDecomposition : cornerSite.1.val =
      index.1 * blockWidth + cornerSite.1.val % blockWidth := by
    calc
      cornerSite.1.val = blockWidth * (cornerSite.1.val / blockWidth) +
          cornerSite.1.val % blockWidth :=
        (Nat.div_add_mod cornerSite.1.val blockWidth).symm
      _ = index.1 * blockWidth + cornerSite.1.val % blockWidth := by
        rw [hrowIndex, Nat.mul_comm]
  have hcolumnDecomposition : cornerSite.2.val =
      index.2 * blockWidth + cornerSite.2.val % blockWidth := by
    calc
      cornerSite.2.val = blockWidth * (cornerSite.2.val / blockWidth) +
          cornerSite.2.val % blockWidth :=
        (Nat.div_add_mod cornerSite.2.val blockWidth).symm
      _ = index.2 * blockWidth + cornerSite.2.val % blockWidth := by
        rw [hcolumnIndex, Nat.mul_comm]
  have hrowModLt : cornerSite.1.val % blockWidth < blockWidth :=
    Nat.mod_lt _ hblockWidth
  have hcolumnModLt : cornerSite.2.val % blockWidth < blockWidth :=
    Nat.mod_lt _ hblockWidth
  have hcornerSquare := (M.projector_support_subset_square check) hcornerSupport
  have hsiteSquare := (M.projector_support_subset_square check) hsiteSupport
  simp only [BPTSquareLattice.mem_square_iff] at hcornerSquare hsiteSquare
  have hcornerCutout : L.lattice.cornerCutout blockWidth margin cornerSite := by
    simpa [BPTSquareLattice.squarePartitionC] using hcornerC
  rcases hcornerCutout with ⟨hrowCorner, hcolumnCorner⟩
  rcases hrowCorner with hrowLower | hrowUpper <;>
    rcases hcolumnCorner with hcolumnLower | hcolumnUpper
  · simp only [BPTSquareLattice.cornerCutoutTileExpandedCover, Finset.mem_union,
      BPTSquareLattice.mem_rectangle_iff]
    omega
  · simp only [BPTSquareLattice.cornerCutoutTileExpandedCover, Finset.mem_union,
      BPTSquareLattice.mem_rectangle_iff]
    omega
  · simp only [BPTSquareLattice.cornerCutoutTileExpandedCover, Finset.mem_union,
      BPTSquareLattice.mem_rectangle_iff]
    omega
  · simp only [BPTSquareLattice.cornerCutoutTileExpandedCover, Finset.mem_union,
      BPTSquareLattice.mem_rectangle_iff]
    omega

/--
The external boundary of a tile with its C corners removed is covered by the
tile's actual thin boundary plus the four enlarged C corners.  This preserves
the exact support-coupling witnesses needed by #403.
-/
theorem externalBoundary_tile_sdiff_squarePartitionC_subset_boundary_union_cornerCover
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin : Nat}
    (hblockWidth : 0 < blockWidth) (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth) (index : Nat × Nat) :
    M.externalBoundary
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin) ⊆
        M.boundary (L.lattice.tile blockWidth index) ∪
          L.lattice.cornerCutoutTileExpandedCover blockWidth margin index := by
  let block := L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin
  intro site hsite
  rcases (M.mem_externalBoundary_iff block site).mp hsite with
    ⟨_, check, hcouples, hsiteSupport⟩
  rcases hcouples.1 with ⟨insideSite, hinside⟩
  rcases hcouples.2 with ⟨outsideSite, houtside⟩
  rcases Finset.mem_inter.mp hinside with ⟨hinsideSupport, hinsideBlock⟩
  rcases Finset.mem_sdiff.mp houtside with ⟨houtsideSupport, houtsideNotBlock⟩
  have hinsideTile : insideSite ∈ L.lattice.tile blockWidth index :=
    (Finset.mem_sdiff.mp hinsideBlock).1
  simp only [Finset.mem_union]
  by_cases houtsideTile : outsideSite ∈ L.lattice.tile blockWidth index
  · right
    have houtsideC : outsideSite ∈ L.lattice.squarePartitionC blockWidth margin := by
      by_contra houtsideNotC
      apply houtsideNotBlock
      exact Finset.mem_sdiff.mpr ⟨houtsideTile, houtsideNotC⟩
    exact M.site_mem_cornerCutoutTileExpandedCover_of_sameProjectorSupport
      hblockWidth hmargin hwidth index check outsideSite site
      (Finset.mem_inter.mpr ⟨houtsideTile, houtsideC⟩) houtsideSupport hsiteSupport
  · left
    have htileCouples : M.supportCouples check (L.lattice.tile blockWidth index) := by
      constructor
      · exact ⟨insideSite, Finset.mem_inter.mpr ⟨hinsideSupport, hinsideTile⟩⟩
      · exact ⟨outsideSite, Finset.mem_sdiff.mpr ⟨houtsideSupport, houtsideTile⟩⟩
    exact M.support_subset_boundary_of_couples
      (L.lattice.tile blockWidth index) check htileCouples hsiteSupport

/--
The previous support cover has the explicit source-scale finite bound
`34 * w * R`: `16*w*R` for the full-tile boundary and at most
`36*w^2 <= 18*w*R` for the four enlarged corners.
-/
theorem boundary_union_cornerCutoutTileExpandedCover_card_le_thirtyfour_mul
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin : Nat}
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth) (index : Nat × Nat) :
    (M.boundary (L.lattice.tile blockWidth index) ∪
      L.lattice.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
        34 * margin * blockWidth := by
  have hboundary : (M.boundary (L.lattice.tile blockWidth index)).card ≤
      16 * M.interactionRange * blockWidth := by
    simpa only [BPTSquareLattice.tile] using
      M.boundary_card_le_sixteen_mul_interactionRange
        (index.1 * blockWidth, index.2 * blockWidth) blockWidth (by omega)
  have hcorner := L.lattice.cornerCutoutTileExpandedCover_card_le_thirtysix_mul_sq
    blockWidth margin index
  have hcornerLinear : 36 * margin * margin ≤ 18 * margin * blockWidth := by
    calc
      36 * margin * margin = 18 * margin * (margin + margin) := by ring
      _ ≤ 18 * margin * blockWidth := Nat.mul_le_mul_left _ hwidth
  calc
    (M.boundary (L.lattice.tile blockWidth index) ∪
      L.lattice.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
        (M.boundary (L.lattice.tile blockWidth index)).card +
          (L.lattice.cornerCutoutTileExpandedCover blockWidth margin index).card :=
      Finset.card_union_le _ _
    _ ≤ 16 * M.interactionRange * blockWidth + 36 * margin * margin := by gcongr
    _ ≤ 16 * margin * blockWidth + 36 * margin * margin := by
      gcongr
    _ ≤ 16 * margin * blockWidth + 18 * margin * blockWidth := by gcongr
    _ = 34 * margin * blockWidth := by ring

/--
Pairwise source separation extends to a single explicit block and the finite
union of all distinct remaining blocks.  The conclusion still speaks about
the concrete `M.support` predicate required by #403.
-/
theorem actualProjectorSeparated_biUnion_of_pairwise
    (M : BPTCommutingProjectorModel L kappa) (block : Finset L.Site)
    (blocks : Finset (Finset L.Site)) (hblock : block ∉ blocks)
    (hseparated : ∀ other ∈ blocks, block ≠ other →
      M.ActualProjectorSeparated block other) :
    M.ActualProjectorSeparated block (blocks.biUnion id) := by
  intro check hboth
  rcases hboth.2 with ⟨site, hsite⟩
  rcases Finset.mem_inter.mp hsite with ⟨hsupport, hblocks⟩
  rcases Finset.mem_biUnion.mp hblocks with ⟨other, hother, hsiteOther⟩
  apply hseparated other hother
  · intro hsame
    exact hblock (hsame ▸ hother)
  · constructor
    · exact hboth.1
    · exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, hsiteOther⟩⟩

/--
The finite induction that the BPT checkerboard argument needs to recover one
color class.  Every induction step invokes #403 on one concrete square block
and the union already recovered from the remaining blocks.  Consequently this
lemma neither assumes a recovery for the final union nor erases the required
external-boundary recovery premise.
-/
theorem regionErasureRecoverable_biUnion_of_pairwise_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (blocks : Finset (Finset L.Site))
    (hnonempty : blocks.Nonempty)
    (hrecoverable : ∀ block ∈ blocks, M.RegionErasureRecoverable block)
    (hexternal : ∀ block ∈ blocks,
      M.RegionErasureRecoverable (M.externalBoundary block))
    (hseparated : ∀ left ∈ blocks, ∀ right ∈ blocks, left ≠ right →
      M.ActualProjectorSeparated left right) :
    M.RegionErasureRecoverable (blocks.biUnion id) := by
  classical
  have hfinite : ∀ family : Finset (Finset L.Site), family.Nonempty →
      (∀ block ∈ family, M.RegionErasureRecoverable block) →
      (∀ block ∈ family, M.RegionErasureRecoverable (M.externalBoundary block)) →
      (∀ left ∈ family, ∀ right ∈ family, left ≠ right →
        M.ActualProjectorSeparated left right) →
      M.RegionErasureRecoverable (family.biUnion id) := by
    intro family
    induction family using Finset.induction_on with
    | empty =>
        intro hfamily _ _ _
        simp at hfamily
    | @insert block family hblockNotMem ih =>
        intro hfamily hrecoverable hexternal hseparated
        by_cases hfamilyEmpty : family = ∅
        · subst family
          simpa using hrecoverable block (Finset.mem_singleton_self block)
        · have hfamilyNonempty : family.Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr hfamilyEmpty
          have htail : M.RegionErasureRecoverable (family.biUnion id) :=
            ih hfamilyNonempty
              (fun other hother =>
                hrecoverable other (Finset.mem_insert_of_mem hother))
              (fun other hother =>
                hexternal other (Finset.mem_insert_of_mem hother))
              (fun left hleft right hright hne =>
                hseparated left (Finset.mem_insert_of_mem hleft)
                  right (Finset.mem_insert_of_mem hright) hne)
          have hhead : M.RegionErasureRecoverable block :=
            hrecoverable block (Finset.mem_insert_self block family)
          have hheadExternal : M.RegionErasureRecoverable (M.externalBoundary block) :=
            hexternal block (Finset.mem_insert_self block family)
          have hheadSeparated : M.ActualProjectorSeparated block (family.biUnion id) :=
            M.actualProjectorSeparated_biUnion_of_pairwise block family hblockNotMem
              (fun other hother hne =>
                hseparated block (Finset.mem_insert_self block family)
                  other (Finset.mem_insert_of_mem hother) hne)
          rw [Finset.biUnion_insert]
          exact M.regionErasureRecoverable_union_of_actualProjectorSeparated block
            (family.biUnion id) hheadSeparated hhead htail hheadExternal
  exact hfinite blocks hnonempty hrecoverable hexternal hseparated

/--
The explicit finite `A` partition is recoverable once its individually seeded
components have their actual external-boundary recoveries and pairwise
actual-projector separation.  The result is an exact #403 iteration, not a
whole-region recovery hypothesis.
-/
theorem squarePartitionA_regionErasureRecoverable_of_components
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hnonempty : (L.lattice.squarePartitionAComponents blockWidth margin).Nonempty)
    (hrecoverable : ∀ block ∈ L.lattice.squarePartitionAComponents blockWidth margin,
      M.RegionErasureRecoverable block)
    (hexternal : ∀ block ∈ L.lattice.squarePartitionAComponents blockWidth margin,
      M.RegionErasureRecoverable (M.externalBoundary block))
    (hseparated : ∀ left ∈ L.lattice.squarePartitionAComponents blockWidth margin,
      ∀ right ∈ L.lattice.squarePartitionAComponents blockWidth margin, left ≠ right →
        M.ActualProjectorSeparated left right) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin) := by
  rw [← L.lattice.biUnion_squarePartitionAComponents_eq_squarePartitionA hblockWidth margin]
  exact M.regionErasureRecoverable_biUnion_of_pairwise_actualProjectorSeparated
    (L.lattice.squarePartitionAComponents blockWidth margin) hnonempty hrecoverable hexternal hseparated

/-- The matching finite #403 assembly for the explicit `B` component family. -/
theorem squarePartitionB_regionErasureRecoverable_of_components
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hnonempty : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty)
    (hrecoverable : ∀ block ∈ L.lattice.squarePartitionBComponents blockWidth margin,
      M.RegionErasureRecoverable block)
    (hexternal : ∀ block ∈ L.lattice.squarePartitionBComponents blockWidth margin,
      M.RegionErasureRecoverable (M.externalBoundary block))
    (hseparated : ∀ left ∈ L.lattice.squarePartitionBComponents blockWidth margin,
      ∀ right ∈ L.lattice.squarePartitionBComponents blockWidth margin, left ≠ right →
        M.ActualProjectorSeparated left right) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin) := by
  rw [← L.lattice.biUnion_squarePartitionBComponents_eq_squarePartitionB hblockWidth margin]
  exact M.regionErasureRecoverable_biUnion_of_pairwise_actualProjectorSeparated
    (L.lattice.squarePartitionBComponents blockWidth margin) hnonempty hrecoverable hexternal hseparated

/--
The `A` assembly with its actual-projector separation proved from the explicit
source geometry.  Only the genuinely independent component and external
boundary recoveries remain as hypotheses.
-/
theorem squarePartitionA_regionErasureRecoverable_of_components_and_geometry
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (hnonempty : (L.lattice.squarePartitionAComponents blockWidth margin).Nonempty)
    (hrecoverable : ∀ block ∈ L.lattice.squarePartitionAComponents blockWidth margin,
      M.RegionErasureRecoverable block)
    (hexternal : ∀ block ∈ L.lattice.squarePartitionAComponents blockWidth margin,
      M.RegionErasureRecoverable (M.externalBoundary block)) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin) := by
  apply M.squarePartitionA_regionErasureRecoverable_of_components hblockWidth margin
    hnonempty hrecoverable hexternal
  intro left hleft right hright hne
  exact M.actualProjectorSeparated_squarePartitionAComponents hblockWidth margin
    hrangeBlock hrangeMargin left hleft right hright hne

/-- The matching `B` assembly with source-derived actual separation. -/
theorem squarePartitionB_regionErasureRecoverable_of_components_and_geometry
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (hnonempty : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty)
    (hrecoverable : ∀ block ∈ L.lattice.squarePartitionBComponents blockWidth margin,
      M.RegionErasureRecoverable block)
    (hexternal : ∀ block ∈ L.lattice.squarePartitionBComponents blockWidth margin,
      M.RegionErasureRecoverable (M.externalBoundary block)) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin) := by
  apply M.squarePartitionB_regionErasureRecoverable_of_components hblockWidth margin
    hnonempty hrecoverable hexternal
  intro left hleft right hright hne
  exact M.actualProjectorSeparated_squarePartitionBComponents hblockWidth margin
    hrangeBlock hrangeMargin left hleft right hright hne

/--
The #402 BPT measurement-distance convention yields a concrete CPTP erasure
recovery for every finite region strictly below that distance.
-/
theorem regionErasureRecoverable_of_measurementDistance_card_lt
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (region : Finset L.Site) (hcard : region.card < distance) :
    M.RegionErasureRecoverable region := by
  apply ((M.regionSubsystem region).noInformationOn_iff_exists_erasureRecovery
    M.codeSpace L.localDimension_positive).mp
  apply hDistance.noInformationOn_of_card_lt
  change Fintype.card ↥region < distance
  rw [Fintype.card_coe]
  exact hcard

/--
Every source square whose finite area is strictly below the BPT measurement
distance is concretely erasure-recoverable.  This is the distance seed used
by the later square-growth and separated-union arguments.
-/
theorem square_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (origin : Nat × Nat) (width : Nat) (hwidth : width * width < distance) :
    M.RegionErasureRecoverable (L.lattice.square origin width) := by
  apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
  exact (L.lattice.square_card_le_width_sq origin width).trans_lt hwidth

/--
The source thin-boundary estimate gives a concrete #402 CPTP recovery for the
full finite `B union C` strip cover when its explicit `16*w*R` bound is below
the BPT measurement distance.
-/
theorem squareBoundaryFrameStripCover_regionErasureRecoverable_of_sixteen_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance) :
    M.RegionErasureRecoverable
      (L.lattice.squareBoundaryFrameStripCover origin width M.interactionRange) := by
  apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
  exact (L.lattice.squareBoundaryFrameStripCover_card_le_sixteen_mul origin width
    M.interactionRange hwidth).trans_lt hthin

/--
Each C-cut source tile has a concrete external-boundary recovery when the
proved `34*w*R` cover is below the exact #402 distance.  This supplies the
otherwise independent #403 premise without reverting to an `R^2` adapter.
-/
theorem externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hthin : 34 * margin * blockWidth < distance) (index : Nat × Nat) :
    M.RegionErasureRecoverable (M.externalBoundary
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin)) := by
  let cover := M.boundary (L.lattice.tile blockWidth index) ∪
    L.lattice.cornerCutoutTileExpandedCover blockWidth margin index
  have hcover : M.RegionErasureRecoverable cover := by
    apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
    change cover.card < distance
    exact (M.boundary_union_cornerCutoutTileExpandedCover_card_le_thirtyfour_mul
      hmargin hwidth index).trans_lt hthin
  apply (M.regionSubsystem (M.externalBoundary
    (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin))).erasureRecoverableFromRegister_mono
      (M.regionSubsystem cover) ?_ M.codeSpace hcover
  simpa only [M.regionSubsystem_selected] using
    M.externalBoundary_tile_sdiff_squarePartitionC_subset_boundary_union_cornerCover
      hblockWidth hmargin hwidth index

/--
One exact BPT #370 growth step.  Starting from the inner square of a proposed
larger block, the proved thin `B union C` recovery and actual boundary cover
make #370 recover the larger square itself.  No maximality assumption is
smuggled into this local step.
-/
theorem square_regionErasureRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (targetOrigin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance)
    (hinner : M.RegionErasureRecoverable
      (L.lattice.square (targetOrigin.1 + M.interactionRange,
        targetOrigin.2 + M.interactionRange) width)) :
    M.RegionErasureRecoverable
      (L.lattice.square targetOrigin (width + M.interactionRange + M.interactionRange)) := by
  let innerOrigin : Nat × Nat :=
    (targetOrigin.1 + M.interactionRange, targetOrigin.2 + M.interactionRange)
  let region := L.lattice.square innerOrigin width
  let inside := L.lattice.squareGrowthInside innerOrigin width M.interactionRange
  let outside := L.lattice.squareGrowthOutside innerOrigin width M.interactionRange
  have hregion : M.RegionErasureRecoverable region := by
    simpa [region, innerOrigin] using hinner
  have hinside : inside ⊆ region := by
    intro site hsite
    exact (Finset.mem_inter.mp hsite).1
  have houtside : outside ⊆ regionᶜ := by
    intro site hsite
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hsite).2
  have hcover : M.RegionErasureRecoverable (inside ∪ outside) := by
    change M.RegionErasureRecoverable
      (L.lattice.squareGrowthInside innerOrigin width M.interactionRange ∪
        L.lattice.squareGrowthOutside innerOrigin width M.interactionRange)
    rw [L.lattice.squareGrowthInside_union_outside_eq_stripCover]
    exact M.squareBoundaryFrameStripCover_regionErasureRecoverable_of_sixteen_mul_lt_measurementDistance
      distance hDistance innerOrigin width hwidth hthin
  have hboundary : M.boundary region ⊆ inside ∪ outside := by
    intro site hsite
    change site ∈ L.lattice.squareGrowthInside innerOrigin width M.interactionRange ∪
      L.lattice.squareGrowthOutside innerOrigin width M.interactionRange
    rw [L.lattice.squareGrowthInside_union_outside_eq_stripCover]
    change site ∈ M.boundary (L.lattice.square innerOrigin width) at hsite
    exact M.boundary_subset_squareBoundaryFrameStripCover innerOrigin width hwidth hsite
  have hgrowth := M.regionErasureRecoverable_union_of_boundary_cover region inside outside
    hregion hinside houtside hcover hboundary
  have hmarginOrigin : M.interactionRange ≤ innerOrigin.1 ∧
      M.interactionRange ≤ innerOrigin.2 := by
    dsimp [innerOrigin]
    omega
  have hshape : L.lattice.square innerOrigin width ∪
      L.lattice.squareGrowthOutside innerOrigin width M.interactionRange =
        L.lattice.square targetOrigin (width + M.interactionRange + M.interactionRange) := by
    simpa [innerOrigin] using
      (L.lattice.square_union_squareGrowthOutside_eq_grownSquare innerOrigin width
        M.interactionRange hwidth hmarginOrigin)
  change M.RegionErasureRecoverable (region ∪ outside) at hgrowth
  simpa only [region, outside, hshape] using hgrowth

/-- Every fully contained coordinate square of one fixed side length is recoverable. -/
def AllFittingSquaresRecoverable (M : BPTCommutingProjectorModel L kappa)
    (width : Nat) : Prop :=
  ∀ origin, L.lattice.squareFits origin width →
    M.RegionErasureRecoverable (L.lattice.square origin width)

/-- Every open-boundary truncation of a coordinate square at one side length is recoverable. -/
def AllSquareBlocksRecoverable (M : BPTCommutingProjectorModel L kappa)
    (width : Nat) : Prop :=
  ∀ origin, M.RegionErasureRecoverable (L.lattice.square origin width)

/-- The exact local maximality certificate used by the source growth contradiction. -/
def LocallyMaximalCorrectableSquareScale (M : BPTCommutingProjectorModel L kappa)
    (width : Nat) : Prop :=
  M.AllSquareBlocksRecoverable width ∧
    ¬ M.AllSquareBlocksRecoverable
      (width + M.interactionRange + M.interactionRange)

/-- Recovering the entire finite lattice forces the source encoded-qubit parameter to vanish. -/
theorem encodedQubits_eq_zero_of_full_recovery
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (hfull : M.RegionErasureRecoverable Finset.univ) :
    parameter.encodedQubits = 0 := by
  have hempty : M.RegionErasureRecoverable (∅ : Finset L.Site) := by
    apply (M.regionSubsystem (∅ : Finset L.Site)).erasureRecoverableFromRegister_mono
      (M.regionSubsystem Finset.univ) ?_ M.codeSpace hfull
    simpa only [M.regionSubsystem_selected] using
      (Finset.empty_subset (Finset.univ : Finset L.Site))
  rcases hfull with ⟨recoveryFull, hcorrectFull⟩
  rcases hempty with ⟨recoveryEmpty, hcorrectEmpty⟩
  let U := _root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
    (M.regionSubsystem (Finset.univ : Finset L.Site))
    (M.regionSubsystem (∅ : Finset L.Site))
  letI : IsEmpty U.ComplementCoordinates := ⟨fun site => by
    have hsite : site.1 ∉ U.selected := site.2
    change site.1 ∉ (Finset.univ ∪ ∅) at hsite
    simp at hsite⟩
  have hentropy := BPTEntropy.bpt_encodedQubits_le_complement_log_dimensions M parameter
    (Finset.univ : Finset L.Site) (∅ : Finset L.Site) (by simp)
      recoveryFull hcorrectFull recoveryEmpty hcorrectEmpty
  have hk : (parameter.encodedQubits : Real) ≤ 0 := by
    simpa [U] using hentropy
  have hkNat : parameter.encodedQubits ≤ 0 := by
    exact_mod_cast hk
  omega

/--
For a nonzero encoded-qubit parameter, a finite first failure along the exact
`2w` source growth progression yields the required locally maximal square
scale.  The terminal failure is concrete: an origin-zero square wider than
both finite lattice dimensions is the full lattice, whose recovery would
force `k = 0` by the #389 entropy theorem.
-/
theorem exists_locallyMaximalCorrectableSquareScale
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (hseed : M.AllSquareBlocksRecoverable (4 * M.interactionRange))
    (hpositive : 0 < parameter.encodedQubits) :
    ∃ width, 4 * M.interactionRange ≤ width ∧
      M.LocallyMaximalCorrectableSquareScale width := by
  let base := 4 * M.interactionRange
  let step := M.interactionRange + M.interactionRange
  let cap := max L.lattice.rows L.lattice.columns
  have hfailure : ∃ t, ¬ M.AllSquareBlocksRecoverable (base + step * t) := by
    refine ⟨cap, ?_⟩
    intro hall
    have hrows : L.lattice.rows ≤ base + step * cap := by
      calc
        L.lattice.rows ≤ cap := le_max_left _ _
        _ ≤ base + step * cap := by
          have hstep : 1 ≤ step := by
            dsimp [step]
            have hrange := M.interactionRange_positive
            omega
          calc
            cap = 1 * cap := by simp
            _ ≤ step * cap := Nat.mul_le_mul_right cap hstep
            _ ≤ base + step * cap := Nat.le_add_left _ _
    have hcolumns : L.lattice.columns ≤ base + step * cap := by
      calc
        L.lattice.columns ≤ cap := le_max_right _ _
        _ ≤ base + step * cap := by
          have hstep : 1 ≤ step := by
            dsimp [step]
            have hrange := M.interactionRange_positive
            omega
          calc
            cap = 1 * cap := by simp
            _ ≤ step * cap := Nat.mul_le_mul_right cap hstep
            _ ≤ base + step * cap := Nat.le_add_left _ _
    have hfull : M.RegionErasureRecoverable Finset.univ := by
      rw [← L.lattice.square_zero_eq_univ_of_le (base + step * cap) hrows hcolumns]
      exact hall (0, 0)
    have hzero := M.encodedQubits_eq_zero_of_full_recovery parameter hfull
    omega
  let n := Nat.find hfailure
  have hnFailure : ¬ M.AllSquareBlocksRecoverable (base + step * n) :=
    Nat.find_spec hfailure
  have hnPositive : 0 < n := by
    by_contra hnot
    have hnZero : n = 0 := by omega
    apply hnFailure
    simpa [n, hnZero, base] using hseed
  have hprev : M.AllSquareBlocksRecoverable (base + step * (n - 1)) := by
    by_contra hnot
    have hnle : n ≤ n - 1 := Nat.find_min' hfailure hnot
    omega
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  refine ⟨base + step * (n - 1), ?_, ?_⟩
  · exact Nat.le_add_right _ _
  constructor
  · exact hprev
  · intro hnext
    apply hnFailure
    have hstepMul : step * n = step * (n - 1) + step := by
      calc
        step * n = step * (n - 1 + 1) := by rw [hn]
        _ = step * (n - 1) + step := Nat.mul_succ _ _
    change M.AllSquareBlocksRecoverable (base + step * n)
    rw [hstepMul]
    simpa [step, Nat.add_assoc] using hnext

/-- A source square-area seed makes every open-boundary square at that scale recoverable. -/
theorem allSquareBlocksRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance width : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hwidth : width * width < distance) :
    M.AllSquareBlocksRecoverable width := by
  intro origin
  exact M.square_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    distance hDistance origin width hwidth

/--
The exact finite `4w` source seed constructs a locally maximal square scale
whenever the encoded-qubit parameter is nonzero.  This is the finite version
of the source's choice of its largest recoverable square, before any
checkerboard geometry is applied.
-/
theorem exists_locallyMaximalCorrectableSquareScale_of_four_mul_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat) (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hseed : (4 * M.interactionRange) * (4 * M.interactionRange) < distance)
    (hpositive : 0 < parameter.encodedQubits) :
    ∃ width, 4 * M.interactionRange ≤ width ∧
      M.LocallyMaximalCorrectableSquareScale width := by
  apply M.exists_locallyMaximalCorrectableSquareScale parameter ?_ hpositive
  exact M.allSquareBlocksRecoverable_of_width_sq_lt_measurementDistance distance
    (4 * M.interactionRange) hDistance hseed

/-- A C-cut tile inherits recovery from the fully present tile containing it. -/
theorem tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allFitting
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hall : M.AllFittingSquaresRecoverable blockWidth) (index : Nat × Nat)
    (hindex : index ∈ L.lattice.occupiedTileIndices blockWidth) :
    M.RegionErasureRecoverable
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin) := by
  have htile : M.RegionErasureRecoverable (L.lattice.tile blockWidth index) := by
    simpa only [BPTSquareLattice.tile] using
      hall (index.1 * blockWidth, index.2 * blockWidth)
        (L.lattice.tile_fits_of_mem_occupiedTileIndices_grid hblockWidth hrows hcolumns
          index hindex)
  apply (M.regionSubsystem
    (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin)).erasureRecoverableFromRegister_mono
      (M.regionSubsystem (L.lattice.tile blockWidth index)) ?_ M.codeSpace htile
  simpa only [M.regionSubsystem_selected] using Finset.sdiff_subset

/-- An even indexed A component inherits the recoverability of its source tile. -/
theorem squarePartitionAComponent_regionErasureRecoverable_of_allFitting
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hall : M.AllFittingSquaresRecoverable blockWidth) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionAComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have hoccupied : index ∈ L.lattice.occupiedTileIndices blockWidth :=
    (Finset.mem_filter.mp hindex).1
  have heven : Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionAComponent_eq_tile_sdiff_C_of_even
    hblockWidth margin index heven]
  exact M.tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allFitting
    hblockWidth hrows hcolumns hall index hoccupied

/-- An odd indexed B component inherits the recoverability of its source tile. -/
theorem squarePartitionBComponent_regionErasureRecoverable_of_allFitting
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hall : M.AllFittingSquaresRecoverable blockWidth) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have hoccupied : index ∈ L.lattice.occupiedTileIndices blockWidth :=
    (Finset.mem_filter.mp hindex).1
  have hodd : ¬ Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionBComponent_eq_tile_sdiff_C_of_odd
    hblockWidth margin index hodd]
  exact M.tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allFitting
    hblockWidth hrows hcolumns hall index hoccupied

/-- An A component obtains its #403 external-boundary premise from the proved thin cover. -/
theorem squarePartitionAComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hthin : 34 * margin * blockWidth < distance) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionAComponents blockWidth margin) :
    M.RegionErasureRecoverable (M.externalBoundary block) := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have heven : Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionAComponent_eq_tile_sdiff_C_of_even
    hblockWidth margin index heven]
  exact M.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    distance hDistance hblockWidth hmargin hwidth hthin index

/-- A B component obtains its #403 external-boundary premise from the proved thin cover. -/
theorem squarePartitionBComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hthin : 34 * margin * blockWidth < distance) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable (M.externalBoundary block) := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have hodd : ¬ Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionBComponent_eq_tile_sdiff_C_of_odd
    hblockWidth margin index hodd]
  exact M.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    distance hDistance hblockWidth hmargin hwidth hthin index

/--
The full finite A checkerboard region is recoverable from regular-grid tiles,
the source-derived same-color separation, and the proved thin external covers.
-/
theorem squarePartitionA_regionErasureRecoverable_of_regularGrid_thirtyfour_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    {blockWidth margin tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hthin : 34 * margin * blockWidth < distance)
    (hall : M.AllFittingSquaresRecoverable blockWidth)
    (hnonempty : (L.lattice.squarePartitionAComponents blockWidth margin).Nonempty) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin) := by
  apply M.squarePartitionA_regionErasureRecoverable_of_components_and_geometry
    hblockWidth margin (by omega) hmargin hnonempty
  · intro block hblock
    exact M.squarePartitionAComponent_regionErasureRecoverable_of_allFitting
      hblockWidth hrows hcolumns hall block hblock
  · intro block hblock
    exact M.squarePartitionAComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
      distance hDistance hblockWidth hmargin hwidth hthin block hblock

/-- The matching finite B checkerboard recovery assembled through the #403 induction. -/
theorem squarePartitionB_regionErasureRecoverable_of_regularGrid_thirtyfour_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    {blockWidth margin tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hthin : 34 * margin * blockWidth < distance)
    (hall : M.AllFittingSquaresRecoverable blockWidth)
    (hnonempty : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin) := by
  apply M.squarePartitionB_regionErasureRecoverable_of_components_and_geometry
    hblockWidth margin (by omega) hmargin hnonempty
  · intro block hblock
    exact M.squarePartitionBComponent_regionErasureRecoverable_of_allFitting
      hblockWidth hrows hcolumns hall block hblock
  · intro block hblock
    exact M.squarePartitionBComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
      distance hDistance hblockWidth hmargin hwidth hthin block hblock

/--
The BPT thin-boundary recursion lifts correctability from every fitting `R`
square to every fitting `(R + 2w)` square, provided the explicit finite
boundary bound remains below the exact #402 distance.
-/
theorem allFittingSquaresRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (width : Nat) (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance)
    (hall : M.AllFittingSquaresRecoverable width) :
    M.AllFittingSquaresRecoverable
      (width + M.interactionRange + M.interactionRange) := by
  intro targetOrigin htargetFits
  apply M.square_regionErasureRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    distance hDistance targetOrigin width hwidth hthin
  apply hall (targetOrigin.1 + M.interactionRange,
    targetOrigin.2 + M.interactionRange)
  simp only [BPTSquareLattice.squareFits] at htargetFits ⊢
  omega

/-- The same #370 step lifts every open-boundary square block, without a fit side condition. -/
theorem allSquareBlocksRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (width : Nat) (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance)
    (hall : M.AllSquareBlocksRecoverable width) :
    M.AllSquareBlocksRecoverable
      (width + M.interactionRange + M.interactionRange) := by
  intro targetOrigin
  exact M.square_regionErasureRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    distance hDistance targetOrigin width hwidth hthin
    (hall (targetOrigin.1 + M.interactionRange,
      targetOrigin.2 + M.interactionRange))

/--
At a locally maximal source square scale, the exact finite BPT distance is at
most the proved thin-boundary size `16*w*R`.  This is the source's maximality
contradiction in contrapositive form, with no asymptotic replacement.
-/
theorem measurementDistance_le_sixteen_mul_of_locallyMaximalCorrectableSquareScale
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (width : Nat) (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hmax : M.LocallyMaximalCorrectableSquareScale width) :
    distance ≤ 16 * M.interactionRange * width := by
  by_contra hnot
  have hthin : 16 * M.interactionRange * width < distance := Nat.lt_of_not_ge hnot
  apply hmax.2
  exact M.allSquareBlocksRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    distance hDistance width hwidth hthin hmax.1

/-- The explicit local expansion of a tile is recoverable below the #402 distance. -/
theorem expandedTile_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance blockWidth margin : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (index : Nat × Nat)
    (hwidth : (blockWidth + margin + margin) * (blockWidth + margin + margin) < distance) :
    M.RegionErasureRecoverable (L.lattice.expandedTile blockWidth margin index) := by
  simpa only [BPTSquareLattice.expandedTile] using
    M.square_regionErasureRecoverable_of_width_sq_lt_measurementDistance distance hDistance
      (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
      (blockWidth + margin + margin) hwidth

/--
An external boundary has a typed recovery when its proved local expanded-tile
cover is below the #402 distance.  The explicit expanded-square condition is
kept in the statement; this is not the later thin-boundary source estimate.
-/
theorem externalBoundary_regionErasureRecoverable_of_expandedTile_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance blockWidth margin : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (index : Nat × Nat) (block : Finset L.Site)
    (hblock : block ⊆ L.lattice.tile blockWidth index)
    (hrange : M.interactionRange ≤ margin)
    (hwidth : (blockWidth + margin + margin) * (blockWidth + margin + margin) < distance) :
    M.RegionErasureRecoverable (M.externalBoundary block) := by
  have hcover : M.RegionErasureRecoverable (L.lattice.expandedTile blockWidth margin index) :=
    M.expandedTile_regionErasureRecoverable_of_width_sq_lt_measurementDistance distance
      blockWidth margin hDistance index hwidth
  apply (M.regionSubsystem (M.externalBoundary block)).erasureRecoverableFromRegister_mono
    (M.regionSubsystem (L.lattice.expandedTile blockWidth margin index)) ?_ M.codeSpace hcover
  simpa only [M.regionSubsystem_selected] using
    M.externalBoundary_subset_expandedTile_of_subset_tile index block hblock hrange

/--
Every concrete `A` component is correctable when its source square area is
strictly below the #402 BPT measurement distance.  This proves the component
seed directly from its finite cardinality, without changing the distance
convention.
-/
theorem squarePartitionAComponent_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance blockWidth margin : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hwidth : blockWidth * blockWidth < distance) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionAComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by
  apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
  exact (L.lattice.squarePartitionAComponent_card_le_width_sq blockWidth margin block hblock).trans_lt hwidth

/-- The matching below-distance recovery seed for every concrete `B` component. -/
theorem squarePartitionBComponent_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance blockWidth margin : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hwidth : blockWidth * blockWidth < distance) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by
  apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
  exact (L.lattice.squarePartitionBComponent_card_le_width_sq blockWidth margin block hblock).trans_lt hwidth

/--
The #389 entropy theorem specialized to the source-constructed square
partition.  The hypotheses are typed erasure-recovery facts for the actual
`A` and `B` sets; later partition lemmas must construct them through #370 and
#403 rather than replace them by an entropy assumption.
-/
theorem encodedQubits_le_squarePartition_complement_log_dimensions
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (blockWidth margin : Nat)
    (hA : M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin))
    (hB : M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin)) :
    (parameter.encodedQubits : Real) <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
        (M.regionSubsystem (L.lattice.squarePartitionA blockWidth margin))
        (M.regionSubsystem (L.lattice.squarePartitionB blockWidth margin))).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by
  rcases hA with ⟨recoveryA, hcorrectA⟩
  rcases hB with ⟨recoveryB, hcorrectB⟩
  exact BPTEntropy.bpt_encodedQubits_le_complement_log_dimensions M parameter
    (L.lattice.squarePartitionA blockWidth margin)
    (L.lattice.squarePartitionB blockWidth margin)
    (L.lattice.squarePartition_pairwise_disjoint blockWidth margin).1
    recoveryA hcorrectA recoveryB hcorrectB

/--
The #389 entropy complement is exactly the finite C corner region, so the
uniform local-dimension bound gives the source inequality `k <= |C| log_2 D`.
-/
theorem encodedQubits_le_squarePartitionC_card_mul_log_uniformDimension
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (blockWidth margin : Nat)
    (hA : M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin))
    (hB : M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin)) :
    (parameter.encodedQubits : Real) ≤
      ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
        Real.logb 2 (L.uniformDimensionBound : Real) := by
  let A := L.lattice.squarePartitionA blockWidth margin
  let B := L.lattice.squarePartitionB blockWidth margin
  let C := L.lattice.squarePartitionC blockWidth margin
  let U := _root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
    (M.regionSubsystem A) (M.regionSubsystem B)
  let e : {site : L.Site // site ∈ C} ≃ U.ComplementCoordinates :=
    Equiv.subtypeEquivRight fun site => by
      change site ∈ C ↔ site ∉ A ∪ B
      rw [L.lattice.squarePartitionAB_eq_compl_C]
      simp [C]
  have hentropy := M.encodedQubits_le_squarePartition_complement_log_dimensions
    parameter blockWidth margin hA hB
  have hsumSubtype : (∑ site : U.ComplementCoordinates,
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site : {site : L.Site // site ∈ C},
        Real.logb 2 (L.localDimension site : Real) := by
    symm
    exact Equiv.sum_comp e (fun site => Real.logb 2 (L.localDimension site : Real))
  have hsubtypeSum : (∑ site : {site : L.Site // site ∈ C},
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site ∈ C, Real.logb 2 (L.localDimension site : Real) := by
    exact (Finset.sum_subtype C (fun _ => Iff.rfl)
      (fun site => Real.logb 2 (L.localDimension site : Real))).symm
  have hsum : (∑ site : U.ComplementCoordinates,
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site ∈ C, Real.logb 2 (L.localDimension site : Real) :=
    hsumSubtype.trans hsubtypeSum
  have huniform : (∑ site ∈ C, Real.logb 2 (L.localDimension site : Real)) ≤
      (C.card : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := by
    have hselected := (M.regionSubsystem C).sum_log_selectedDimensions_le_card_mul_log_uniformDimension
      L.localDimension_positive L.uniformDimensionBound
        (fun site _ => L.localDimension_le_uniform site)
    simpa only [M.regionSubsystem_selected] using hselected
  change (parameter.encodedQubits : Real) ≤
    ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
      Real.logb 2 (L.uniformDimensionBound : Real)
  calc
    (parameter.encodedQubits : Real) ≤ ∑ site : U.ComplementCoordinates,
        Real.logb 2 (L.localDimension site : Real) := by
      simpa [A, B, U] using hentropy
    _ = ∑ site ∈ C, Real.logb 2 (L.localDimension site : Real) := hsum
    _ ≤ (C.card : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := huniform
    _ = ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
        Real.logb 2 (L.uniformDimensionBound : Real) := by rfl

/-- The empty erased region is recoverable directly from a positive exact BPT distance. -/
theorem empty_regionErasureRecoverable_of_positive_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hpositive : 0 < distance) :
    M.RegionErasureRecoverable (∅ : Finset L.Site) := by
  apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
  simpa using hpositive

/--
The finite global entropy/dimension estimate used only in the small-distance
branch.  It is derived from the exact BPT entropy theorem with two genuinely
empty recoverable regions, never from the desired tradeoff conclusion.
-/
theorem encodedQubits_le_siteCount_mul_log_uniformDimension_of_positive_measurementDistance
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat) (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hpositive : 0 < distance) :
    (parameter.encodedQubits : Real) ≤
      (L.lattice.siteCount : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := by
  let Empty : Finset L.Site := ∅
  let Full : Finset L.Site := Finset.univ
  let U := _root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
    (M.regionSubsystem Empty) (M.regionSubsystem Empty)
  have hempty : M.RegionErasureRecoverable Empty := by
    change M.RegionErasureRecoverable ∅
    exact M.empty_regionErasureRecoverable_of_positive_measurementDistance
      distance hDistance hpositive
  rcases hempty with ⟨recovery, hcorrect⟩
  let e : {site : L.Site // site ∈ Full} ≃ U.ComplementCoordinates :=
    Equiv.subtypeEquivRight fun site => by
      change site ∈ Full ↔ site ∉ Empty ∪ Empty
      simp [Full, Empty]
  have hentropy := BPTEntropy.bpt_encodedQubits_le_complement_log_dimensions M parameter
    Empty Empty (by simpa [Empty]) recovery hcorrect recovery hcorrect
  have hsumSubtype : (∑ site : U.ComplementCoordinates,
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site : {site : L.Site // site ∈ Full},
        Real.logb 2 (L.localDimension site : Real) := by
    symm
    exact Equiv.sum_comp e (fun site => Real.logb 2 (L.localDimension site : Real))
  have hsubtypeSum : (∑ site : {site : L.Site // site ∈ Full},
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site ∈ Full, Real.logb 2 (L.localDimension site : Real) := by
    exact (Finset.sum_subtype Full (fun _ => Iff.rfl)
      (fun site => Real.logb 2 (L.localDimension site : Real))).symm
  have hsum : (∑ site : U.ComplementCoordinates,
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site ∈ Full, Real.logb 2 (L.localDimension site : Real) :=
    hsumSubtype.trans hsubtypeSum
  have huniform : (∑ site ∈ Full, Real.logb 2 (L.localDimension site : Real)) ≤
      (Full.card : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := by
    have hselected := (M.regionSubsystem Full).sum_log_selectedDimensions_le_card_mul_log_uniformDimension
      L.localDimension_positive L.uniformDimensionBound
        (fun site _ => L.localDimension_le_uniform site)
    simpa only [M.regionSubsystem_selected] using hselected
  have hfullCard : Full.card = L.lattice.siteCount := by
    simp [Full, BPTSquareLattice.siteCount]
  calc
    (parameter.encodedQubits : Real) ≤ ∑ site : U.ComplementCoordinates,
        Real.logb 2 (L.localDimension site : Real) := by
      simpa [Empty, U] using hentropy
    _ = ∑ site ∈ Full, Real.logb 2 (L.localDimension site : Real) := hsum
    _ ≤ (Full.card : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := huniform
    _ = (L.lattice.siteCount : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := by
      rw [hfullCard]

/-!
## Envelope-scale checkerboard recovery

The source calls the largest correctable square size `R`. Its checkerboard
pieces must be strictly smaller than that envelope: a core tile of side
`r = R - 2w` and its external boundary are both contained in an open-boundary
square of side `R`. This supplies the external-boundary premise of the
separated-union lemma without imposing the incompatible condition `w * R < d`
at the maximal scale.
-/

/-- A core tile is contained in the square envelope with the same lower-left corner. -/
theorem tile_subset_square_same_origin_of_le (L : BPTSquareLattice)
    {blockWidth envelopeWidth : Nat} (hwidth : blockWidth ≤ envelopeWidth)
    (index : Nat × Nat) :
    L.tile blockWidth index ⊆
      L.square (index.1 * blockWidth, index.2 * blockWidth) envelopeWidth := by
  intro site hsite
  simp only [BPTSquareLattice.tile, BPTSquareLattice.mem_square_iff] at hsite ⊢
  constructor
  · exact hsite.1
  constructor
  · omega
  constructor
  · exact hsite.2.2.1
  · omega

/-- An envelope-recoverable square recovers every smaller core tile it contains. -/
theorem tile_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth envelopeWidth : Nat}
    (hwidth : blockWidth ≤ envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth) (index : Nat × Nat) :
    M.RegionErasureRecoverable (L.lattice.tile blockWidth index) := by
  apply (M.regionSubsystem (L.lattice.tile blockWidth index)).erasureRecoverableFromRegister_mono
    (M.regionSubsystem (L.lattice.square
      (index.1 * blockWidth, index.2 * blockWidth) envelopeWidth)) ?_ M.codeSpace
      (hall (index.1 * blockWidth, index.2 * blockWidth))
  simpa only [M.regionSubsystem_selected] using
    tile_subset_square_same_origin_of_le L.lattice hwidth index

/--
The external boundary of a core C-cut tile is recoverable from its `R` square
envelope. This is the source union-lemma premise at the maximal scale.
-/
theorem externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hrange : M.interactionRange ≤ margin)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth) (index : Nat × Nat) :
    M.RegionErasureRecoverable (M.externalBoundary
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin)) := by
  apply (M.regionSubsystem (M.externalBoundary
    (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin))).erasureRecoverableFromRegister_mono
      (M.regionSubsystem (L.lattice.expandedTile blockWidth margin index)) ?_ M.codeSpace
      (by
        have hport := hall
          (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
        simp only [BPTSquareLattice.expandedTile, henvelope] at hport ⊢
        exact hport)
  simpa only [M.regionSubsystem_selected] using
    M.externalBoundary_subset_expandedTile_of_subset_tile index
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin)
      Finset.sdiff_subset hrange

/-- Every even checkerboard core is recoverable from a same-origin square envelope. -/
theorem squarePartitionAComponent_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hwidth : blockWidth ≤ envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionAComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have heven : Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionAComponent_eq_tile_sdiff_C_of_even hblockWidth margin index heven]
  apply (M.regionSubsystem (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin)).erasureRecoverableFromRegister_mono
    (M.regionSubsystem (L.lattice.tile blockWidth index))
      (by simpa only [M.regionSubsystem_selected] using Finset.sdiff_subset) M.codeSpace
  exact M.tile_regionErasureRecoverable_of_allSquareBlocks hwidth hall index

/-- Every odd checkerboard core is recoverable from a same-origin square envelope. -/
theorem squarePartitionBComponent_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hwidth : blockWidth ≤ envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have hodd : ¬ Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionBComponent_eq_tile_sdiff_C_of_odd hblockWidth margin index hodd]
  apply (M.regionSubsystem (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin)).erasureRecoverableFromRegister_mono
    (M.regionSubsystem (L.lattice.tile blockWidth index))
      (by simpa only [M.regionSubsystem_selected] using Finset.sdiff_subset) M.codeSpace
  exact M.tile_regionErasureRecoverable_of_allSquareBlocks hwidth hall index

/-- The A cores assemble by #403 once their recoverable envelopes are explicit. -/
theorem squarePartitionA_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth)
    (hnonempty : (L.lattice.squarePartitionAComponents blockWidth margin).Nonempty) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin) := by
  apply M.squarePartitionA_regionErasureRecoverable_of_components_and_geometry
    hblockWidth margin hrangeBlock hrangeMargin hnonempty
  · intro block hblock
    exact M.squarePartitionAComponent_regionErasureRecoverable_of_allSquareBlocks hblockWidth
      (by omega) hall block hblock
  · intro block hblock
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
    have heven : Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
    rw [L.lattice.squarePartitionAComponent_eq_tile_sdiff_C_of_even hblockWidth margin index heven]
    exact M.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allSquareBlocks
      hrangeMargin henvelope hall index

/-- The B cores assemble by the same envelope-scale #403 construction. -/
theorem squarePartitionB_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth)
    (hnonempty : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin) := by
  apply M.squarePartitionB_regionErasureRecoverable_of_components_and_geometry
    hblockWidth margin hrangeBlock hrangeMargin hnonempty
  · intro block hblock
    exact M.squarePartitionBComponent_regionErasureRecoverable_of_allSquareBlocks hblockWidth
      (by omega) hall block hblock
  · intro block hblock
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
    have hodd : ¬ Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
    rw [L.lattice.squarePartitionBComponent_eq_tile_sdiff_C_of_odd hblockWidth margin index hodd]
    exact M.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allSquareBlocks
      hrangeMargin henvelope hall index

/--
An empty color class is harmless: otherwise the proved #403 envelope assembly
applies.  This removes the former caller-supplied nonempty-A hypothesis.
-/
theorem squarePartitionA_regionErasureRecoverable_of_allSquareBlocks_or_empty
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth)
    (hempty : M.RegionErasureRecoverable (∅ : Finset L.Site)) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin) := by
  by_cases hnonempty : (L.lattice.squarePartitionAComponents blockWidth margin).Nonempty
  · exact M.squarePartitionA_regionErasureRecoverable_of_allSquareBlocks hblockWidth
      hrangeBlock hrangeMargin henvelope hall hnonempty
  · have hcomponents : L.lattice.squarePartitionAComponents blockWidth margin = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hA : L.lattice.squarePartitionA blockWidth margin = ∅ := by
      rw [← L.lattice.biUnion_squarePartitionAComponents_eq_squarePartitionA hblockWidth]
      simp [hcomponents]
    rw [hA]
    exact hempty

/-- The matching empty-or-assembled construction removes the nonempty-B input. -/
theorem squarePartitionB_regionErasureRecoverable_of_allSquareBlocks_or_empty
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth)
    (hempty : M.RegionErasureRecoverable (∅ : Finset L.Site)) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin) := by
  by_cases hnonempty : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty
  · exact M.squarePartitionB_regionErasureRecoverable_of_allSquareBlocks hblockWidth
      hrangeBlock hrangeMargin henvelope hall hnonempty
  · have hcomponents : L.lattice.squarePartitionBComponents blockWidth margin = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hB : L.lattice.squarePartitionB blockWidth margin = ∅ := by
      rw [← L.lattice.biUnion_squarePartitionBComponents_eq_squarePartitionB hblockWidth]
      simp [hcomponents]
    rw [hB]
    exact hempty

end BPTCommutingProjectorModel

namespace BPTSquareLattice

/-- The finite site count of a rectangular BPT lattice is its row-column product. -/
theorem siteCount_eq_rows_mul_columns (L : BPTSquareLattice) :
    L.siteCount = L.rows * L.columns := by
  simp [BPTSquareLattice.siteCount]

/--
The regular core tiling gives the exact finite C bound after restoring the
envelope scale: `|C| * R^2 <= 16 w^2 n`. No boundary remainder is hidden.
-/
theorem squarePartitionC_card_mul_envelope_sq_le
    (L : BPTSquareLattice) {blockWidth margin envelopeWidth tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth) (hseparationWidth : margin + margin ≤ blockWidth)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth) :
    (L.squarePartitionC blockWidth margin).card * (envelopeWidth * envelopeWidth) ≤
      16 * margin * margin * L.siteCount := by
  have hcount := L.squarePartitionC_card_le_grid_four_mul_sq (margin := margin) hblockWidth
    (by omega) hrows hcolumns
  have henvelopeLe : envelopeWidth ≤ 2 * blockWidth := by omega
  have henvelopeSq : envelopeWidth * envelopeWidth ≤
      (2 * blockWidth) * (2 * blockWidth) :=
    Nat.mul_le_mul henvelopeLe henvelopeLe
  have hsites : L.siteCount = tileRows * tileColumns * blockWidth * blockWidth := by
    rw [siteCount_eq_rows_mul_columns L, hrows, hcolumns]
    ring
  calc
    (L.squarePartitionC blockWidth margin).card * (envelopeWidth * envelopeWidth) ≤
        (tileRows * tileColumns * (4 * margin * margin)) *
          (envelopeWidth * envelopeWidth) :=
      Nat.mul_le_mul_right _ hcount
    _ ≤ (tileRows * tileColumns * (4 * margin * margin)) *
          ((2 * blockWidth) * (2 * blockWidth)) :=
      Nat.mul_le_mul_left _ henvelopeSq
    _ = 16 * margin * margin * (tileRows * tileColumns * blockWidth * blockWidth) := by
      ring
    _ = 16 * margin * margin * L.siteCount := by rw [hsites]

/--
For the source's regular open square lattice, clipped final tiles preserve the
finite BPT corner estimate.  No block-width divisibility is required: the
last tile in each direction is included in the proved quotient count.
-/
theorem squarePartitionC_card_mul_envelope_sq_le_of_regularSquare
    (L : BPTSquareLattice) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hmargin : margin + margin ≤ blockWidth)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hregular : L.rows = L.columns) (hblockLeSide : blockWidth ≤ L.rows) :
    (L.squarePartitionC blockWidth margin).card * (envelopeWidth * envelopeWidth) ≤
      64 * margin * margin * L.siteCount := by
  let side := L.rows
  let tileCount := (side - 1) / blockWidth + 1
  have hcount := L.squarePartitionC_card_le_openGrid_four_mul_sq (margin := margin)
    hblockWidth (by omega)
  have hcountSquare : (L.squarePartitionC blockWidth margin).card ≤
      (tileCount * tileCount) * (4 * margin * margin) := by
    simpa [side, tileCount, hregular] using hcount
  have htileCountWidth : tileCount * blockWidth ≤ 2 * side := by
    have hdiv : ((side - 1) / blockWidth) * blockWidth ≤ side - 1 :=
      Nat.div_mul_le_self _ _
    have hsidePositive : 0 < side := L.rows_positive
    calc
      tileCount * blockWidth = ((side - 1) / blockWidth) * blockWidth + blockWidth := by
        dsimp [tileCount]
        ring
      _ ≤ (side - 1) + blockWidth := Nat.add_le_add_right hdiv _
      _ ≤ 2 * side := by omega
  have htileCountWidthSq :
      (tileCount * tileCount) * (blockWidth * blockWidth) ≤ (2 * side) * (2 * side) := by
    calc
      (tileCount * tileCount) * (blockWidth * blockWidth) =
          (tileCount * blockWidth) * (tileCount * blockWidth) := by ring
      _ ≤ (2 * side) * (2 * side) := Nat.mul_le_mul htileCountWidth htileCountWidth
  have henvelopeLe : envelopeWidth ≤ 2 * blockWidth := by omega
  have henvelopeSq : envelopeWidth * envelopeWidth ≤
      (2 * blockWidth) * (2 * blockWidth) :=
    Nat.mul_le_mul henvelopeLe henvelopeLe
  have hsites : L.siteCount = side * side := by
    dsimp [side]
    rw [siteCount_eq_rows_mul_columns, hregular]
  calc
    (L.squarePartitionC blockWidth margin).card * (envelopeWidth * envelopeWidth) ≤
        ((tileCount * tileCount) * (4 * margin * margin)) *
          ((2 * blockWidth) * (2 * blockWidth)) := by
      exact Nat.mul_le_mul hcountSquare henvelopeSq
    _ = 16 * margin * margin *
          ((tileCount * tileCount) * (blockWidth * blockWidth)) := by ring
    _ ≤ 16 * margin * margin * ((2 * side) * (2 * side)) :=
      Nat.mul_le_mul_left _ htileCountWidthSq
    _ = 64 * margin * margin * (side * side) := by ring
    _ = 64 * margin * margin * L.siteCount := by rw [hsites]

end BPTSquareLattice

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
The exact finite BPT synthesis under the source maximal-square certificate.
The checkerboard cores have side `R - 2w`, while their recoverable envelopes
have side `R`; the resulting constant is explicit and depends only on the
local range upper bound and the local dimension upper bound.
-/
theorem encodedQubits_mul_measurementDistance_sq_le_of_locallyMaximalSquareScale
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance blockWidth margin envelopeWidth tileRows tileColumns : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hblockWidth : 0 < blockWidth) (hrange : M.interactionRange ≤ margin)
    (hseparationWidth : margin + margin ≤ blockWidth)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hmax : M.LocallyMaximalCorrectableSquareScale envelopeWidth)
    (hnonemptyA : (L.lattice.squarePartitionAComponents blockWidth margin).Nonempty)
    (hnonemptyB : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty) :
    (parameter.encodedQubits : Real) * (distance : Real) ^ 2 ≤
      (4096 : Real) * (margin : Real) ^ 4 *
        Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by
  have hmarginBlock : margin ≤ blockWidth := by omega
  have hrangeBlock : M.interactionRange ≤ blockWidth := hrange.trans hmarginBlock
  have hA := M.squarePartitionA_regionErasureRecoverable_of_allSquareBlocks
    hblockWidth hrangeBlock hrange henvelope hmax.1 hnonemptyA
  have hB := M.squarePartitionB_regionErasureRecoverable_of_allSquareBlocks
    hblockWidth hrangeBlock hrange henvelope hmax.1 hnonemptyB
  have hentropy := M.encodedQubits_le_squarePartitionC_card_mul_log_uniformDimension
    parameter blockWidth margin hA hB
  have hlocalWidth : M.interactionRange + M.interactionRange ≤ envelopeWidth := by omega
  have hdistanceBase :=
    M.measurementDistance_le_sixteen_mul_of_locallyMaximalCorrectableSquareScale
      distance hDistance envelopeWidth hlocalWidth hmax
  have hdistanceNat : distance ≤ 16 * margin * envelopeWidth :=
    hdistanceBase.trans (by
      calc
        16 * M.interactionRange * envelopeWidth =
            (16 * M.interactionRange) * envelopeWidth := by ring
        _ ≤ (16 * margin) * envelopeWidth :=
          Nat.mul_le_mul_right envelopeWidth (Nat.mul_le_mul_left 16 hrange)
        _ = 16 * margin * envelopeWidth := by ring)
  have hCnat := L.lattice.squarePartitionC_card_mul_envelope_sq_le hblockWidth
    hseparationWidth henvelope hrows hcolumns
  have hCReal : ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
      (envelopeWidth : Real) ^ 2 ≤
      (16 : Real) * (margin : Real) ^ 2 * (L.lattice.siteCount : Real) := by
    have hCReal' :
        ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
          ((envelopeWidth : Real) * (envelopeWidth : Real)) ≤
        (16 : Real) * (margin : Real) * (margin : Real) * (L.lattice.siteCount : Real) := by
      exact_mod_cast hCnat
    convert hCReal' using 1 <;> ring
  have hdistanceReal : (distance : Real) ≤
      (16 : Real) * (margin : Real) * (envelopeWidth : Real) := by
    exact_mod_cast hdistanceNat
  have hdistanceSq : (distance : Real) ^ 2 ≤
      ((16 : Real) * (margin : Real) * (envelopeWidth : Real)) ^ 2 := by
    have hdistanceNonneg : 0 ≤ (distance : Real) := by positivity
    have hupperNonneg : 0 ≤ (16 : Real) * (margin : Real) * (envelopeWidth : Real) := by
      positivity
    nlinarith [sq_nonneg ((distance : Real) -
      ((16 : Real) * (margin : Real) * (envelopeWidth : Real)))]
  have huniformOneNat : 1 ≤ L.uniformDimensionBound := L.uniformDimensionBound_positive
  have huniformOne : (1 : Real) ≤ (L.uniformDimensionBound : Real) := by
    exact_mod_cast huniformOneNat
  have hlog : 0 ≤ Real.logb 2 (L.uniformDimensionBound : Real) :=
    Real.logb_nonneg (by norm_num) huniformOne
  have hCLogNonneg : 0 ≤
      ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
        Real.logb 2 (L.uniformDimensionBound : Real) :=
    mul_nonneg (by positivity) hlog
  have hscaleNonneg : 0 ≤ (256 : Real) * (margin : Real) ^ 2 *
      Real.logb 2 (L.uniformDimensionBound : Real) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hlog
  calc
    (parameter.encodedQubits : Real) * (distance : Real) ^ 2 ≤
        (((L.lattice.squarePartitionC blockWidth margin).card : Real) *
          Real.logb 2 (L.uniformDimensionBound : Real)) * (distance : Real) ^ 2 :=
      mul_le_mul_of_nonneg_right hentropy (sq_nonneg _)
    _ ≤ (((L.lattice.squarePartitionC blockWidth margin).card : Real) *
          Real.logb 2 (L.uniformDimensionBound : Real)) *
          ((16 : Real) * (margin : Real) * (envelopeWidth : Real)) ^ 2 :=
      mul_le_mul_of_nonneg_left hdistanceSq hCLogNonneg
    _ = ((256 : Real) * (margin : Real) ^ 2 *
          Real.logb 2 (L.uniformDimensionBound : Real)) *
        (((L.lattice.squarePartitionC blockWidth margin).card : Real) *
          (envelopeWidth : Real) ^ 2) := by ring
    _ ≤ ((256 : Real) * (margin : Real) ^ 2 *
          Real.logb 2 (L.uniformDimensionBound : Real)) *
        ((16 : Real) * (margin : Real) ^ 2 * (L.lattice.siteCount : Real)) :=
      mul_le_mul_of_nonneg_left hCReal hscaleNonneg
    _ = (4096 : Real) * (margin : Real) ^ 4 *
        Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by
      ring

/--
The finite BPT square-partition bound for the source's regular open square
lattice.  The visible regularity equality is exactly the source convention;
all scale, color, entropy, and finite-remainder facts are constructed here.
-/
theorem encodedQubits_mul_measurementDistance_sq_le_bpt_squarePartition
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat) (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hregular : L.lattice.rows = L.lattice.columns) :
    (parameter.encodedQubits : Real) * (distance : Real) ^ 2 ≤
      (16384 : Real) * (M.interactionRange : Real) ^ 4 *
        Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by
  have hdimensionOneNat : 1 ≤ L.uniformDimensionBound := L.uniformDimensionBound_positive
  have hdimensionOne : (1 : Real) ≤ (L.uniformDimensionBound : Real) := by
    exact_mod_cast hdimensionOneNat
  have hlog : 0 ≤ Real.logb 2 (L.uniformDimensionBound : Real) :=
    Real.logb_nonneg (by norm_num) hdimensionOne
  have hsiteLogNonneg : 0 ≤
      (L.lattice.siteCount : Real) * Real.logb 2 (L.uniformDimensionBound : Real) :=
    mul_nonneg (by positivity) hlog
  have htargetNonneg : 0 ≤ (16384 : Real) * (M.interactionRange : Real) ^ 4 *
      Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by
    positivity
  by_cases hdistanceZero : distance = 0
  · simpa [hdistanceZero] using htargetNonneg
  have hdistancePositive : 0 < distance := Nat.pos_of_ne_zero hdistanceZero
  by_cases hseed : (4 * M.interactionRange) * (4 * M.interactionRange) < distance
  · by_cases hparameterZero : parameter.encodedQubits = 0
    · simpa [hparameterZero] using htargetNonneg
    have hparameterPositive : 0 < parameter.encodedQubits :=
      Nat.pos_of_ne_zero hparameterZero
    rcases M.exists_locallyMaximalCorrectableSquareScale_of_four_mul_width_sq_lt_measurementDistance
      parameter distance hDistance hseed hparameterPositive with
      ⟨envelopeWidth, henvelopeBase, hmax⟩
    let blockWidth := envelopeWidth - M.interactionRange - M.interactionRange
    have henvelope : blockWidth + M.interactionRange + M.interactionRange = envelopeWidth := by
      dsimp [blockWidth]
      omega
    have hblockWidth : 0 < blockWidth := by
      dsimp [blockWidth]
      have hrangePositive := M.interactionRange_positive
      omega
    have hseparationWidth : M.interactionRange + M.interactionRange ≤ blockWidth := by
      dsimp [blockWidth]
      omega
    have hblockLeSide : blockWidth ≤ L.lattice.rows := by
      by_contra hnot
      have hsideLt : L.lattice.rows < envelopeWidth := by
        have hblockLt : L.lattice.rows < blockWidth := Nat.lt_of_not_ge hnot
        omega
      have hfull : M.RegionErasureRecoverable Finset.univ := by
        rw [← L.lattice.square_zero_eq_univ_of_le envelopeWidth (by omega) (by omega)]
        exact hmax.1 (0, 0)
      have hzero := M.encodedQubits_eq_zero_of_full_recovery parameter hfull
      omega
    have hempty := M.empty_regionErasureRecoverable_of_positive_measurementDistance
      distance hDistance hdistancePositive
    have hA := M.squarePartitionA_regionErasureRecoverable_of_allSquareBlocks_or_empty
      hblockWidth (by omega) (by rfl) henvelope hmax.1 hempty
    have hB := M.squarePartitionB_regionErasureRecoverable_of_allSquareBlocks_or_empty
      hblockWidth (by omega) (by rfl) henvelope hmax.1 hempty
    have hentropy := M.encodedQubits_le_squarePartitionC_card_mul_log_uniformDimension
      parameter blockWidth M.interactionRange hA hB
    have hdistanceNat :=
      M.measurementDistance_le_sixteen_mul_of_locallyMaximalCorrectableSquareScale
        distance hDistance envelopeWidth (by omega) hmax
    have hCnat := L.lattice.squarePartitionC_card_mul_envelope_sq_le_of_regularSquare
      hblockWidth hseparationWidth henvelope hregular hblockLeSide
    have hCReal : ((L.lattice.squarePartitionC blockWidth M.interactionRange).card : Real) *
        (envelopeWidth : Real) ^ 2 ≤
        (64 : Real) * (M.interactionRange : Real) ^ 2 * (L.lattice.siteCount : Real) := by
      have hCReal' :
          ((L.lattice.squarePartitionC blockWidth M.interactionRange).card : Real) *
            ((envelopeWidth : Real) * (envelopeWidth : Real)) ≤
          (64 : Real) * (M.interactionRange : Real) * (M.interactionRange : Real) *
            (L.lattice.siteCount : Real) := by
        exact_mod_cast hCnat
      convert hCReal' using 1 <;> ring
    have hdistanceReal : (distance : Real) ≤
        (16 : Real) * (M.interactionRange : Real) * (envelopeWidth : Real) := by
      exact_mod_cast hdistanceNat
    have hdistanceSq : (distance : Real) ^ 2 ≤
        ((16 : Real) * (M.interactionRange : Real) * (envelopeWidth : Real)) ^ 2 := by
      have hdistanceNonneg : 0 ≤ (distance : Real) := by positivity
      have hupperNonneg : 0 ≤ (16 : Real) * (M.interactionRange : Real) *
          (envelopeWidth : Real) := by positivity
      nlinarith [sq_nonneg ((distance : Real) -
        ((16 : Real) * (M.interactionRange : Real) * (envelopeWidth : Real)))]
    have hCLogNonneg : 0 ≤
        ((L.lattice.squarePartitionC blockWidth M.interactionRange).card : Real) *
          Real.logb 2 (L.uniformDimensionBound : Real) :=
      mul_nonneg (by positivity) hlog
    have hscaleNonneg : 0 ≤ (256 : Real) * (M.interactionRange : Real) ^ 2 *
        Real.logb 2 (L.uniformDimensionBound : Real) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hlog
    calc
      (parameter.encodedQubits : Real) * (distance : Real) ^ 2 ≤
          (((L.lattice.squarePartitionC blockWidth M.interactionRange).card : Real) *
            Real.logb 2 (L.uniformDimensionBound : Real)) * (distance : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hentropy (sq_nonneg _)
      _ ≤ (((L.lattice.squarePartitionC blockWidth M.interactionRange).card : Real) *
            Real.logb 2 (L.uniformDimensionBound : Real)) *
            ((16 : Real) * (M.interactionRange : Real) * (envelopeWidth : Real)) ^ 2 :=
        mul_le_mul_of_nonneg_left hdistanceSq hCLogNonneg
      _ = ((256 : Real) * (M.interactionRange : Real) ^ 2 *
            Real.logb 2 (L.uniformDimensionBound : Real)) *
          (((L.lattice.squarePartitionC blockWidth M.interactionRange).card : Real) *
            (envelopeWidth : Real) ^ 2) := by ring
      _ ≤ ((256 : Real) * (M.interactionRange : Real) ^ 2 *
            Real.logb 2 (L.uniformDimensionBound : Real)) *
          ((64 : Real) * (M.interactionRange : Real) ^ 2 * (L.lattice.siteCount : Real)) :=
        mul_le_mul_of_nonneg_left hCReal hscaleNonneg
      _ = (16384 : Real) * (M.interactionRange : Real) ^ 4 *
          Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by
        ring
  · have hsmallNat : distance ≤ 16 * M.interactionRange * M.interactionRange := by
      have hnotSeed : distance ≤ (4 * M.interactionRange) * (4 * M.interactionRange) :=
        Nat.le_of_not_gt hseed
      calc
        distance ≤ (4 * M.interactionRange) * (4 * M.interactionRange) := hnotSeed
        _ = 16 * M.interactionRange * M.interactionRange := by ring
    have hsmallSqNat : distance * distance ≤
        256 * M.interactionRange * M.interactionRange * M.interactionRange * M.interactionRange := by
      calc
        distance * distance ≤ (16 * M.interactionRange * M.interactionRange) *
            (16 * M.interactionRange * M.interactionRange) :=
          Nat.mul_le_mul hsmallNat hsmallNat
        _ = 256 * M.interactionRange * M.interactionRange * M.interactionRange *
            M.interactionRange := by ring
    have hsmallSqNat' : distance ^ 2 ≤ 256 * M.interactionRange ^ 4 := by
      calc
        distance ^ 2 = distance * distance := by ring
        _ ≤ 256 * M.interactionRange * M.interactionRange * M.interactionRange *
            M.interactionRange := hsmallSqNat
        _ = 256 * M.interactionRange ^ 4 := by ring
    have hsmallSq : (distance : Real) ^ 2 ≤
        (256 : Real) * (M.interactionRange : Real) ^ 4 := by
      exact_mod_cast hsmallSqNat'
    have hglobal :=
      M.encodedQubits_le_siteCount_mul_log_uniformDimension_of_positive_measurementDistance
        parameter distance hDistance hdistancePositive
    calc
      (parameter.encodedQubits : Real) * (distance : Real) ^ 2 ≤
          ((L.lattice.siteCount : Real) * Real.logb 2 (L.uniformDimensionBound : Real)) *
            (distance : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hglobal (sq_nonneg _)
      _ ≤ ((L.lattice.siteCount : Real) * Real.logb 2 (L.uniformDimensionBound : Real)) *
            ((256 : Real) * (M.interactionRange : Real) ^ 4) :=
        mul_le_mul_of_nonneg_left hsmallSq hsiteLogNonneg
      _ ≤ ((L.lattice.siteCount : Real) * Real.logb 2 (L.uniformDimensionBound : Real)) *
            ((16384 : Real) * (M.interactionRange : Real) ^ 4) := by
        have hconstant : (256 : Real) * (M.interactionRange : Real) ^ 4 ≤
            (16384 : Real) * (M.interactionRange : Real) ^ 4 := by
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_left hconstant hsiteLogNonneg
      _ = (16384 : Real) * (M.interactionRange : Real) ^ 4 *
          Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by
        ring

end BPTCommutingProjectorModel

end Bounds
end QEC
