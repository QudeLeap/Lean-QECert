import QEC.Locality.OptimalTradeoff.Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Dai--Li finite planar packing and translated-grid averaging

This module proves the internal geometric lemmas used by the Dai--Li locality
branch.  Rectangle packing is derived from the unit Euclidean separation stored
by `UnitSeparatedEmbedding2D`; its cardinalities remain `Nat` until the final
real inequalities.  Grid translations are modeled by the two-dimensional
torus `AddCircle w × AddCircle w`, so Haar averaging constructs a translation
instead of accepting a good tiling as input.

Near a grid vertex means that both periodic coordinate distances are bounded,
which is exactly the source's `ℓ∞` convention.  Near an axis-parallel grid
edge means that at least one periodic coordinate distance is bounded; that
coordinate is the ordinary Euclidean normal distance to the corresponding
line.  Finite index types model multisets: repeated indices may map to the same
point and are counted with multiplicity.
-/

open MeasureTheory Set Metric

noncomputable section

open scoped ENNReal

namespace QEC.Locality

local instance instClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A translation class for an axis-parallel grid of real side length `w`. -/
abbrev GridTranslation (w : ℝ) := AddCircle w × AddCircle w

/-- The two periodic coordinate phases of a point relative to a width-`w` grid. -/
def phase (w : ℝ) (p : ℝ × ℝ) : AddCircle w × AddCircle w :=
  ((p.1 : AddCircle w), (p.2 : AddCircle w))

/-- A concrete representative for a torus translation.  It is used only to
enumerate the finitely many grid cells occupied by the finite qubit set. -/
noncomputable def gridOrigin (w : ℝ) (t : GridTranslation w) : ℝ × ℝ :=
  (Quotient.out t.1, Quotient.out t.2)

/-- The chosen representative realizes the original periodic translation. -/
theorem phase_gridOrigin (w : ℝ) (t : GridTranslation w) :
    phase w (gridOrigin w t) = t := by
  ext <;> exact Quotient.out_eq _

/-- The quotient-circle metric is no larger than the ordinary coordinate
distance to any chosen representative of a grid line.  This is the bridge
from finite Euclidean strip witnesses back to the translated periodic counts. -/
theorem addCircle_dist_le_abs_sub (w a x : ℝ) (hw : 0 < w) :
    dist (a : AddCircle w) (x : AddCircle w) ≤ |x - a| := by
  rw [dist_comm, dist_eq_norm]
  change ‖((x - a : ℝ) : AddCircle w)‖ ≤ |x - a|
  rw [AddCircle.norm_eq]
  let z : ℝ := w⁻¹ * (x - a)
  have hround : |z - (round z : ℝ)| ≤ |z| := by
    simpa [z] using (round_le (w⁻¹ * (x - a)) (0 : ℤ))
  have hscale : x - a = w * z := by
    dsimp [z]
    field_simp
  have hnorm : |(x - a) - (round (w⁻¹ * (x - a)) : ℝ) * w| =
      w * |z - (round z : ℝ)| := by
    change |(x - a) - (round z : ℝ) * w| = w * |z - (round z : ℝ)|
    rw [hscale]
    have hfactor : w * z - (round z : ℝ) * w = w * (z - (round z : ℝ)) := by ring
    rw [hfactor, abs_mul, abs_of_pos hw]
  rw [hnorm, hscale, abs_mul, abs_of_pos hw]
  exact mul_le_mul_of_nonneg_left hround hw.le

/-- Translating a real representative by an integral number of periods does
not change its point on the quotient circle. -/
theorem addCircle_coe_add_int_mul_period (w x : ℝ) (m : ℤ) :
    ((x + (m : ℝ) * w : ℝ) : AddCircle w) = (x : AddCircle w) := by
  have hperiod : (((m : ℝ) * w : ℝ) : AddCircle w) = 0 := by
    apply (AddCircle.coe_eq_zero_iff w).mpr
    refine ⟨m, ?_⟩
    rw [zsmul_eq_mul]
  rw [AddCircle.coe_add, hperiod, add_zero]

/-- The integer grid cell containing a point for a concrete width and origin. -/
def gridCellIndex (w : ℝ) (origin point : ℝ × ℝ) : ℤ × ℤ :=
  (⌊(point.1 - origin.1) / w⌋, ⌊(point.2 - origin.2) / w⌋)

/-- Lower-left corner of an indexed axis-parallel grid cell. -/
def gridCellLower (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : ℝ × ℝ :=
  (origin.1 + cell.1 * w, origin.2 + cell.2 * w)

/-- Upper-right corner of an indexed axis-parallel grid cell. -/
def gridCellUpper (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : ℝ × ℝ :=
  (origin.1 + (cell.1 + 1) * w, origin.2 + (cell.2 + 1) * w)

/-- Actual qubits assigned to one half-open grid cell. -/
def UnitSeparatedEmbedding2D.gridCellQubits {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : Finset ι :=
  Finset.univ.filter fun q => gridCellIndex w origin (embedding.point q) = cell

/-- The finite set of grid-cell indices occupied by actual qubits. -/
def UnitSeparatedEmbedding2D.gridOccupiedCells {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) : Finset (ℤ × ℤ) :=
  Finset.univ.image fun q => gridCellIndex w origin (embedding.point q)

@[simp]
theorem UnitSeparatedEmbedding2D.mem_gridCellQubits_iff {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) (q : ι) :
    q ∈ embedding.gridCellQubits w origin cell ↔
      gridCellIndex w origin (embedding.point q) = cell := by
  simp [UnitSeparatedEmbedding2D.gridCellQubits]

@[simp]
theorem UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    cell ∈ embedding.gridOccupiedCells w origin ↔
      ∃ q : ι, gridCellIndex w origin (embedding.point q) = cell := by
  simp [UnitSeparatedEmbedding2D.gridOccupiedCells]

/-- Every qubit is assigned to its concrete grid cell. -/
theorem UnitSeparatedEmbedding2D.mem_gridCellQubits_self {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (q : ι) :
    q ∈ embedding.gridCellQubits w origin
      (gridCellIndex w origin (embedding.point q)) := by
  simp

/-- Different occupied cell indices select disjoint finite qubit regions. -/
theorem UnitSeparatedEmbedding2D.gridCellQubits_pairwise_disjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ) :
    (↑(embedding.gridOccupiedCells w origin) : Set (ℤ × ℤ)).PairwiseDisjoint
      (embedding.gridCellQubits w origin) := by
  intro first hfirst second hsecond hne
  apply Finset.disjoint_left.mpr
  intro q hqFirst hqSecond
  have hFirst : gridCellIndex w origin (embedding.point q) = first :=
    (embedding.mem_gridCellQubits_iff w origin first q).1 hqFirst
  have hSecond : gridCellIndex w origin (embedding.point q) = second :=
    (embedding.mem_gridCellQubits_iff w origin second q).1 hqSecond
  exact hne (hFirst.symm.trans hSecond)

/-- The occupied finite cell family covers every qubit exactly once. -/
theorem UnitSeparatedEmbedding2D.gridCellQubits_cover {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) :
    (embedding.gridOccupiedCells w origin).biUnion
      (embedding.gridCellQubits w origin) = Finset.univ := by
  ext q
  constructor
  · intro _
    simp
  · intro _
    refine Finset.mem_biUnion.mpr ⟨gridCellIndex w origin (embedding.point q), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
    · exact embedding.mem_gridCellQubits_self w origin q

/-- Periodic `ℓ∞` distance from a point to the translated grid-vertex lattice. -/
def periodicInfinityDistance (w : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) : ℝ :=
  max (dist t.1 (phase w p).1) (dist t.2 (phase w p).2)

/-- Periodic Euclidean normal distance from a point to the nearest grid edge. -/
def periodicEdgeDistance (w : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) : ℝ :=
  min (dist t.1 (phase w p).1) (dist t.2 (phase w p).2)

/-- The source's vertex neighborhood: periodic `ℓ∞` distance at most `r`. -/
def vertexBad (w r : ℝ) (t : AddCircle w × AddCircle w) (p : ℝ × ℝ) : Prop :=
  dist t.1 (phase w p).1 ≤ r ∧ dist t.2 (phase w p).2 ≤ r

theorem vertexBad_iff_periodicInfinityDistance_le
    (w r : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) :
    vertexBad w r t p ↔ periodicInfinityDistance w t p ≤ r := by
  simp [vertexBad, periodicInfinityDistance]

theorem measurableSet_vertexBad (w r : ℝ) (p : ℝ × ℝ) :
    MeasurableSet {t : AddCircle w × AddCircle w | vertexBad w r t p} := by
  change MeasurableSet (closedBall (phase w p).1 r ×ˢ closedBall (phase w p).2 r)
  exact measurableSet_closedBall.prod measurableSet_closedBall

theorem vertexBad_set (w r : ℝ) (p : ℝ × ℝ) :
    {t : AddCircle w × AddCircle w | vertexBad w r t p} =
      closedBall (phase w p).1 r ×ˢ closedBall (phase w p).2 r := by
  ext t
  simp [vertexBad, phase]

theorem measure_vertexBad (w r : ℝ) [Fact (0 < w)] (p : ℝ × ℝ) :
    volume {t : AddCircle w × AddCircle w | vertexBad w r t p} =
      ENNReal.ofReal (min w (2 * r)) ^ 2 := by
  rw [vertexBad_set, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Measure.prod_prod, AddCircle.volume_closedBall,
    AddCircle.volume_closedBall, pow_two]

/-- The source's edge neighborhood, using ordinary distance normal to either grid line. -/
def edgeBad (w r : ℝ) (t : AddCircle w × AddCircle w) (p : ℝ × ℝ) : Prop :=
  dist t.1 (phase w p).1 ≤ r ∨ dist t.2 (phase w p).2 ≤ r

theorem edgeBad_iff_periodicEdgeDistance_le
    (w r : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) :
    edgeBad w r t p ↔ periodicEdgeDistance w t p ≤ r := by
  simp [edgeBad, periodicEdgeDistance]

theorem edgeBad_set (w r : ℝ) (p : ℝ × ℝ) :
    {t : AddCircle w × AddCircle w | edgeBad w r t p} =
      (closedBall (phase w p).1 r ×ˢ Set.univ) ∪
        (Set.univ ×ˢ closedBall (phase w p).2 r) := by
  ext t
  simp [edgeBad, phase]

theorem measurableSet_edgeBad (w r : ℝ) (p : ℝ × ℝ) :
    MeasurableSet {t : AddCircle w × AddCircle w | edgeBad w r t p} := by
  rw [edgeBad_set]
  exact (measurableSet_closedBall.prod MeasurableSet.univ).union
    (MeasurableSet.univ.prod measurableSet_closedBall)

theorem measure_edgeBad_le (w r : ℝ) [Fact (0 < w)] (p : ℝ × ℝ) :
    volume {t : AddCircle w × AddCircle w | edgeBad w r t p} ≤
      2 * (ENNReal.ofReal (min w (2 * r)) * ENNReal.ofReal w) := by
  rw [edgeBad_set, MeasureTheory.Measure.volume_eq_prod]
  calc
    _ ≤ volume (closedBall (phase w p).1 r ×ˢ (Set.univ : Set (AddCircle w))) +
        volume ((Set.univ : Set (AddCircle w)) ×ˢ closedBall (phase w p).2 r) :=
      measure_union_le _ _
    _ = _ := by
      change (volume.prod volume) (closedBall (phase w p).1 r ×ˢ Set.univ) +
        (volume.prod volume) (Set.univ ×ˢ closedBall (phase w p).2 r) = _
      rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.prod_prod,
        AddCircle.volume_closedBall, AddCircle.volume_closedBall,
        AddCircle.measure_univ]
      ring

theorem average_vertex_indicator (w ell : ℝ) [Fact (0 < w)]
    (hell : 0 ≤ ell) (hscale : 4 * ell ≤ w) (p : ℝ × ℝ) :
    (⨍ t : AddCircle w × AddCircle w,
      (if vertexBad w (2 * ell) t p then (1 : ℝ) else 0) ∂volume) =
      16 * ell ^ 2 / w ^ 2 := by
  classical
  have hmin : min w (2 * (2 * ell)) = 4 * ell := by
    rw [min_eq_right] <;> linarith
  have hind : (fun t : AddCircle w × AddCircle w =>
      if vertexBad w (2 * ell) t p then (1 : ℝ) else 0) =
      {t | vertexBad w (2 * ell) t p}.indicator 1 := by
    funext t
    by_cases h : vertexBad w (2 * ell) t p <;> simp [Set.indicator, h]
  rw [hind, MeasureTheory.average_eq,
    integral_indicator_one (measurableSet_vertexBad w (2 * ell) p)]
  change (ENNReal.toReal (volume (Set.univ : Set (AddCircle w × AddCircle w))))⁻¹ *
    ENNReal.toReal (volume {t | vertexBad w (2 * ell) t p}) = _
  rw [measure_vertexBad, hmin, ← Set.univ_prod_univ,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    AddCircle.measure_univ]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * ell),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (Fact.out : 0 < w))]
  field_simp
  ring

theorem average_edge_indicator_le (w ell : ℝ) [Fact (0 < w)]
    (hell : 0 ≤ ell) (hscale : 4 * ell ≤ w) (p : ℝ × ℝ) :
    (⨍ t : AddCircle w × AddCircle w,
      (if edgeBad w (2 * ell) t p then (1 : ℝ) else 0) ∂volume) ≤
      8 * ell / w := by
  classical
  have hmin : min w (2 * (2 * ell)) = 4 * ell := by
    rw [min_eq_right] <;> linarith
  have hind : (fun t : AddCircle w × AddCircle w =>
      if edgeBad w (2 * ell) t p then (1 : ℝ) else 0) =
      {t | edgeBad w (2 * ell) t p}.indicator 1 := by
    funext t
    by_cases h : edgeBad w (2 * ell) t p <;> simp [Set.indicator, h]
  rw [hind, MeasureTheory.average_eq,
    integral_indicator_one (measurableSet_edgeBad w (2 * ell) p)]
  change (ENNReal.toReal (volume (Set.univ : Set (AddCircle w × AddCircle w))))⁻¹ *
    ENNReal.toReal (volume {t | edgeBad w (2 * ell) t p}) ≤ _
  have huniv : ENNReal.toReal (volume (Set.univ : Set (AddCircle w × AddCircle w))) =
      w * w := by
    rw [← Set.univ_prod_univ, MeasureTheory.Measure.volume_eq_prod,
      MeasureTheory.Measure.prod_prod, AddCircle.measure_univ]
    simp only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (le_of_lt (Fact.out : 0 < w))]
  rw [huniv]
  have hmeasure := measure_edgeBad_le w (2 * ell) p
  rw [hmin] at hmeasure
  have hfinite : 2 * (ENNReal.ofReal (4 * ell) * ENNReal.ofReal w) ≠
      (∞ : ENNReal) := by finiteness
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top volume _) hfinite).2 hmeasure
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * ell),
    ENNReal.toReal_ofReal (le_of_lt (Fact.out : 0 < w))] at hreal
  norm_num at hreal
  rw [show (w * w)⁻¹ *
      ENNReal.toReal (volume {t : AddCircle w × AddCircle w | edgeBad w (2 * ell) t p}) =
      ENNReal.toReal (volume {t : AddCircle w × AddCircle w | edgeBad w (2 * ell) t p}) /
        w ^ 2 by rw [div_eq_mul_inv, pow_two, mul_comm]]
  rw [show 8 * ell / w = (8 * ell * w) / w ^ 2 by field_simp]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos (Fact.out : 0 < w))).2
  calc
    ENNReal.toReal (volume {t : AddCircle w × AddCircle w | edgeBad w (2 * ell) t p})
        ≤ 2 * (4 * ell * w) := hreal
    _ = 8 * ell * w := by ring

def vertexScore {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) : ℝ :=
  ∑ i : a, if vertexBad w r t (points i) then 1 else 0

def edgeScore {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) : ℝ :=
  ∑ i : a, if edgeBad w r t (points i) then 1 else 0

/-- Vertex-neighborhood multiplicity for a finite point family. -/
def vertexBadCount {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) : ℕ :=
  (Finset.univ.filter fun i => vertexBad w r t (points i)).card

/-- Edge-neighborhood multiplicity for a finite point family. -/
def edgeBadCount {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) : ℕ :=
  (Finset.univ.filter fun i => edgeBad w r t (points i)).card

theorem vertexScore_eq_cast_count {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) :
    vertexScore w r points t = (vertexBadCount w r points t : ℝ) := by
  rw [vertexScore, vertexBadCount, Finset.sum_boole]

theorem edgeScore_eq_cast_count {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) :
    edgeScore w r points t = (edgeBadCount w r points t : ℝ) := by
  rw [edgeScore, edgeBadCount, Finset.sum_boole]

theorem integrable_vertexScore {a : Type*} [Fintype a] (w r : ℝ) [Fact (0 < w)]
    (points : a → ℝ × ℝ) : Integrable (vertexScore w r points) volume := by
  classical
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  rw [show (fun t : AddCircle w × AddCircle w =>
      if vertexBad w r t (points i) then (1 : ℝ) else 0) =
      {t | vertexBad w r t (points i)}.indicator 1 by
        funext t
        by_cases h : vertexBad w r t (points i) <;> simp [Set.indicator, h]]
  exact (MeasureTheory.integrable_const (1 : ℝ)).indicator
    (measurableSet_vertexBad w r (points i))

theorem integrable_edgeScore {a : Type*} [Fintype a] (w r : ℝ) [Fact (0 < w)]
    (points : a → ℝ × ℝ) : Integrable (edgeScore w r points) volume := by
  classical
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  rw [show (fun t : AddCircle w × AddCircle w =>
      if edgeBad w r t (points i) then (1 : ℝ) else 0) =
      {t | edgeBad w r t (points i)}.indicator 1 by
        funext t
        by_cases h : edgeBad w r t (points i) <;> simp [Set.indicator, h]]
  exact (MeasureTheory.integrable_const (1 : ℝ)).indicator
    (measurableSet_edgeBad w r (points i))

theorem average_vertexScore {a : Type*} [Fintype a] (w ell : ℝ) [Fact (0 < w)]
    (hell : 0 ≤ ell) (hscale : 4 * ell ≤ w) (points : a → ℝ × ℝ) :
    (⨍ t, vertexScore w (2 * ell) points t ∂volume) =
      Fintype.card a * (16 * ell ^ 2 / w ^ 2) := by
  rw [MeasureTheory.average_eq]
  simp only [vertexScore]
  rw [
    MeasureTheory.integral_finsetSum Finset.univ (fun i _ => by
      rw [show (fun t : AddCircle w × AddCircle w =>
          if vertexBad w (2 * ell) t (points i) then (1 : ℝ) else 0) =
          {t | vertexBad w (2 * ell) t (points i)}.indicator 1 by
            funext t
            by_cases h : vertexBad w (2 * ell) t (points i) <;>
              simp [Set.indicator, h]]
      exact (MeasureTheory.integrable_const (1 : ℝ)).indicator
        (measurableSet_vertexBad w (2 * ell) (points i)))]
  rw [Finset.smul_sum]
  calc
    _ = ∑ _i : a, (16 * ell ^ 2 / w ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← MeasureTheory.average_eq]
      exact average_vertex_indicator w ell hell hscale (points i)
    _ = _ := by simp [nsmul_eq_mul]

theorem average_edgeScore_le {a : Type*} [Fintype a] (w ell : ℝ) [Fact (0 < w)]
    (hell : 0 ≤ ell) (hscale : 4 * ell ≤ w) (points : a → ℝ × ℝ) :
    (⨍ t, edgeScore w (2 * ell) points t ∂volume) ≤
      Fintype.card a * (8 * ell / w) := by
  rw [MeasureTheory.average_eq]
  simp only [edgeScore]
  rw [
    MeasureTheory.integral_finsetSum Finset.univ (fun i _ => by
      rw [show (fun t : AddCircle w × AddCircle w =>
          if edgeBad w (2 * ell) t (points i) then (1 : ℝ) else 0) =
          {t | edgeBad w (2 * ell) t (points i)}.indicator 1 by
            funext t
            by_cases h : edgeBad w (2 * ell) t (points i) <;>
              simp [Set.indicator, h]]
      exact (MeasureTheory.integrable_const (1 : ℝ)).indicator
        (measurableSet_edgeBad w (2 * ell) (points i)))]
  rw [Finset.smul_sum]
  calc
    _ ≤ ∑ _i : a, (8 * ell / w) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← MeasureTheory.average_eq]
      exact average_edge_indicator_le w ell hell hscale (points i)
    _ = _ := by simp [nsmul_eq_mul]

theorem average_const_mul_add {a : Type*} [MeasurableSpace a]
    (mu : Measure a) (f g : a → ℝ) (A B : ℝ)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    (⨍ x, B * f x + A * g x ∂mu) =
      B * (⨍ x, f x ∂mu) + A * (⨍ x, g x ∂mu) := by
  rw [MeasureTheory.average_eq', MeasureTheory.average_eq', MeasureTheory.average_eq',
    MeasureTheory.integral_add (hf.to_average.const_mul B) (hg.to_average.const_mul A),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

theorem volume_gridTranslation_ne_zero (w : ℝ) [Fact (0 < w)] :
    (volume : Measure (AddCircle w × AddCircle w)) ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero, ← Set.univ_prod_univ,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  simp only [AddCircle.measure_univ]
  have hw : 0 < ENNReal.ofReal w := ENNReal.ofReal_pos.2 (Fact.out : 0 < w)
  positivity

theorem exists_good_vertex_translation
    {a : Type*} [Fintype a] (w ell : ℝ) (hell : 0 < ell) (hscale : 4 * ell ≤ w)
    (X : a → ℝ × ℝ) :
    ∃ t : AddCircle w × AddCircle w,
      (vertexBadCount w (2 * ell) X t : ℝ) ≤
        (32 * ell ^ 2 / w ^ 2) * Fintype.card a := by
  have hw : 0 < w := lt_of_lt_of_le (by nlinarith [hell]) hscale
  letI : Fact (0 < w) := ⟨hw⟩
  obtain ⟨t, ht⟩ := MeasureTheory.exists_le_average
    (volume_gridTranslation_ne_zero w) (integrable_vertexScore w (2 * ell) X)
  refine ⟨t, ?_⟩
  rw [← vertexScore_eq_cast_count]
  calc
    _ ≤ (⨍ s, vertexScore w (2 * ell) X s ∂volume) := ht
    _ = Fintype.card a * (16 * ell ^ 2 / w ^ 2) :=
      average_vertexScore w ell hell.le hscale X
    _ = 16 * (ell ^ 2 / w ^ 2) * Fintype.card a := by ring
    _ ≤ 32 * (ell ^ 2 / w ^ 2) * Fintype.card a := by gcongr <;> norm_num
    _ = (32 * ell ^ 2 / w ^ 2) * Fintype.card a := by ring

theorem exists_good_edge_translation
    {b : Type*} [Fintype b] (w ell : ℝ) (hell : 0 < ell) (hscale : 4 * ell ≤ w)
    (Y : b → ℝ × ℝ) :
    ∃ t : AddCircle w × AddCircle w,
      (edgeBadCount w (2 * ell) Y t : ℝ) ≤
        (16 * ell / w) * Fintype.card b := by
  have hw : 0 < w := lt_of_lt_of_le (by nlinarith [hell]) hscale
  letI : Fact (0 < w) := ⟨hw⟩
  obtain ⟨t, ht⟩ := MeasureTheory.exists_le_average
    (volume_gridTranslation_ne_zero w) (integrable_edgeScore w (2 * ell) Y)
  refine ⟨t, ?_⟩
  rw [← edgeScore_eq_cast_count]
  calc
    _ ≤ (⨍ s, edgeScore w (2 * ell) Y s ∂volume) := ht
    _ ≤ Fintype.card b * (8 * ell / w) :=
      average_edgeScore_le w ell hell.le hscale Y
    _ = 8 * (ell / w) * Fintype.card b := by ring
    _ ≤ 16 * (ell / w) * Fintype.card b := by gcongr <;> norm_num
    _ = (16 * ell / w) * Fintype.card b := by ring

theorem exists_good_translation_nonempty
    {a b : Type*} [Fintype a] [Fintype b] [Nonempty a] [Nonempty b]
    (w ell : ℝ) (hell : 0 < ell) (hscale : 4 * ell ≤ w)
    (X : a → ℝ × ℝ) (Y : b → ℝ × ℝ) :
    ∃ t : AddCircle w × AddCircle w,
      (vertexBadCount w (2 * ell) X t : ℝ) ≤
          (32 * ell ^ 2 / w ^ 2) * Fintype.card a ∧
        (edgeBadCount w (2 * ell) Y t : ℝ) ≤
          (16 * ell / w) * Fintype.card b := by
  have hw : 0 < w := lt_of_lt_of_le (by nlinarith [hell]) hscale
  letI : Fact (0 < w) := ⟨hw⟩
  let A : ℝ := Fintype.card a * (16 * ell ^ 2 / w ^ 2)
  let B : ℝ := Fintype.card b * (8 * ell / w)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let score : AddCircle w × AddCircle w → ℝ := fun t =>
    B * vertexScore w (2 * ell) X t + A * edgeScore w (2 * ell) Y t
  have hvertexInt := integrable_vertexScore w (2 * ell) X
  have hedgeInt := integrable_edgeScore w (2 * ell) Y
  have hscoreInt : Integrable score volume :=
    (hvertexInt.const_mul B).add (hedgeInt.const_mul A)
  obtain ⟨t, ht⟩ := MeasureTheory.exists_le_average
    (volume_gridTranslation_ne_zero w) hscoreInt
  have havg : (⨍ s, score s ∂volume) ≤ 2 * A * B := by
    rw [show (⨍ s, score s ∂volume) =
        B * (⨍ s, vertexScore w (2 * ell) X s ∂volume) +
          A * (⨍ s, edgeScore w (2 * ell) Y s ∂volume) by
      exact average_const_mul_add volume _ _ A B hvertexInt hedgeInt]
    rw [average_vertexScore w ell hell.le hscale X]
    have hedgeAvg := average_edgeScore_le w ell hell.le hscale Y
    dsimp [A, B]
    nlinarith
  have hscore : score t ≤ 2 * A * B := ht.trans havg
  have hvnonneg : 0 ≤ vertexScore w (2 * ell) X t := by
    rw [vertexScore_eq_cast_count]
    positivity
  have henonneg : 0 ≤ edgeScore w (2 * ell) Y t := by
    rw [edgeScore_eq_cast_count]
    positivity
  have hv : vertexScore w (2 * ell) X t ≤ 2 * A := by
    dsimp [score] at hscore
    nlinarith
  have he : edgeScore w (2 * ell) Y t ≤ 2 * B := by
    dsimp [score] at hscore
    nlinarith
  refine ⟨t, ?_, ?_⟩
  · rw [← vertexScore_eq_cast_count]
    calc
      _ ≤ 2 * A := hv
      _ = _ := by dsimp [A]; ring
  · rw [← edgeScore_eq_cast_count]
    calc
      _ ≤ 2 * B := he
      _ = _ := by dsimp [B]; ring

/--
The Dai--Li translated-grid lemma for two finite multisets.  The finite index
types carry multiplicity, and the same translation simultaneously satisfies
the vertex and edge bounds.  The constants `32` and `16` are obtained by
doubling the per-point Haar averages `16` and `8`.
-/
theorem exists_good_translation
    {a b : Type*} [Fintype a] [Fintype b]
    (w ell : ℝ) (hell : 0 < ell) (hscale : 4 * ell ≤ w)
    (X : a → ℝ × ℝ) (Y : b → ℝ × ℝ) :
    ∃ t : AddCircle w × AddCircle w,
      (vertexBadCount w (2 * ell) X t : ℝ) ≤
          (32 * ell ^ 2 / w ^ 2) * Fintype.card a ∧
        (edgeBadCount w (2 * ell) Y t : ℝ) ≤
          (16 * ell / w) * Fintype.card b := by
  classical
  by_cases ha : Nonempty a
  · letI : Nonempty a := ha
    by_cases hb : Nonempty b
    · letI : Nonempty b := hb
      exact exists_good_translation_nonempty w ell hell hscale X Y
    · letI : IsEmpty b := ⟨fun x => hb ⟨x⟩⟩
      obtain ⟨t, ht⟩ := exists_good_vertex_translation w ell hell hscale X
      refine ⟨t, ht, ?_⟩
      simp [edgeBadCount]
  · letI : IsEmpty a := ⟨fun x => ha ⟨x⟩⟩
    obtain ⟨t, ht⟩ := exists_good_edge_translation w ell hell hscale Y
    refine ⟨t, ?_, ht⟩
    simp [vertexBadCount]

/-- A closed, axis-parallel rectangle, including its boundary. -/
def rectangle (lower upper : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.Icc lower.1 upper.1 ×ˢ Set.Icc lower.2 upper.2

def packingRadius : ℝ := Real.sqrt 2 / 4

def packingBox (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo (p.1 - packingRadius) (p.1 + packingRadius) ×ˢ
    Set.Ioo (p.2 - packingRadius) (p.2 + packingRadius)

theorem packingRadius_pos : 0 < packingRadius := by
  rw [packingRadius]
  positivity

theorem two_mul_packingRadius : 2 * packingRadius = Real.sqrt 2 / 2 := by
  rw [packingRadius]
  ring

theorem packingBox_pairwise_disjoint
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i) :
    (s : Set i).PairwiseDisjoint (packingBox ∘ embedding.point) := by
  rw [Set.pairwiseDisjoint_iff]
  intro p hp q hq hpq
  by_contra hne
  obtain ⟨z, hzp, hzq⟩ := hpq
  have hpx : |(embedding.point p).1 - z.1| < packingRadius := by
    rcases hzp with ⟨⟨hzpl, hzpu⟩, _⟩
    rw [abs_lt]
    constructor <;> linarith
  have hqx : |z.1 - (embedding.point q).1| < packingRadius := by
    rcases hzq with ⟨⟨hzql, hzqu⟩, _⟩
    rw [abs_lt]
    constructor <;> linarith
  have hpy : |(embedding.point p).2 - z.2| < packingRadius := by
    rcases hzp with ⟨_, ⟨hzpl, hzpu⟩⟩
    rw [abs_lt]
    constructor <;> linarith
  have hqy : |z.2 - (embedding.point q).2| < packingRadius := by
    rcases hzq with ⟨_, ⟨hzql, hzqu⟩⟩
    rw [abs_lt]
    constructor <;> linarith
  have hx : |(embedding.point p).1 - (embedding.point q).1| < Real.sqrt 2 / 2 := by
    calc
      _ ≤ |(embedding.point p).1 - z.1| + |z.1 - (embedding.point q).1| := by
        simpa only [sub_add_sub_cancel] using
          abs_add_le ((embedding.point p).1 - z.1) (z.1 - (embedding.point q).1)
      _ < 2 * packingRadius := by linarith
      _ = _ := two_mul_packingRadius
  have hy : |(embedding.point p).2 - (embedding.point q).2| < Real.sqrt 2 / 2 := by
    calc
      _ ≤ |(embedding.point p).2 - z.2| + |z.2 - (embedding.point q).2| := by
        simpa only [sub_add_sub_cancel] using
          abs_add_le ((embedding.point p).2 - z.2) (z.2 - (embedding.point q).2)
      _ < 2 * packingRadius := by linarith
      _ = _ := two_mul_packingRadius
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx2 : ((embedding.point p).1 - (embedding.point q).1) ^ 2 < 1 / 2 := by
    rw [← sq_abs]
    have habs : 0 ≤ |(embedding.point p).1 - (embedding.point q).1| := abs_nonneg _
    have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith
  have hy2 : ((embedding.point p).2 - (embedding.point q).2) ^ 2 < 1 / 2 := by
    rw [← sq_abs]
    have habs : 0 ≤ |(embedding.point p).2 - (embedding.point q).2| := abs_nonneg _
    have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith
  have hsep := embedding.unitSeparated hne
  have hsum0 : 0 ≤ ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
      ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by positivity
  rw [QEC.Locality.euclideanDistance2D] at hsep
  nlinarith [Real.sq_sqrt hsum0]

def expandedRectangle (lower upper : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo (lower.1 - packingRadius) (upper.1 + packingRadius) ×ˢ
    Set.Ioo (lower.2 - packingRadius) (upper.2 + packingRadius)

theorem measurableSet_packingBox (p : ℝ × ℝ) : MeasurableSet (packingBox p) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem volume_packingBox (p : ℝ × ℝ) :
    volume (packingBox p) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [packingBox, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [show p.1 + packingRadius - (p.1 - packingRadius) = 2 * packingRadius by ring,
    show p.2 + packingRadius - (p.2 - packingRadius) = 2 * packingRadius by ring,
    two_mul_packingRadius]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.sqrt 2 / 2)]
  congr 1
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem packingBoxes_subset_expandedRectangle
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (⋃ p ∈ s, packingBox (embedding.point p)) ⊆ expandedRectangle lower upper := by
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨p, hpS, hzp⟩ := hz
  have hpR := hmem p hpS
  rcases hpR with ⟨⟨hplx, hpux⟩, ⟨hply, hpuy⟩⟩
  rcases hzp with ⟨⟨hzlx, hzux⟩, ⟨hzly, hzuy⟩⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem packing_card_div_two_le_expanded_area
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlx : lower.1 ≤ upper.1) (hly : lower.2 ≤ upper.2)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) / 2 ≤
      (upper.1 - lower.1 + 2 * packingRadius) *
        (upper.2 - lower.2 + 2 * packingRadius) := by
  have hdisj := packingBox_pairwise_disjoint embedding s
  have hunion : volume (⋃ p ∈ s, packingBox (embedding.point p)) =
      ∑ p ∈ s, volume (packingBox (embedding.point p)) :=
    measure_biUnion_finset hdisj (fun p _ => measurableSet_packingBox _)
  have hmono : volume (⋃ p ∈ s, packingBox (embedding.point p)) ≤
      volume (expandedRectangle lower upper) :=
    measure_mono (packingBoxes_subset_expandedRectangle embedding s lower upper hmem)
  have hmeasure : (s.card : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) ≤
      ENNReal.ofReal (upper.1 - lower.1 + 2 * packingRadius) *
        ENNReal.ofReal (upper.2 - lower.2 + 2 * packingRadius) := by
    calc
      _ = ∑ p ∈ s, volume (packingBox (embedding.point p)) := by
        simp [volume_packingBox]
      _ = volume (⋃ p ∈ s, packingBox (embedding.point p)) := hunion.symm
      _ ≤ volume (expandedRectangle lower upper) := hmono
      _ = _ := by
        rw [expandedRectangle, MeasureTheory.Measure.volume_eq_prod,
          MeasureTheory.Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
        congr 2 <;> ring
  have hfiniteLeft : (s.card : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) ≠ ∞ := by
    finiteness
  have hfiniteRight : ENNReal.ofReal (upper.1 - lower.1 + 2 * packingRadius) *
      ENNReal.ofReal (upper.2 - lower.2 + 2 * packingRadius) ≠ ∞ := by
    finiteness
  have hreal := (ENNReal.toReal_le_toReal hfiniteLeft hfiniteRight).2 hmeasure
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hreal
  rw [ENNReal.toReal_ofReal (by nlinarith [packingRadius_pos.le] :
      0 ≤ upper.1 - lower.1 + 2 * packingRadius),
    ENNReal.toReal_ofReal (by nlinarith [packingRadius_pos.le] :
      0 ≤ upper.2 - lower.2 + 2 * packingRadius)] at hreal
  norm_num at hreal
  convert hreal using 1 <;> ring

theorem one_add_two_mul_packingRadius_sq_le_three :
    (1 + 2 * packingRadius) ^ 2 ≤ (3 : ℝ) := by
  rw [two_mul_packingRadius]
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem expanded_area_le_three_mul_area
    {width height : ℝ} (hwidth : 1 ≤ width) (hheight : 1 ≤ height) :
    (width + 2 * packingRadius) * (height + 2 * packingRadius) ≤
      3 * (width * height) := by
  have hr : 0 ≤ 2 * packingRadius :=
    mul_nonneg (by norm_num) packingRadius_pos.le
  have hx : width + 2 * packingRadius ≤ (1 + 2 * packingRadius) * width := by
    nlinarith [mul_nonneg hr (sub_nonneg.2 hwidth)]
  have hy : height + 2 * packingRadius ≤ (1 + 2 * packingRadius) * height := by
    nlinarith [mul_nonneg hr (sub_nonneg.2 hheight)]
  have hlowerY0 : 0 ≤ height + 2 * packingRadius := by
    nlinarith [packingRadius_pos.le]
  have hupperX0 : 0 ≤ (1 + 2 * packingRadius) * width := by
    exact mul_nonneg (by nlinarith [packingRadius_pos.le]) (by linarith)
  calc
    _ ≤ ((1 + 2 * packingRadius) * width) *
        ((1 + 2 * packingRadius) * height) := mul_le_mul hx hy hlowerY0 hupperX0
    _ = (1 + 2 * packingRadius) ^ 2 * (width * height) := by ring
    _ ≤ 3 * (width * height) := by
      exact mul_le_mul_of_nonneg_right one_add_two_mul_packingRadius_sq_le_three
        (mul_nonneg (by linarith) (by linarith))

theorem expanded_thin_area_le_three_mul_longSide
    {longSide thinSide : ℝ} (hlong : 1 ≤ longSide)
    (hthin0 : 0 ≤ thinSide) (hthin1 : thinSide ≤ 1) :
    (longSide + 2 * packingRadius) * (thinSide + 2 * packingRadius) ≤
      3 * longSide := by
  have hr : 0 ≤ 2 * packingRadius :=
    mul_nonneg (by norm_num) packingRadius_pos.le
  have hx : longSide + 2 * packingRadius ≤
      (1 + 2 * packingRadius) * longSide := by
    nlinarith [mul_nonneg hr (sub_nonneg.2 hlong)]
  have hy : thinSide + 2 * packingRadius ≤ 1 + 2 * packingRadius := by linarith
  have hlowerY0 : 0 ≤ thinSide + 2 * packingRadius := by
    nlinarith [packingRadius_pos.le]
  have hupperX0 : 0 ≤ (1 + 2 * packingRadius) * longSide := by
    exact mul_nonneg (by nlinarith [packingRadius_pos.le]) (by linarith)
  calc
    _ ≤ ((1 + 2 * packingRadius) * longSide) *
        (1 + 2 * packingRadius) := mul_le_mul hx hy hlowerY0 hupperX0
    _ = (1 + 2 * packingRadius) ^ 2 * longSide := by ring
    _ ≤ 3 * longSide := by
      exact mul_le_mul_of_nonneg_right one_add_two_mul_packingRadius_sq_le_three
        (by linarith)

/-- The source-scale packing bound for rectangles whose two sides are at least one. -/
theorem unitSeparated_card_in_rectangle_le_six_mul_area
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hwidth : 1 ≤ upper.1 - lower.1) (hheight : 1 ≤ upper.2 - lower.2)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) := by
  have hpack := packing_card_div_two_le_expanded_area embedding s lower upper
    (by linarith) (by linarith) hmem
  have harea := expanded_area_le_three_mul_area hwidth hheight
  nlinarith

/--
The source thin-rectangle constant, proved by a finite binning argument.

The source's circle-intersection sketch is not used here: at a rectangle corner
its claimed `t / 4` lower bound can fail.  Instead, the proof splits the thin
coordinate in two.  For long sides below `3 / 2`, the resulting four cells all
have diameter below one.  Otherwise, bins of width `3 / 4`, again split in two,
inject the point set into `Fin (⌊4s/3⌋₊ + 1) × Bool`; the floor estimate gives
the exact factor four without a boundary-error term.
-/
theorem unitSeparated_card_in_thin_rectangle_le_four_mul_longSide
    {i : Type*} [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.1 - lower.1)
    (hthin0 : 0 ≤ upper.2 - lower.2) (hthin1 : upper.2 - lower.2 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 4 * (upper.1 - lower.1) := by
  let width := upper.1 - lower.1
  let height := upper.2 - lower.2
  let xmid := (lower.1 + upper.1) / 2
  let ymid := (lower.2 + upper.2) / 2
  have hheight0 : 0 ≤ height := by simpa [height] using hthin0
  have eq_of_close
      (p q : i) (hxabs : |(embedding.point p).1 - (embedding.point q).1| < 3 / 4)
      (hyabs : |(embedding.point p).2 - (embedding.point q).2| < 1 / 2) : p = q := by
    by_contra hpq
    have hsep := embedding.unitSeparated hpq
    rw [euclideanDistance2D] at hsep
    have hxnonneg : 0 ≤ |(embedding.point p).1 - (embedding.point q).1| := abs_nonneg _
    have hynonneg : 0 ≤ |(embedding.point p).2 - (embedding.point q).2| := abs_nonneg _
    have hsumnonneg : 0 ≤ ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by positivity
    have hsqrt := Real.sq_sqrt hsumnonneg
    have hsqrt0 := Real.sqrt_nonneg (((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2)
    have hx2 : ((embedding.point p).1 - (embedding.point q).1) ^ 2 < 9 / 16 := by
      rw [← sq_abs]
      nlinarith
    have hy2 : ((embedding.point p).2 - (embedding.point q).2) ^ 2 < 1 / 4 := by
      rw [← sq_abs]
      nlinarith
    nlinarith
  by_cases hwidth : width < 3 / 2
  · let code : {p // p ∈ s} → Bool × Bool := fun p =>
      (decide ((embedding.point p.1).1 < xmid), decide ((embedding.point p.1).2 < ymid))
    have hcode : Function.Injective code := by
      intro p q hpq
      apply Subtype.ext
      apply eq_of_close p.1 q.1
      · have hpR := hmem p.1 p.2
        have hqR := hmem q.1 q.2
        rcases hpR with ⟨⟨hplx, hpux⟩, _⟩
        rcases hqR with ⟨⟨hqlx, hqux⟩, _⟩
        have hxCode := congrArg Prod.fst hpq
        have hxabs : |(embedding.point p.1).1 - (embedding.point q.1).1| ≤ width / 2 := by
          by_cases hpx : (embedding.point p.1).1 < xmid
          · have hqx : (embedding.point q.1).1 < xmid := by
              simpa [code, hpx] using hxCode
            rw [abs_le]
            constructor <;> dsimp [width, xmid] at * <;> linarith
          · have hqx : ¬ (embedding.point q.1).1 < xmid := by
              simpa [code, hpx] using hxCode
            rw [abs_le]
            constructor <;> dsimp [width, xmid] at * <;> linarith
        linarith
      · have hpR := hmem p.1 p.2
        have hqR := hmem q.1 q.2
        rcases hpR with ⟨_, ⟨hply, hpuy⟩⟩
        rcases hqR with ⟨_, ⟨hqly, hquy⟩⟩
        have hyCode := congrArg Prod.snd hpq
        have hyabs : |(embedding.point p.1).2 - (embedding.point q.1).2| ≤ height / 2 := by
          by_cases hpy : (embedding.point p.1).2 < ymid
          · have hqy : (embedding.point q.1).2 < ymid := by
              simpa [code, hpy] using hyCode
            rw [abs_le]
            constructor <;> dsimp [height, ymid] at * <;> linarith
          · have hqy : ¬ (embedding.point q.1).2 < ymid := by
              simpa [code, hpy] using hyCode
            rw [abs_le]
            constructor <;> dsimp [height, ymid] at * <;> linarith
        dsimp [height] at hyabs
        nlinarith [hheight0]
    have hcard := Fintype.card_le_of_injective code hcode
    have hs4 : s.card ≤ 4 := by simpa [code] using hcard
    have hs4R : (s.card : ℝ) ≤ 4 := by exact_mod_cast hs4
    dsimp [width] at hwidth ⊢
    nlinarith
  · let bins := Nat.floor (4 * width / 3) + 1
    let code : {p // p ∈ s} → Fin bins × Bool := fun p =>
      (⟨Nat.floor (4 * ((embedding.point p.1).1 - lower.1) / 3), by
          apply Nat.lt_succ_of_le
          apply Nat.floor_mono
          have hpR := hmem p.1 p.2
          rcases hpR with ⟨⟨_, hpux⟩, _⟩
          dsimp [width]
          linarith⟩,
        decide ((embedding.point p.1).2 < ymid))
    have hcode : Function.Injective code := by
      intro p q hpq
      apply Subtype.ext
      apply eq_of_close p.1 q.1
      · have hxCode :
            Nat.floor (4 * ((embedding.point p.1).1 - lower.1) / 3) =
              Nat.floor (4 * ((embedding.point q.1).1 - lower.1) / 3) := by
          have := congrArg (fun z => z.1.val) hpq
          simpa [code] using this
        have hpR := hmem p.1 p.2
        have hqR := hmem q.1 q.2
        rcases hpR with ⟨⟨hplx, _⟩, _⟩
        rcases hqR with ⟨⟨hqlx, _⟩, _⟩
        have hpFloor := Nat.floor_le
          (show 0 ≤ 4 * ((embedding.point p.1).1 - lower.1) / 3 by positivity)
        have hqFloor := Nat.floor_le
          (show 0 ≤ 4 * ((embedding.point q.1).1 - lower.1) / 3 by positivity)
        have hpNext := Nat.lt_floor_add_one
          (4 * ((embedding.point p.1).1 - lower.1) / 3)
        have hqNext := Nat.lt_floor_add_one
          (4 * ((embedding.point q.1).1 - lower.1) / 3)
        rw [hxCode] at hpFloor hpNext
        rw [abs_lt]
        constructor <;> norm_num at hpFloor hqFloor hpNext hqNext ⊢ <;> linarith
      · have hpR := hmem p.1 p.2
        have hqR := hmem q.1 q.2
        rcases hpR with ⟨_, ⟨hply, hpuy⟩⟩
        rcases hqR with ⟨_, ⟨hqly, hquy⟩⟩
        have hyCode : decide ((embedding.point p.1).2 < ymid) =
            decide ((embedding.point q.1).2 < ymid) := by
          have := congrArg Prod.snd hpq
          simpa [code] using this
        have hyabs : |(embedding.point p.1).2 - (embedding.point q.1).2| ≤ height / 2 := by
          by_cases hpy : (embedding.point p.1).2 < ymid
          · have hqy : (embedding.point q.1).2 < ymid := by
              simpa [hpy] using hyCode
            rw [abs_le]
            constructor <;> dsimp [height, ymid] at * <;> linarith
          · have hqy : ¬ (embedding.point q.1).2 < ymid := by
              simpa [hpy] using hyCode
            rw [abs_le]
            constructor <;> dsimp [height, ymid] at * <;> linarith
        dsimp [height] at hyabs
        nlinarith [hheight0]
    have hcard := Fintype.card_le_of_injective code hcode
    have hcard' : s.card ≤ 2 * (Nat.floor (4 * width / 3) + 1) := by
      simpa [code, bins, Nat.mul_comm] using hcard
    have hcardR : (s.card : ℝ) ≤ 2 * ((Nat.floor (4 * width / 3) : ℝ) + 1) := by
      exact_mod_cast hcard'
    have hfloor : (Nat.floor (4 * width / 3) : ℝ) ≤ 4 * width / 3 := by
      apply Nat.floor_le
      have : (0 : ℝ) ≤ width := by linarith [hlong]
      positivity
    dsimp [width] at hwidth hcardR hfloor ⊢
    nlinarith

/-- The exact thin-rectangle source constant with the long side vertical. -/
theorem unitSeparated_card_in_thin_rectangle_le_four_mul_height
    {i : Type*} [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.2 - lower.2)
    (hthin0 : 0 ≤ upper.1 - lower.1) (hthin1 : upper.1 - lower.1 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 4 * (upper.2 - lower.2) := by
  let swapped : UnitSeparatedEmbedding2D i :=
    { point := fun p => ((embedding.point p).2, (embedding.point p).1)
      unitSeparated := by
        intro p q hpq
        simpa [euclideanDistance2D, add_comm] using embedding.unitSeparated hpq }
  apply unitSeparated_card_in_thin_rectangle_le_four_mul_longSide swapped s
      (lower.2, lower.1) (upper.2, upper.1) hlong hthin0 hthin1
  intro p hp
  have hpR := hmem p hp
  rcases hpR with ⟨⟨hplx, hpux⟩, ⟨hply, hpuy⟩⟩
  exact ⟨⟨hply, hpuy⟩, ⟨hplx, hpux⟩⟩

/-- A relaxed corollary of the exact factor-four horizontal thin-strip bound. -/
theorem unitSeparated_card_in_thin_rectangle_le_six_mul_longSide
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.1 - lower.1)
    (hthin0 : 0 ≤ upper.2 - lower.2) (hthin1 : upper.2 - lower.2 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * (upper.1 - lower.1) := by
  have hfour := unitSeparated_card_in_thin_rectangle_le_four_mul_longSide
    embedding s lower upper hlong hthin0 hthin1 hmem
  nlinarith

/-- A relaxed corollary of the exact factor-four vertical thin-strip bound. -/
theorem unitSeparated_card_in_thin_rectangle_le_six_mul_height
    {i : Type*} [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.2 - lower.2)
    (hthin0 : 0 ≤ upper.1 - lower.1) (hthin1 : upper.1 - lower.1 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * (upper.2 - lower.2) := by
  have hfour := unitSeparated_card_in_thin_rectangle_le_four_mul_height
    embedding s lower upper hlong hthin0 hthin1 hmem
  nlinarith

/-- Actual embedded qubits lying in a closed axis-parallel rectangle. -/
def UnitSeparatedEmbedding2D.qubitsInRectangle
    {i : Type*} [Fintype i] [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (lower upper : ℝ × ℝ) : Finset i :=
  Finset.univ.filter fun p => embedding.point p ∈ rectangle lower upper

@[simp]
theorem UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
    {i : Type*} [Fintype i] [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (lower upper : ℝ × ℝ) (p : i) :
    p ∈ embedding.qubitsInRectangle lower upper ↔ embedding.point p ∈ rectangle lower upper := by
  simp [UnitSeparatedEmbedding2D.qubitsInRectangle]

/-- Downstream-ready form of the two-dimensional rectangle packing bound. -/
theorem UnitSeparatedEmbedding2D.card_qubitsInRectangle_le_six_mul_area
    {i : Type*} [Fintype i] [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (lower upper : ℝ × ℝ)
    (hwidth : 1 ≤ upper.1 - lower.1) (hheight : 1 ≤ upper.2 - lower.2) :
    ((embedding.qubitsInRectangle lower upper).card : ℝ) ≤
      6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) := by
  apply unitSeparated_card_in_rectangle_le_six_mul_area embedding
    (embedding.qubitsInRectangle lower upper) lower upper hwidth hheight
  intro p hp
  simpa using hp

/-- A half-open cell is contained in its corresponding closed geometric
rectangle, which is the form consumed by the existing packing estimates. -/
theorem UnitSeparatedEmbedding2D.gridCellQubits_subset_qubitsInRectangle
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    embedding.gridCellQubits w origin cell ⊆
      embedding.qubitsInRectangle (gridCellLower w origin cell)
        (gridCellUpper w origin cell) := by
  intro q hq
  have hCell : gridCellIndex w origin (embedding.point q) = cell :=
    (embedding.mem_gridCellQubits_iff w origin cell q).1 hq
  have hxFloor : ⌊((embedding.point q).1 - origin.1) / w⌋ = cell.1 :=
    congrArg Prod.fst hCell
  have hyFloor : ⌊((embedding.point q).2 - origin.2) / w⌋ = cell.2 :=
    congrArg Prod.snd hCell
  have hxLower : (cell.1 : ℝ) ≤ ((embedding.point q).1 - origin.1) / w := by
    rw [← hxFloor]
    exact Int.floor_le _
  have hxUpper : ((embedding.point q).1 - origin.1) / w < (cell.1 : ℝ) + 1 := by
    rw [← hxFloor]
    exact Int.lt_floor_add_one _
  have hyLower : (cell.2 : ℝ) ≤ ((embedding.point q).2 - origin.2) / w := by
    rw [← hyFloor]
    exact Int.floor_le _
  have hyUpper : ((embedding.point q).2 - origin.2) / w < (cell.2 : ℝ) + 1 := by
    rw [← hyFloor]
    exact Int.lt_floor_add_one _
  have hxLowerRaw := (le_div_iff₀ hw).mp hxLower
  have hxUpperRaw := (div_lt_iff₀ hw).mp hxUpper
  have hyLowerRaw := (le_div_iff₀ hw).mp hyLower
  have hyUpperRaw := (div_lt_iff₀ hw).mp hyUpper
  have hxLower' : origin.1 + cell.1 * w ≤ (embedding.point q).1 := by
    nlinarith
  have hxUpper' : (embedding.point q).1 ≤ origin.1 + (cell.1 + 1) * w := by
    linarith
  have hyLower' : origin.2 + cell.2 * w ≤ (embedding.point q).2 := by
    nlinarith
  have hyUpper' : (embedding.point q).2 ≤ origin.2 + (cell.2 + 1) * w := by
    linarith
  exact (embedding.mem_qubitsInRectangle_iff
    (gridCellLower w origin cell) (gridCellUpper w origin cell) q).2
      ⟨⟨hxLower', hxUpper'⟩, ⟨hyLower', hyUpper'⟩⟩

end QEC.Locality

namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

universe u v

variable {i : Type u} [Fintype i] [DecidableEq i]
variable {kappa : Type v} [Fintype kappa]

/--
Multiplicity index for the endpoint-incidence multiset of long interactions.
An index is a qubit together with one slot for every incident long edge.
-/
abbrev daiLiLongIncidenceIndex
    (P : BinaryStabilizerPresentation (ι := i) (κ := kappa))
    (embedding : Locality.UnitSeparatedEmbedding2D i) (threshold : ℝ) :=
  Σ q : i, Fin (P.daiLiInteractionCounter embedding threshold q)

/-- The endpoint point carried by one long-interaction incidence. -/
def daiLiLongIncidencePoint
    (P : BinaryStabilizerPresentation (ι := i) (κ := kappa))
    (embedding : Locality.UnitSeparatedEmbedding2D i) (threshold : ℝ) :
    P.daiLiLongIncidenceIndex embedding threshold → ℝ × ℝ :=
  fun incidence => embedding.point incidence.1

/-- The incidence multiset has exactly twice the distinct unordered long-edge count. -/
theorem card_daiLiLongIncidenceIndex_eq_two_mul_longInteractionCount
    (P : BinaryStabilizerPresentation (ι := i) (κ := kappa))
    (embedding : Locality.UnitSeparatedEmbedding2D i) (threshold : ℝ) :
    Fintype.card (P.daiLiLongIncidenceIndex embedding threshold) =
      2 * P.longInteractionCount embedding threshold := by
  rw [Fintype.card_sigma]
  simpa using P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding threshold

/--
Downstream tiling handoff: one translated grid controls all qubits near vertices
and the actual long-interaction endpoint multiset near edges.
-/
theorem exists_good_translation_for_qubits_and_longIncidences
    (P : BinaryStabilizerPresentation (ι := i) (κ := kappa))
    (embedding : Locality.UnitSeparatedEmbedding2D i) (threshold w ell : ℝ)
    (hell : 0 < ell) (hscale : 4 * ell ≤ w) :
    ∃ t : Locality.GridTranslation w,
      (Locality.vertexBadCount w (2 * ell) embedding.point t : ℝ) ≤
          (32 * ell ^ 2 / w ^ 2) * Fintype.card i ∧
        (Locality.edgeBadCount w (2 * ell)
            (P.daiLiLongIncidencePoint embedding threshold) t : ℝ) ≤
          (16 * ell / w) * (2 * P.longInteractionCount embedding threshold) := by
  obtain ⟨t, hvertex, hedge⟩ := Locality.exists_good_translation w ell hell hscale
    embedding.point (P.daiLiLongIncidencePoint embedding threshold)
  refine ⟨t, hvertex, ?_⟩
  rw [P.card_daiLiLongIncidenceIndex_eq_two_mul_longInteractionCount embedding threshold] at hedge
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hedge

end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
