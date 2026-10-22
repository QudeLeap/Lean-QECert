import QEC.Coding.FiniteAlternatingConstruction.TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Finite flat-patch counting for replacement embeddings

This module proves the geometric counting closure used by the replacement
embedding slice of [BDL26, Section 3]. A flat patch has two coincident square
layers and two collapsed seams, each with two copies. Images retain their
cell labels even when they coincide. Every seam image lies in a specified
positive cell, and a positive cell receives at most two seam labels.

The name `PositiveCell` denotes the grid-layer label class only. An arbitrary
grid map can collapse these cells too; no nonzero area is asserted here.

The patch is defined here, not supplied with a density certificate. Relating
these patch coordinates to the actual RX/RZ tagged cells and proving the
incoming-triangle packing estimate remain separate obligations of #854.
No recursive embedding or numerical source witness is asserted.
-/

namespace QEC.Coding.BDL26ReplacementEmbedding

open BDL26FiniteTannerSquare

/-- A grid-square label retains its layer and its two grid coordinates.
The word positive distinguishes its family from seams, not its actual area. -/
abbrev PositiveCell (S : OddScale) := Two × (Fin S.ell × Fin S.ell)

/-- A collapsed seam retains its layer and its segment coordinate. -/
abbrev SeamCell (S : OddScale) := Two × Fin S.ell

/-- Two positive layers plus horizontal and vertical collapsed seams. -/
abbrev FlatCell (S : OddScale) := PositiveCell S ⊕ (SeamCell S ⊕ SeamCell S)

/-- The last grid strip; the seams lie on its lower and left sides. -/
def lastStrip (S : OddScale) : Fin S.ell := ⟨S.ell - 1, by have := S.three_le; omega⟩

/-- Canonical positive cell containing a flat cell's image. -/
def charge (S : OddScale) : FlatCell S → PositiveCell S
  | .inl p => p
  | .inr (.inl h) => (h.1, h.2, lastStrip S)
  | .inr (.inr v) => (v.1, lastStrip S, v.2)

/-- Keep the three cell families distinct after charging. -/
def chargeTag (S : OddScale) : FlatCell S → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- Each positive cell receives at most one label from each family. -/
theorem taggedCharge_injective (S : OddScale) :
    Function.Injective (fun c : FlatCell S => (chargeTag S c, charge S c)) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (congrArg (fun p => p.2) hab)
  · rcases b with b | b <;> simp [chargeTag] at hab
  · rcases a with a | a <;> simp [chargeTag] at hab
  · rcases a with a | a <;> rcases b with b | b
    · have h := congrArg (fun p : Fin 3 × PositiveCell S => (p.2.1, p.2.2.1)) hab
      have h' : a = b := by simpa [charge] using h
      exact congrArg (fun x => Sum.inr (Sum.inl x)) h'
    · simp [chargeTag] at hab
    · simp [chargeTag] at hab
    · have h := congrArg (fun p : Fin 3 × PositiveCell S => (p.2.1, p.2.2.2)) hab
      have h' : a = b := by simpa [charge] using h
      exact congrArg (fun x => Sum.inr (Sum.inr x)) h'

/-- Exact positive multiplicity, without identifying coincident layers. -/
theorem positiveCell_card (S : OddScale) :
    Fintype.card (PositiveCell S) = 2 * S.ell ^ 2 := by
  simp [PositiveCell, Two, pow_two]

/-- Exact domain-cell count, including all collapsed seam cells. -/
theorem flatCell_card (S : OddScale) :
    Fintype.card (FlatCell S) = 2 * S.ell ^ 2 + 4 * S.ell := by
  simp only [FlatCell, Fintype.card_sum, SeamCell, Fintype.card_prod,
    Fintype.card_fin, show Fintype.card Two = 2 from rfl]
  ring

/-- Lower endpoint of a grid interval. -/
def lower (S : OddScale) (i : Fin S.ell) : Fin (S.ell + 1) :=
  ⟨i.1, Nat.lt_succ_of_lt i.2⟩

/-- Upper endpoint of a grid interval. -/
def upper (S : OddScale) (i : Fin S.ell) : Fin (S.ell + 1) :=
  ⟨i.1 + 1, by omega⟩

section Images

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Grid vertices can lie in any real vector space; layers coincide. -/
abbrev GridMap (S : OddScale) (E : Type*) :=
  Fin (S.ell + 1) → Fin (S.ell + 1) → E

/-- A folded square is the union of its two closed affine triangles. -/
def positiveImage (S : OddScale) (p : GridMap S E) (c : PositiveCell S) : Set E :=
  convexHull ℝ {p (lower S c.2.1) (lower S c.2.2),
    p (upper S c.2.1) (lower S c.2.2), p (upper S c.2.1) (upper S c.2.2)} ∪
  convexHull ℝ {p (lower S c.2.1) (lower S c.2.2),
    p (upper S c.2.1) (upper S c.2.2), p (lower S c.2.1) (upper S c.2.2)}

/-- The horizontal collapsed seam is the lower side of the last row. -/
def horizontalImage (S : OddScale) (p : GridMap S E) (c : SeamCell S) : Set E :=
  segment ℝ (p (lower S c.2) (lower S (lastStrip S)))
    (p (upper S c.2) (lower S (lastStrip S)))

/-- The vertical collapsed seam is the left side of the last column. -/
def verticalImage (S : OddScale) (p : GridMap S E) (c : SeamCell S) : Set E :=
  segment ℝ (p (lower S (lastStrip S)) (lower S c.2))
    (p (lower S (lastStrip S)) (upper S c.2))

/-- A collapsed domain two-cell keeps its segment image and its own label. -/
def cellImage (S : OddScale) (p : GridMap S E) : FlatCell S → Set E
  | .inl c => positiveImage S p c
  | .inr (.inl c) => horizontalImage S p c
  | .inr (.inr c) => verticalImage S p c

/-- Image containment is derived from the actual segment and triangle formulas. -/
theorem cellImage_subset_charge (S : OddScale) (p : GridMap S E) (c : FlatCell S) :
    cellImage S p c ⊆ positiveImage S p (charge S c) := by
  rcases c with c | c
  · exact Set.Subset.rfl
  · rcases c with c | c
    · exact Set.Subset.trans
        (segment_subset_convexHull (by simp [charge]) (by simp [charge])) Set.subset_union_left
    · exact Set.Subset.trans
        (segment_subset_convexHull (by simp [charge]) (by simp [charge])) Set.subset_union_right

/-- Labeled positive cells meeting any selected region. -/
noncomputable def positiveHits (S : OddScale) (p : GridMap S E) (region : Set E) :
    Finset (PositiveCell S) := by
  classical
  exact Finset.univ.filter fun c => (positiveImage S p c ∩ region).Nonempty

/-- All labeled cells meeting the region, with collapsed multiplicities intact. -/
noncomputable def allHits (S : OddScale) (p : GridMap S E) (region : Set E) :
    Finset (FlatCell S) := by
  classical
  exact Finset.univ.filter fun c => (cellImage S p c ∩ region).Nonempty

/-- No enlargement of the queried region is needed to charge collapsed cells. -/
theorem allHits_card_le_three_mul_positiveHits
    (S : OddScale) (p : GridMap S E) (region : Set E) :
    (allHits S p region).card ≤ 3 * (positiveHits S p region).card := by
  classical
  let target := (Finset.univ : Finset (Fin 3)) ×ˢ positiveHits S p region
  have hcard : (allHits S p region).card ≤ target.card := by
    apply Finset.card_le_card_of_injOn
      (fun c => (chargeTag S c, charge S c))
    · intro c hc
      obtain ⟨x, hx, hregion⟩ := (Finset.mem_filter.mp hc).2
      have hhit : (positiveImage S p (charge S c) ∩ region).Nonempty :=
        ⟨x, cellImage_subset_charge S p c hx, hregion⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit⟩⟩
    · exact (taggedCharge_injective S).injOn
  simpa [target] using hcard

end Images

/-! ## Honest odd-rounding slack -/

/-- Source odd rounding cannot justify replacing `lambda / ell` by `1 / A`. -/
theorem rounded_ratio_lt {A lam ell : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hround : A * lam < ell) : lam / ell < 1 / A := by
  have hell : 0 < ell := lt_trans (mul_pos hA hlam) hround
  apply (div_lt_div_iff₀ hell hA).2
  nlinarith

/-- The conservative factor 48 leaves enough slack for odd rounding once L≥13. -/
theorem rounded_density_slack {L ell : ℝ} (hL : 13 ≤ L)
    (hell : 0 ≤ ell) (hround : ell ≤ L + 2) :
    48 * ell ^ 2 ≤ 64 * L ^ 2 := by
  have hsquare : ell ^ 2 ≤ (L + 2) ^ 2 := by nlinarith
  have hproduct : 0 ≤ (L - 13) * (L + 1) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Multiplying the exact slack by a nonnegative geometric coefficient is valid. -/
theorem rounded_density_handoff {L ell coefficient : ℝ}
    (hL : 13 ≤ L) (hell : 0 ≤ ell) (hround : ell ≤ L + 2)
    (hcoefficient : 0 ≤ coefficient) :
    48 * coefficient * ell ^ 2 ≤ 64 * coefficient * L ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (rounded_density_slack hL hell hround) hcoefficient
  nlinarith

/-! ## Geometric family charging and derived lattice counts -/

open scoped BigOperators

/-- Labeled geometric hits retain all domain multiplicities. -/
noncomputable def familyHits {ι E : Type*} [Fintype ι]
    (images : ι → Set E) (region : Set E) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => (images i ∩ region).Nonempty

/-- Geometric charging works for the actual positive images as well as the
canonical flat triangulation. Only proved image containments are needed. -/
theorem familyHits_card_le_three_mul_positive {Owner E : Type*} [Fintype Owner]
    (S : OddScale) (images : Owner × FlatCell S → Set E) (region : Set E)
    (himage : ∀ owner cell, images (owner, cell) ⊆
      images (owner, .inl (charge S cell))) :
    (familyHits images region).card ≤
      3 * (familyHits (fun p : Owner × PositiveCell S => images (p.1, .inl p.2)) region).card := by
  classical
  let positives := familyHits (fun p : Owner × PositiveCell S => images (p.1, .inl p.2)) region
  let target := (Finset.univ : Finset (Fin 3)) ×ˢ positives
  have hcard : (familyHits images region).card ≤ target.card := by
    apply Finset.card_le_card_of_injOn
      (fun p => (chargeTag S p.2, p.1, charge S p.2))
    · intro p hp
      obtain ⟨x, hx, hregion⟩ := (Finset.mem_filter.mp hp).2
      refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, himage p.1 p.2 hx, hregion⟩
    · intro p _ q _ heq
      have ho : p.1 = q.1 := congrArg (fun z => z.2.1) heq
      have hc : p.2 = q.2 := taggedCharge_injective S
        (congrArg (fun z => (z.1, z.2.2)) heq)
      exact Prod.ext ho hc
  simpa [target, positives] using hcard

/-- A finite integer set contained in a real interval has the expected endpoint-inclusive count. -/
theorem int_interval_card_le (s : Finset ℤ) {a b : ℝ} (hab : a ≤ b)
    (hmem : ∀ z ∈ s, a ≤ (z : ℝ) ∧ (z : ℝ) ≤ b) :
    (s.card : ℝ) ≤ b - a + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let lo := s.min' hs
    let hi := s.max' hs
    have hlo : lo ∈ s := s.min'_mem hs
    have hhi : hi ∈ s := s.max'_mem hs
    have horder : lo ≤ hi := s.min'_le hi hhi
    have hsub : s ⊆ Finset.Icc lo hi := by
      intro z hz
      exact Finset.mem_Icc.mpr ⟨s.min'_le z hz, s.le_max' z hz⟩
    have hc : (s.card : ℤ) ≤ hi + 1 - lo := by
      calc
        (s.card : ℤ) ≤ ((Finset.Icc lo hi).card : ℤ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ = hi + 1 - lo := Int.card_Icc_of_le lo hi (by omega)
    have hcR : (s.card : ℝ) ≤ (hi : ℝ) + 1 - lo := by exact_mod_cast hc
    have hl := hmem lo hlo
    have hh := hmem hi hhi
    linarith
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    linarith

/-- Count lattice points in a translated real interval; no separation certificate is assumed. -/
theorem int_affine_interval_card_le (s : Finset ℤ) {spacing center radius : ℝ}
    (hspacing : 0 < spacing) (hradius : 0 ≤ radius)
    (hmem : ∀ z ∈ s, |spacing * (z : ℝ) - center| ≤ radius) :
    (s.card : ℝ) ≤ 2 * radius / spacing + 1 := by
  have hab : (center - radius) / spacing ≤ (center + radius) / spacing :=
    (div_le_div_iff_of_pos_right hspacing).2 (by linarith)
  have hc := int_interval_card_le s hab (fun z hz => by
    have ha := abs_le.mp (hmem z hz)
    constructor
    · apply (div_le_iff₀ hspacing).2
      nlinarith
    · apply (le_div_iff₀ hspacing).2
      nlinarith)
  convert hc using 1 <;> field_simp <;> ring

/-- Row-by-row counting in an actual shear lattice. Two Euclidean coordinate inequalities
are sufficient; no bound on the number of lattice points is supplied by the caller. -/
theorem shear_lattice_card_le (s : Finset (ℤ × ℤ)) {a h c x y : ℝ}
    (ha : 0 < a) (hh : 0 < h)
    (hx : ∀ p ∈ s, |a * (p.1 : ℝ) + c * (p.2 : ℝ) - x| ≤ 2)
    (hy : ∀ p ∈ s, |h * (p.2 : ℝ) - y| ≤ 2) :
    (s.card : ℝ) ≤ (4 / h + 1) * (4 / a + 1) := by
  classical
  let rows := s.image Prod.snd
  let fiber (j : ℤ) := s.filter fun p => p.2 = j
  have hrows : (rows.card : ℝ) ≤ 4 / h + 1 := by
    have hc := int_affine_interval_card_le rows hh (by norm_num : (0 : ℝ) ≤ 2)
      (fun j hj => by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
        exact hy p hp)
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hc
  have hfiber (j : ℤ) : ((fiber j).card : ℝ) ≤ 4 / a + 1 := by
    have hinj : Set.InjOn Prod.fst ((fiber j : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
      intro p hp q hq he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
    rw [← Finset.card_image_of_injOn hinj]
    have hc := int_affine_interval_card_le ((fiber j).image Prod.fst) ha
      (by norm_num : (0 : ℝ) ≤ 2) (center := x - c * j) (fun i hi => by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
        have hm := Finset.mem_filter.mp hp
        have hc := hx p hm.1
        simpa [hm.2, sub_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hc)
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hc
  have hc : (s.card : ℝ) = ∑ j ∈ rows, ((fiber j).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image Prod.snd s
  calc
    (s.card : ℝ) = ∑ j ∈ rows, ((fiber j).card : ℝ) := hc
    _ ≤ ∑ j ∈ rows, (4 / a + 1) := Finset.sum_le_sum fun j _ => hfiber j
    _ = (rows.card : ℝ) * (4 / a + 1) := by simp <;> ring
    _ ≤ (4 / h + 1) * (4 / a + 1) :=
      mul_le_mul_of_nonneg_right hrows (by positivity)

/-- The exact finite count fits the source packing envelope for subunit spacings. -/
theorem shear_lattice_card_le_pi (s : Finset (ℤ × ℤ)) {a h c x y : ℝ}
    (ha : 0 < a) (hh : 0 < h) (ha1 : a ≤ 1) (hh1 : h ≤ 1)
    (hx : ∀ p ∈ s, |a * (p.1 : ℝ) + c * (p.2 : ℝ) - x| ≤ 2)
    (hy : ∀ p ∈ s, |h * (p.2 : ℝ) - y| ≤ 2) :
    (s.card : ℝ) ≤ 8 * Real.pi / (a * h) := by
  have ha5 : 4 / a + 1 ≤ 5 / a := by
    apply (le_div_iff₀ ha).2
    rw [add_mul, div_mul_cancel₀ _ ha.ne', one_mul]
    linarith
  have hh5 : 4 / h + 1 ≤ 5 / h := by
    apply (le_div_iff₀ hh).2
    rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul]
    linarith
  calc
    (s.card : ℝ) ≤ (4 / h + 1) * (4 / a + 1) :=
      shear_lattice_card_le s ha hh hx hy
    _ ≤ (5 / h) * (5 / a) := mul_le_mul hh5 ha5 (by positivity) (by positivity)
    _ = 25 / (a * h) := by ring
    _ ≤ 8 * Real.pi / (a * h) :=
      (div_le_div_iff_of_pos_right (mul_pos ha hh)).2 (by linarith [Real.pi_gt_d2])

end QEC.Coding.BDL26ReplacementEmbedding
