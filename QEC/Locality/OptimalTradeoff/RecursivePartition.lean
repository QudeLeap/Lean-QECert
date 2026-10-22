import QEC.Locality.CorrectableRegions.CorrectableRegionClosure
import QEC.Locality.OptimalTradeoff.PackingTiling
/-!
# Dai--Li recursive-partition infrastructure

This internal module supplies a finite growing-square proof closure for the
still-open Dai--Li partition argument.  The growth boundary is computed from
the actual planar embedding and fixed-generator long-interaction graph: it is
the geometric shell together with actual outside endpoints of long
interactions, not a supplied partition or stored correctability assertion.

The module now also contains the first source-exact partition slice: actual
good/bad interaction classification, horizontal subdivision primitives,
periodic `B/B'` edge buffers for the no-bad-rectangle case, and a semantic
`d >= k` recovery composition through the proved distance and decoupled-union
APIs.  The full greedy subdivision theorem, both complete `A/B` recoveries,
quantitative `C` bound, and logical-dimension handoff remain open.
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

local instance instClassicalDecidableRecursive (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The Dai--Li endpoint-incidence counter restricted to a finite qubit
region.  It is introduced before the growth lemmas because those lemmas charge
every intermediate boundary to this concrete finite sum. -/
def regionInteractionCounter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) : Nat :=
  ∑ q ∈ region, P.daiLiInteractionCounter embedding threshold q

/-- The actual long-interaction counter is monotone under finite region
inclusion. -/
theorem regionInteractionCounter_mono
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    {inner outer : Finset ι} (hSubset : inner ⊆ outer) :
    regionInteractionCounter P embedding threshold inner ≤
      regionInteractionCounter P embedding threshold outer := by
  unfold regionInteractionCounter
  exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun _ _ _ => Nat.zero_le _)

/-- The closed square centered at `center` with half-side `radius`. -/
def centeredSquare (center : ℝ × ℝ) (radius : ℝ) : Set (ℝ × ℝ) :=
  rectangle (center.1 - radius, center.2 - radius)
    (center.1 + radius, center.2 + radius)

/-- Actual embedded qubits in a closed centered square. -/
def squareQubits (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (radius : ℝ) : Finset ι :=
  embedding.qubitsInRectangle
    (center.1 - radius, center.2 - radius)
    (center.1 + radius, center.2 + radius)

/-- The concrete finite subsystem selected by `squareQubits`. -/
def squareSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (radius : ℝ) : FiniteSubsystem ι :=
  ⟨squareQubits embedding center radius⟩

@[simp]
theorem mem_squareQubits_iff (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (radius : ℝ) (q : ι) :
    q ∈ squareQubits embedding center radius ↔
      embedding.point q ∈ centeredSquare center radius := by
  simp [squareQubits, centeredSquare]

/-- Actual long-interaction neighbors of a finite qubit region. -/
def longNeighborsOf
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) : Finset ι := by
  classical
  exact region.biUnion fun q =>
    (P.longInteractionGraph embedding threshold).neighborFinset q

/-- Long-interaction neighbors lying outside the selected region. -/
def longOutsideNeighborsOf
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) : Finset ι :=
  longNeighborsOf P embedding threshold region \ region

@[simp]
theorem mem_longNeighborsOf_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) (q : ι) :
    q ∈ longNeighborsOf P embedding threshold region ↔
      ∃ p ∈ region,
        P.fixedGeneratorInteraction p q ∧ threshold ≤ embedding.distance p q := by
  classical
  simp only [longNeighborsOf, Finset.mem_biUnion, SimpleGraph.mem_neighborFinset]
  rfl

/-- A union bound converts local long incidences into an endpoint count. -/
theorem card_longNeighborsOf_le_sum_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) :
    (longNeighborsOf P embedding threshold region).card ≤
      ∑ q ∈ region, P.daiLiInteractionCounter embedding threshold q := by
  classical
  calc
    _ ≤ ∑ q ∈ region,
        ((P.longInteractionGraph embedding threshold).neighborFinset q).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [daiLiInteractionCounter, ← SimpleGraph.card_neighborFinset_eq_degree]

theorem card_longOutsideNeighborsOf_le_sum_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) :
    (longOutsideNeighborsOf P embedding threshold region).card ≤
      ∑ q ∈ region, P.daiLiInteractionCounter embedding threshold q := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    (card_longNeighborsOf_le_sum_counter P embedding threshold region)

/--
The actual boundary used in one growing-square step: the geometric shell plus
outside endpoints of long interactions from the inner square.
-/
def squareGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) : FiniteSubsystem ι :=
  ⟨(squareQubits embedding center outerRadius \
      squareQubits embedding center (outerRadius - threshold)) ∪
    longOutsideNeighborsOf P embedding threshold
      (squareQubits embedding center (outerRadius - threshold))⟩

/-- Four strips covering the one-threshold shell of a centered square. -/
def squareShellStrips (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerRadius threshold : ℝ) : Fin 4 → Finset ι
  | 0 => embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 - outerRadius)
      (center.1 - outerRadius + threshold, center.2 + outerRadius)
  | 1 => embedding.qubitsInRectangle
      (center.1 + outerRadius - threshold, center.2 - outerRadius)
      (center.1 + outerRadius, center.2 + outerRadius)
  | 2 => embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 - outerRadius)
      (center.1 + outerRadius, center.2 - outerRadius + threshold)
  | 3 => embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 + outerRadius - threshold)
      (center.1 + outerRadius, center.2 + outerRadius)

/-- The concrete union of the four shell strips. -/
def squareShellCover (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerRadius threshold : ℝ) : Finset ι :=
  Finset.univ.biUnion (squareShellStrips embedding center outerRadius threshold)

/-- The geometric square shell is covered by the four explicit strips. -/
theorem square_shell_subset_shellCover
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) :
    squareQubits embedding center outerRadius \
        squareQubits embedding center (outerRadius - threshold) ⊆
      squareShellCover embedding center outerRadius threshold := by
  intro q hq
  rcases Finset.mem_sdiff.mp hq with ⟨hqOuter, hqNotInner⟩
  have hOuter := (mem_squareQubits_iff embedding center outerRadius q).1 hqOuter
  rcases hOuter with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  by_contra hqNotCover
  have h0 : q ∉ squareShellStrips embedding center outerRadius threshold 0 := by
    exact fun h => hqNotCover (Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, h⟩)
  have h1 : q ∉ squareShellStrips embedding center outerRadius threshold 1 := by
    exact fun h => hqNotCover (Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, h⟩)
  have h2 : q ∉ squareShellStrips embedding center outerRadius threshold 2 := by
    exact fun h => hqNotCover (Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, h⟩)
  have h3 : q ∉ squareShellStrips embedding center outerRadius threshold 3 := by
    exact fun h => hqNotCover (Finset.mem_biUnion.mpr ⟨3, Finset.mem_univ _, h⟩)
  have hxLower : center.1 - (outerRadius - threshold) ≤ (embedding.point q).1 := by
    by_contra h
    apply h0
    rw [squareShellStrips, UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxl, by linarith [le_of_not_ge h]⟩, ⟨hyl, hyu⟩⟩
  have hxUpper : (embedding.point q).1 ≤ center.1 + (outerRadius - threshold) := by
    by_contra h
    apply h1
    rw [squareShellStrips, UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨by linarith [le_of_not_ge h], hxu⟩, ⟨hyl, hyu⟩⟩
  have hyLower : center.2 - (outerRadius - threshold) ≤ (embedding.point q).2 := by
    by_contra h
    apply h2
    rw [squareShellStrips, UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxl, hxu⟩, ⟨hyl, by linarith [le_of_not_ge h]⟩⟩
  have hyUpper : (embedding.point q).2 ≤ center.2 + (outerRadius - threshold) := by
    by_contra h
    apply h3
    rw [squareShellStrips, UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxl, hxu⟩, ⟨by linarith [le_of_not_ge h], hyu⟩⟩
  exact hqNotInner ((mem_squareQubits_iff embedding center
    (outerRadius - threshold) q).2 ⟨⟨hxLower, hxUpper⟩, ⟨hyLower, hyUpper⟩⟩)

/-- Each explicit shell strip has the source-level `6 * area` packing bound. -/
theorem card_squareShellStrips_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (hdiameter : 1 ≤ 2 * outerRadius) (j : Fin 4) :
    ((squareShellStrips embedding center outerRadius threshold j).card : ℝ) ≤
      12 * outerRadius * threshold := by
  fin_cases j
  · have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (center.1 - outerRadius, center.2 - outerRadius)
      (center.1 - outerRadius + threshold, center.2 + outerRadius)
      (by simpa using hthreshold) (by linarith)
    change ((embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 - outerRadius)
      (center.1 - outerRadius + threshold, center.2 + outerRadius)).card : ℝ) ≤ _
    calc
      _ ≤ 6 * (threshold * (outerRadius + outerRadius)) := by simpa using h
      _ = _ := by ring
  · have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (center.1 + outerRadius - threshold, center.2 - outerRadius)
      (center.1 + outerRadius, center.2 + outerRadius)
      (by simpa using hthreshold) (by linarith)
    change ((embedding.qubitsInRectangle
      (center.1 + outerRadius - threshold, center.2 - outerRadius)
      (center.1 + outerRadius, center.2 + outerRadius)).card : ℝ) ≤ _
    calc
      _ ≤ 6 * (threshold * (outerRadius + outerRadius)) := by simpa using h
      _ = _ := by ring
  · have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (center.1 - outerRadius, center.2 - outerRadius)
      (center.1 + outerRadius, center.2 - outerRadius + threshold)
      (by linarith) (by simpa using hthreshold)
    change ((embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 - outerRadius)
      (center.1 + outerRadius, center.2 - outerRadius + threshold)).card : ℝ) ≤ _
    calc
      _ ≤ 6 * ((outerRadius + outerRadius) * threshold) := by simpa using h
      _ = _ := by ring
  · have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (center.1 - outerRadius, center.2 + outerRadius - threshold)
      (center.1 + outerRadius, center.2 + outerRadius)
      (by linarith) (by simpa using hthreshold)
    change ((embedding.qubitsInRectangle
      (center.1 - outerRadius, center.2 + outerRadius - threshold)
      (center.1 + outerRadius, center.2 + outerRadius)).card : ℝ) ≤ _
    calc
      _ ≤ 6 * ((outerRadius + outerRadius) * threshold) := by simpa using h
      _ = _ := by ring

/-- The complete geometric shell has the Dai--Li `24 * side * ell` bound. -/
theorem card_square_shell_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (hdiameter : 1 ≤ 2 * outerRadius) :
    ((squareQubits embedding center outerRadius \
        squareQubits embedding center (outerRadius - threshold)).card : ℝ) ≤
      48 * outerRadius * threshold := by
  have hsubset := square_shell_subset_shellCover embedding center outerRadius threshold
  have hcoverNat :
      (squareShellCover embedding center outerRadius threshold).card ≤
        ∑ j : Fin 4,
          (squareShellStrips embedding center outerRadius threshold j).card := by
    exact Finset.card_biUnion_le
  calc
    _ ≤ ((squareShellCover embedding center outerRadius threshold).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ j : Fin 4,
        ((squareShellStrips embedding center outerRadius threshold j).card : ℝ) := by
      exact_mod_cast hcoverNat
    _ ≤ ∑ _j : Fin 4, 12 * outerRadius * threshold := by
      apply Finset.sum_le_sum
      intro j _
      exact card_squareShellStrips_le embedding center outerRadius threshold
        hthreshold hdiameter j
    _ = 48 * outerRadius * threshold := by simp; ring

/--
One growth boundary is bounded by the exact geometric shell estimate plus the
actual long-interaction incidence counter over the inner square.
-/
theorem card_squareGrowthBoundary_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (hdiameter : 1 ≤ 2 * outerRadius) :
    ((squareGrowthBoundary P embedding center outerRadius threshold).selected.card : ℝ) ≤
      48 * outerRadius * threshold +
        ((∑ q ∈ squareQubits embedding center (outerRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
  let shell := squareQubits embedding center outerRadius \
    squareQubits embedding center (outerRadius - threshold)
  let outside := longOutsideNeighborsOf P embedding threshold
    (squareQubits embedding center (outerRadius - threshold))
  have hunionNat : (shell ∪ outside).card ≤ shell.card + outside.card :=
    Finset.card_union_le shell outside
  have houtside := card_longOutsideNeighborsOf_le_sum_counter P embedding threshold
    (squareQubits embedding center (outerRadius - threshold))
  calc
    _ ≤ (shell.card : ℝ) + (outside.card : ℝ) := by
      exact_mod_cast hunionNat
    _ ≤ 48 * outerRadius * threshold +
        ((∑ q ∈ squareQubits embedding center (outerRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
      gcongr
      · exact card_square_shell_le embedding center outerRadius threshold
          hthreshold hdiameter

/-- Leaving the one-threshold enlarged square forces Euclidean distance above the threshold. -/
theorem threshold_lt_distance_of_mem_inner_not_mem_outer
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ)
    {p q : ι}
    (hp : p ∈ squareQubits embedding center (outerRadius - threshold))
    (hq : q ∉ squareQubits embedding center outerRadius) :
    threshold < embedding.distance p q := by
  have hp' := (mem_squareQubits_iff embedding center (outerRadius - threshold) p).1 hp
  rcases hp' with ⟨⟨hplx, hpux⟩, ⟨hply, hpuy⟩⟩
  have hcoord :
      threshold < |(embedding.point p).1 - (embedding.point q).1| ∨
        threshold < |(embedding.point p).2 - (embedding.point q).2| := by
    by_cases hqxLower : center.1 - outerRadius ≤ (embedding.point q).1
    · by_cases hqxUpper : (embedding.point q).1 ≤ center.1 + outerRadius
      · by_cases hqyLower : center.2 - outerRadius ≤ (embedding.point q).2
        · by_cases hqyUpper : (embedding.point q).2 ≤ center.2 + outerRadius
          · exfalso
            exact hq ((mem_squareQubits_iff embedding center outerRadius q).2
              ⟨⟨hqxLower, hqxUpper⟩, ⟨hqyLower, hqyUpper⟩⟩)
          · right
            apply lt_abs.mpr
            right
            linarith
        · right
          apply lt_abs.mpr
          left
          linarith
      · left
        apply lt_abs.mpr
        right
        linarith
    · left
      apply lt_abs.mpr
      left
      linarith
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  rcases hcoord with hx | hy
  · have hxSq :
        ((embedding.point p).1 - (embedding.point q).1) ^ 2 ≤
          ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
            ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
        nlinarith [sq_nonneg ((embedding.point p).2 - (embedding.point q).2)]
    exact hx.trans_le (Real.abs_le_sqrt hxSq)
  · have hySq :
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 ≤
          ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
            ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
        nlinarith [sq_nonneg ((embedding.point p).1 - (embedding.point q).1)]
    exact hy.trans_le (Real.abs_le_sqrt hySq)

/--
Every actual fixed-generator outer-boundary qubit of the inner square is in the
computed growth boundary: shell qubits are included geometrically, and qubits
beyond the shell are included only after proving their interaction is long.
-/
theorem fixedGeneratorOuterBoundary_square_subset_growthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) :
    P.fixedGeneratorOuterBoundary
        ((squareSubsystem embedding center (outerRadius - threshold)).selected : Set ι) ⊆
      ((squareGrowthBoundary P embedding center outerRadius threshold).selected : Set ι) := by
  intro q hq
  rcases (P.mem_fixedGeneratorOuterBoundary_iff
      ((squareSubsystem embedding center (outerRadius - threshold)).selected : Set ι) q).1 hq with
    ⟨hqNotInner, p, hpInner, hpq⟩
  have hpInner' : p ∈ squareQubits embedding center (outerRadius - threshold) := by
    simpa [squareSubsystem] using hpInner
  have hqNotInner' : q ∉ squareQubits embedding center (outerRadius - threshold) := by
    simpa [squareSubsystem] using hqNotInner
  by_cases hqOuter : q ∈ squareQubits embedding center outerRadius
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hqOuter, hqNotInner'⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hqNotInner'⟩
    rw [mem_longNeighborsOf_iff]
    refine ⟨p, hpInner', hpq, ?_⟩
    exact (threshold_lt_distance_of_mem_inner_not_mem_outer
      embedding center outerRadius threshold hpInner' hqOuter).le

/-- The enlarged square lies in the union of the inner square and its computed boundary. -/
theorem squareSubsystem_subset_inner_union_growthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) :
    (squareSubsystem embedding center outerRadius).selected ⊆
      (unionSubsystem
        (squareSubsystem embedding center (outerRadius - threshold))
        (squareGrowthBoundary P embedding center outerRadius threshold)).selected := by
  intro q hq
  by_cases hqInner : q ∈ squareQubits embedding center (outerRadius - threshold)
  · exact Finset.mem_union_left _ hqInner
  · apply Finset.mem_union_right
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hq, hqInner⟩)

/--
One source-faithful growing-square step.  Semantic distance corrects the
computed shell/crossing boundary, #377 expands an already-correctable inner
square across that actual boundary, and #373 shrinks the union to the concrete
outer square.
-/
theorem exists_erasureRecovery_square_growth_step
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ) (outerRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hdiameter : 1 ≤ 2 * outerRadius)
    (hBoundarySmall :
      48 * outerRadius * threshold +
          ((∑ q ∈ squareQubits embedding center (outerRadius - threshold),
            P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryInner :
      ∃ recovery : QuantumChannel
          (squareSubsystem embedding center
            (outerRadius - threshold)).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (squareSubsystem embedding center
            (outerRadius - threshold)).complementSystem
          P.semanticCode
          (squareSubsystem embedding center
            (outerRadius - threshold)).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel
        (squareSubsystem embedding center outerRadius).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (squareSubsystem embedding center outerRadius).complementSystem
        P.semanticCode
        (squareSubsystem embedding center outerRadius).erasureChannelFromRegister recovery := by
  let inner := squareSubsystem embedding center (outerRadius - threshold)
  let boundary := squareGrowthBoundary P embedding center outerRadius threshold
  have hBoundaryCardReal : (boundary.selected.card : ℝ) < d :=
    (card_squareGrowthBoundary_le P embedding center outerRadius threshold
      hthreshold hdiameter).trans_lt hBoundarySmall
  have hBoundaryCard : boundary.selected.card < d := by
    exact_mod_cast hBoundaryCardReal
  obtain ⟨recoveryInner, hRecoveryInner'⟩ := hRecoveryInner
  obtain ⟨recoveryBoundary, hRecoveryBoundary⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance boundary hBoundaryCard
  have hOuterBoundary :
      P.fixedGeneratorOuterBoundary (inner.selected : Set ι) ⊆
        (boundary.selected : Set ι) := by
    simpa [inner, boundary] using
      fixedGeneratorOuterBoundary_square_subset_growthBoundary
        P embedding center outerRadius threshold
  obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
    exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
      P inner boundary recoveryInner recoveryBoundary
      (by simpa [inner] using hRecoveryInner')
      (by simpa [boundary,
        StabilizerCode.BinaryStabilizerPresentation.semanticCode] using
        hRecoveryBoundary)
      hOuterBoundary
  exact
    (exists_qudit_erasureRecovery_of_subset
      (quditSubsystemOfFinite (squareSubsystem embedding center outerRadius))
      (quditSubsystemOfFinite (unionSubsystem inner boundary))
      (by
        exact
          (squareSubsystem_subset_inner_union_growthBoundary
            P embedding center outerRadius threshold))
      P.semanticCode ⟨recoveryExpanded, hRecoveryExpanded⟩)

/-- Radius after a finite number of threshold-sized growing-square steps. -/
def squareGrowthRadius (baseRadius threshold : ℝ) (step : Nat) : ℝ :=
  baseRadius + step * threshold

@[simp]
theorem squareGrowthRadius_zero (baseRadius threshold : ℝ) :
    squareGrowthRadius baseRadius threshold 0 = baseRadius := by
  simp [squareGrowthRadius]

@[simp]
theorem squareGrowthRadius_succ_sub (baseRadius threshold : ℝ) (step : Nat) :
    squareGrowthRadius baseRadius threshold (step + 1) - threshold =
      squareGrowthRadius baseRadius threshold step := by
  simp [squareGrowthRadius]
  ring

/--
Finite recursion of the concrete growing-square step.  The indexed budget is
checked at every actual radius; no raw partition or prepackaged correctability
field is accepted.
-/
theorem exists_erasureRecovery_square_growth_iterate
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ) (baseRadius threshold : ℝ) (steps : Nat)
    (hthreshold : 1 ≤ threshold)
    (hdiameter : ∀ step, step ≤ steps →
      1 ≤ 2 * squareGrowthRadius baseRadius threshold step)
    (hBoundarySmall : ∀ step, step < steps →
      48 * squareGrowthRadius baseRadius threshold (step + 1) * threshold +
          ((∑ q ∈ squareQubits embedding center
              (squareGrowthRadius baseRadius threshold step),
            P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryBase :
      ∃ recovery : QuantumChannel
          (squareSubsystem embedding center baseRadius).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (squareSubsystem embedding center baseRadius).complementSystem
          P.semanticCode
          (squareSubsystem embedding center baseRadius).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel
        (squareSubsystem embedding center
          (squareGrowthRadius baseRadius threshold steps)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (squareSubsystem embedding center
          (squareGrowthRadius baseRadius threshold steps)).complementSystem
        P.semanticCode
        (squareSubsystem embedding center
          (squareGrowthRadius baseRadius threshold steps)).erasureChannelFromRegister recovery := by
  induction steps with
  | zero =>
      have hr : squareGrowthRadius baseRadius threshold 0 = baseRadius := by
        norm_num [squareGrowthRadius]
      rw [hr]
      exact hRecoveryBase
  | succ steps ih =>
      have hRecoveryPrevious := ih
        (fun step hstep => hdiameter step (hstep.trans (Nat.le_succ steps)))
        (fun step hstep => hBoundarySmall step (hstep.trans (Nat.lt_succ_self steps)))
      apply exists_erasureRecovery_square_growth_step
        P embedding d hDistance center
          (squareGrowthRadius baseRadius threshold (steps + 1)) threshold
          hthreshold (hdiameter (steps + 1) (by rfl))
          (by
            rw [squareGrowthRadius_succ_sub]
            exact hBoundarySmall steps (Nat.lt_succ_self steps))
      rw [squareGrowthRadius_succ_sub]
      exact hRecoveryPrevious

/-! ## Centered-rectangle growth

The source describes the growing-square argument after reducing a rectangle
to a square.  That reduction is not sound for a low-interaction rectangle:
enlarging it can introduce new long incidences that are not charged by the
rectangle's counter.  The following parallel construction grows an actual
centered rectangle.  Its two half-sides may differ, but every non-base step
expands all four sides by exactly the same long-interaction scale.
-/

/-- A closed axis-parallel rectangle described by its center and two
half-sides. -/
def centeredRectangle (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℝ) :
    Set (ℝ × ℝ) :=
  rectangle (center.1 - horizontalRadius, center.2 - verticalRadius)
    (center.1 + horizontalRadius, center.2 + verticalRadius)

/-- The actual qubits lying in a centered rectangle. -/
def centeredRectangleQubits (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℝ) : Finset ι :=
  embedding.qubitsInRectangle
    (center.1 - horizontalRadius, center.2 - verticalRadius)
    (center.1 + horizontalRadius, center.2 + verticalRadius)

/-- The finite subsystem selected by a centered rectangle. -/
def centeredRectangleSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℝ) : FiniteSubsystem ι :=
  ⟨centeredRectangleQubits embedding center horizontalRadius verticalRadius⟩

@[simp]
theorem mem_centeredRectangleQubits_iff (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℝ) (q : ι) :
    q ∈ centeredRectangleQubits embedding center horizontalRadius verticalRadius ↔
      embedding.point q ∈ centeredRectangle center horizontalRadius verticalRadius := by
  simp [centeredRectangleQubits, centeredRectangle]

/-- The computed boundary of one simultaneous four-sided rectangle-growth
step.  Outside endpoints are included only when the corresponding interaction
is actually long at `threshold`. -/
def centeredRectangleGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ) : FiniteSubsystem ι :=
  ⟨(centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
      centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
        (outerVerticalRadius - threshold)) ∪
    longOutsideNeighborsOf P embedding threshold
      (centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
        (outerVerticalRadius - threshold))⟩

/-- The four explicit strips covering the shell of a simultaneous
four-sided rectangle-growth step. -/
def centeredRectangleShellStrips (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    Fin 4 → Finset ι
  | 0 => embedding.qubitsInRectangle
      (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
      (center.1 - outerHorizontalRadius + threshold, center.2 + outerVerticalRadius)
  | 1 => embedding.qubitsInRectangle
      (center.1 + outerHorizontalRadius - threshold, center.2 - outerVerticalRadius)
      (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)
  | 2 => embedding.qubitsInRectangle
      (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
      (center.1 + outerHorizontalRadius, center.2 - outerVerticalRadius + threshold)
  | 3 => embedding.qubitsInRectangle
      (center.1 - outerHorizontalRadius, center.2 + outerVerticalRadius - threshold)
      (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)

def centeredRectangleShellCover (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    Finset ι :=
  Finset.univ.biUnion
    (centeredRectangleShellStrips embedding center outerHorizontalRadius outerVerticalRadius
      threshold)

/-- The actual geometric shell lies in its four explicit packing strips. -/
theorem centeredRectangle_shell_subset_shellCover
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold) ⊆
      centeredRectangleShellCover embedding center outerHorizontalRadius outerVerticalRadius
        threshold := by
  intro q hq
  rcases Finset.mem_sdiff.mp hq with ⟨hqOuter, hqNotInner⟩
  have hOuter := (mem_centeredRectangleQubits_iff embedding center
    outerHorizontalRadius outerVerticalRadius q).1 hqOuter
  rcases hOuter with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  by_contra hqNotCover
  have h0 : q ∉ centeredRectangleShellStrips embedding center
      outerHorizontalRadius outerVerticalRadius threshold 0 := by
    exact fun h => hqNotCover (Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, h⟩)
  have h1 : q ∉ centeredRectangleShellStrips embedding center
      outerHorizontalRadius outerVerticalRadius threshold 1 := by
    exact fun h => hqNotCover (Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, h⟩)
  have h2 : q ∉ centeredRectangleShellStrips embedding center
      outerHorizontalRadius outerVerticalRadius threshold 2 := by
    exact fun h => hqNotCover (Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, h⟩)
  have h3 : q ∉ centeredRectangleShellStrips embedding center
      outerHorizontalRadius outerVerticalRadius threshold 3 := by
    exact fun h => hqNotCover (Finset.mem_biUnion.mpr ⟨3, Finset.mem_univ _, h⟩)
  have hxLower : center.1 - (outerHorizontalRadius - threshold) ≤
      (embedding.point q).1 := by
    by_contra h
    apply h0
    rw [centeredRectangleShellStrips, UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxl, by linarith [le_of_not_ge h]⟩, ⟨hyl, hyu⟩⟩
  have hxUpper : (embedding.point q).1 ≤ center.1 +
      (outerHorizontalRadius - threshold) := by
    by_contra h
    apply h1
    rw [centeredRectangleShellStrips, UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨by linarith [le_of_not_ge h], hxu⟩, ⟨hyl, hyu⟩⟩
  have hyLower : center.2 - (outerVerticalRadius - threshold) ≤
      (embedding.point q).2 := by
    by_contra h
    apply h2
    rw [centeredRectangleShellStrips, UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxl, hxu⟩, ⟨hyl, by linarith [le_of_not_ge h]⟩⟩
  have hyUpper : (embedding.point q).2 ≤ center.2 +
      (outerVerticalRadius - threshold) := by
    by_contra h
    apply h3
    rw [centeredRectangleShellStrips, UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxl, hxu⟩, ⟨by linarith [le_of_not_ge h], hyu⟩⟩
  exact hqNotInner ((mem_centeredRectangleQubits_iff embedding center
    (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold) q).2
      ⟨⟨hxLower, hxUpper⟩, ⟨hyLower, hyUpper⟩⟩)

/- The two vertical shell strips obey the two-dimensional packing estimate. -/
theorem card_centeredRectangleShellStrip_zero_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleShellStrips embedding center outerHorizontalRadius outerVerticalRadius
      threshold 0).card : ℝ) ≤ 12 * outerVerticalRadius * threshold := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
    (center.1 - outerHorizontalRadius + threshold, center.2 + outerVerticalRadius)
    (by simpa using hthreshold) (by linarith)
  change ((embedding.qubitsInRectangle
    (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
    (center.1 - outerHorizontalRadius + threshold, center.2 + outerVerticalRadius)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * (threshold * (outerVerticalRadius + outerVerticalRadius)) := by simpa using h
    _ = _ := by ring

theorem card_centeredRectangleShellStrip_one_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleShellStrips embedding center outerHorizontalRadius outerVerticalRadius
      threshold 1).card : ℝ) ≤ 12 * outerVerticalRadius * threshold := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (center.1 + outerHorizontalRadius - threshold, center.2 - outerVerticalRadius)
    (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)
    (by simpa using hthreshold) (by linarith)
  change ((embedding.qubitsInRectangle
    (center.1 + outerHorizontalRadius - threshold, center.2 - outerVerticalRadius)
    (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * (threshold * (outerVerticalRadius + outerVerticalRadius)) := by simpa using h
    _ = _ := by ring

/- The two horizontal shell strips obey the two-dimensional packing estimate. -/
theorem card_centeredRectangleShellStrip_two_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius) :
    ((centeredRectangleShellStrips embedding center outerHorizontalRadius outerVerticalRadius
      threshold 2).card : ℝ) ≤ 12 * outerHorizontalRadius * threshold := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
    (center.1 + outerHorizontalRadius, center.2 - outerVerticalRadius + threshold)
    (by linarith) (by simpa using hthreshold)
  change ((embedding.qubitsInRectangle
    (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
    (center.1 + outerHorizontalRadius, center.2 - outerVerticalRadius + threshold)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * ((outerHorizontalRadius + outerHorizontalRadius) * threshold) := by simpa using h
    _ = _ := by ring

theorem card_centeredRectangleShellStrip_three_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius) :
    ((centeredRectangleShellStrips embedding center outerHorizontalRadius outerVerticalRadius
      threshold 3).card : ℝ) ≤ 12 * outerHorizontalRadius * threshold := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (center.1 - outerHorizontalRadius, center.2 + outerVerticalRadius - threshold)
    (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)
    (by linarith) (by simpa using hthreshold)
  change ((embedding.qubitsInRectangle
    (center.1 - outerHorizontalRadius, center.2 + outerVerticalRadius - threshold)
    (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * ((outerHorizontalRadius + outerHorizontalRadius) * threshold) := by simpa using h
    _ = _ := by ring

/-
The four specialized forms above deliberately avoid an `if` indexed by `Fin 4`:
the identities are consumed directly in the perimeter sum below and preserve
the orientation of the exact thin packing estimate.
-/
/-
  · have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
      (center.1 - outerHorizontalRadius + threshold, center.2 + outerVerticalRadius)
      (by simpa using hthreshold) (by linarith)
    change ((embedding.qubitsInRectangle
      (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
      (center.1 - outerHorizontalRadius + threshold, center.2 + outerVerticalRadius)).card : ℝ) ≤ _
    simp only [Fin.isValue, or_self, ↓reduceIte]
    calc
      _ ≤ 6 * (threshold * (outerVerticalRadius + outerVerticalRadius)) := by simpa using h
      _ = _ := by ring
  · have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (center.1 + outerHorizontalRadius - threshold, center.2 - outerVerticalRadius)
      (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)
      (by simpa using hthreshold) (by linarith)
    change ((embedding.qubitsInRectangle
      (center.1 + outerHorizontalRadius - threshold, center.2 - outerVerticalRadius)
      (center.1 + outerHorizontalRadius, center.2 + outerVerticalRadius)).card : ℝ) ≤ _
    simp only [Fin.isValue, or_true, ↓reduceIte]
    calc
      _ ≤ 6 * (threshold * (outerVerticalRadius + outerVerticalRadius)) := by simpa using h
      _ = _ := by ring
  · have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
      (center.1 + outerHorizontalRadius, center.2 - outerVerticalRadius + threshold)
      (by linarith) (by simpa using hthreshold)
    change ((embedding.qubitsInRectangle
      (center.1 - outerHorizontalRadius, center.2 - outerVerticalRadius)
      (center.1 + outerHorizontalRadius, center.2 - outerVerticalRadius + threshold)).card : ℝ) ≤ _
    simp only [Fin.isValue, false_or, ↓reduceIte]
    calc
      _ ≤ 6 * ((outerHorizontalRadius + outerHorizontalRadius) * threshold) := by simpa using h
      _ = _ := by ring
-/

/-- The shell of a simultaneously grown rectangle has the perimeter-scale
packing bound needed by Dai--Li's growing-region argument. -/
theorem card_centeredRectangle_shell_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).card : ℝ) ≤
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold := by
  have hsubset := centeredRectangle_shell_subset_shellCover embedding center
    outerHorizontalRadius outerVerticalRadius threshold
  have hcoverNat :
      (centeredRectangleShellCover embedding center outerHorizontalRadius outerVerticalRadius
        threshold).card ≤
        ∑ j : Fin 4,
          (centeredRectangleShellStrips embedding center outerHorizontalRadius
            outerVerticalRadius threshold j).card :=
    Finset.card_biUnion_le
  calc
    _ ≤ ((centeredRectangleShellCover embedding center outerHorizontalRadius outerVerticalRadius
      threshold).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ j : Fin 4,
        ((centeredRectangleShellStrips embedding center outerHorizontalRadius
          outerVerticalRadius threshold j).card : ℝ) := by exact_mod_cast hcoverNat
    _ ≤ 2 * (12 * outerVerticalRadius * threshold) +
        2 * (12 * outerHorizontalRadius * threshold) := by
      rw [Fin.sum_univ_four]
      nlinarith [card_centeredRectangleShellStrip_zero_le embedding center
        outerHorizontalRadius outerVerticalRadius threshold hthreshold hVertical,
        card_centeredRectangleShellStrip_one_le embedding center
          outerHorizontalRadius outerVerticalRadius threshold hthreshold hVertical,
        card_centeredRectangleShellStrip_two_le embedding center
          outerHorizontalRadius outerVerticalRadius threshold hthreshold hHorizontal,
        card_centeredRectangleShellStrip_three_le embedding center
          outerHorizontalRadius outerVerticalRadius threshold hthreshold hHorizontal]
    _ = _ := by ring

/-- A centered rectangle with smaller half-sides selects a subsystem of the
corresponding larger rectangle. -/
theorem centeredRectangleQubits_subset_of_radii_le
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    {innerHorizontalRadius outerHorizontalRadius innerVerticalRadius outerVerticalRadius : ℝ}
    (hHorizontal : innerHorizontalRadius ≤ outerHorizontalRadius)
    (hVertical : innerVerticalRadius ≤ outerVerticalRadius) :
    centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius ⊆
      centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius := by
  intro q hq
  rcases (mem_centeredRectangleQubits_iff embedding center
    innerHorizontalRadius innerVerticalRadius q).1 hq with
    ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  apply (mem_centeredRectangleQubits_iff embedding center
    outerHorizontalRadius outerVerticalRadius q).2
  constructor <;> constructor <;> linarith

/-- Leaving the simultaneously enlarged rectangle forces Euclidean distance
strictly above the common growth threshold. -/
theorem threshold_lt_distance_of_mem_inner_not_mem_outer_centeredRectangle
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    {p q : ι}
    (hp : p ∈ centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold))
    (hq : q ∉ centeredRectangleQubits embedding center
      outerHorizontalRadius outerVerticalRadius) :
    threshold < embedding.distance p q := by
  have hp' := (mem_centeredRectangleQubits_iff embedding center
    (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold) p).1 hp
  rcases hp' with ⟨⟨hplx, hpux⟩, ⟨hply, hpuy⟩⟩
  have hcoord :
      threshold < |(embedding.point p).1 - (embedding.point q).1| ∨
        threshold < |(embedding.point p).2 - (embedding.point q).2| := by
    by_cases hqxLower : center.1 - outerHorizontalRadius ≤ (embedding.point q).1
    · by_cases hqxUpper : (embedding.point q).1 ≤ center.1 + outerHorizontalRadius
      · by_cases hqyLower : center.2 - outerVerticalRadius ≤ (embedding.point q).2
        · by_cases hqyUpper : (embedding.point q).2 ≤ center.2 + outerVerticalRadius
          · exfalso
            exact hq ((mem_centeredRectangleQubits_iff embedding center
              outerHorizontalRadius outerVerticalRadius q).2
              ⟨⟨hqxLower, hqxUpper⟩, ⟨hqyLower, hqyUpper⟩⟩)
          · right
            apply lt_abs.mpr
            right
            linarith
        · right
          apply lt_abs.mpr
          left
          linarith
      · left
        apply lt_abs.mpr
        right
        linarith
    · left
      apply lt_abs.mpr
      left
      linarith
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  rcases hcoord with hx | hy
  · have hxSq :
        ((embedding.point p).1 - (embedding.point q).1) ^ 2 ≤
          ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
            ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
        nlinarith [sq_nonneg ((embedding.point p).2 - (embedding.point q).2)]
    exact hx.trans_le (Real.abs_le_sqrt hxSq)
  · have hySq :
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 ≤
          ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
            ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
        nlinarith [sq_nonneg ((embedding.point p).1 - (embedding.point q).1)]
    exact hy.trans_le (Real.abs_le_sqrt hySq)

/-- The computed rectangle-growth boundary contains every actual
fixed-generator outer-boundary qubit of the inner rectangle. -/
theorem fixedGeneratorOuterBoundary_centeredRectangle_subset_growthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    P.fixedGeneratorOuterBoundary
        ((centeredRectangleSubsystem embedding center
          (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).selected : Set ι) ⊆
      ((centeredRectangleGrowthBoundary P embedding center outerHorizontalRadius
        outerVerticalRadius threshold).selected : Set ι) := by
  intro q hq
  rcases (P.mem_fixedGeneratorOuterBoundary_iff
      ((centeredRectangleSubsystem embedding center
        (outerHorizontalRadius - threshold)
        (outerVerticalRadius - threshold)).selected : Set ι) q).1 hq with
    ⟨hqNotInner, p, hpInner, hpq⟩
  have hpInner' : p ∈ centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold) := by
    simpa [centeredRectangleSubsystem] using hpInner
  have hqNotInner' : q ∉ centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold) := by
    simpa [centeredRectangleSubsystem] using hqNotInner
  by_cases hqOuter : q ∈ centeredRectangleQubits embedding center
      outerHorizontalRadius outerVerticalRadius
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hqOuter, hqNotInner'⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hqNotInner'⟩
    rw [mem_longNeighborsOf_iff]
    refine ⟨p, hpInner', hpq, ?_⟩
    exact (threshold_lt_distance_of_mem_inner_not_mem_outer_centeredRectangle
      embedding center outerHorizontalRadius outerVerticalRadius threshold hpInner' hqOuter).le

/-- The grown rectangle is selected by the union of the prior rectangle and
the computed shell/crossing boundary. -/
theorem centeredRectangleSubsystem_subset_inner_union_growthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    (centeredRectangleSubsystem embedding center outerHorizontalRadius
      outerVerticalRadius).selected ⊆
      (unionSubsystem
        (centeredRectangleSubsystem embedding center
          (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold))
        (centeredRectangleGrowthBoundary P embedding center outerHorizontalRadius
          outerVerticalRadius threshold)).selected := by
  intro q hq
  by_cases hqInner : q ∈ centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold)
  · exact Finset.mem_union_left _ hqInner
  · apply Finset.mem_union_right
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hq, hqInner⟩)

/-- The actual rectangle-growth boundary is controlled by the four-strip
packing estimate and the true long-incidence counter of the inner rectangle. -/
theorem card_centeredRectangleGrowthBoundary_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleGrowthBoundary P embedding center outerHorizontalRadius
      outerVerticalRadius threshold).selected.card : ℝ) ≤
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
  let shell := centeredRectangleQubits embedding center outerHorizontalRadius
    outerVerticalRadius \ centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold)
  let outside := longOutsideNeighborsOf P embedding threshold
    (centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold))
  have hUnionNat : (shell ∪ outside).card ≤ shell.card + outside.card :=
    Finset.card_union_le shell outside
  have hOutside := card_longOutsideNeighborsOf_le_sum_counter P embedding threshold
    (centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold))
  calc
    _ ≤ (shell.card : ℝ) + (outside.card : ℝ) := by exact_mod_cast hUnionNat
    _ ≤ 24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
      gcongr
      exact card_centeredRectangle_shell_le embedding center outerHorizontalRadius
        outerVerticalRadius threshold hthreshold hHorizontal hVertical

/-- One source-faithful actual rectangle-growth step.  The boundary recovery
comes from semantic distance, then #377 expands it over the concrete
fixed-generator boundary, and #373 restricts back to the target rectangle. -/
theorem exists_erasureRecovery_centeredRectangle_growth_step
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ) (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hVertical : 1 ≤ 2 * outerVerticalRadius)
    (hBoundarySmall :
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
          ((∑ q ∈ centeredRectangleQubits embedding center
            (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold),
            P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryInner :
      ∃ recovery : QuantumChannel
          (centeredRectangleSubsystem embedding center
            (outerHorizontalRadius - threshold)
            (outerVerticalRadius - threshold)).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (centeredRectangleSubsystem embedding center
            (outerHorizontalRadius - threshold)
            (outerVerticalRadius - threshold)).complementSystem
          P.semanticCode
          (centeredRectangleSubsystem embedding center
            (outerHorizontalRadius - threshold)
            (outerVerticalRadius - threshold)).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        P.semanticCode
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).erasureChannelFromRegister recovery := by
  let inner := centeredRectangleSubsystem embedding center
    (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold)
  let boundary := centeredRectangleGrowthBoundary P embedding center
    outerHorizontalRadius outerVerticalRadius threshold
  have hBoundaryCardReal : (boundary.selected.card : ℝ) < d :=
    (card_centeredRectangleGrowthBoundary_le P embedding center outerHorizontalRadius
      outerVerticalRadius threshold hthreshold hHorizontal hVertical).trans_lt hBoundarySmall
  have hBoundaryCard : boundary.selected.card < d := by exact_mod_cast hBoundaryCardReal
  obtain ⟨recoveryInner, hRecoveryInner'⟩ := hRecoveryInner
  obtain ⟨recoveryBoundary, hRecoveryBoundary⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance boundary hBoundaryCard
  have hOuterBoundary :
      P.fixedGeneratorOuterBoundary (inner.selected : Set ι) ⊆
        (boundary.selected : Set ι) := by
    simpa [inner, boundary] using
      fixedGeneratorOuterBoundary_centeredRectangle_subset_growthBoundary
        P embedding center outerHorizontalRadius outerVerticalRadius threshold
  obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
    exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
      P inner boundary recoveryInner recoveryBoundary
      (by simpa [inner] using hRecoveryInner')
      (by simpa [boundary,
        StabilizerCode.BinaryStabilizerPresentation.semanticCode] using hRecoveryBoundary)
      hOuterBoundary
  exact
    (exists_qudit_erasureRecovery_of_subset
      (quditSubsystemOfFinite (centeredRectangleSubsystem embedding center
        outerHorizontalRadius outerVerticalRadius))
      (quditSubsystemOfFinite (unionSubsystem inner boundary))
      (by exact
        (centeredRectangleSubsystem_subset_inner_union_growthBoundary
          P embedding center outerHorizontalRadius outerVerticalRadius threshold))
      P.semanticCode ⟨recoveryExpanded, hRecoveryExpanded⟩)

/-- The one-threshold collar immediately outside a target rectangle.  It is
needed when a general rectangle-growth step changes its two half-sides by
different amounts: short interactions can then leave the target through an
ungrown side and must be charged explicitly rather than treated as long. -/
def centeredRectangleExternalCollar (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (outerHorizontalRadius outerVerticalRadius threshold : ℝ) : Finset ι :=
  centeredRectangleQubits embedding center (outerHorizontalRadius + threshold)
    (outerVerticalRadius + threshold) \
      centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius

/-- The boundary for one general rectangle step: the newly covered shell, the
short-range collar just outside the target, and actual threshold-long outside
neighbors of the previous rectangle. -/
def centeredRectangleGeneralGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ) : FiniteSubsystem ι :=
  ⟨((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
      centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius) ∪
    centeredRectangleExternalCollar embedding center outerHorizontalRadius outerVerticalRadius
      threshold) ∪
    longOutsideNeighborsOf P embedding threshold
      (centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius)⟩

/-- A point in the target rectangle but outside an inner rectangle that is at
most one threshold inset lies in the standard target shell. -/
theorem centeredRectangle_shell_subset_of_inset
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hHorizontalInner : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInner : outerVerticalRadius - threshold ≤ innerVerticalRadius) :
    centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius ⊆
      centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold) := by
  intro q hq
  refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hq).1, ?_⟩
  intro hqDeep
  exact (Finset.mem_sdiff.mp hq).2
    (centeredRectangleQubits_subset_of_radii_le embedding center
      hHorizontalInner hVerticalInner hqDeep)

/-- Leaving the target together with its one-threshold collar forces a
strictly threshold-long geometric separation from every point in the target. -/
theorem threshold_lt_distance_of_mem_target_not_mem_collar
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    {p q : ι}
    (hp : p ∈ centeredRectangleQubits embedding center
      outerHorizontalRadius outerVerticalRadius)
    (hq : q ∉ centeredRectangleQubits embedding center
      (outerHorizontalRadius + threshold) (outerVerticalRadius + threshold)) :
    threshold < embedding.distance p q := by
  have hp' := (mem_centeredRectangleQubits_iff embedding center
    outerHorizontalRadius outerVerticalRadius p).1 hp
  rcases hp' with ⟨⟨hplx, hpux⟩, ⟨hply, hpuy⟩⟩
  have hcoord :
      threshold < |(embedding.point p).1 - (embedding.point q).1| ∨
        threshold < |(embedding.point p).2 - (embedding.point q).2| := by
    by_cases hqxLower : center.1 - (outerHorizontalRadius + threshold) ≤
        (embedding.point q).1
    · by_cases hqxUpper : (embedding.point q).1 ≤
          center.1 + (outerHorizontalRadius + threshold)
      · by_cases hqyLower : center.2 - (outerVerticalRadius + threshold) ≤
          (embedding.point q).2
        · by_cases hqyUpper : (embedding.point q).2 ≤
            center.2 + (outerVerticalRadius + threshold)
          · exfalso
            exact hq ((mem_centeredRectangleQubits_iff embedding center
              (outerHorizontalRadius + threshold)
              (outerVerticalRadius + threshold) q).2
              ⟨⟨hqxLower, hqxUpper⟩, ⟨hqyLower, hqyUpper⟩⟩)
          · right
            apply lt_abs.mpr
            right
            linarith
        · right
          apply lt_abs.mpr
          left
          linarith
      · left
        apply lt_abs.mpr
        right
        linarith
    · left
      apply lt_abs.mpr
      left
      linarith
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  rcases hcoord with hx | hy
  · have hxSq :
        ((embedding.point p).1 - (embedding.point q).1) ^ 2 ≤
          ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
            ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
        nlinarith [sq_nonneg ((embedding.point p).2 - (embedding.point q).2)]
    exact hx.trans_le (Real.abs_le_sqrt hxSq)
  · have hySq :
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 ≤
          ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
            ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
        nlinarith [sq_nonneg ((embedding.point p).1 - (embedding.point q).1)]
    exact hy.trans_le (Real.abs_le_sqrt hySq)

/-- The computed general boundary contains every fixed-generator outer
boundary qubit of the previous rectangle.  Short crossings are caught by the
explicit collar; only genuinely long crossings use the interaction counter. -/
theorem fixedGeneratorOuterBoundary_centeredRectangle_subset_generalGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hHorizontal : innerHorizontalRadius ≤ outerHorizontalRadius)
    (hVertical : innerVerticalRadius ≤ outerVerticalRadius) :
    P.fixedGeneratorOuterBoundary
        ((centeredRectangleSubsystem embedding center innerHorizontalRadius
          innerVerticalRadius).selected : Set ι) ⊆
      ((centeredRectangleGeneralGrowthBoundary P embedding center
        innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
        outerVerticalRadius threshold).selected : Set ι) := by
  intro q hq
  rcases (P.mem_fixedGeneratorOuterBoundary_iff
      ((centeredRectangleSubsystem embedding center innerHorizontalRadius
        innerVerticalRadius).selected : Set ι) q).1 hq with
    ⟨hqNotInner, p, hpInner, hpq⟩
  have hpInner' : p ∈ centeredRectangleQubits embedding center
      innerHorizontalRadius innerVerticalRadius := by
    simpa [centeredRectangleSubsystem] using hpInner
  have hqNotInner' : q ∉ centeredRectangleQubits embedding center
      innerHorizontalRadius innerVerticalRadius := by
    simpa [centeredRectangleSubsystem] using hqNotInner
  have hpOuter : p ∈ centeredRectangleQubits embedding center
      outerHorizontalRadius outerVerticalRadius :=
    centeredRectangleQubits_subset_of_radii_le embedding center hHorizontal hVertical hpInner'
  by_cases hqCollar : q ∈ centeredRectangleQubits embedding center
      (outerHorizontalRadius + threshold) (outerVerticalRadius + threshold)
  · apply Finset.mem_union_left
    by_cases hqOuter : q ∈ centeredRectangleQubits embedding center
        outerHorizontalRadius outerVerticalRadius
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hqOuter, hqNotInner'⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hqCollar, hqOuter⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hqNotInner'⟩
    rw [mem_longNeighborsOf_iff]
    refine ⟨p, hpInner', hpq, ?_⟩
    exact (threshold_lt_distance_of_mem_target_not_mem_collar embedding center
      outerHorizontalRadius outerVerticalRadius threshold hpOuter hqCollar).le

/-- The target rectangle is selected by the previous rectangle and the
computed general boundary. -/
theorem centeredRectangleSubsystem_subset_inner_union_generalGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ) :
    (centeredRectangleSubsystem embedding center outerHorizontalRadius
      outerVerticalRadius).selected ⊆
      (unionSubsystem
        (centeredRectangleSubsystem embedding center innerHorizontalRadius innerVerticalRadius)
        (centeredRectangleGeneralGrowthBoundary P embedding center
          innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
          outerVerticalRadius threshold)).selected := by
  intro q hq
  by_cases hqInner : q ∈ centeredRectangleQubits embedding center
      innerHorizontalRadius innerVerticalRadius
  · exact Finset.mem_union_left _ hqInner
  · apply Finset.mem_union_right
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨hq, hqInner⟩))

/-- The general rectangle boundary has a concrete finite cardinality bound.
The extra `48 * threshold^2` relative to simultaneous growth is the explicit
short-range exterior collar, so no crossing interaction is silently dropped. -/
theorem card_centeredRectangleGeneralGrowthBoundary_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hThreshold : 1 ≤ threshold)
    (hOuterHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hOuterVertical : 1 ≤ 2 * outerVerticalRadius)
    (hHorizontalInset : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInset : outerVerticalRadius - threshold ≤ innerVerticalRadius) :
    ((centeredRectangleGeneralGrowthBoundary P embedding center
      innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold).selected.card : ℝ) ≤
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          innerHorizontalRadius innerVerticalRadius,
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
  let newShell := centeredRectangleQubits embedding center
    outerHorizontalRadius outerVerticalRadius \
      centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius
  let collar := centeredRectangleExternalCollar embedding center
    outerHorizontalRadius outerVerticalRadius threshold
  let longOutside := longOutsideNeighborsOf P embedding threshold
    (centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius)
  have hNewShellSubset := centeredRectangle_shell_subset_of_inset embedding center
    innerHorizontalRadius innerVerticalRadius outerHorizontalRadius outerVerticalRadius
    threshold hHorizontalInset hVerticalInset
  have hNewShellReal :
      ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius).card : ℝ) ≤
      ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hNewShellSubset
  have hNewShell' : (newShell.card : ℝ) ≤
      ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).card : ℝ) := by
    simpa [newShell] using hNewShellReal
  have hNewShell : (newShell.card : ℝ) ≤
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold := by
    exact hNewShell'.trans
      (card_centeredRectangle_shell_le embedding center
        outerHorizontalRadius outerVerticalRadius threshold hThreshold
        hOuterHorizontal hOuterVertical)
  have hExpandedHorizontal : 1 ≤ 2 * (outerHorizontalRadius + threshold) := by
    nlinarith
  have hExpandedVertical : 1 ≤ 2 * (outerVerticalRadius + threshold) := by
    nlinarith
  have hCollarRaw := card_centeredRectangle_shell_le embedding center
    (outerHorizontalRadius + threshold) (outerVerticalRadius + threshold)
    threshold hThreshold hExpandedHorizontal hExpandedVertical
  have hCollar : (collar.card : ℝ) ≤
      24 * ((outerHorizontalRadius + threshold) +
        (outerVerticalRadius + threshold)) * threshold := by
    dsimp [collar, centeredRectangleExternalCollar]
    convert hCollarRaw using 1 <;> ring
  have hLong : (longOutside.card : ℝ) ≤
      ((∑ q ∈ centeredRectangleQubits embedding center
        innerHorizontalRadius innerVerticalRadius,
        P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
    dsimp [longOutside]
    exact_mod_cast card_longOutsideNeighborsOf_le_sum_counter P embedding threshold
      (centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius)
  have hUnionNat :
      ((newShell ∪ collar) ∪ longOutside).card ≤
        newShell.card + collar.card + longOutside.card := by
    calc
      _ ≤ (newShell ∪ collar).card + longOutside.card := Finset.card_union_le _ _
      _ ≤ (newShell.card + collar.card) + longOutside.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by omega
  have hUnion :
      (((newShell ∪ collar) ∪ longOutside).card : ℝ) ≤
        (newShell.card : ℝ) + (collar.card : ℝ) + (longOutside.card : ℝ) := by
    exact_mod_cast hUnionNat
  change (((newShell ∪ collar) ∪ longOutside).card : ℝ) ≤ _
  calc
    _ ≤ (newShell.card : ℝ) + (collar.card : ℝ) + (longOutside.card : ℝ) := hUnion
    _ ≤ 24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
          24 * ((outerHorizontalRadius + threshold) +
            (outerVerticalRadius + threshold)) * threshold +
          ((∑ q ∈ centeredRectangleQubits embedding center
            innerHorizontalRadius innerVerticalRadius,
            P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
      linarith
    _ = _ := by ring

/-- One actual rectangle-growth step with independently moving half-sides.
It constructs the boundary recovery from semantic distance, applies #377 to
the exact fixed-generator outer boundary, then applies #373 to the target
rectangle. -/
theorem exists_erasureRecovery_centeredRectangle_general_growth_step
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hThreshold : 1 ≤ threshold)
    (hOuterHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hOuterVertical : 1 ≤ 2 * outerVerticalRadius)
    (hHorizontal : innerHorizontalRadius ≤ outerHorizontalRadius)
    (hVertical : innerVerticalRadius ≤ outerVerticalRadius)
    (hHorizontalInset : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInset : outerVerticalRadius - threshold ≤ innerVerticalRadius)
    (hBoundarySmall :
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          innerHorizontalRadius innerVerticalRadius,
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryInner :
      ∃ recovery : QuantumChannel
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).complementSystem
          P.semanticCode
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        P.semanticCode
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).erasureChannelFromRegister recovery := by
  let inner := centeredRectangleSubsystem embedding center
    innerHorizontalRadius innerVerticalRadius
  let boundary := centeredRectangleGeneralGrowthBoundary P embedding center
    innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
    outerVerticalRadius threshold
  have hBoundaryCardReal : (boundary.selected.card : ℝ) < d :=
    (card_centeredRectangleGeneralGrowthBoundary_le P embedding center
      innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold hThreshold hOuterHorizontal hOuterVertical
      hHorizontalInset hVerticalInset).trans_lt hBoundarySmall
  have hBoundaryCard : boundary.selected.card < d := by
    exact_mod_cast hBoundaryCardReal
  obtain ⟨recoveryInner, hRecoveryInner'⟩ := hRecoveryInner
  obtain ⟨recoveryBoundary, hRecoveryBoundary⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance boundary hBoundaryCard
  have hOuterBoundary :
      P.fixedGeneratorOuterBoundary (inner.selected : Set ι) ⊆
        (boundary.selected : Set ι) := by
    simpa [inner, boundary] using
      fixedGeneratorOuterBoundary_centeredRectangle_subset_generalGrowthBoundary
        P embedding center innerHorizontalRadius innerVerticalRadius
          outerHorizontalRadius outerVerticalRadius threshold hHorizontal hVertical
  obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
    exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
      P inner boundary recoveryInner recoveryBoundary
      (by simpa [inner] using hRecoveryInner')
      (by simpa [boundary,
        StabilizerCode.BinaryStabilizerPresentation.semanticCode] using hRecoveryBoundary)
      hOuterBoundary
  exact
    (exists_qudit_erasureRecovery_of_subset
      (quditSubsystemOfFinite (centeredRectangleSubsystem embedding center
        outerHorizontalRadius outerVerticalRadius))
      (quditSubsystemOfFinite (unionSubsystem inner boundary))
      (by exact
        (centeredRectangleSubsystem_subset_inner_union_generalGrowthBoundary
          P embedding center innerHorizontalRadius innerVerticalRadius
            outerHorizontalRadius outerVerticalRadius threshold))
      P.semanticCode ⟨recoveryExpanded, hRecoveryExpanded⟩)

/-- Finite iteration of independently moving rectangle half-sides.  The
caller provides only geometric/numerical inequalities and a distance-small
base; every CPTP witness, including every intermediate boundary recovery, is
constructed internally. -/
theorem exists_erasureRecovery_centeredRectangle_general_growth_iterate
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℕ → ℝ)
    (threshold : ℝ) (steps : ℕ) (hThreshold : 1 ≤ threshold)
    (hHorizontalDiameter : ∀ step, step ≤ steps →
      1 ≤ 2 * horizontalRadius step)
    (hVerticalDiameter : ∀ step, step ≤ steps →
      1 ≤ 2 * verticalRadius step)
    (hHorizontalMonotone : ∀ step, step < steps →
      horizontalRadius step ≤ horizontalRadius (step + 1))
    (hVerticalMonotone : ∀ step, step < steps →
      verticalRadius step ≤ verticalRadius (step + 1))
    (hHorizontalInset : ∀ step, step < steps →
      horizontalRadius (step + 1) - threshold ≤ horizontalRadius step)
    (hVerticalInset : ∀ step, step < steps →
      verticalRadius (step + 1) - threshold ≤ verticalRadius step)
    (hBoundarySmall : ∀ step, step < steps →
      48 * (horizontalRadius (step + 1) + verticalRadius (step + 1) + threshold) *
          threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          (horizontalRadius step) (verticalRadius step),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hBaseCard : (centeredRectangleQubits embedding center
      (horizontalRadius 0) (verticalRadius 0)).card < d) :
    ∃ recovery : QuantumChannel
        (centeredRectangleSubsystem embedding center
          (horizontalRadius steps) (verticalRadius steps)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (centeredRectangleSubsystem embedding center
          (horizontalRadius steps) (verticalRadius steps)).complementSystem
        P.semanticCode
        (centeredRectangleSubsystem embedding center
          (horizontalRadius steps) (verticalRadius steps)).erasureChannelFromRegister
          recovery := by
  induction steps with
  | zero =>
      exact semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
        (centeredRectangleSubsystem embedding center (horizontalRadius 0) (verticalRadius 0))
        (by simpa [centeredRectangleSubsystem] using hBaseCard)
  | succ steps ih =>
      have hRecoveryPrevious := ih
        (fun step hstep => hHorizontalDiameter step (hstep.trans (Nat.le_succ steps)))
        (fun step hstep => hVerticalDiameter step (hstep.trans (Nat.le_succ steps)))
        (fun step hstep => hHorizontalMonotone step
          (Nat.lt_trans hstep (Nat.lt_succ_self steps)))
        (fun step hstep => hVerticalMonotone step
          (Nat.lt_trans hstep (Nat.lt_succ_self steps)))
        (fun step hstep => hHorizontalInset step
          (Nat.lt_trans hstep (Nat.lt_succ_self steps)))
        (fun step hstep => hVerticalInset step
          (Nat.lt_trans hstep (Nat.lt_succ_self steps)))
        (fun step hstep => hBoundarySmall step
          (Nat.lt_trans hstep (Nat.lt_succ_self steps)))
      exact exists_erasureRecovery_centeredRectangle_general_growth_step
        P embedding d hDistance center
          (horizontalRadius steps) (verticalRadius steps)
          (horizontalRadius (steps + 1)) (verticalRadius (steps + 1)) threshold
          hThreshold
          (hHorizontalDiameter (steps + 1) (by rfl))
          (hVerticalDiameter (steps + 1) (by rfl))
          (hHorizontalMonotone steps (Nat.lt_succ_self steps))
          (hVerticalMonotone steps (Nat.lt_succ_self steps))
          (hHorizontalInset steps (Nat.lt_succ_self steps))
          (hVerticalInset steps (Nat.lt_succ_self steps))
          (hBoundarySmall steps (Nat.lt_succ_self steps))
          hRecoveryPrevious

/-- The canonical finite rectangle-growth schedule: advance by at most one
threshold per step and clip the final step exactly at the requested half-side. -/
def centeredRectangleClippedGrowthRadius
    (baseRadius targetRadius threshold : ℝ) (step : ℕ) : ℝ :=
  min targetRadius (baseRadius + step * threshold)

@[simp]
theorem centeredRectangleClippedGrowthRadius_zero
    (baseRadius targetRadius threshold : ℝ) (hBase : baseRadius ≤ targetRadius) :
    centeredRectangleClippedGrowthRadius baseRadius targetRadius threshold 0 = baseRadius := by
  simp [centeredRectangleClippedGrowthRadius, hBase]

theorem centeredRectangleClippedGrowthRadius_eq_target
    (baseRadius targetRadius threshold : ℝ) (steps : ℕ)
    (hReach : targetRadius ≤ baseRadius + steps * threshold) :
    centeredRectangleClippedGrowthRadius baseRadius targetRadius threshold steps =
      targetRadius := by
  simp [centeredRectangleClippedGrowthRadius, hReach]

/-- A good rectangle with bounded sides has a concrete CPTP recovery from a
finite clipped growth schedule.  This is the executable replacement for the
source's informal reduction of rectangles to squares: no enlargement imports
uncontrolled long incidences, and no recovery is accepted as a premise. -/
theorem exists_erasureRecovery_centeredRectangle_of_good_clipped_growth
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ)
    (baseHorizontalRadius baseVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ outerHorizontalRadius)
    (hBaseVertical : baseVerticalRadius ≤ outerVerticalRadius)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : outerHorizontalRadius ≤
      baseHorizontalRadius + steps * threshold)
    (hReachVertical : outerVerticalRadius ≤
      baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding center
      baseHorizontalRadius baseVerticalRadius).card < d)
    (hGoodCounter : 10 * regionInteractionCounter P embedding threshold
      (centeredRectangleQubits embedding center outerHorizontalRadius
        outerVerticalRadius) ≤ d)
    (hBoundaryBudget :
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        (d : ℝ) / 10 < d) :
    ∃ recovery : QuantumChannel
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        P.semanticCode
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).erasureChannelFromRegister recovery := by
  let horizontalRadius := centeredRectangleClippedGrowthRadius
    baseHorizontalRadius outerHorizontalRadius threshold
  let verticalRadius := centeredRectangleClippedGrowthRadius
    baseVerticalRadius outerVerticalRadius threshold
  have hHorizontalTarget : horizontalRadius steps = outerHorizontalRadius := by
    simpa [horizontalRadius] using
      centeredRectangleClippedGrowthRadius_eq_target baseHorizontalRadius
        outerHorizontalRadius threshold steps hReachHorizontal
  have hVerticalTarget : verticalRadius steps = outerVerticalRadius := by
    simpa [verticalRadius] using
      centeredRectangleClippedGrowthRadius_eq_target baseVerticalRadius
        outerVerticalRadius threshold steps hReachVertical
  have hGoodCounterReal :
      ((regionInteractionCounter P embedding threshold
        (centeredRectangleQubits embedding center outerHorizontalRadius
          outerVerticalRadius) : Nat) : ℝ) ≤ (d : ℝ) / 10 := by
    have hGoodCounterCast :
        (10 : ℝ) *
          ((regionInteractionCounter P embedding threshold
            (centeredRectangleQubits embedding center outerHorizontalRadius
              outerVerticalRadius) : Nat) : ℝ) ≤ d := by
      exact_mod_cast hGoodCounter
    nlinarith
  rw [← hHorizontalTarget, ← hVerticalTarget]
  apply exists_erasureRecovery_centeredRectangle_general_growth_iterate
    P embedding d hDistance center horizontalRadius verticalRadius threshold steps
    hThreshold
  · intro step hstep
    have hBaseLe : baseHorizontalRadius ≤ horizontalRadius step := by
      dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
      apply le_min hBaseHorizontal
      have hNonneg : 0 ≤ (step : ℝ) * threshold :=
        mul_nonneg (Nat.cast_nonneg _) (by linarith)
      linarith
    nlinarith
  · intro step hstep
    have hBaseLe : baseVerticalRadius ≤ verticalRadius step := by
      dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
      apply le_min hBaseVertical
      have hNonneg : 0 ≤ (step : ℝ) * threshold :=
        mul_nonneg (Nat.cast_nonneg _) (by linarith)
      linarith
    nlinarith
  · intro step hstep
    dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
    apply min_le_min le_rfl
    have hSucc : ((step + 1 : ℕ) : ℝ) = (step : ℝ) + 1 := by norm_num
    rw [hSucc]
    nlinarith [hThreshold]
  · intro step hstep
    dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
    apply min_le_min le_rfl
    have hSucc : ((step + 1 : ℕ) : ℝ) = (step : ℝ) + 1 := by norm_num
    rw [hSucc]
    nlinarith [hThreshold]
  · intro step hstep
    dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
    have hSucc : ((step + 1 : ℕ) : ℝ) = (step : ℝ) + 1 := by norm_num
    rw [hSucc]
    by_cases hCap : outerHorizontalRadius ≤
        baseHorizontalRadius + (step + 1) * threshold
    · rw [min_eq_left hCap]
      apply le_min
      · linarith
      · have hCap' : outerHorizontalRadius - threshold ≤
            baseHorizontalRadius + step * threshold := by
          norm_num [Nat.cast_add, Nat.cast_one] at hCap ⊢
          nlinarith
        exact hCap'
    · have hNext : baseHorizontalRadius + (step + 1) * threshold ≤
          outerHorizontalRadius := le_of_lt (lt_of_not_ge hCap)
      have hPrevious : baseHorizontalRadius + step * threshold ≤
          outerHorizontalRadius := by
        nlinarith [hThreshold]
      rw [min_eq_right hNext, min_eq_right hPrevious]
      convert le_rfl using 1 <;> first | rfl | ring
  · intro step hstep
    dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
    have hSucc : ((step + 1 : ℕ) : ℝ) = (step : ℝ) + 1 := by norm_num
    rw [hSucc]
    by_cases hCap : outerVerticalRadius ≤
        baseVerticalRadius + (step + 1) * threshold
    · rw [min_eq_left hCap]
      apply le_min
      · linarith
      · have hCap' : outerVerticalRadius - threshold ≤
            baseVerticalRadius + step * threshold := by
          norm_num [Nat.cast_add, Nat.cast_one] at hCap ⊢
          nlinarith
        exact hCap'
    · have hNext : baseVerticalRadius + (step + 1) * threshold ≤
          outerVerticalRadius := le_of_lt (lt_of_not_ge hCap)
      have hPrevious : baseVerticalRadius + step * threshold ≤
          outerVerticalRadius := by
        nlinarith [hThreshold]
      rw [min_eq_right hNext, min_eq_right hPrevious]
      convert le_rfl using 1 <;> first | rfl | ring
  · intro step hstep
    have hHorizontalStep : horizontalRadius step ≤ outerHorizontalRadius := by
      dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
      exact min_le_left _ _
    have hVerticalStep : verticalRadius step ≤ outerVerticalRadius := by
      dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
      exact min_le_left _ _
    have hHorizontalNext : horizontalRadius (step + 1) ≤ outerHorizontalRadius := by
      dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
      exact min_le_left _ _
    have hVerticalNext : verticalRadius (step + 1) ≤ outerVerticalRadius := by
      dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
      exact min_le_left _ _
    have hCounterNat := regionInteractionCounter_mono P embedding threshold
      (centeredRectangleQubits_subset_of_radii_le embedding center
        hHorizontalStep hVerticalStep)
    have hCounterReal :
        ((∑ q ∈ centeredRectangleQubits embedding center
          (horizontalRadius step) (verticalRadius step),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) ≤
        ((regionInteractionCounter P embedding threshold
          (centeredRectangleQubits embedding center outerHorizontalRadius
            outerVerticalRadius) : Nat) : ℝ) := by
      exact_mod_cast hCounterNat
    have hPerimeter :
        48 * (horizontalRadius (step + 1) + verticalRadius (step + 1) + threshold) *
            threshold ≤
          48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold := by
      have hSum : horizontalRadius (step + 1) + verticalRadius (step + 1) + threshold ≤
          outerHorizontalRadius + outerVerticalRadius + threshold := by
        linarith
      have hScaled : 48 *
          (horizontalRadius (step + 1) + verticalRadius (step + 1) + threshold) ≤
          48 * (outerHorizontalRadius + outerVerticalRadius + threshold) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hScaled (by linarith)
    calc
      _ ≤ 48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
          ((regionInteractionCounter P embedding threshold
            (centeredRectangleQubits embedding center outerHorizontalRadius
              outerVerticalRadius) : Nat) : ℝ) := by
        linarith
      _ < _ := by linarith
  · simpa [horizontalRadius, verticalRadius,
      centeredRectangleClippedGrowthRadius,
      hBaseHorizontal, hBaseVertical] using hBaseCard


/-! ## Finite side-strip witnesses

Each source `B` component is represented by one concrete finite rectangle
around a side of a physical rectangle, with the `2 * ell` vertex neighborhoods
removed from its two ends.  These are geometry, not a caller-supplied
partition.  The later grid construction indexes only the finitely many strips
that contain an actual qubit.
-/

/-- The source `ell`-edge strip on one of the four sides of a concrete
rectangle, with a `2 * ell` buffer removed around both adjacent vertices. -/
def daiLiRectangleSideStripQubits (embedding : UnitSeparatedEmbedding2D ι)
    (ell : ℝ) (lower upper : ℝ × ℝ) : Fin 4 → Finset ι
  | 0 => embedding.qubitsInRectangle
      (lower.1 - ell, lower.2 + 2 * ell)
      (lower.1 + ell, upper.2 - 2 * ell)
  | 1 => embedding.qubitsInRectangle
      (upper.1 - ell, lower.2 + 2 * ell)
      (upper.1 + ell, upper.2 - 2 * ell)
  | 2 => embedding.qubitsInRectangle
      (lower.1 + 2 * ell, lower.2 - ell)
      (upper.1 - 2 * ell, lower.2 + ell)
  | 3 => embedding.qubitsInRectangle
      (lower.1 + 2 * ell, upper.2 - ell)
      (upper.1 - 2 * ell, upper.2 + ell)

def daiLiRectangleSideStripSubsystem (embedding : UnitSeparatedEmbedding2D ι)
    (ell : ℝ) (lower upper : ℝ × ℝ) (side : Fin 4) : FiniteSubsystem ι :=
  ⟨daiLiRectangleSideStripQubits embedding ell lower upper side⟩

/-- The left finite side strip obeys its exact area packing bound. -/
theorem card_daiLiRectangleSideStrip_zero_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.2 - lower.2 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 0).card : ℝ) ≤
      12 * ell * (upper.2 - lower.2 - 4 * ell) := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (lower.1 - ell, lower.2 + 2 * ell)
    (lower.1 + ell, upper.2 - 2 * ell) (by linarith) (by linarith)
  change ((embedding.qubitsInRectangle
    (lower.1 - ell, lower.2 + 2 * ell)
    (lower.1 + ell, upper.2 - 2 * ell)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * ((ell + ell) * (upper.2 - 2 * ell - (lower.2 + 2 * ell))) := by
      convert h using 1 <;> norm_num
    _ = 6 * ((2 * ell) * (upper.2 - lower.2 - 4 * ell)) := by ring
    _ = _ := by ring

theorem card_daiLiRectangleSideStrip_one_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.2 - lower.2 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 1).card : ℝ) ≤
      12 * ell * (upper.2 - lower.2 - 4 * ell) := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (upper.1 - ell, lower.2 + 2 * ell)
    (upper.1 + ell, upper.2 - 2 * ell) (by linarith) (by linarith)
  change ((embedding.qubitsInRectangle
    (upper.1 - ell, lower.2 + 2 * ell)
    (upper.1 + ell, upper.2 - 2 * ell)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * ((ell + ell) * (upper.2 - 2 * ell - (lower.2 + 2 * ell))) := by
      convert h using 1 <;> norm_num
    _ = 6 * ((2 * ell) * (upper.2 - lower.2 - 4 * ell)) := by ring
    _ = _ := by ring

theorem card_daiLiRectangleSideStrip_two_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.1 - lower.1 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 2).card : ℝ) ≤
      12 * ell * (upper.1 - lower.1 - 4 * ell) := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (lower.1 + 2 * ell, lower.2 - ell)
    (upper.1 - 2 * ell, lower.2 + ell) (by linarith) (by linarith)
  change ((embedding.qubitsInRectangle
    (lower.1 + 2 * ell, lower.2 - ell)
    (upper.1 - 2 * ell, lower.2 + ell)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * ((upper.1 - 2 * ell - (lower.1 + 2 * ell)) * (ell + ell)) := by
      convert h using 1 <;> norm_num
    _ = 6 * ((upper.1 - lower.1 - 4 * ell) * (2 * ell)) := by ring
    _ = _ := by ring

theorem card_daiLiRectangleSideStrip_three_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.1 - lower.1 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 3).card : ℝ) ≤
      12 * ell * (upper.1 - lower.1 - 4 * ell) := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (lower.1 + 2 * ell, upper.2 - ell)
    (upper.1 - 2 * ell, upper.2 + ell) (by linarith) (by linarith)
  change ((embedding.qubitsInRectangle
    (lower.1 + 2 * ell, upper.2 - ell)
    (upper.1 - 2 * ell, upper.2 + ell)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * ((upper.1 - 2 * ell - (lower.1 + 2 * ell)) * (ell + ell)) := by
      convert h using 1 <;> norm_num
    _ = 6 * ((upper.1 - lower.1 - 4 * ell) * (2 * ell)) := by ring
    _ = _ := by ring

/-- Any finite geometric side strip has a typed CPTP recovery once the
explicit packing bound is below the semantic distance.  This is the local
recovery used for `B`, not a recovery witness supplied by a partition. -/
theorem exists_erasureRecovery_daiLiRectangleSideStrip_of_card_lt
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell : ℝ) (lower upper : ℝ × ℝ) (side : Fin 4)
    (hCard : (daiLiRectangleSideStripQubits embedding ell lower upper side).card < d) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        P.semanticCode
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).erasureChannelFromRegister
          recovery := by
  exact semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
    (daiLiRectangleSideStripSubsystem embedding ell lower upper side)
    (by simpa [daiLiRectangleSideStripSubsystem] using hCard)

/-! ## Translated-grid bad-point counting infrastructure

These declarations only collect the point sets counted by the averaging
lemmas from #385.  They do not show that deleting the set leaves the
source-required Dai--Li bad-square / `B/B'` partition, and they do not construct
recoveries for the remaining regions.
-/

/-- Long-interaction incidences whose embedded endpoint lies near a translated grid edge. -/
def gridBadLongIncidences
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset (P.daiLiLongIncidenceIndex embedding threshold) :=
  Finset.univ.filter fun incidence =>
    edgeBad w (2 * ell) t (P.daiLiLongIncidencePoint embedding threshold incidence)

/-- Actual endpoint qubits represented by the bad long-incidence multiset. -/
def gridBadLongEndpointQubits
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  (gridBadLongIncidences P embedding threshold w ell t).image Sigma.fst

/--
Candidate grid-bad points: physical qubits near grid vertices together with
actual endpoints of long interactions whose incidence point lies near a grid
edge.  This is a counting set, not the source-required Dai--Li separator.
-/
def gridBadPointSet
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  (Finset.univ.filter fun q => vertexBad w (2 * ell) t (embedding.point q)) ∪
    gridBadLongEndpointQubits P embedding threshold w ell t

/-- Deduplicating actual long-incidence endpoints can only lower their count. -/
theorem card_gridBadLongEndpointQubits_le_edgeBadCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    (gridBadLongEndpointQubits P embedding threshold w ell t).card ≤
      edgeBadCount w (2 * ell)
        (P.daiLiLongIncidencePoint embedding threshold) t := by
  exact Finset.card_image_le.trans_eq (by
    simp [gridBadLongIncidences, edgeBadCount])

/-- The candidate grid-bad set is controlled by the two actual counts from #385. -/
theorem card_gridBadPointSet_le_badCounts
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    ((gridBadPointSet P embedding threshold w ell t).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (edgeBadCount w (2 * ell)
          (P.daiLiLongIncidencePoint embedding threshold) t : ℝ) := by
  have hunion := Finset.card_union_le
    (Finset.univ.filter fun q => vertexBad w (2 * ell) t (embedding.point q))
    (gridBadLongEndpointQubits P embedding threshold w ell t)
  have hendpoints := card_gridBadLongEndpointQubits_le_edgeBadCount
    P embedding threshold w ell t
  have hunionReal :
      ((gridBadPointSet P embedding threshold w ell t).card : ℝ) ≤
        ((Finset.univ.filter fun q =>
          vertexBad w (2 * ell) t (embedding.point q)).card : ℝ) +
          ((gridBadLongEndpointQubits P embedding threshold w ell t).card : ℝ) := by
    exact_mod_cast hunion
  calc
    _ ≤ ((Finset.univ.filter fun q =>
          vertexBad w (2 * ell) t (embedding.point q)).card : ℝ) +
          ((gridBadLongEndpointQubits P embedding threshold w ell t).card : ℝ) := hunionReal
    _ ≤ (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (edgeBadCount w (2 * ell)
          (P.daiLiLongIncidencePoint embedding threshold) t : ℝ) := by
      rw [vertexBadCount]
      gcongr

/--
There is a translation whose candidate grid-bad point set has the explicit
#385 count.  This is only an averaging/counting result: it does not prove that
the set is a separator or that either complementary region is correctable.
-/
theorem exists_gridBadPointSet_card_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (hell : 0 < ell) (hscale : 4 * ell ≤ w) :
    ∃ t : GridTranslation w,
      ((gridBadPointSet P embedding threshold w ell t).card : ℝ) ≤
        (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
          (32 * ell / w) * P.longInteractionCount embedding threshold := by
  obtain ⟨t, hvertex, hedge⟩ :=
    P.exists_good_translation_for_qubits_and_longIncidences
      embedding threshold w ell hell hscale
  refine ⟨t, (card_gridBadPointSet_le_badCounts
    P embedding threshold w ell t).trans ?_⟩
  calc
    _ ≤ (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
        (16 * ell / w) * (2 * P.longInteractionCount embedding threshold) :=
      add_le_add hvertex hedge
    _ = _ := by ring

/-! ## Source-faithful square classification and edge buffers

The following finite definitions mirror the objects used in DL24,
`main.tex:1102-1125`.  In particular, a good square is classified by its
actual endpoint-incidence counter, and the `B/B'` regions are periodic edge
buffers with the `2 * ell` vertex buffer removed.  They are not whole-cell
parity classes.
-/

/-- DL24's exact division-free convention `f_{>=ell}(S) < d / 10`. -/
def IsGoodInteractionRegion
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (region : Finset ι) : Prop :=
  10 * regionInteractionCounter P embedding threshold region < d

/-- The complementary bad-region convention `d / 10 <= f_{>=ell}(S)`. -/
def IsBadInteractionRegion
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (region : Finset ι) : Prop :=
  d ≤ 10 * regionInteractionCounter P embedding threshold region

/-- A concrete centered square is good according to its actual long-incidence count. -/
def IsGoodInteractionSquare
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (center : ℝ × ℝ) (radius : ℝ) : Prop :=
  IsGoodInteractionRegion P embedding threshold d
    (squareQubits embedding center radius)

/-- The complementary classification of a concrete centered square as bad. -/
def IsBadInteractionSquare
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (center : ℝ × ℝ) (radius : ℝ) : Prop :=
  IsBadInteractionRegion P embedding threshold d
    (squareQubits embedding center radius)

theorem isBadInteractionRegion_iff_not_isGoodInteractionRegion
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (d : Nat) (region : Finset ι) :
    IsBadInteractionRegion P embedding threshold d region ↔
      ¬ IsGoodInteractionRegion P embedding threshold d region := by
  simp [IsBadInteractionRegion, IsGoodInteractionRegion]

/-- The actual qubits participating in at least one threshold-long interaction. -/
def longInteractionEndpointQubits
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) : Finset ι :=
  Finset.univ.filter fun q => 0 < P.daiLiInteractionCounter embedding threshold q

/-- Every bad qubit contributes at least one incidence to the global counter. -/
theorem card_longInteractionEndpointQubits_le_sum_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    (longInteractionEndpointQubits P embedding threshold).card ≤
      ∑ q, P.daiLiInteractionCounter embedding threshold q := by
  classical
  calc
    _ = ∑ q ∈ longInteractionEndpointQubits P embedding threshold, 1 := by simp
    _ ≤ ∑ q ∈ longInteractionEndpointQubits P embedding threshold,
        P.daiLiInteractionCounter embedding threshold q := by
      apply Finset.sum_le_sum
      intro q hq
      have : 0 < P.daiLiInteractionCounter embedding threshold q := by
        simpa [longInteractionEndpointQubits] using hq
      omega
    _ ≤ ∑ q ∈ (Finset.univ : Finset ι),
        P.daiLiInteractionCounter embedding threshold q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by
          simpa [longInteractionEndpointQubits] using
            (Finset.filter_subset (fun q : ι =>
              0 < P.daiLiInteractionCounter embedding threshold q) Finset.univ))
        (fun _ _ _ => Nat.zero_le _)
    _ = _ := by simp

@[simp]
theorem mem_longInteractionEndpointQubits_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (q : ι) :
    q ∈ longInteractionEndpointQubits P embedding threshold ↔
      0 < P.daiLiInteractionCounter embedding threshold q := by
  simp [longInteractionEndpointQubits]

/-- The `k >= d` branch's disposal of every bad qubit removes every threshold-long
fixed-generator interaction from the remaining qubits. -/
theorem no_long_interaction_from_outside_endpoint_set
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (p q : ι)
    (hp : p ∉ longInteractionEndpointQubits P embedding threshold) :
    ¬ (P.fixedGeneratorInteraction p q ∧ threshold ≤ embedding.distance p q) := by
  intro hpq
  have hPositive : 0 < P.daiLiInteractionCounter embedding threshold p := by
    rw [P.daiLiInteractionCounter_eq_neighborFinset_card embedding threshold p]
    apply Finset.card_pos.mpr
    refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, ?_⟩⟩
    exact ⟨hpq.1.1, hpq.1.2, hpq.2⟩
  exact hp (mem_longInteractionEndpointQubits_iff P embedding threshold p |>.2 hPositive)

/--
Two concrete regions are fixed-generator decoupled when they are disjoint,
every selected qubit is outside the actual threshold-long endpoint set, and
their embedded points are separated by the threshold.  The proof splits a
putative cross interaction into its long and short cases; it does not assume
that ``good'' interactions exhaust the fixed-generator interaction graph.
-/
theorem fixedGeneratorDecoupled_of_separated_outside_longEndpoints
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (left right : Finset ι)
    (hDisjoint : Disjoint left right)
    (hLeftOutside : left ⊆ (longInteractionEndpointQubits P embedding threshold)ᶜ)
    (hRightOutside : right ⊆ (longInteractionEndpointQubits P embedding threshold)ᶜ)
    (hSeparated : ∀ p ∈ left, ∀ q ∈ right,
      threshold ≤ embedding.distance p q) :
    P.fixedGeneratorDecoupled (left : Set ι) (right : Set ι) := by
  refine ⟨by simpa using hDisjoint, ?_⟩
  intro p hp q hq hInteraction
  have hpLeft : p ∈ left := by simpa using hp
  have hqRight : q ∈ right := by simpa using hq
  have hpOutside : p ∉ longInteractionEndpointQubits P embedding threshold :=
    Finset.mem_compl.mp (hLeftOutside hpLeft)
  have hLength : threshold ≤ embedding.distance p q := hSeparated p hpLeft q hqRight
  exact no_long_interaction_from_outside_endpoint_set P embedding threshold p q hpOutside
    ⟨hInteraction, hLength⟩

/-- Qubits in a closed rectangle whose vertical coordinate lies below a cut. -/
def lowerHorizontalRectangleQubits
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) : Finset ι :=
  (embedding.qubitsInRectangle lower upper).filter fun q =>
    (embedding.point q).2 ≤ cut

/-- Qubits in the complementary, upper half of a horizontal cut. -/
def upperHorizontalRectangleQubits
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) : Finset ι :=
  (embedding.qubitsInRectangle lower upper).filter fun q =>
    cut < (embedding.point q).2

/-- A horizontal cut is an actual disjoint subdivision of the parent rectangle's qubits. -/
theorem horizontalRectangleQubits_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) :
    Disjoint (lowerHorizontalRectangleQubits embedding lower upper cut)
      (upperHorizontalRectangleQubits embedding lower upper cut) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hLower hUpper
  have hqLower : (embedding.point q).2 ≤ cut := by
    exact (Finset.mem_filter.mp hLower).2
  have hqUpper : cut < (embedding.point q).2 := by
    exact (Finset.mem_filter.mp hUpper).2
  exact (not_lt_of_ge hqLower) hqUpper

theorem horizontalRectangleQubits_union
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) :
    lowerHorizontalRectangleQubits embedding lower upper cut ∪
        upperHorizontalRectangleQubits embedding lower upper cut =
      embedding.qubitsInRectangle lower upper := by
  classical
  ext q
  by_cases hq : (embedding.point q).2 ≤ cut
  · simp [lowerHorizontalRectangleQubits, upperHorizontalRectangleQubits, hq]
  · have hq' : cut < (embedding.point q).2 := lt_of_not_ge hq
    simp [lowerHorizontalRectangleQubits, upperHorizontalRectangleQubits, hq, hq']

/-- Endpoint incidences add exactly across one genuine horizontal subdivision. -/
theorem regionInteractionCounter_horizontal_add
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (lower upper : ℝ × ℝ) (cut : ℝ) :
    regionInteractionCounter P embedding threshold
        (lowerHorizontalRectangleQubits embedding lower upper cut) +
      regionInteractionCounter P embedding threshold
        (upperHorizontalRectangleQubits embedding lower upper cut) =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle lower upper) := by
  classical
  unfold regionInteractionCounter
  rw [← Finset.sum_union
      (horizontalRectangleQubits_disjoint embedding lower upper cut),
    horizontalRectangleQubits_union]

/-- DL24's `C`: qubits within periodic `ell_infty` distance `2 * ell` of a grid vertex. -/
def gridVertexBufferQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  Finset.univ.filter fun q => vertexBad w (2 * ell) t (embedding.point q)

/-- DL24's `B` in the no-bad-rectangle case: the `ell` edge buffer outside `C`. -/
def gridEdgeBufferQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  Finset.univ.filter fun q =>
    ¬ vertexBad w (2 * ell) t (embedding.point q) ∧
      edgeBad w ell t (embedding.point q)

/-- DL24's `B'`: the wider `2 * ell` edge buffer, still outside `C`. -/
def gridWideEdgeBufferQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  Finset.univ.filter fun q =>
    ¬ vertexBad w (2 * ell) t (embedding.point q) ∧
      edgeBad w (2 * ell) t (embedding.point q)

/-- DL24's `A` in the no-bad-rectangle case: the complement of `B` and `C`. -/
def gridInteriorQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) : Finset ι :=
  Finset.univ.filter fun q =>
    ¬ vertexBad w (2 * ell) t (embedding.point q) ∧
      ¬ edgeBad w ell t (embedding.point q)

theorem gridEdgeBufferQubits_subset_gridWideEdgeBufferQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) (hell : 0 ≤ ell) :
    gridEdgeBufferQubits embedding w ell t ⊆
      gridWideEdgeBufferQubits embedding w ell t := by
  classical
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨_, hNotVertex, hEdge⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ q, hNotVertex, ?_⟩
  rcases hEdge with hEdge | hEdge
  · exact Or.inl (hEdge.trans (by linarith))
  · exact Or.inr (hEdge.trans (by linarith))

theorem gridInterior_edge_vertex_pairwise_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) :
    Disjoint (gridInteriorQubits embedding w ell t)
        (gridEdgeBufferQubits embedding w ell t) ∧
      Disjoint (gridInteriorQubits embedding w ell t)
        (gridVertexBufferQubits embedding w ell t) ∧
      Disjoint (gridEdgeBufferQubits embedding w ell t)
        (gridVertexBufferQubits embedding w ell t) := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hA hB
    have hNotEdge : ¬ edgeBad w ell t (embedding.point q) := by
      exact (Finset.mem_filter.mp hA).2.2
    have hEdge : edgeBad w ell t (embedding.point q) := by
      exact (Finset.mem_filter.mp hB).2.2
    exact hNotEdge hEdge
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hA hC
    have hNotVertex : ¬ vertexBad w (2 * ell) t (embedding.point q) := by
      exact (Finset.mem_filter.mp hA).2.1
    have hVertex : vertexBad w (2 * ell) t (embedding.point q) := by
      simpa [gridVertexBufferQubits] using hC
    exact hNotVertex hVertex
  · apply Finset.disjoint_left.mpr
    intro q hB hC
    have hNotVertex : ¬ vertexBad w (2 * ell) t (embedding.point q) := by
      exact (Finset.mem_filter.mp hB).2.1
    have hVertex : vertexBad w (2 * ell) t (embedding.point q) := by
      simpa [gridVertexBufferQubits] using hC
    exact hNotVertex hVertex

/-- In the `d >= k` branch, where DL24 proves there are no bad rectangles,
the actual grid predicates form the source `A/B/C` partition. -/
theorem gridInterior_edge_vertex_cover
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) :
    gridInteriorQubits embedding w ell t ∪
        gridEdgeBufferQubits embedding w ell t ∪
        gridVertexBufferQubits embedding w ell t = Finset.univ := by
  classical
  ext q
  by_cases hVertex : vertexBad w (2 * ell) t (embedding.point q)
  · simp [gridInteriorQubits, gridEdgeBufferQubits, gridVertexBufferQubits, hVertex]
  · by_cases hEdge : edgeBad w ell t (embedding.point q)
    · simp [gridInteriorQubits, gridEdgeBufferQubits, gridVertexBufferQubits,
        hVertex, hEdge]
    · simp [gridInteriorQubits, gridEdgeBufferQubits, gridVertexBufferQubits,
        hVertex, hEdge]

/-! ## The `d >= k` correctability composition step

The paper's `B` recovery is a finite decoupled union of the remaining bad
qubits and edge-centered rectangles.  The theorem below performs exactly that
semantic step: strict distance bounds produce every recovery through #363,
then #373 combines the actual fixed-generator-decoupled family.  No recovery
witness is supplied as a hypothesis.
-/

/-- Index the exceptional bad-qubit piece together with the edge-strip pieces. -/
def caseDGeKPieceFamily {α : Type*}
    (badQubits : FiniteSubsystem ι) (edgeStrips : α → FiniteSubsystem ι) :
    Option α → FiniteSubsystem ι
  | none => badQubits
  | some a => edgeStrips a

/-- The finite index set containing the bad-qubit piece and selected edge strips. -/
def caseDGeKPieceIndices {α : Type*} [DecidableEq α] (s : Finset α) :
    Finset (Option α) :=
  insert none (s.image some)

/-- The selected subsystem is exactly the bad-qubit piece together with all edge strips. -/
theorem caseDGeKPieceFamily_union_selected {α : Type*} [DecidableEq α]
    (badQubits : FiniteSubsystem ι) (edgeStrips : α → FiniteSubsystem ι)
    (s : Finset α) :
    (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
        (caseDGeKPieceIndices s)).selected =
      badQubits.selected ∪ s.biUnion fun a => (edgeStrips a).selected := by
  classical
  ext q
  simp [familyUnionSubsystem, caseDGeKPieceIndices, caseDGeKPieceFamily]

/-- Source-faithful `d >= k` recovery composition for bad qubits plus edge strips. -/
theorem exists_erasureRecovery_caseDGeK_badQubits_edgeStrips
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (badQubits : FiniteSubsystem ι) (edgeStrips : α → FiniteSubsystem ι)
    (s : Finset α)
    (hCard : ∀ a, a ∈ caseDGeKPieceIndices s →
      (caseDGeKPieceFamily badQubits edgeStrips a).selected.card < d)
    (hDecoupled : ∀ a, a ∈ caseDGeKPieceIndices s →
      ∀ b, b ∈ caseDGeKPieceIndices s → a ≠ b →
        P.fixedGeneratorDecoupled
          ((caseDGeKPieceFamily badQubits edgeStrips a).selected : Set ι)
          ((caseDGeKPieceFamily badQubits edgeStrips b).selected : Set ι)) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).complementSystem
        P.semanticCode
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).erasureChannelFromRegister recovery := by
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
  · intro a ha
    exact semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance (caseDGeKPieceFamily badQubits edgeStrips a) (hCard a ha)
  · exact hDecoupled

end QEC.Locality
