import QEC.Coding.FiniteAlternatingConstruction.ReplacementEmbeddingCoordinates
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.DaviesLocality

/-!
# Physical label density and Euclidean locality

BDL26 v1 `paper.tex:1326–1340,302–309`, approved source gate #841.
The factors two and the radii below are derived from literal Tanner incidences.
All face and qubit labels are counted even when their images coincide.
-/

noncomputable section
namespace QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Count domain qubit labels, not distinct points of the image. -/
def qubitHits (P : TannerSquarePresentation) (J : Vertex P → E) (ball : Set E) : Finset P.Q :=
  Finset.univ.filter (fun q => J (.q q) ∈ ball)

theorem face_corner_mem (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (k : Two) : J (.q (P.faceQ f k)) ∈ tannerFaceImage P J f := by
  fin_cases k
  · apply Set.mem_union_left
    exact (subset_convexHull ℝ _) (by simp)
  · apply Set.mem_union_right
    exact (subset_convexHull ℝ _) (by simp)

/-- This charging witness is chosen from proved admissibility, not geometric data. -/
def qubitCorner (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q) :
    P.Face × Two := Classical.choose (faceQ_surjective P A q)

theorem qubitCorner_recovers (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) : P.faceQ (qubitCorner P A q).1 (qubitCorner P A q).2 = q :=
  Classical.choose_spec (faceQ_surjective P A q)

theorem qubitCorner_injective (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    Function.Injective (qubitCorner P A) := by
  intro q r h
  have hh := congrArg (fun z : P.Face × Two => P.faceQ z.1 z.2) h
  simpa only [qubitCorner_recovers] using hh

/-- The localized injection works for arbitrary regions, including collapsed images. -/
theorem qubitHits_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (J : Vertex P → E) (ball : Set E) :
    (qubitHits P J ball).card ≤ 2 * (familyHits (tannerFaceImage P J) ball).card := by
  let target := familyHits (tannerFaceImage P J) ball ×ˢ (Finset.univ : Finset Two)
  have hc : (qubitHits P J ball).card ≤ target.card := by
    apply Finset.card_le_card_of_injOn (qubitCorner P A)
    · intro q hq
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, J (.q q), ?_, (Finset.mem_filter.mp hq).2⟩
      simpa only [qubitCorner_recovers] using
        face_corner_mem P J (qubitCorner P A q).1 (qubitCorner P A q).2
    · exact fun q _ r _ h => qubitCorner_injective P A h
  simpa only [target, Finset.card_product, Finset.card_univ,
    Two, Fintype.card_fin, Nat.mul_comm] using hc

theorem qubit_density_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (J : Vertex P → E) {t : ℝ} (hJ : IsBoundedDensityLocalMap P J t) (c : E) :
    ((qubitHits P J (Metric.closedBall c 1)).card : ℝ) ≤ 2*t := by
  have hc : ((qubitHits P J (Metric.closedBall c 1)).card : ℝ) ≤
      2*((familyHits (tannerFaceImage P J) (Metric.closedBall c 1)).card : ℝ) := by
    exact_mod_cast qubitHits_card_le P A J (Metric.closedBall c 1)
  exact hc.trans (mul_le_mul_of_nonneg_left (hJ.2.2 c) (by norm_num))

theorem localMap_mono (P : TannerSquarePresentation) (J : Vertex P → E)
    {s t : ℝ} (hJ : IsBoundedDensityLocalMap P J s) (hst : s ≤ t) :
    IsBoundedDensityLocalMap P J t :=
  ⟨hJ.1, hJ.2.1, fun c => (hJ.2.2 c).trans hst⟩

/-- The actual labelled check vertex, in the source's Z+X order. -/
def checkCenter (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E) :
    Sum (ZLabel S n) (XLabel S n) → E
  | .inl z => J (.z z)
  | .inr x => J (.x x)

theorem check_radius (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    {t : ℝ} (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (j : Sum (ZLabel S n) (XLabel S n)) (r : Physical S n)
    (hr : r ∈ checkSupport S n j) : dist (J (.q r)) (checkCenter S n J j) ≤ 1 := by
  cases j with
  | inl z => exact hJ.2.1 r z ((mem_z_checkSupport S n z r).mp hr)
  | inr x => exact (dist_comm _ _).trans_le (hJ.1 x r ((mem_x_checkSupport S n x r).mp hr))

theorem check_diameter (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    {t : ℝ} (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (j : Sum (ZLabel S n) (XLabel S n)) (r s : Physical S n)
    (hr : r ∈ checkSupport S n j) (hs : s ∈ checkSupport S n j) :
    dist (J (.q r)) (J (.q s)) ≤ 2 := by
  calc
    _ ≤ dist (J (.q r)) (checkCenter S n J j) +
        dist (checkCenter S n J j) (J (.q s)) := dist_triangle _ _ _
    _ ≤ 1+1 := add_le_add (check_radius S n J hJ j r hr)
      (by simpa only [dist_comm] using check_radius S n J hJ j s hs)
    _ = 2 := by norm_num

theorem region_radius (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    {t : ℝ} (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (q r : Physical S n) (hr : r ∈ region S n q) : dist (J (.q r)) (J (.q q)) ≤ 2 := by
  rcases Finset.mem_union.mp hr with hr | hr
  · have he : r = q := Finset.mem_singleton.mp hr
    subst r
    simp
  · obtain ⟨j, hj, hr⟩ := Finset.mem_biUnion.mp hr
    have hq : q ∈ checkSupport S n j := (Finset.mem_filter.mp hj).2
    exact check_diameter S n J hJ j r q hr hq

theorem region_diameter (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    {t : ℝ} (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (q r s : Physical S n) (hr : r ∈ region S n q) (hs : s ∈ region S n q) :
    dist (J (.q r)) (J (.q s)) ≤ 4 := by
  calc
    _ ≤ dist (J (.q r)) (J (.q q)) + dist (J (.q q)) (J (.q s)) := dist_triangle _ _ _
    _ ≤ 2+2 := add_le_add (region_radius S n J hJ q r hr)
      (by simpa only [dist_comm] using region_radius S n J hJ q s hs)
    _ = 4 := by norm_num

/-- Complete physical geometry is a proposition, never an assumed output certificate. -/
def PhysicalGeometry (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    (t : ℝ) : Prop :=
  (∀ c, ((qubitHits (state S n).presentation J (Metric.closedBall c 1)).card : ℝ) ≤ 2*t) ∧
  (∀ j : Sum (ZLabel S n) (XLabel S n),
    (∀ r ∈ checkSupport S n j, dist (J (.q r)) (checkCenter S n J j) ≤ 1) ∧
    (∀ r ∈ checkSupport S n j, ∀ s ∈ checkSupport S n j, dist (J (.q r)) (J (.q s)) ≤ 2) ∧
    (checkSupport S n j).card ≤ 7) ∧
  (∀ q : Physical S n,
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (region S n q).card ≤ 50)

/-- Reindex a physical map along an actual level equality, retaining all labels. -/
theorem physicalGeometry_cast (S : OddScale) (m n : Nat) (h : m = n)
    (J : Vertex (state S m).presentation → E) (t : ℝ) (hg : PhysicalGeometry S m J t) :
    PhysicalGeometry S n
      (fun v => J (cast (congrArg (fun a => Vertex (state S a).presentation) h.symm) v)) t := by
  subst n
  exact hg

/-- All physical conclusions are derived from actual admissibility and incidences. -/
theorem physicalGeometry_of_localMap (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : IsBoundedDensityLocalMap (state S n).presentation J t) : PhysicalGeometry S n J t := by
  refine ⟨?_, ?_, ?_⟩
  · exact qubit_density_le _ (state S n).admissible.toTannerSquareAdmissible J hJ
  · intro j
    exact ⟨check_radius S n J hJ j,
      fun r hr s hs => check_diameter S n J hJ j r s hr hs, check_card_le_seven S n j⟩
  · intro q
    exact ⟨region_radius S n J hJ q,
      fun r hr s hs => region_diameter S n J hJ q r s hr hs, region_card_le_fifty S n q⟩

/-- The metric conclusion concerns exactly the subsystem of the full-H frequency. -/
theorem frequency_physical (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (BDL26CSSDaviesLocality.subsystem S n q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian S n) (BDL26CSSDaviesLocality.hamiltonian_symmetric S n)
        (BDL26CSSDaviesLocality.coupling S n q a) ω) ∧
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem S n q).selected.card ≤ 50 :=
  ⟨BDL26CSSDaviesLocality.frequency_supported S n q a ω, region_radius S n J hJ q,
    fun r hr s hs => region_diameter S n J hJ q r s hr hs, region_card_le_fifty S n q⟩

/-- Arbitrary rates retain the actual sqrt-rate jump and the very same metric region. -/
theorem weightedJump_physical (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (rate : BDL26CSSDaviesLocality.CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S n) :
    (BDL26CSSDaviesLocality.subsystem S n q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian S n) (BDL26CSSDaviesLocality.hamiltonian_symmetric S n)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex S n =>
          BDL26CSSDaviesLocality.coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem S n q).selected.card ≤ 50 :=
  ⟨BDL26CSSDaviesLocality.weightedJump_supported S n rate q a ω, region_radius S n J hJ q,
    fun r hr s hs => region_diameter S n J hJ q r s hr hs, region_card_le_fifty S n q⟩

end QEC.Coding.BDL26RandomPhysicalLocality
