import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Incidence
import QEC.Coding.ProbabilisticConstruction.SphericalCap.JointTriangleHit

/-!
# The exact Borel domain of bounded-density local maps

Face labels are never identified by their images. A density violation has a
finite label witness and a centre in a countable compact-ball exhaustion. The
triangle witnesses may be degenerate and the centre is not restricted to a grid.
-/
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set

def faceBallHit (P : TannerSquarePresentation) (J : Vertex P → Space)
    (f : P.Face) (c : Space) : Prop :=
  ∃ y ∈ tannerFaceImage P J f, dist y c ≤ 1

theorem mem_familyHits_iff_faceBallHit (P : TannerSquarePresentation)
    (J : Vertex P → Space) (f : P.Face) (c : Space) :
    f ∈ familyHits (tannerFaceImage P J) (Metric.closedBall c 1) ↔
      faceBallHit P J f c := by
  simp only [familyHits, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.nonempty_def, Set.mem_inter_iff, Metric.mem_closedBall, faceBallHit]

theorem isClosed_faceBallHit (P : TannerSquarePresentation) (f : P.Face) :
    IsClosed {z : (Vertex P → Space) × Space | faceBallHit P z.1 f z.2} := by
  let lo : Fin 3 → Vertex P := ![.x (P.faceX f), .q (P.faceQ f 0), .z (P.faceZ f)]
  let hi : Fin 3 → Vertex P := ![.x (P.faceX f), .z (P.faceZ f), .q (P.faceQ f 1)]
  have hc (a : Fin 3 → Vertex P) : IsClosed
      {z : (Vertex P → Space) × Space |
        (fun _ : Fin 3 => (0 : Space)) ∈
          triangleHit (fun i => z.1 (a i)) z.2 1} := by
    let vertices : ((Vertex P → Space) × Space) → Fin 3 → Space :=
      fun z i => z.1 (a i)
    let offsets : ((Vertex P → Space) × Space) → Fin 3 → Space := fun _ _ => 0
    let centres : ((Vertex P → Space) × Space) → Space := Prod.snd
    let radii : ((Vertex P → Space) × Space) → ℝ := fun _ => 1
    have hv : Continuous vertices := by
      apply continuous_pi
      intro i
      exact (continuous_apply (a i)).comp continuous_fst
    have hu : Continuous offsets := continuous_const
    have hc : Continuous centres := continuous_snd
    have hr : Continuous radii := continuous_const
    exact isClosed_triangleHit_of_continuous vertices offsets centres radii hv hu hc hr
  have he : {z : (Vertex P → Space) × Space | faceBallHit P z.1 f z.2} =
      {z | (fun _ : Fin 3 => (0 : Space)) ∈ triangleHit (fun i => z.1 (lo i)) z.2 1} ∪
      {z | (fun _ : Fin 3 => (0 : Space)) ∈ triangleHit (fun i => z.1 (hi i)) z.2 1} := by
    ext z
    have hzero (r : Fin 3 → Space) (c : Space) :
        (fun _ : Fin 3 => (0 : Space)) ∈ triangleHit r c 1 ↔
          ∃ y ∈ convexHull ℝ (Set.range r), dist y c ≤ 1 := by
      change (∃ y ∈ convexHull ℝ (Set.range fun i => r i+(0 : Space)), dist y c ≤ 1) ↔ _
      simp only [add_zero]
    have hlo : Set.range (fun i => z.1 (lo i)) =
        {z.1 (.x (P.faceX f)),z.1 (.q (P.faceQ f 0)),z.1 (.z (P.faceZ f))} := by
      ext y
      simp [lo, Fin.exists_fin_succ, eq_comm]
    have hhi : Set.range (fun i => z.1 (hi i)) =
        {z.1 (.x (P.faceX f)),z.1 (.z (P.faceZ f)),z.1 (.q (P.faceQ f 1))} := by
      ext y
      simp [hi, Fin.exists_fin_succ, eq_comm]
    have hloHit := hzero (fun i => z.1 (lo i)) z.2
    rw [hlo] at hloHit
    have hhiHit := hzero (fun i => z.1 (hi i)) z.2
    rw [hhi] at hhiHit
    change faceBallHit P z.1 f z.2 ↔
      ((fun _ : Fin 3 => (0 : Space)) ∈ triangleHit (fun i => z.1 (lo i)) z.2 1) ∨
      ((fun _ : Fin 3 => (0 : Space)) ∈ triangleHit (fun i => z.1 (hi i)) z.2 1)
    constructor
    · rintro ⟨y,hy,hd⟩
      rcases hy with hyl | hyr
      · exact Or.inl (hloHit.mpr ⟨y,hyl,hd⟩)
      · exact Or.inr (hhiHit.mpr ⟨y,hyr,hd⟩)
    · rintro (hl | hr)
      · obtain ⟨y,hy,hd⟩ := hloHit.mp hl
        exact ⟨y,Or.inl hy,hd⟩
      · obtain ⟨y,hy,hd⟩ := hhiHit.mp hr
        exact ⟨y,Or.inr hy,hd⟩
  rw [he]
  exact (hc lo).union (hc hi)

/-- A finite family of labelled hits with a bounded, continuously varying centre. -/
def boundedLabelHit (P : TannerSquarePresentation) (s : Finset P.Face) (N : ℕ) :
    Set (Vertex P → Space) :=
  {J | ∃ c : Metric.closedBall (0 : Space) (N : ℝ), ∀ f ∈ s, faceBallHit P J f c}

theorem isClosed_boundedLabelHit (P : TannerSquarePresentation) (s : Finset P.Face)
    (N : ℕ) : IsClosed (boundedLabelHit P s N) := by
  letI : CompactSpace (Metric.closedBall (0 : Space) (N : ℝ)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space) (N : ℝ))
  let E : Set ((Vertex P → Space) × Metric.closedBall (0 : Space) (N : ℝ)) :=
    {z | ∀ f ∈ s, faceBallHit P z.1 f z.2}
  have hc : IsClosed E := by
    have he : E = ⋂ f : P.Face, ⋂ (_ : f ∈ s),
        (fun z : (Vertex P → Space) × Metric.closedBall (0 : Space) (N : ℝ) =>
          (z.1,(z.2 : Space))) ⁻¹' {z | faceBallHit P z.1 f z.2} := by
      ext z
      simp only [E, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [he]
    exact isClosed_iInter fun f : P.Face => isClosed_iInter fun _ : f ∈ s =>
      (isClosed_faceBallHit P f).preimage
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have he : boundedLabelHit P s N = Prod.fst '' E := by
    ext J
    simp only [boundedLabelHit, E, Set.mem_setOf_eq, Set.mem_image, Prod.exists]
    constructor
    · rintro ⟨c,hc⟩
      exact ⟨J,c,hc,rfl⟩
    · rintro ⟨J',c,hc,he⟩
      subst J'
      exact ⟨c,hc⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc

/-- The witness uses face DOMAIN labels and every real centre. -/
theorem density_violation_iff (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) :
    (∃ c, t < ((familyHits (tannerFaceImage P J) (Metric.closedBall c 1)).card : ℝ)) ↔
      ∃ (N : ℕ) (s : Finset P.Face), t < (s.card : ℝ) ∧ J ∈ boundedLabelHit P s N := by
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨N,hN⟩ := exists_nat_ge ‖c‖
    refine ⟨N,familyHits (tannerFaceImage P J) (Metric.closedBall c 1),hc,?_⟩
    refine ⟨⟨c,?_⟩,?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hN
    · intro f hf
      exact (mem_familyHits_iff_faceBallHit P J f c).mp hf
  · rintro ⟨N,s,hs,c,hc⟩
    refine ⟨c,hs.trans_le ?_⟩
    have hsub : s ⊆ familyHits (tannerFaceImage P J) (Metric.closedBall (c : Space) 1) := by
      intro f hf
      exact (mem_familyHits_iff_faceBallHit P J f c).mpr (hc f hf)
    exact_mod_cast Finset.card_le_card hsub

theorem measurableSet_density_violation (P : TannerSquarePresentation) (t : ℝ) :
    MeasurableSet {J : Vertex P → Space |
      ∃ c, t < ((familyHits (tannerFaceImage P J) (Metric.closedBall c 1)).card : ℝ)} := by
  have he : {J : Vertex P → Space |
      ∃ c, t < ((familyHits (tannerFaceImage P J) (Metric.closedBall c 1)).card : ℝ)} =
      ⋃ N : ℕ, ⋃ s : Finset P.Face, ⋃ (_ : t < (s.card : ℝ)), boundedLabelHit P s N := by
    ext J
    simp only [Set.mem_setOf_eq, density_violation_iff, Set.mem_iUnion]
    constructor <;> rintro ⟨N,s,ht,hJ⟩ <;> exact ⟨N,s,ht,hJ⟩
  rw [he]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun s =>
    MeasurableSet.iUnion fun _ => (isClosed_boundedLabelHit P s N).measurableSet

/-- The exact original all-centre, multiplicity-preserving input/output domain is Borel. -/
theorem measurableSet_boundedDensityLocalMap (P : TannerSquarePresentation) (t : ℝ) :
    MeasurableSet {J : Vertex P → Space | IsBoundedDensityLocalMap P J t} := by
  have hx (x : P.X) (q : P.Q) : MeasurableSet
      {J : Vertex P → Space | dist (J (.x x)) (J (.q q)) ≤ 1} :=
    (isClosed_le ((continuous_apply _).dist (continuous_apply _)) continuous_const).measurableSet
  have hz (q : P.Q) (z : P.Z) : MeasurableSet
      {J : Vertex P → Space | dist (J (.q q)) (J (.z z)) ≤ 1} :=
    (isClosed_le ((continuous_apply _).dist (continuous_apply _)) continuous_const).measurableSet
  have hedge : MeasurableSet {J : Vertex P → Space |
      (∀ x q, P.xq x q = true → dist (J (.x x)) (J (.q q)) ≤ 1) ∧
      (∀ q z, P.qz q z = true → dist (J (.q q)) (J (.z z)) ≤ 1)} := by
    have he : {J : Vertex P → Space |
        (∀ x q, P.xq x q = true → dist (J (.x x)) (J (.q q)) ≤ 1) ∧
        (∀ q z, P.qz q z = true → dist (J (.q q)) (J (.z z)) ≤ 1)} =
        (⋂ x : P.X, ⋂ q : P.Q, ⋂ (_ : P.xq x q = true),
          {J | dist (J (.x x)) (J (.q q)) ≤ 1}) ∩
        (⋂ q : P.Q, ⋂ z : P.Z, ⋂ (_ : P.qz q z = true),
          {J | dist (J (.q q)) (J (.z z)) ≤ 1}) := by
      ext J
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [he]
    exact (MeasurableSet.iInter fun x : P.X => MeasurableSet.iInter fun q : P.Q =>
      MeasurableSet.iInter fun _ : P.xq x q = true => hx x q).inter
      (MeasurableSet.iInter fun q : P.Q => MeasurableSet.iInter fun z : P.Z =>
        MeasurableSet.iInter fun _ : P.qz q z = true => hz q z)
  convert hedge.inter (measurableSet_density_violation P t).compl using 1
  ext J
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff,
    not_exists, not_lt, IsBoundedDensityLocalMap, and_assoc]

end QEC.Coding.BDL26RandomPerturbation
