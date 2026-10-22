import QEC.Coding.ProbabilisticConstruction.SphericalCap.TriangleGeometry

/-!
# Joint triangle hits

The compact simplex witness works when all vertices, perturbations, the centre
and the radius vary. No affine independence or positive radius is required.
-/
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators

/-- Compact barycentric witnesses give a closed relation for all varying data. -/
theorem isClosed_triangleHit_of_continuous {Y : Type*} [TopologicalSpace Y]
    (r p : Y → Fin 3 → Space) (z : Y → Space) (ρ : Y → ℝ)
    (hr : Continuous r) (hp : Continuous p) (hz : Continuous z) (hρ : Continuous ρ) :
    IsClosed {y | p y ∈ triangleHit (r y) (z y) (ρ y)} := by
  let E : Set (Y × stdSimplex ℝ (Fin 3)) :=
    {yw | dist (∑ j, (yw.2 : Fin 3 → ℝ) j • (r yw.1 j+p yw.1 j))
      (z yw.1) ≤ ρ yw.1}
  have hw (j : Fin 3) : Continuous
      (fun yw : Y × stdSimplex ℝ (Fin 3) => (yw.2 : Fin 3 → ℝ) j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  have hv (j : Fin 3) : Continuous
      (fun yw : Y × stdSimplex ℝ (Fin 3) => r yw.1 j+p yw.1 j) :=
    (((continuous_apply j).comp hr).comp continuous_fst).add
      (((continuous_apply j).comp hp).comp continuous_fst)
  have hs : Continuous (fun yw : Y × stdSimplex ℝ (Fin 3) =>
      ∑ j, (yw.2 : Fin 3 → ℝ) j • (r yw.1 j+p yw.1 j)) :=
    continuous_finset_sum _ fun j _ => (hw j).smul (hv j)
  have hc : IsClosed E :=
    isClosed_le (hs.dist (hz.comp continuous_fst)) (hρ.comp continuous_fst)
  have he : {y | p y ∈ triangleHit (r y) (z y) (ρ y)} = Prod.fst '' E := by
    ext y
    simp only [Set.mem_setOf_eq, triangleHit_iff_weights, Set.mem_image, Prod.exists]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨y,w,hw,rfl⟩
    · rintro ⟨y',w,hw,he⟩
      subst y'
      exact ⟨w,hw⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc

/-- Complete joint data, with the perturbation array as the last coordinate. -/
abbrev TriangleHitData := (Fin 3 → Space) × Space × ℝ × (Fin 3 → Space)

theorem isClosed_jointTriangleHit : IsClosed
    {d : TriangleHitData | d.2.2.2 ∈ triangleHit d.1 d.2.1 d.2.2.1} :=
  isClosed_triangleHit_of_continuous (fun d : TriangleHitData => d.1)
    (fun d => d.2.2.2) (fun d => d.2.1) (fun d => d.2.2.1)
    continuous_fst continuous_snd.snd.snd continuous_snd.fst continuous_snd.snd.fst

/-- Joint Borel input data pull back the actual convex-hull hit relation. -/
theorem measurableSet_triangleHit_of_measurable {Y : Type*} [MeasurableSpace Y]
    (r p : Y → Fin 3 → Space) (z : Y → Space) (ρ : Y → ℝ)
    (hr : Measurable r) (hp : Measurable p) (hz : Measurable z) (hρ : Measurable ρ) :
    MeasurableSet {y | p y ∈ triangleHit (r y) (z y) (ρ y)} := by
  let F : Y → TriangleHitData := fun y => (r y,z y,ρ y,p y)
  have htail : Measurable (fun y => (ρ y,p y)) := hρ.prodMk hp
  have hmiddle : Measurable (fun y => (z y,ρ y,p y)) := hz.prodMk htail
  have hF : Measurable F := hr.prodMk hmiddle
  have hclosed : MeasurableSet
      {d : TriangleHitData | d.2.2.2 ∈ triangleHit d.1 d.2.1 d.2.2.1} :=
    isClosed_jointTriangleHit.measurableSet
  have hpull : MeasurableSet
      (F ⁻¹' {d : TriangleHitData | d.2.2.2 ∈ triangleHit d.1 d.2.1 d.2.2.1}) :=
    hclosed.preimage hF
  exact hpull

end QEC.Coding.ProbabilisticConstruction.SphericalCap
