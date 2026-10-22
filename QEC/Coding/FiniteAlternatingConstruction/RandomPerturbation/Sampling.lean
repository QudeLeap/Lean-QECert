import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Coloring
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Geometry
import QEC.Coding.ProbabilisticConstruction.TriangleHit
import QEC.Coding.ProbabilisticConstruction.Resampling.TableProbability

/-! # Actual joint cap sampling and full infinite-table support -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory

/-- Axes follow the domain constructors, independently of geometric coincidences. -/
noncomputable def vertexAxis (P : TannerSquarePresentation) (v : Vertex P) : Sphere :=
  coordinateAxis (vertexColor P v)

noncomputable def vertexLaw (P : TannerSquarePresentation) (R c : ℝ) (v : Vertex P) :
    Measure Space := capDisplacementLaw R (vertexAxis P v) c

theorem vertexLaw_probability (P : TannerSquarePresentation) (R : ℝ) {c : ℝ} (hc : c < 1)
    (v : Vertex P) : IsProbabilityMeasure (vertexLaw P R c v) :=
  capDisplacementLaw_isProbabilityMeasure R (vertexAxis P v) hc

/-- The initial finite product is supported on the actual cap-valued assignments. -/
theorem finite_cap_support (P : TannerSquarePresentation) {R c : ℝ} (hR : 0 < R)
    (hc : c < 1) :
    ∀ᵐ p ∂Measure.pi (vertexLaw P R c), ∀ v,
      p v ∈ displacementCap R (vertexAxis P v) c := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  apply ae_all_iff.mpr
  intro v
  have hm := measurableSet_displacementCap R (vertexAxis P v) c
  apply (mem_ae_iff_prob_eq_one (hm.preimage (measurable_pi_apply v))).mpr
  have hp := measurePreserving_eval (vertexLaw P R c) v
  rw [hp.measure_preimage hm.nullMeasurableSet]
  exact capDisplacementLaw_capSupport hR (vertexAxis P v) hc

/-- Every entry, including all future resampling columns, has the required support. -/
theorem table_cap_support (P : TannerSquarePresentation) {R c : ℝ} (hR : 0 < R)
    (hc : c < 1) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    ∀ᵐ T ∂tableLaw (vertexLaw P R c), ∀ p : Vertex P × ℕ,
      T p ∈ displacementCap R (vertexAxis P p.1) c := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  apply ae_all_iff.mpr
  intro p
  have hm := measurableSet_displacementCap R (vertexAxis P p.1) c
  apply (mem_ae_iff_prob_eq_one (hm.preimage (measurable_pi_apply p))).mpr
  change (Measure.infinitePi (fun p : Vertex P × ℕ => vertexLaw P R c p.1))
    ((fun T => T p) ⁻¹' displacementCap R (vertexAxis P p.1) c) = 1
  have hp := measurePreserving_eval_infinitePi (fun p : Vertex P × ℕ => vertexLaw P R c p.1) p
  rw [hp.measure_preimage hm.nullMeasurableSet]
  exact capDisplacementLaw_capSupport hR (vertexAxis P p.1) hc

/-- The full-table event suffices for arbitrary counters, including data-dependent ones. -/
theorem assignment_cap_support (P : TannerSquarePresentation) {R c : ℝ} (hR : 0 < R)
    (hc : c < 1) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    ∀ᵐ T ∂tableLaw (vertexLaw P R c), ∀ n : Vertex P → ℕ, ∀ v : Vertex P,
      assignment T n v ∈ displacementCap R (vertexAxis P v) c := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  filter_upwards [table_cap_support P hR hc] with T hT
  intro n v
  exact hT (v,n v)

/-- Joint address injectivity follows from the proved incidence-rank coloring. -/
theorem monochromatic_addresses_injective (P : TannerSquarePresentation)
    {A : Type*} (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, triangleColor P (labels a) = triangleColor P (labels b)) :
    Function.Injective (fun s : (a : A) × Fin 3 => triangleVertex P (labels s.1) s.2) := by
  intro s t h
  have hab := hinj (triangleColor_same_vertex P (hcolor s.1 t.1) h)
  rcases s with ⟨a,i⟩
  rcases t with ⟨b,j⟩
  dsimp at hab
  subst b
  have hij := triangleVertex_injective P (labels a) h
  change i = j at hij
  subst j
  rfl

/-- Reindexing the actual vertex product derives a joint product of triangle laws. -/
theorem triangle_family_law (P : TannerSquarePresentation) {A : Type*} [Fintype A]
    (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, triangleColor P (labels a) = triangleColor P (labels b))
    (ν : Vertex P → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun p a i => p (triangleVertex P (labels a) i)) =
      Measure.pi (fun a => Measure.pi (fun i => ν (triangleVertex P (labels a) i))) := by
  let key : ((a : A) × Fin 3) → Vertex P := fun s => triangleVertex P (labels s.1) s.2
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := ν) (f := key) (monochromatic_addresses_injective P labels hinj hcolor)
  have hcur := congrArg
    (fun m => m.map (MeasurableEquiv.piCurry (fun (_a : A) (_i : Fin 3) => Space))) hflat
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hcur
  change _ = (Measure.infinitePi (fun s : (a : A) × Fin 3 => ν (key s))).map
    (MeasurableEquiv.piCurry (fun (_a : A) (_i : Fin 3) => Space)) at hcur
  rw [Measure.infinitePi_map_piCurry (fun (a : A) (i : Fin 3) => ν (key ⟨a,i⟩))] at hcur
  simp only [Function.comp_def,MeasurableEquiv.coe_piCurry,Measure.infinitePi_eq_pi] at hcur
  have he : (fun (p : Vertex P → Space) => Sigma.curry (fun s : (a : A) × Fin 3 => p (key s))) =
      (fun (p : Vertex P → Space) a i => p (triangleVertex P (labels a) i)) := by
    funext p a i
    rfl
  rw [he] at hcur
  exact hcur

/-- A fixed ball is tested against every selected triangle; no pairwise-only shortcut. -/
theorem monochromatic_triangle_hit_probability (P : TannerSquarePresentation)
    {A : Type*} [Fintype A] (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, triangleColor P (labels a) = triangleColor P (labels b))
    {R c ρ : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) (hρ : 0 ≤ ρ)
    (J : Vertex P → Space) (z : Space) :
    Measure.pi (vertexLaw P R c)
      {p | ∀ a, (fun i => p (triangleVertex P (labels a) i)) ∈
        triangleHit (fun i => J (triangleVertex P (labels a) i)) z ρ} ≤
      ENNReal.ofReal (18*ρ/(R*(1-c))) ^ Fintype.card A := by
  letI (v : Vertex P) := vertexLaw_probability P R hc1 v
  let read := fun (p : Vertex P → Space) a i => p (triangleVertex P (labels a) i)
  let test := fun a => triangleHit (fun i => J (triangleVertex P (labels a) i)) z ρ
  have hm : Measurable read := by fun_prop
  have ht : ∀ a, MeasurableSet (test a) := fun a => measurableSet_triangleHit _ _ _
  have he : {p | ∀ a, read p a ∈ test a} = read ⁻¹' Set.univ.pi test := by ext p; simp
  change Measure.pi (vertexLaw P R c) {p | ∀ a, read p a ∈ test a} ≤ _
  rw [he,← Measure.map_apply hm (MeasurableSet.univ_pi ht)]
  change ((Measure.pi (vertexLaw P R c)).map
    (fun p a i => p (triangleVertex P (labels a) i))) (Set.univ.pi test) ≤ _
  rw [triangle_family_law P labels hinj hcolor,Measure.pi_pi]
  calc
    _ ≤ ∏ _a : A, ENNReal.ofReal (18*ρ/(R*(1-c))) := by
      apply Finset.prod_le_prod'
      intro a _
      exact capProduct_triangleHit_le_same_cutoff hR hρ
        (fun i => vertexAxis P (triangleVertex P (labels a) i)) hc0 hc1 _ _
    _ = _ := by simp

end QEC.Coding.BDL26RandomPerturbation
