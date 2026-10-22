import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Density
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.SupportGeometry
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Sampling

/-! # Actual supported perturbations supply the replacement geometry interface -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

noncomputable def perturbedMap (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (p : Vertex P → Space) : Vertex P → Space :=
  fun v => lambda • ((1/2 : ℝ) • J v)+p v

/-- The approved halfscale preprocessing supplies all three old diameter bounds. -/
theorem scaled_half_triangle_sides (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) {lambda : ℝ} (hl : 0 ≤ lambda)
    (a : Triangle P) (i j : Fin 3) :
    ‖lambda • ((1/2 : ℝ) • J (triangleVertex P a i))-
      lambda • ((1/2 : ℝ) • J (triangleVertex P a j))‖ ≤ lambda := by
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hl]
  simpa using mul_le_mul_of_nonneg_left (half_triangle_sides P J t hJ a i j) hl

theorem supported_triangle_pair (P : TannerSquarePresentation) {R θ : ℝ}
    (hR : 0 < R) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/24) (p : Vertex P → Space)
    (hp : ∀ v, p v ∈ displacementCap R (vertexAxis P v) (Real.cos θ))
    (a : Triangle P) {i j : Fin 3} (hij : i ≠ j) :
    R ≤ ‖p (triangleVertex P a i)-p (triangleVertex P a j)‖ ∧
      ⟪p (triangleVertex P a i),p (triangleVertex P a j)⟫_ℝ ≤ R^2/4 := by
  have hi : p (triangleVertex P a i) ∈ displacementCap R (coordinateAxis i) (Real.cos θ) := by
    simpa only [vertexAxis,vertexColor_triangleVertex] using hp (triangleVertex P a i)
  have hj : p (triangleVertex P a j) ∈ displacementCap R (coordinateAxis j) (Real.cos θ) := by
    simpa only [vertexAxis,vertexColor_triangleVertex] using hp (triangleVertex P a j)
  exact ⟨supported_pair_chord _ _ hR hθ0 hθ1 hij hi hj,
    supported_pair_inner _ _ hR hθ0 hθ1 hij hi hj⟩

/-- Source bounds apply to the actual map and the genuinely rounded odd scale. -/
theorem supported_incoming_geometry (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) {m : ℕ} (hm : 2 ≤ m)
    {lambda : ℝ} (hl : 0 < lambda) (S : OddScale)
    (hscale : (2*(6*(m : ℝ))+1)*lambda ≤ S.ell) (p : Vertex P → Space)
    (hp : ∀ v, p v ∈ displacementCap (6*(m : ℝ)*lambda) (vertexAxis P v)
      (Real.cos (1/(12*(m : ℝ))))) :
    IncomingFaceGeometry P S (perturbedMap P J lambda p)
      (((m : ℝ)-1)*lambda) ((6*(m : ℝ)*widthFactor-1)*lambda) := by
  let R : ℝ := 6*(m : ℝ)*lambda
  let old : Vertex P → Space := fun v => lambda • ((1/2 : ℝ) • J v)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hR : 0 < R := by dsimp [R]; positivity
  have hθ := cap_integer_narrow hm
  have hold (a : Triangle P) (i j : Fin 3) :
      ‖old (triangleVertex P a i)-old (triangleVertex P a j)‖ ≤ lambda :=
    scaled_half_triangle_sides P J t hJ hl.le a i j
  have hpair (a : Triangle P) (i j : Fin 3) (hij : i ≠ j) :=
    supported_triangle_pair P hR hθ.1.le hθ.2 p hp a hij
  have hedges (a : Triangle P) (i j : Fin 3) (hij : i ≠ j) :
      ((m : ℝ)-1)*lambda ≤
        ‖perturbedMap P J lambda p (triangleVertex P a i)-perturbedMap P J lambda p (triangleVertex P a j)‖ ∧
      ‖perturbedMap P J lambda p (triangleVertex P a i)-perturbedMap P J lambda p (triangleVertex P a j)‖ ≤
        (2*(6*(m : ℝ))+1)*lambda := by
    have hlow := perturbed_edge_lower _ _ _ _ (hpair a i j hij).1 (hold a i j)
    have hupp := perturbed_edge_upper _ _ _ _ (hp (triangleVertex P a i)).1
      (hp (triangleVertex P a j)).1 (hold a i j)
    change R-lambda ≤ ‖perturbedMap P J lambda p (triangleVertex P a i)-
      perturbedMap P J lambda p (triangleVertex P a j)‖ at hlow
    change ‖perturbedMap P J lambda p (triangleVertex P a i)-
      perturbedMap P J lambda p (triangleVertex P a j)‖ ≤ 2*R+lambda at hupp
    dsimp [R] at hlow hupp
    have hml : 0 ≤ (m : ℝ)*lambda := mul_nonneg (by positivity) hl.le
    constructor <;> nlinarith
  apply incomingFaceGeometry_of_source_bounds P S _ hscale
  · intro f s; exact (hedges (f,s) 1 0 (by decide)).1
  · intro f; exact (hedges (f,0) 2 0 (by decide)).1
  · intro f s; exact (hedges (f,s) 2 1 (by decide)).1
  · intro f s; exact (hedges (f,s) 1 0 (by decide)).2
  · intro f; exact (hedges (f,0) 2 0 (by decide)).2
  · intro f s; exact (hedges (f,s) 2 1 (by decide)).2
  · intro f s
    let a : Triangle P := (f,s)
    have hw := perturbed_triangle_width
      (old (triangleVertex P a 0)) (old (triangleVertex P a 1)) (old (triangleVertex P a 2))
      (p (triangleVertex P a 0)) (p (triangleVertex P a 1)) (p (triangleVertex P a 2))
      hR (hp _).1 (hp _).1 (hp _).1
      (hpair a 0 1 (by decide)).2 (hpair a 0 2 (by decide)).2 (hpair a 1 2 (by decide)).2
      (hold a 0 1) (hold a 0 2) (hold a 1 2)
    have hwidth : (6*(m : ℝ)*widthFactor-1)*lambda ≤ R*(1-1/4)-lambda := by
      have hb := mul_le_mul_of_nonneg_left widthFactor_le_three_quarters hR.le
      dsimp [R] at hb ⊢
      nlinarith
    exact ⟨fun u hu0 hu1 => hwidth.trans (hw.1 u hu0 hu1),
      fun u hu0 hu1 => hwidth.trans (hw.2.1 u hu0 hu1),
      fun u hu0 hu1 => hwidth.trans (hw.2.2 u hu0 hu1)⟩

end QEC.Coding.BDL26RandomPerturbation
