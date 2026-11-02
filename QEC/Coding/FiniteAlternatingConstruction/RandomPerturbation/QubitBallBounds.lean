import QEC.Coding.Core.Definitions
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Density
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.PhysicalLocality
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.RandomizedEmbeddingStep

/-!
# Labelled physical-qubit ball bounds

These reusable bounds count domain labels, including distinct qubits at the
same point. Unit density supplies arbitrary-radius bounds by the existing
finite grid cover. The numerical parameter enlargement is independent of all
finite depths and contains no geometric or proof conclusion as data.
-/
noncomputable section
namespace QEC.Coding.BDL26QubitBallBounds
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26CSSHamiltonian
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- A point image retains its original qubit label. -/
theorem qubitHits_singletons (P : TannerSquarePresentation) (J : Vertex P → Space)
    (region : Set Space) :
    qubitHits P J region=familyHits (fun q : P.Q => {J (.q q)}) region := by
  ext q
  simp [qubitHits,familyHits]

/-- Integer-radius bounds follow from labelled unit density without injectivity. -/
theorem integer_ball_card (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (K : Nat) (center : Space) :
    ((qubitHits (state S n).presentation J (Metric.closedBall center K)).card : ℝ) ≤
      ((2*K+1 : Nat)^3 : ℝ)*(2*t) := by
  have h := familyHits_integer_ball_le
    (fun q : (state S n).presentation.Q => {J (.q q)}) (2*t)
    (fun c => by rw [← qubitHits_singletons]; exact geometry.1 c) K center
  rw [← qubitHits_singletons] at h
  exact h

/-- Ceiling the radius gives a finite labelled-count budget at every real radius. -/
def ballBudget (t R : ℝ) : Nat :=
  Nat.ceil (((2*Nat.ceil R+1 : Nat) : ℝ)^3*(2*t))

theorem real_ball_card (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (R : ℝ) (center : Space) :
    (qubitHits (state S n).presentation J (Metric.closedBall center R)).card ≤ ballBudget t R := by
  have sub : qubitHits (state S n).presentation J (Metric.closedBall center R) ⊆
      qubitHits (state S n).presentation J (Metric.closedBall center (Nat.ceil R)) := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact Metric.mem_closedBall.mpr
      ((Metric.mem_closedBall.mp (Finset.mem_filter.mp hq).2).trans (Nat.le_ceil R))
  have cover := integer_ball_card S n J geometry (Nat.ceil R) center
  have ceiling : ((2*Nat.ceil R+1 : Nat) : ℝ)^3*(2*t) ≤ (ballBudget t R : ℝ) :=
    Nat.le_ceil (((2*Nat.ceil R+1 : Nat) : ℝ)^3*(2*t))
  have cast : ((qubitHits (state S n).presentation J (Metric.closedBall center R)).card : ℝ) ≤
      (ballBudget t R : ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card sub)).trans (cover.trans ceiling)
  exact_mod_cast cast

/-- Every literal mask in a ball has the same label budget, even for adaptive masks. -/
theorem mask_card_le (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (R : ℝ) (center : Space)
    (A : Finset (state S n).presentation.Q)
    (inside : ∀ q ∈ A, dist (J (.q q)) center ≤ R) : A.card ≤ ballBudget t R := by
  apply (Finset.card_le_card (show A ⊆
    qubitHits (state S n).presentation J (Metric.closedBall center R) from ?_)).trans
      (real_ball_card S n J geometry R center)
  intro q hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Metric.mem_closedBall.mpr (inside q hq)⟩

/-- Only the nonzero support of a word must lie in the ball. The mask used
by a caller may also contain zero-valued coordinates outside it. -/
theorem supported_word_weight_le {F : Type*} [Zero F] [DecidableEq F]
    (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S n J t) (R : ℝ) (center : Space)
    (w : QEC.Coding.Word F (state S n).presentation.Q)
    (inside : ∀ q ∈ QEC.Coding.hammingSupport w, dist (J (.q q)) center ≤ R) :
    QEC.Coding.HammingWeight w ≤ ballBudget t R := by
  rw [QEC.Coding.HammingWeight_eq_card_hammingSupport]
  exact mask_card_le S n J geometry R center (QEC.Coding.hammingSupport w) inside

/-- Increase only the numerical subdivision multiplier; all original inequalities persist. -/
def enlargeScale {L : ℝ} (p : GeometricParameters L) : GeometricParameters L :=
  { p with
    lambda := max p.lambda 2
    lambda_one := le_trans p.lambda_one (le_max_left _ _)
    rounding := by
      have hl : (p.lambda : ℝ) ≤ (max p.lambda 2 : Nat) := by exact_mod_cast le_max_left p.lambda 2
      have hc : 0 ≤ 2*(6*(p.m : ℝ))+1 := by positivity
      exact p.rounding.trans (mul_le_mul_of_nonneg_left hl hc)
    probability := by
      exact p.probability.trans (by exact_mod_cast le_max_left p.lambda 2) }

theorem enlarged_scale_large {L : ℝ} (p : GeometricParameters L) :
    33 ≤ (perturbationOddScale (enlargeScale p)).ell := by
  have bound := (perturbationOddScale_bounds (enlargeScale p)).1
  have hm : (2 : ℝ) ≤ (enlargeScale p).m := by exact_mod_cast (enlargeScale p).m_two
  have hl : (2 : ℝ) ≤ (enlargeScale p).lambda := by
    change (2 : ℝ) ≤ (max p.lambda 2 : Nat)
    exact_mod_cast le_max_right p.lambda 2
  have base : (25 : ℝ) ≤ 2*(6*((enlargeScale p).m : ℝ))+1 := by linarith
  have product : (49 : ℝ) ≤
      (2*(6*((enlargeScale p).m : ℝ))+1)*((enlargeScale p).lambda : ℝ) := by
    calc
      (49 : ℝ) ≤ 25*2 := by norm_num
      _ ≤ _ := mul_le_mul base hl (by norm_num) (by positivity)
  have actual : (33 : ℝ) ≤ (perturbationOddScale (enlargeScale p)).ell := by linarith
  exact_mod_cast actual

/-- Legal fixed parameters with the response scale threshold exist before all depths. -/
theorem large_parameters_exist (L : ℝ) :
    ∃ p : GeometricParameters L, 33 ≤ (perturbationOddScale p).ell := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  exact ⟨enlargeScale p,enlarged_scale_large p⟩

end QEC.Coding.BDL26QubitBallBounds
