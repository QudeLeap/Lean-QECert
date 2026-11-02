import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.QubitBallBounds
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeFiniteComposition
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.RXIncidenceHullRetainedGrowth

/-!
# Actual singleton hulls escape every fixed physical ball

Retained-root growth and measured labelled density are both needed. The
coordinate histories and their original law are unchanged; no injectivity or
connectivity of the complete successor carrier is assumed.
-/
noncomputable section
namespace QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- An explicit legal even RX source level above the finite ball budget. -/
def hullLevel (B : Nat) : Nat := 2*(B+1)

def hullStep (B : Nat) : StepIndex (hullLevel B+1) := ⟨hullLevel B,by omega⟩

theorem hullStep_even (B : Nat) : (hullStep B).val % 2=0 := by
  change (2*(B+1))%2=0
  omega

theorem singleton_above_budget (S : OddScale) (B : Nat) :
    B < (incidenceHull S (hullLevel B+1) (hullStep B) (seed S (hullLevel B))).card := by
  have lower := singleton_hull_card_lower S (hullLevel B+1) (hullStep B)
  have power := (hullLevel B).lt_two_pow_self
  have level : B < hullLevel B := by unfold hullLevel; omega
  change 5*2^(hullLevel B) ≤
    (incidenceHull S (hullLevel B+1) (hullStep B) (seed S (hullLevel B))).card at lower
  omega

/-- Cardinality becomes a spatial escape only after applying actual density. -/
theorem large_mask_escapes (S : OddScale) (m : Nat)
    (J : Vertex (state S m).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S m J t) (R : ℝ)
    (A : Finset (state S m).presentation.Q) (heavy : ballBudget t R < A.card)
    (center : Space) : ∃ q ∈ A, R < dist (J (.q q)) center := by
  by_contra none
  have inside : ∀ q ∈ A, dist (J (.q q)) center ≤ R := by
    intro q hq
    exact le_of_not_gt (fun beyond => none ⟨q,hq,beyond⟩)
  have bound := mask_card_le S m J geometry R center A inside
  omega

theorem singleton_escapes (S : OddScale) {t : ℝ} (R : ℝ)
    (J : Vertex (state S (hullLevel (ballBudget t R))).presentation → Space)
    (geometry : PhysicalGeometry S (hullLevel (ballBudget t R)) J t) (center : Space) :
    ∃ q ∈ incidenceHull S (hullLevel (ballBudget t R)+1) (hullStep (ballBudget t R))
      (seed S (hullLevel (ballBudget t R))), R < dist (J (.q q)) center :=
  large_mask_escapes S _ J geometry R _ (singleton_above_budget S _) center

/-- Every successful original native history has this same singleton escape. -/
theorem native_singleton_escapes {L : ℝ} (p : GeometricParameters L) (R : ℝ)
    {z : BDL26NativeFiniteComposition.Experiment p (hullLevel (ballBudget p.t R)+1)}
    (success : z ∈ BDL26NativeFiniteComposition.finiteSuccess p (hullLevel (ballBudget p.t R)+1))
    (center : Space) :
    ∃ q ∈ incidenceHull (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
      (hullStep (ballBudget p.t R)) (seed (perturbationOddScale p) (hullLevel (ballBudget p.t R))),
      R < dist (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
        ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by
  exact singleton_escapes (perturbationOddScale p) R _
    (BDL26NativeFiniteComposition.finiteSuccess_geometry p _ success
      ⟨hullLevel (ballBudget p.t R),by omega⟩) center

/-- The lower mask of every original all-word commuting pair escapes too. -/
theorem native_commuting_mask_escapes {L : ℝ} (p : GeometricParameters L) (R : ℝ)
    {z : BDL26NativeFiniteComposition.Experiment p (hullLevel (ballBudget p.t R)+1)}
    (success : z ∈ BDL26NativeFiniteComposition.finiteSuccess p (hullLevel (ballBudget p.t R)+1))
    (A : Finset (state (perturbationOddScale p) (hullLevel (ballBudget p.t R))).presentation.Q)
    (B : Finset (FamilyZ (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
      (hullStep (ballBudget p.t R)).succ))
    (hseed : seed (perturbationOddScale p) (hullLevel (ballBudget p.t R)) ⊆ A)
    (commutes : ∀ w, maskWord B
      (nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1) (hullStep (ballBudget p.t R)) w) =
      nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
        (hullStep (ballBudget p.t R)) (maskWord A w)) (center : Space) :
    ∃ q ∈ A, R < dist
      (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
        ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by
  obtain ⟨q,hq,outside⟩ := native_singleton_escapes p R success center
  have contains := (incidenceHull_le_every_commuting_pair (perturbationOddScale p)
    (hullLevel (ballBudget p.t R)+1) (hullStep (ballBudget p.t R)) (hullStep_even _) _ A B hseed commutes).1
  exact ⟨q,contains hq,outside⟩

/-- Universal successful-history conclusions lift to the original native law. -/
theorem native_singleton_escapes_ae {L : ℝ} (p : GeometricParameters L) (R : ℝ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (hullLevel (ballBudget p.t R)+1),
      ∀ center : Space,
        ∃ q ∈ incidenceHull (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
          (hullStep (ballBudget p.t R)) (seed (perturbationOddScale p) (hullLevel (ballBudget p.t R))),
          R < dist (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
            ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p (hullLevel (ballBudget p.t R)+1)] with z success
  exact native_singleton_escapes p R success

/-- All commuting masks and centres are simultaneous under the original law. -/
theorem native_commuting_mask_escapes_ae {L : ℝ} (p : GeometricParameters L) (R : ℝ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (hullLevel (ballBudget p.t R)+1),
      ∀ (A : Finset (state (perturbationOddScale p) (hullLevel (ballBudget p.t R))).presentation.Q)
    (B : Finset (FamilyZ (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
      (hullStep (ballBudget p.t R)).succ))
    (hseed : seed (perturbationOddScale p) (hullLevel (ballBudget p.t R)) ⊆ A)
    (commutes : ∀ w, maskWord B
      (nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1) (hullStep (ballBudget p.t R)) w) =
      nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
        (hullStep (ballBudget p.t R)) (maskWord A w)) (center : Space),
    ∃ q ∈ A, R < dist
      (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
        ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p (hullLevel (ballBudget p.t R)+1)] with z success
  exact native_commuting_mask_escapes p R success

end QEC.Coding.BDL26RXIncidenceHullGeometry
