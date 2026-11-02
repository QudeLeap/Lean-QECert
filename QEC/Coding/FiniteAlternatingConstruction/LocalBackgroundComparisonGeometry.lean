import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.QubitBallBounds
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeFiniteComposition
import QEC.Coding.FiniteAlternatingConstruction.LocalBackgroundComparisonDepth

/-!
# A fixed physical-radius response cannot preserve every logical defect

The background and flipped qubit are selected in the actual code BEFORE the
random coordinate history. Every successful native history, every centre and
every literal restricted word are then covered simultaneously. Only support
containment is required: the restriction mask may contain irrelevant zero
coordinates outside the ball. Distinct labels at one point are retained.
-/
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalBackgroundComparisonResponse BDL26LocalBackgroundComparisonDepth
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- This predicate uses the literal full residuals and the literal restricted
background. It is a proved semantic postcondition, never an input certificate. -/
def ChangesDefect (S : OddScale) (n : Nat) (g : W S n) (q : Q S n)
    (A : Finset (Q S n)) : Prop :=
  BDL26AllDepthBottomComparisonStability.residual S n
    (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
    (canonicalBasisWord (F:=BDL26Field) q)-
  BDL26AllDepthBottomComparisonStability.residual S n
    (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      (backgroundRestriction S n g A)) (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n

/-- Physical level is suffix depth PLUS TWO, on the same native history. -/
def responseLevel (t R : ℝ) : Nat := budgetDepth (ballBudget t R)+2

theorem responseLevel_source_even (t R : ℝ) :
    responseLevel t R=2*(4*ballBudget t R+2) ∧ 0 < responseLevel t R := by
  have h := budgetDepth_source_even (ballBudget t R)
  unfold responseLevel
  omega

/-- One genuine bad background/flip works for EVERY successful native history
and EVERY support-contained restricted word at every centre. -/
theorem native_response_obstruction {L : ℝ} (p : GeometricParameters L)
    (large : 33 ≤ (perturbationOddScale p).ell) (R : ℝ) :
    ∃ (g : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))
      (q : Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R))),
      ballBudget p.t R < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠
        (0 : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) ∧
      BDL26AllDepthBottomComparisonStability.residual (perturbationOddScale p) (budgetDepth (ballBudget p.t R))
        (perturbTop (perturbationOddScale p) (budgetDepth (ballBudget p.t R))
          (BDL26NonzeroBackgroundComparisonStability.zeroInput (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉
          boundaries (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) ∧
      ∀ (z : BDL26NativeFiniteComposition.Experiment p (responseLevel p.t R)),
        z ∈ BDL26NativeFiniteComposition.finiteSuccess p (responseLevel p.t R) →
        ∀ (center : Space) (A : Finset (Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))),
          (∀ u ∈ hammingSupport (backgroundRestriction (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g A),
            dist (BDL26NativeFiniteComposition.history p (responseLevel p.t R) z
              (Fin.last (responseLevel p.t R)) (.q u)) center ≤ R) →
          ChangesDefect (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g q A := by
  let S := perturbationOddScale p
  let B := ballBudget p.t R
  let n := budgetDepth B
  obtain ⟨P,q,hP,hq,hn,heavy,nonzero,flip,bad,exclude⟩ := fixed_scale_no_bounded_response S large B
  let g := backgroundRestriction S n (BDL26HistoryLogicalResidual.logicalError S n) P
  refine ⟨g,q,heavy,nonzero,flip,bad,?_⟩
  intro z success center A inside
  have geometry := BDL26NativeFiniteComposition.finiteSuccess_geometry p (responseLevel p.t R) success
    (Fin.last (responseLevel p.t R))
  have small : HammingWeight (backgroundRestriction S n g A) ≤ B :=
    supported_word_weight_le S (n+2) _ geometry R center (backgroundRestriction S n g A) inside
  exact exclude A small

/-- The mask-contained version permits arbitrary adaptive masks and centres. -/
theorem support_inside_of_mask_inside (S : OddScale) (n : Nat) (g : W S n)
    (A : Finset (Q S n)) (J : Vertex (state S (n+2)).presentation → Space)
    (center : Space) (R : ℝ) (inside : ∀ q ∈ A, dist (J (.q q)) center ≤ R) :
    ∀ q ∈ hammingSupport (backgroundRestriction S n g A), dist (J (.q q)) center ≤ R := by
  intro q hq
  have member : q ∈ A := by
    by_contra outside
    have zero : backgroundRestriction S n g A q=0 := by
      simp [backgroundRestriction,BDL26NonzeroBackgroundComparisonStability.partialWord,outside]
    exact (Finset.mem_filter.mp hq).2 zero
  exact inside q member

/-- The same deterministic background/flip is chosen before the almost-sure
history quantifier; no uncountable intersection of AE events is used. -/
theorem native_response_obstruction_ae {L : ℝ} (p : GeometricParameters L)
    (large : 33 ≤ (perturbationOddScale p).ell) (R : ℝ) :
    ∃ (g : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))
      (q : Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R))),
      g ≠ 0 ∧ canonicalBasisWord (F:=BDL26Field) q ≠
        (0 : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (responseLevel p.t R),
        ∀ (center : Space) (A : Finset (Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))),
          (∀ u ∈ hammingSupport (backgroundRestriction (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g A),
            dist (BDL26NativeFiniteComposition.history p (responseLevel p.t R) z
              (Fin.last (responseLevel p.t R)) (.q u)) center ≤ R) →
          ChangesDefect (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g q A := by
  obtain ⟨g,q,heavy,nonzero,flip,bad,all⟩ := native_response_obstruction p large R
  refine ⟨g,q,nonzero,flip,?_⟩
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p (responseLevel p.t R)] with z success
  exact all z success

/-- One legal numerical choice precedes every radius and every resulting depth.
Existence of the original native experiment and its geometry is proved, not assumed. -/
theorem fixed_parameters_before_all_radii (L : ℝ) :
    ∃ p : GeometricParameters L, 33 ≤ (perturbationOddScale p).ell ∧
      ∀ R : ℝ,
    ∃ (g : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))
      (q : Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R))),
      g ≠ 0 ∧ canonicalBasisWord (F:=BDL26Field) q ≠
        (0 : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (responseLevel p.t R),
        ∀ (center : Space) (A : Finset (Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))),
          (∀ u ∈ hammingSupport (backgroundRestriction (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g A),
            dist (BDL26NativeFiniteComposition.history p (responseLevel p.t R) z
              (Fin.last (responseLevel p.t R)) (.q u)) center ≤ R) →
          ChangesDefect (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g q A := by
  obtain ⟨p,large⟩ := large_parameters_exist L
  exact ⟨p,large,fun R => native_response_obstruction_ae p large R⟩

end QEC.Coding.BDL26LocalBackgroundComparisonGeometry
