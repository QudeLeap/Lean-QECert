import QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Execution
import QEC.Coding.FiniteAlternatingConstruction.DecodingGraph

/-!
# Variable labels in the SAME geometric perturbation experiment

Event P J r and geometricEventOrder are unchanged. Supports, local predicates
and native vertex laws are pulled through u. No fresh Tanner rank/section/order
or setup/operational-cost theorem is asserted. BDL26 v1 paper.tex:1428 and
2227–2238 are context for this project-derived internal refinement.
-/
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation.VariableRelabeling

open BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26DecodingGraph
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- SAME original geometric event labels and their original rank-derived order. -/
def pulledSupport (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ)
    (u : A ≃ Vertex P) : Event P J r → Finset A := codedSupport u (eventSupport P J r)

def pulledBad (P : TannerSquarePresentation) (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ)
    (u : A ≃ Vertex P) : ∀ e, Set (pulledSupport P J r u e → Space) :=
  codedBad u (eventSupport P J r) (eventBad P J r lambda K)

def pulledOutput (P : TannerSquarePresentation) (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ)
    (u : A ≃ Vertex P) (T : HTable A Space) : A → Space :=
  output (pulledSupport P J r u) (pulledBad P J r lambda K u) T

/-- Native original cap law at the transported vertex, not fresh native colors. -/
def pulledVertexLaw (P : TannerSquarePresentation) (R c : ℝ) (u : A ≃ Vertex P) (a : A) :
    Measure Space := vertexLaw P R c (u a)

theorem pulledVertexLaw_probability (P : TannerSquarePresentation) (R c : ℝ) (hc : c<1)
    (u : A ≃ Vertex P) (a : A) : IsProbabilityMeasure (pulledVertexLaw P R c u a) :=
  vertexLaw_probability P R hc (u a)

theorem support_membership (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ)
    (u : A ≃ Vertex P) (e : Event P J r) (a : A) :
    a∈pulledSupport P J r u e ↔ u a∈eventSupport P J r e := mem_codedSupport u _ e a

theorem original_firstBadFrom (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (L : List (Event P J r)) (z : A → Space) :
    firstBadFrom (localEvent (pulledSupport P J r u) (pulledBad P J r lambda K u)) L z=
      firstBadFrom (localEvent (eventSupport P J r) (eventBad P J r lambda K)) L
        (decodeAssignment u z) := firstBadFrom_conjugacy u _ _ L z

theorem original_counters (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P)
    (T : HTable (Vertex P) Space) (m : ℕ) (a : A) :
    counters (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T) m a=
      counters (eventSupport P J r) (eventBad P J r lambda K) T m (u a) :=
  congrFun (counters_conjugacy u _ _ T m) a

theorem original_selected (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) (m : ℕ) :
    selected (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T) m=
      selected (eventSupport P J r) (eventBad P J r lambda K) T m :=
  selected_conjugacy u _ _ T m

theorem original_halts (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) :
    Halts (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T) ↔
      Halts (eventSupport P J r) (eventBad P J r lambda K) T := halts_conjugacy u _ _ T

theorem original_haltTime (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) :
    haltTime (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T)=
      haltTime (eventSupport P J r) (eventBad P J r lambda K) T := haltTime_conjugacy u _ _ T

theorem original_output (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) (a : A) :
    pulledOutput P J r lambda K u (encodeTable u T) a=
      output (eventSupport P J r) (eventBad P J r lambda K) T (u a) :=
  congrFun (output_conjugacy u _ _ T) a

theorem original_prefixCount (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space)
    (m : ℕ) (e : Event P J r) :
    prefixCount (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T) m e=
      prefixCount (eventSupport P J r) (eventBad P J r lambda K) T m e :=
  prefixCount_conjugacy u _ _ T m e

theorem original_totalCount (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) (e : Event P J r) :
    totalCount (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T) e=
      totalCount (eventSupport P J r) (eventBad P J r lambda K) T e :=
  totalCount_conjugacy u _ _ T e

theorem original_totalSteps (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) :
    totalSteps (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T)=
      totalSteps (eventSupport P J r) (eventBad P J r lambda K) T :=
  totalSteps_conjugacy u _ _ T

theorem original_nonhalting_output (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space)
    (h : ¬Halts (eventSupport P J r) (eventBad P J r lambda K) T) :
    pulledOutput P J r lambda K u (encodeTable u T)=fun a => T (u a,0) :=
  nonhalting_output u _ _ T h

theorem measurable_pulledOutput (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) :
    Measurable (pulledOutput P J r lambda K u) :=
  measurable_output (X := fun _ : A => Space) _ _ (measurableSet_codedBad u _ _ (measurableSet_eventBad P J r lambda K))

/-- This uses the same original geometric parameter package, including C0. -/
theorem geometric_output (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (u : A ≃ Vertex P)
    (T : HTable (Vertex P) Space) (a : A) :
    pulledOutput P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) u (encodeTable u T) a=
      geometricOutput P J p T (u a) := original_output P J _ _ _ u T a

/-- The literal original perturbation, not a new interpolation or coordinate law. -/
theorem perturbed_expression (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (u : A ≃ Vertex P)
    (T : HTable (Vertex P) Space) (a : A) :
    p.lambda • ((1/2 : ℝ) • (J ∘ u) a)+
      pulledOutput P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) u (encodeTable u T) a=
      perturbedMap P J p.lambda (geometricOutput P J p T) (u a) := by
  rw [geometric_output]
  change p.lambda • ((1/2 : ℝ) • J (u a))+geometricOutput P J p T (u a)=
    (p.lambda : ℝ) • ((1/2 : ℝ) • J (u a))+geometricOutput P J p T (u a)
  rw [Nat.cast_smul_eq_nsmul]

/-- Current native original cap coordinates reindex without changing Nat columns. -/
theorem pulled_table_law (P : TannerSquarePresentation) (R c : ℝ) (hc : c<1)
    (u : A ≃ Vertex P) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    letI (a : A) := pulledVertexLaw_probability P R c hc u a
    (tableLaw (vertexLaw P R c)).map (encodeTable u)=tableLaw (pulledVertexLaw P R c u) := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  letI (a : A) := pulledVertexLaw_probability P R c hc u a
  exact table_law u (vertexLaw P R c)

/-- All counters, event path, Halts flag, least time, output and all counts jointly. -/
theorem original_joint_observation (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) :
    decodedObservation u (eventSupport P J r) (eventBad P J r lambda K) (encodeTable u T)=
      jointObservation (eventSupport P J r) (eventBad P J r lambda K) T :=
  jointObservation_conjugacy u _ _ T

theorem measurable_original_joint_observation (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) :
    Measurable (decodedObservation u (eventSupport P J r) (eventBad P J r lambda K)) :=
  measurable_decodedObservation u _ _ (measurableSet_eventBad P J r lambda K)

/-- Native pulled laws give the complete joint law, no output-marginal substitution. -/
theorem original_joint_law (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (R c : ℝ) (hc : c<1) (u : A ≃ Vertex P) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    letI (a : A) := pulledVertexLaw_probability P R c hc u a
    (tableLaw (pulledVertexLaw P R c u)).map
      (decodedObservation u (eventSupport P J r) (eventBad P J r lambda K))=
      (tableLaw (vertexLaw P R c)).map
        (jointObservation (eventSupport P J r) (eventBad P J r lambda K)) := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  letI (a : A) := pulledVertexLaw_probability P R c hc u a
  exact jointObservation_law u _ _ (measurableSet_eventBad P J r lambda K) (vertexLaw P R c)

end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
