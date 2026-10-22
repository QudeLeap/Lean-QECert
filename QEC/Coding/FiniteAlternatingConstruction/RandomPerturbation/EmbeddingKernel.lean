import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.JointExecution
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GoodMapMeasurability
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.PhysicalSuccessor
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The actual one-step embedding kernel

The numerical parameters precede the level and the incoming distribution. The
kernel maps the original independent cap table through the literal total output;
no conditioning on termination or selection of a good embedding is performed.
This one-step handoff does not construct a recursive program or its total cost.
-/
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory

theorem continuous_facePoint (P : TannerSquarePresentation) (f : P.Face) (u v : ℝ) :
    Continuous (fun J : Vertex P → Space => facePoint P J f u v) := by
  unfold facePoint foldedSquare
  split_ifs <;> fun_prop

theorem continuous_starVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (v : XStarVertex P x) :
    Continuous (fun J : Vertex P → Space => starVertexPoint P S J x v) := by
  unfold starVertexPoint
  fun_prop

theorem continuous_subdivisionVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (v : SubdivisionVertex P x S) :
    Continuous (fun J : Vertex P → Space => subdivisionVertexPoint P S J x v) := by
  rcases v with v | (⟨edge,i⟩ | ⟨f,i,j⟩)
  · exact continuous_starVertexPoint P S x v
  · let t : ℝ := ((i.val : ℝ)+1)/S.half
    exact ((continuous_starVertexPoint P S x _).const_smul (1-t)).add
      ((continuous_starVertexPoint P S x _).const_smul t)
  · exact continuous_facePoint P f.1 _ _

theorem continuous_qSubdivisionVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (v : QSubdivisionVertex P q S) :
    Continuous (fun J : Vertex P → Space => qSubdivisionVertexPoint P S J q v) := by
  rcases v with (v | edge) | ⟨edge,i⟩
  · exact continuous_apply _
  · exact ((continuous_apply _).const_smul (1-contractionRatio S)).add
      ((continuous_apply _).const_smul (contractionRatio S))
  · let t : ℝ := 2*((i.val : ℝ)+1)/S.ell
    exact ((continuous_apply _).const_smul (1-t)).add ((continuous_apply _).const_smul t)

theorem continuous_rxOnePoint (P : TannerSquarePresentation) (S : OddScale) (v : RX1 P S) :
    Continuous (fun J : Vertex P → Space => rxOnePoint P S J v) := by
  rcases v with ⟨x,edge⟩ | ⟨q,copy,v⟩
  · exact ((continuous_subdivisionVertexPoint P S x _).add
      (continuous_subdivisionVertexPoint P S x _)).const_smul (1/2 : ℝ)
  · exact continuous_qSubdivisionVertexPoint P S q v

theorem continuous_rxTwoPoint (P : TannerSquarePresentation) (S : OddScale) (v : RX2 P S) :
    Continuous (fun J : Vertex P → Space => rxTwoPoint P S J v) := by
  rcases v with (⟨x,(⟨copy,f,i,j⟩ | edge)⟩ | ⟨q,edge⟩) | ⟨z,tag⟩
  · exact continuous_facePoint P f.1 _ _
  · exact ((continuous_subdivisionVertexPoint P S x _).add
      (continuous_subdivisionVertexPoint P S x _)).const_smul (1/2 : ℝ)
  · exact ((continuous_qSubdivisionVertexPoint P S q _).add
      (continuous_qSubdivisionVertexPoint P S q _)).const_smul (1/2 : ℝ)
  · exact continuous_apply _

theorem continuous_rxVertexPoint (P : TannerSquarePresentation) (S : OddScale)
    (v : Vertex (rxReplacementPresentation P S)) :
    Continuous (fun J : Vertex P → Space => rxVertexPoint P S J v) := by
  cases v with
  | x v => exact continuous_subdivisionVertexPoint P S v.1 v.2.2
  | q v => exact continuous_rxOnePoint P S v
  | z v => exact continuous_rxTwoPoint P S v

theorem continuous_transposePointMap (P : TannerSquarePresentation) :
    Continuous (transposePointMap P (E := Space)) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_rzVertexPoint (P : TannerSquarePresentation)
    (A : BDL26TannerLocalRegularity.TannerSquareAdmissible P) (S : OddScale)
    (v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S)) :
    Continuous (fun J : Vertex P → Space => rzVertexPoint P A S J v) := by
  cases v with
  | x v =>
      exact (continuous_rxTwoPoint (transposePresentation P) S v).comp
        (continuous_transposePointMap P)
  | q v =>
      exact (continuous_rxOnePoint (transposePresentation P) S v).comp
        (continuous_transposePointMap P)
  | z v =>
      exact (continuous_subdivisionVertexPoint (transposePresentation P) S v.1 v.2.2).comp
        (continuous_transposePointMap P)

/-- Both parity branches are the actual fixed affine replacement coordinates. -/
theorem continuous_replacementOutput (S : OddScale) (n : ℕ) (C : ConstructionState) :
    Continuous (replacementOutput S n C) := by
  apply continuous_pi
  intro v
  by_cases h : n % 2 = 0
  · simp only [replacementOutput_rx S n C _ h]
    exact continuous_rxVertexPoint C.presentation S _
  · simp only [replacementOutput_rz S n C _ h]
    exact continuous_rzVertexPoint C.presentation C.admissible.toTannerSquareAdmissible S _

theorem measurable_joint_perturbationEmbeddingOutput (P : TannerSquarePresentation)
    {L : ℝ} (p : GeometricParameters L) : Measurable
      (fun z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
        perturbationEmbeddingOutput P z.1 p z.2) := by
  unfold perturbationEmbeddingOutput perturbedMap
  apply measurable_pi_lambda
  intro v
  have hcoord : Measurable (fun z : (Vertex P → Space) ×
      Table (X := fun _ : Vertex P => Space) => z.1 v) :=
    (measurable_pi_apply v).comp measurable_fst
  exact ((hcoord.const_smul (1/2 : ℝ)).const_smul (p.lambda : ℝ)).add
    ((measurable_pi_apply v).comp (measurable_joint_geometricOutput P p))

/-- Joint measurability of the literal total successor, including its default tables. -/
theorem measurable_joint_physicalSuccessorOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun z :
      (Vertex (state (perturbationOddScale p) n).presentation → Space) ×
        Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space) =>
      physicalSuccessorOutput p n z.1 z.2) :=
  (continuous_replacementOutput (perturbationOddScale p) n
    (state (perturbationOddScale p) n)).measurable.comp
      (measurable_joint_perturbationEmbeddingOutput _ p)

instance physicalTableLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (physicalTableLaw p n) := by
  let P := (state (perturbationOddScale p) n).presentation
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  change IsProbabilityMeasure
    (tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)))
  infer_instance

/-- The independent fresh table is mapped by the actual total physical successor. -/
def successorKernel {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Kernel (Vertex (state (perturbationOddScale p) n).presentation → Space)
      (Vertex (state (perturbationOddScale p) (n+1)).presentation → Space) :=
  (Kernel.id ×ₖ Kernel.const _ (physicalTableLaw p n)).map
    (fun z => physicalSuccessorOutput p n z.1 z.2)

instance successorKernel_markov {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsMarkovKernel (successorKernel p n) :=
  Kernel.IsMarkovKernel.map _ (measurable_joint_physicalSuccessorOutput p n)

private theorem map_freshTable_apply {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ν : Measure B) [SFinite ν] (F : A × B → C) (hF : Measurable F) (a : A) :
    ((Kernel.id ×ₖ Kernel.const A ν).map F) a = ν.map (fun b => F (a,b)) := by
  have hslice : Measurable (fun b => F (a,b)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  ext s hs
  rw [Kernel.map_apply _ hF, Measure.map_apply hF hs,
    Kernel.id_prod_apply' _ _ (hF hs), Kernel.const_apply, Measure.map_apply hslice hs] <;> rfl

private theorem map_freshTable_law {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    (F : A × B → C) (hF : Measurable F) :
    (μ.prod ν).map F = ((Kernel.id ×ₖ Kernel.const A ν).map F) ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro a
  have hslice : Measurable (fun b => F (a,b)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [map_freshTable_apply ν F hF a, Measure.map_apply hslice hs] <;> rfl

/-- Every input, valid or not, has the exact original pushforward measure. -/
theorem successorKernel_apply {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space) :
    successorKernel p n J = (physicalTableLaw p n).map (physicalSuccessorOutput p n J) := by
  exact map_freshTable_apply (physicalTableLaw p n)
    (fun z => physicalSuccessorOutput p n z.1 z.2)
    (measurable_joint_physicalSuccessorOutput p n) J

/-- Exact law of the literal product experiment, expressed as kernel composition. -/
theorem physicalSuccessorOutput_law {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (μ : Measure (Vertex (state (perturbationOddScale p) n).presentation → Space))
    [IsProbabilityMeasure μ] :
    (μ.prod (physicalTableLaw p n)).map (fun z => physicalSuccessorOutput p n z.1 z.2) =
      (successorKernel p n) ∘ₘ μ := by
  exact map_freshTable_law μ (physicalTableLaw p n)
    (fun z => physicalSuccessorOutput p n z.1 z.2)
    (measurable_joint_physicalSuccessorOutput p n)

/-- Only the measurable halting-and-good-map event is needed for the full endpoint. -/
theorem physicalSuccessorFacts_of_halts_localMap {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space))
    (hh : Halts (eventSupport (state (perturbationOddScale p) n).presentation J (anchorRadius p.m))
      (eventBad (state (perturbationOddScale p) n).presentation J
        (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)
    (hg : IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation
      (physicalSuccessorOutput p n J T) p.t) : PhysicalSuccessorFacts p n J T :=
  ⟨hh,hg,physicalGeometry_of_localMap _ _ _ hg,
    BDL26CSSDaviesLocality.frequency_supported _ _,
    BDL26CSSDaviesLocality.weightedJump_supported _ _⟩

theorem measurableSet_physical_success {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurableSet {z :
      (Vertex (state (perturbationOddScale p) n).presentation → Space) ×
        Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space) |
      Halts (eventSupport (state (perturbationOddScale p) n).presentation z.1 (anchorRadius p.m))
        (eventBad (state (perturbationOddScale p) n).presentation z.1
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) z.2 ∧
      IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation
        (physicalSuccessorOutput p n z.1 z.2) p.t} :=
  (measurableSet_joint_halts _ _ _ _).inter
    ((measurableSet_boundedDensityLocalMap _ _).preimage
      (measurable_joint_physicalSuccessorOutput p n))

/-- A genuine incoming probability law uses the same independent fresh cap table. -/
theorem physical_successor_random_input_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (μ : Measure (Vertex (state (perturbationOddScale p) n).presentation → Space))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ J ∂μ, IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ z ∂μ.prod (physicalTableLaw p n), PhysicalSuccessorFacts p n z.1 z.2 := by
  have hs := (Measure.ae_prod_iff_ae_ae (measurableSet_physical_success p n)).mpr (by
    filter_upwards [hμ] with J hJ
    filter_upwards [physical_successor_ae p n J hJ] with T hT
    exact ⟨hT.1,hT.2.1⟩)
  filter_upwards [hs] with z hz
  exact physicalSuccessorFacts_of_halts_localMap p n z.1 z.2 hz.1 hz.2

instance successorLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (μ : Measure (Vertex (state (perturbationOddScale p) n).presentation → Space))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure ((successorKernel p n) ∘ₘ μ) := by
  infer_instance

theorem successorLaw_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (μ : Measure (Vertex (state (perturbationOddScale p) n).presentation → Space))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ J ∂μ, IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ J' ∂(successorKernel p n) ∘ₘ μ,
      IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation J' p.t := by
  rw [← physicalSuccessorOutput_law p n μ]
  apply (ae_map_iff (measurable_joint_physicalSuccessorOutput p n).aemeasurable
    (measurableSet_boundedDensityLocalMap _ _)).mpr
  filter_upwards [physical_successor_random_input_ae p n μ hμ] with z hz
  exact hz.2.1

end QEC.Coding.BDL26RandomPerturbation
