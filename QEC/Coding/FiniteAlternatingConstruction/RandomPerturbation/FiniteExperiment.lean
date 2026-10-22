import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperiment.Laws

/-!
# Original execution at every experimentPrefix of the finite experiment

These observations use the original eligible events, counter update, scan,
totalized least halting time and default output. The common master-event
carrier only represents the same original selected labels.
-/

noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

abbrev StagePresentation {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  (state (perturbationOddScale p) n).presentation

def stageCounters {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (time : ℕ) (z : Experiment p n) :=
  counters (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (stageInput p n i z)
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z) time

def stageSelected {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (time : ℕ) (z : Experiment p n) : Option (MasterEvent (StagePresentation p i.val)) :=
  (selected (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (stageInput p n i z)
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z) time).map
        (eventToMaster (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))

def stageHalts {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : Prop :=
  Halts (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (stageInput p n i z)
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z)

def stageHaltTime {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : ℕ :=
  haltTime (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (stageInput p n i z)
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z)

def stageGeometricOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : StageMaps p i.val :=
  geometricOutput (StagePresentation p i.val) (stageInput p n i z) p (tableAt p n i z)

def stagePerturbedOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : StageMaps p i.val :=
  perturbationEmbeddingOutput (StagePresentation p i.val) (stageInput p n i z) p (tableAt p n i z)

def stagePhysicalOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : StageMaps p (i.val+1) :=
  physicalSuccessorOutput p i.val (stageInput p n i z) (tableAt p n i z)

/-- Pointwise original-label conjugacy, including `none`, `some` and nonhalting inputs. -/
theorem stageSelected_original {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (time : ℕ) (z : Experiment p n) :
    stageSelected p n i time z =
      selected (masterSupport (StagePresentation p i.val))
        (masterBad (StagePresentation p i.val) (anchorRadius p.m) p.lambda
          ((6*p.m+2)*p.lambda) (stageInput p n i z)) (tableAt p n i z) time :=
  master_selected_original _ _ _ _ _ _ _

theorem stageHaltTime_of_not_halts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p n) (hh : ¬ stageHalts p n i z) :
    stageHaltTime p n i z = 0 := by
  unfold stageHalts at hh
  simp only [stageHaltTime, haltTime, dif_neg hh]

/-- Nonhalting tables return the original assignment at the zero counters. -/
theorem stageGeometricOutput_of_not_halts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p n) (hh : ¬ stageHalts p n i z) :
    stageGeometricOutput p n i z = assignment (tableAt p n i z) (fun _ => 0) := by
  unfold stageHalts at hh
  simp only [stageGeometricOutput, geometricOutput, output, haltTime, dif_neg hh, counters]

theorem stageSelected_none_iff {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (time : ℕ) (z : Experiment p n) :
    stageSelected p n i time z = none ↔
      selected (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
        (eventBad (StagePresentation p i.val) (stageInput p n i z)
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z) time = none := by
  exact Option.map_eq_none_iff

/-- Every observation of a retained stage has exactly the same input and table. -/
theorem stage_observation_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) {Y : Type*}
    (F : StageMaps p i.val × StageTables p i.val → Y) (z : Experiment p n) :
    F (stagePair p m i (experimentPrefix p m n h z)) = F (stagePair p n (i.castLE h) z) :=
  congrArg F (stagePair_prefix p h i z)

/-- All original execution data, not just the final embedding, survive truncation. -/
theorem original_execution_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (time : ℕ) (z : Experiment p n) :
    stageCounters p m i time (experimentPrefix p m n h z) = stageCounters p n (i.castLE h) time z ∧
    stageSelected p m i time (experimentPrefix p m n h z) = stageSelected p n (i.castLE h) time z ∧
    (stageHalts p m i (experimentPrefix p m n h z) ↔ stageHalts p n (i.castLE h) z) ∧
    stageHaltTime p m i (experimentPrefix p m n h z) = stageHaltTime p n (i.castLE h) z ∧
    stageGeometricOutput p m i (experimentPrefix p m n h z) = stageGeometricOutput p n (i.castLE h) z ∧
    stagePerturbedOutput p m i (experimentPrefix p m n h z) = stagePerturbedOutput p n (i.castLE h) z ∧
    stagePhysicalOutput p m i (experimentPrefix p m n h z) = stagePhysicalOutput p n (i.castLE h) z := by
  have hInput := congrArg Prod.fst (stagePair_prefix p h i z)
  have hTable := congrArg Prod.snd (stagePair_prefix p h i z)
  dsimp only [stagePair] at hInput hTable
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold stageCounters
    simp only [Fin.val_castLE]
    rw [hInput, hTable]
  · unfold stageSelected
    simp only [Fin.val_castLE]
    rw [hInput, hTable]
  · apply Iff.of_eq
    unfold stageHalts
    simp only [Fin.val_castLE]
    rw [hInput, hTable]
  · unfold stageHaltTime
    simp only [Fin.val_castLE]
    rw [hInput, hTable]
  · simpa only [stageGeometricOutput, stagePair, Fin.val_castLE] using
      stage_observation_prefix p h i
        (fun w : StageMaps p i.val × StageTables p i.val =>
          geometricOutput (StagePresentation p i.val) w.1 p w.2) z
  · simpa only [stagePerturbedOutput, stagePair, Fin.val_castLE] using
      stage_observation_prefix p h i
        (fun w : StageMaps p i.val × StageTables p i.val =>
          perturbationEmbeddingOutput (StagePresentation p i.val) w.1 p w.2) z
  · simpa only [stagePhysicalOutput, stagePair, Fin.val_castLE] using
      stage_observation_prefix p h i
        (fun w : StageMaps p i.val × StageTables p i.val => physicalSuccessorOutput p i.val w.1 w.2) z

theorem measurable_stageCounters {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (time : ℕ) : Measurable (stageCounters p n i time) := by
  let f : StageMaps p i.val × StageTables p i.val → Counters (Vertex (StagePresentation p i.val)) :=
    fun w => counters (eventSupport (StagePresentation p i.val) w.1 (anchorRadius p.m))
      (eventBad (StagePresentation p i.val) w.1 (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda)) w.2 time
  have hf : Measurable f := measurable_joint_counters (StagePresentation p i.val)
    (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) time
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val)
    (Counters (Vertex (StagePresentation p i.val))) inferInstance inferInstance inferInstance
    f (stagePair p n i) hf (measurable_stagePair p n i)

theorem measurable_stageSelected {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (time : ℕ) : Measurable (stageSelected p n i time) := by
  let f : StageMaps p i.val × StageTables p i.val → Option (MasterEvent (StagePresentation p i.val)) :=
    fun w => (selected (eventSupport (StagePresentation p i.val) w.1 (anchorRadius p.m))
      (eventBad (StagePresentation p i.val) w.1 (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda)) w.2 time).map
          (eventToMaster (StagePresentation p i.val) w.1 (anchorRadius p.m))
  have hf : Measurable f := measurable_joint_selected (StagePresentation p i.val)
    (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) time
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val)
    (Option (MasterEvent (StagePresentation p i.val))) inferInstance inferInstance inferInstance
    f (stagePair p n i) hf (measurable_stagePair p n i)

theorem measurableSet_stageHalts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) : MeasurableSet {z | stageHalts p n i z} := by
  let B : Set (StageMaps p i.val × StageTables p i.val) :=
    {w | Halts (eventSupport (StagePresentation p i.val) w.1 (anchorRadius p.m))
      (eventBad (StagePresentation p i.val) w.1 (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda)) w.2}
  have hB : MeasurableSet B := measurableSet_joint_halts (StagePresentation p i.val)
    (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
  change MeasurableSet (stagePair p n i ⁻¹' B)
  exact (measurable_stagePair p n i) hB

theorem measurable_stageHaltTime {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) : Measurable (stageHaltTime p n i) := by
  let f : StageMaps p i.val × StageTables p i.val → ℕ :=
    fun w => haltTime (eventSupport (StagePresentation p i.val) w.1 (anchorRadius p.m))
      (eventBad (StagePresentation p i.val) w.1 (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda)) w.2
  have hf : Measurable f := measurable_joint_haltTime (StagePresentation p i.val)
    (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val) ℕ
    inferInstance inferInstance inferInstance f (stagePair p n i) hf (measurable_stagePair p n i)

theorem measurable_stageGeometricOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) : Measurable (stageGeometricOutput p n i) := by
  let f : StageMaps p i.val × StageTables p i.val → StageMaps p i.val :=
    fun w => geometricOutput (StagePresentation p i.val) w.1 p w.2
  have hf : Measurable f := measurable_joint_geometricOutput (StagePresentation p i.val) p
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val) (StageMaps p i.val)
    inferInstance inferInstance inferInstance f (stagePair p n i) hf (measurable_stagePair p n i)

theorem measurable_stagePerturbedOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) : Measurable (stagePerturbedOutput p n i) := by
  let f : StageMaps p i.val × StageTables p i.val → StageMaps p i.val :=
    fun w => perturbationEmbeddingOutput (StagePresentation p i.val) w.1 p w.2
  have hf : Measurable f := measurable_joint_perturbationEmbeddingOutput (StagePresentation p i.val) p
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val) (StageMaps p i.val)
    inferInstance inferInstance inferInstance f (stagePair p n i) hf (measurable_stagePair p n i)

theorem measurable_stagePhysicalOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) : Measurable (stagePhysicalOutput p n i) := by
  let f : StageMaps p i.val × StageTables p i.val → StageMaps p (i.val+1) :=
    fun w => physicalSuccessorOutput p i.val w.1 w.2
  have hf : Measurable f := measurable_joint_physicalSuccessorOutput p i.val
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val) (StageMaps p (i.val+1))
    inferInstance inferInstance inferInstance f (stagePair p n i) hf (measurable_stagePair p n i)

/-- The physical endpoint is the literal next history entry at every experiment point. -/
theorem history_stage {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) :
    history p n z ⟨i.val+1, by omega⟩ = stagePhysicalOutput p n i z :=
  evaluate_prefix_succ p i.isLt z

theorem stagePhysicalOutput_rx {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (h : i.val % 2 = 0) (z : Experiment p n) :
    stagePhysicalOutput p n i z = fun v =>
      rxVertexPoint _ (perturbationOddScale p) (stagePerturbedOutput p n i z)
        (nextRXVertex _ i.val (state (perturbationOddScale p) i.val) h v) :=
  physicalSuccessorOutput_rx p i.val _ _ h

theorem stagePhysicalOutput_rz {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (h : ¬ i.val % 2 = 0) (z : Experiment p n) :
    stagePhysicalOutput p n i z = fun v =>
      rzVertexPoint _ (state (perturbationOddScale p) i.val).admissible.toTannerSquareAdmissible
        (perturbationOddScale p) (stagePerturbedOutput p n i z)
        (nextRZVertex _ i.val (state (perturbationOddScale p) i.val) h v) :=
  physicalSuccessorOutput_rz p i.val _ _ h

end QEC.Coding.BDL26FiniteEmbeddingExperiment
