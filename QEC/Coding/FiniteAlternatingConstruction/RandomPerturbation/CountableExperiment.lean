import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountableExperiment.Core
import Mathlib.Probability.Independence.InfinitePi

/-!
# One actual countable stage-table experiment

The common measure has exactly the original finite experiment laws. Only
tables are independent. All finite observations and outputs retain their
original total execution, including exceptional nonhalting tables.
-/

noncomputable section
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators

def streamLaw {L : ℝ} (p : GeometricParameters L) : Measure (Omega p) :=
  Measure.infinitePi (fun n => physicalTableLaw p n)

instance streamLaw_probability {L : ℝ} (p : GeometricParameters L) :
    IsProbabilityMeasure (streamLaw p) := by
  unfold streamLaw
  infer_instance

/-- The original nested law, read as its full dependent vector, is the product law. -/
theorem unpackTables_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (experimentLaw p n).map (unpackTables p n) =
      Measure.pi (fun i : Fin n => physicalTableLaw p i.val) := by
  symm
  apply Measure.pi_eq
  intro B hB
  have heq : unpackTables p n ⁻¹' Set.univ.pi B =
      {z : Experiment p n | ∀ i, tableAt p n i z ∈ B i} := by
    ext z
    simp [unpackTables]
  rw [Measure.map_apply (measurable_unpackTables p n) (MeasurableSet.univ_pi hB), heq]
  exact full_rectangle_probability p n B

theorem packTables_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (Measure.pi (fun i : Fin n => physicalTableLaw p i.val)).map (packTables p n) =
      experimentLaw p n := by
  rw [← unpackTables_law p n,
    Measure.map_map (measurable_packTables p n) (measurable_unpackTables p n)]
  have heq : packTables p n ∘ unpackTables p n = id := funext (pack_unpackTables p n)
  rw [heq, Measure.map_id]

/-- Injective restriction of the genuine infinite product, not a supplied marginal. -/
theorem restrictTables_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (restrictTables p n) =
      Measure.pi (fun i : Fin n => physicalTableLaw p i.val) := by
  change (Measure.infinitePi (physicalTableLaw p)).map
    (fun omega : (j : ℕ) → StageTables p j => fun i : Fin n => omega i.val) =
      Measure.pi (fun i : Fin n => physicalTableLaw p i.val)
  exact (Measure.map_infinitePi_infinitePi_of_inj
    (Ω := StageTables p)
    (mΩ := fun j => inferInstanceAs (MeasurableSpace (StageTables p j)))
    (P := physicalTableLaw p) (f := fun i : Fin n => i.val)
    (by intro i j hij; exact Fin.ext hij)).trans
      (Measure.infinitePi_eq_pi (fun i : Fin n => physicalTableLaw p i.val))

theorem truncate_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (truncate p n) = experimentLaw p n := by
  calc
    (streamLaw p).map (truncate p n) =
        ((streamLaw p).map (restrictTables p n)).map (packTables p n) := by
      rw [Measure.map_map (measurable_packTables p n) (measurable_restrictTables p n)]
      exact congrArg ((streamLaw p).map) (funext (truncate_eq_packTables p n))
    _ = experimentLaw p n := by rw [restrictTables_law, packTables_law]

theorem measurePreserving_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurePreserving (truncate p n) (streamLaw p) (experimentLaw p n) :=
  ⟨measurable_truncate p n, truncate_law p n⟩

theorem measurePreserving_streamTable {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurePreserving (fun omega : Omega p => omega n) (streamLaw p) (physicalTableLaw p n) :=
  measurePreserving_eval_infinitePi (physicalTableLaw p) n

theorem streamTable_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => omega n) = physicalTableLaw p n :=
  (measurePreserving_streamTable p n).map_eq

/-- Arbitrary selected finite whole-table rectangles, including the empty set. -/
theorem stream_rectangle_probability {L : ℝ} (p : GeometricParameters L)
    (A : Finset ℕ) (B : (n : ℕ) → Set (StageTables p n))
    (hB : ∀ n ∈ A, MeasurableSet (B n)) :
    streamLaw p (Set.pi (A : Set ℕ) B) = ∏ n ∈ A, physicalTableLaw p n (B n) :=
  Measure.infinitePi_pi (physicalTableLaw p) hB

theorem streamTables_iIndepFun {L : ℝ} (p : GeometricParameters L) :
    iIndepFun (fun n (omega : Omega p) => omega n) (streamLaw p) :=
  iIndepFun_infinitePi (P := physicalTableLaw p)
    (X := fun n (t : StageTables p n) => t) (fun _ => measurable_id)

/-- The actual finite evaluation at each level, with its original total default. -/
def levelMap {L : ℝ} (p : GeometricParameters L) (omega : Omega p) (n : ℕ) :
    StageMaps p n := evaluate p n (truncate p n omega)

def process {L : ℝ} (p : GeometricParameters L) :
    Omega p → (n : ℕ) → StageMaps p n := fun omega n => levelMap p omega n

@[simp] theorem levelMap_zero {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    levelMap p omega 0 = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) := rfl

theorem levelMap_succ {L : ℝ} (p : GeometricParameters L) (omega : Omega p) (n : ℕ) :
    levelMap p omega (n+1) = physicalSuccessorOutput p n (levelMap p omega n) (omega n) := rfl

theorem measurable_levelMap {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun omega => levelMap p omega n) :=
  @Measurable.comp (Omega p) (Experiment p n) (StageMaps p n)
    inferInstance inferInstance inferInstance (evaluate p n) (truncate p n)
    (measurable_evaluate p n) (measurable_truncate p n)

theorem measurable_process {L : ℝ} (p : GeometricParameters L) : Measurable (process p) :=
  measurable_pi_lambda _ (fun n => measurable_levelMap p n)

theorem history_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (i : Fin (n+1)) :
    history p n (truncate p n omega) i = levelMap p omega i.val := by
  unfold history
  rw [truncate_prefix]
  rfl

theorem stageInput_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (i : Fin n) :
    stageInput p n i (truncate p n omega) = levelMap p omega i.val := by
  unfold stageInput
  rw [truncate_prefix]
  rfl

theorem stagePair_truncate {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (i : Fin n) :
    stagePair p n i (truncate p n omega) = (levelMap p omega i.val, omega i.val) := by
  apply Prod.ext
  · exact stageInput_truncate p n omega i
  · exact tableAt_truncate p n i omega

theorem levelMap_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => levelMap p omega n) = outputLaw p n := by
  change (streamLaw p).map (evaluate p n ∘ truncate p n) = outputLaw p n
  rw [← Measure.map_map (measurable_evaluate p n) (measurable_truncate p n), truncate_law]
  rfl

/-- An independent fresh table paired with the recursively dependent input map. -/
theorem stream_freshPair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => (levelMap p omega n, omega n)) =
      (outputLaw p n).prod (physicalTableLaw p n) := by
  let f : Experiment p (n+1) → StageMaps p n × StageTables p n :=
    fun z => (evaluate p n z.1, z.2)
  have hf : Measurable f := by
    have hfirst : Measurable (fun z : Experiment p (n+1) => evaluate p n z.1) :=
      @Measurable.comp (Experiment p (n+1)) (Experiment p n) (StageMaps p n)
        inferInstance inferInstance inferInstance (evaluate p n) Prod.fst
        (measurable_evaluate p n) measurable_fst
    exact hfirst.prodMk measurable_snd
  change (streamLaw p).map (f ∘ truncate p (n+1)) = _
  rw [← Measure.map_map hf (measurable_truncate p (n+1)), truncate_law]
  exact freshPair_law p n

theorem stream_successor_kernel {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => levelMap p omega (n+1)) =
      successorKernel p n ∘ₘ ((streamLaw p).map (fun omega => levelMap p omega n)) := by
  rw [levelMap_law, levelMap_law]
  exact outputLaw_succ p n

theorem stream_successor_bind {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => levelMap p omega (n+1)) =
      ((streamLaw p).map (fun omega => levelMap p omega n)).bind (successorKernel p n) := by
  rw [levelMap_law, levelMap_law]
  exact outputLaw_succ_bind p n

def streamCounters {L : ℝ} (p : GeometricParameters L) (n time : ℕ) (omega : Omega p) :=
  stageCounters p (n+1) (Fin.last n) time (truncate p (n+1) omega)

def streamSelected {L : ℝ} (p : GeometricParameters L) (n time : ℕ) (omega : Omega p) :=
  stageSelected p (n+1) (Fin.last n) time (truncate p (n+1) omega)

def streamHalts {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) : Prop :=
  stageHalts p (n+1) (Fin.last n) (truncate p (n+1) omega)

def streamHaltTime {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) : ℕ :=
  stageHaltTime p (n+1) (Fin.last n) (truncate p (n+1) omega)

def streamGeometricOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) :=
  stageGeometricOutput p (n+1) (Fin.last n) (truncate p (n+1) omega)

def streamPerturbedOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) :=
  stagePerturbedOutput p (n+1) (Fin.last n) (truncate p (n+1) omega)

def streamPhysicalOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) :=
  stagePhysicalOutput p (n+1) (Fin.last n) (truncate p (n+1) omega)

theorem streamPhysicalOutput_eq_levelMap_succ {L : ℝ} (p : GeometricParameters L)
    (n : ℕ) (omega : Omega p) :
    streamPhysicalOutput p n omega = levelMap p omega (n+1) := by
  unfold streamPhysicalOutput stagePhysicalOutput
  rw [stageInput_truncate, tableAt_truncate]
  exact (levelMap_succ p omega n).symm

theorem streamSelected_original {L : ℝ} (p : GeometricParameters L)
    (n time : ℕ) (omega : Omega p) :
    streamSelected p n time omega =
      selected (masterSupport (StagePresentation p n))
        (masterBad (StagePresentation p n) (anchorRadius p.m) p.lambda
          ((6*p.m+2)*p.lambda) (levelMap p omega n)) (omega n) time := by
  have h := stageSelected_original p (n+1) (Fin.last n) time (truncate p (n+1) omega)
  simpa only [stageInput_truncate, tableAt_truncate, Fin.val_last, streamSelected] using h

/-- The finite original execution is the same stream execution on every prefix. -/
theorem original_stream_prefix {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (time : ℕ) (omega : Omega p) :
    streamCounters p i.val time omega = stageCounters p N i time (truncate p N omega) ∧
    streamSelected p i.val time omega = stageSelected p N i time (truncate p N omega) ∧
    (streamHalts p i.val omega ↔ stageHalts p N i (truncate p N omega)) ∧
    streamHaltTime p i.val omega = stageHaltTime p N i (truncate p N omega) ∧
    streamGeometricOutput p i.val omega = stageGeometricOutput p N i (truncate p N omega) ∧
    streamPerturbedOutput p i.val omega = stagePerturbedOutput p N i (truncate p N omega) ∧
    streamPhysicalOutput p i.val omega = stagePhysicalOutput p N i (truncate p N omega) := by
  have hInput :
      stageInput p (i.val+1) (Fin.last i.val) (truncate p (i.val+1) omega) =
        stageInput p N i (truncate p N omega) :=
    (stageInput_truncate p (i.val+1) omega (Fin.last i.val)).trans
      (stageInput_truncate p N omega i).symm
  have hTable :
      tableAt p (i.val+1) (Fin.last i.val) (truncate p (i.val+1) omega) =
        tableAt p N i (truncate p N omega) :=
    (tableAt_truncate p (i.val+1) (Fin.last i.val) omega).trans
      (tableAt_truncate p N i omega).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold streamCounters stageCounters
    rw [hInput, hTable]
    simp only [Fin.val_last]
  · unfold streamSelected stageSelected
    rw [hInput, hTable]
    simp only [Fin.val_last]
  · apply Iff.of_eq
    unfold streamHalts stageHalts
    rw [hInput, hTable]
    simp only [Fin.val_last]
  · unfold streamHaltTime stageHaltTime
    rw [hInput, hTable]
    simp only [Fin.val_last]
  · unfold streamGeometricOutput stageGeometricOutput
    rw [hInput, hTable]
    simp only [Fin.val_last]
  · unfold streamPerturbedOutput stagePerturbedOutput
    rw [hInput, hTable]
    simp only [Fin.val_last]
  · unfold streamPhysicalOutput stagePhysicalOutput
    rw [hInput, hTable]
    simp only [Fin.val_last]

private theorem measurable_observation {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {A : Type*} [MeasurableSpace A] (f : Experiment p (n+1) → A) (hf : Measurable f) :
    Measurable (f ∘ truncate p (n+1)) :=
  @Measurable.comp (Omega p) (Experiment p (n+1)) A inferInstance inferInstance inferInstance
    f (truncate p (n+1)) hf (measurable_truncate p (n+1))

theorem measurable_streamCounters {L : ℝ} (p : GeometricParameters L) (n time : ℕ) :
    Measurable (streamCounters p n time) :=
  measurable_observation p n _ (measurable_stageCounters p (n+1) (Fin.last n) time)

theorem measurable_streamSelected {L : ℝ} (p : GeometricParameters L) (n time : ℕ) :
    Measurable (streamSelected p n time) :=
  measurable_observation p n _ (measurable_stageSelected p (n+1) (Fin.last n) time)

theorem measurableSet_streamHalts {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurableSet {omega | streamHalts p n omega} :=
  (measurableSet_stageHalts p (n+1) (Fin.last n)).preimage (measurable_truncate p (n+1))

theorem measurable_streamHaltTime {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamHaltTime p n) :=
  measurable_observation p n _ (measurable_stageHaltTime p (n+1) (Fin.last n))

theorem measurable_streamGeometricOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamGeometricOutput p n) :=
  measurable_observation p n _ (measurable_stageGeometricOutput p (n+1) (Fin.last n))

theorem measurable_streamPerturbedOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamPerturbedOutput p n) :=
  measurable_observation p n _ (measurable_stagePerturbedOutput p (n+1) (Fin.last n))

theorem measurable_streamPhysicalOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamPhysicalOutput p n) :=
  measurable_observation p n _ (measurable_stagePhysicalOutput p (n+1) (Fin.last n))

/-- All stages and all execution times form one jointly measurable observation. -/
theorem measurable_streamCounterProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun n time => streamCounters p n time omega) :=
  measurable_pi_lambda _ (fun n =>
    measurable_pi_lambda _ (fun time => measurable_streamCounters p n time))

theorem measurable_streamSelectedProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun n time => streamSelected p n time omega) :=
  measurable_pi_lambda _ (fun n =>
    measurable_pi_lambda _ (fun time => measurable_streamSelected p n time))

theorem measurable_streamHaltTimeProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun n => streamHaltTime p n omega) :=
  measurable_pi_lambda _ (fun n => measurable_streamHaltTime p n)

theorem measurable_streamPhysicalProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun n => streamPhysicalOutput p n omega) :=
  measurable_pi_lambda _ (fun n => measurable_streamPhysicalOutput p n)

theorem streamHaltTime_of_not_halts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (hh : ¬ streamHalts p n omega) : streamHaltTime p n omega = 0 :=
  stageHaltTime_of_not_halts p (n+1) (Fin.last n) (truncate p (n+1) omega) hh

theorem streamGeometricOutput_of_not_halts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : Omega p) (hh : ¬ streamHalts p n omega) :
    streamGeometricOutput p n omega = assignment (omega n) (fun _ => 0) := by
  unfold streamGeometricOutput
  have h := stageGeometricOutput_of_not_halts p (n+1) (Fin.last n)
    (truncate p (n+1) omega) hh
  simpa only [tableAt_truncate, Fin.val_last] using h

end QEC.Coding.BDL26CountableEmbeddingExperiment
