import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ReplacementMaterialization
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.IncomingRowsExecution
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountableExperimentCost

/-!
# Retained paid rows on the original finite and common-stream experiments

This project-derived refinement composes the actual incoming-row perturbation,
actual RX/RZ coordinate interpreter, and an explicitly paid counter-zero wrapper.
The initial seed rows are supplied data. Original rank-list, finite presentation,
constructor/incidence generation, initial cache/setup and finite-bit sampling
costs remain outside this exact-real primitive model. Original Fintype order,
selectors, whole table factors and total nonhalting defaults are unchanged.
Source: [BDL26, Section 3, construction, perturbation algorithm, replacement and
Theorem 1(1) induction; paper.tex:1277-1323,1400-1428,2120-2198,2227-2238,2252-2256].
-/
noncomputable section
namespace QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

/-- Two local record operations, plus the existing map-list operation per row. -/
def stampRowsQuery {A : Type*} (R : List (A × Space)) : List (A × ℕ × Space) × ℕ :=
  mapQuery (fun row => ((row.1,0,row.2),2)) R

theorem stampRowsQuery_value {A : Type*} (R : List (A × Space)) :
    (stampRowsQuery R).1 = R.map (fun row => (row.1,0,row.2)) :=
  mapQuery_value _ R

theorem stampRowsQuery_cost {A : Type*} (R : List (A × Space)) :
    (stampRowsQuery R).2 = 3*R.length := by
  have h := mapQuery_cost_constant (fun row : A × Space => ((row.1,0,row.2),2))
    2 (fun _ => rfl) R
  simpa only [stampRowsQuery,Nat.mul_comm] using h

theorem stampRowsQuery_labels {A : Type*} (R : List (A × Space)) :
    ((stampRowsQuery R).1).map Prod.fst = R.map Prod.fst := by
  simp only [stampRowsQuery_value,List.map_map,Function.comp_def]

theorem stampRowsQuery_length {A : Type*} (R : List (A × Space)) :
    (stampRowsQuery R).1.length = R.length := by
  simp only [stampRowsQuery_value,List.length_map]

/-- Equality includes actual first-match lookup costs, missing labels and duplicates. -/
theorem stampRowsQuery_read (P : TannerSquarePresentation)
    (R : List (Vertex P × Space)) (v : Vertex P) :
    incomingRead P (stampRowsQuery R).1 v = pointRowQuery v R := by
  have hlookup : stateRowQuery v (R.map (fun row => (row.1,0,row.2))) =
      ((0,(pointRowQuery v R).1),(pointRowQuery v R).2) := by
    induction R with
    | nil => rfl
    | cons row R ih =>
        by_cases h : row.1 = v
        · simp only [List.map_cons,stateRowQuery,pointRowQuery,if_pos h]
        · simp only [List.map_cons,stateRowQuery,pointRowQuery,if_neg h,ih]
  simp only [stampRowsQuery_value,incomingRead,hlookup]

theorem stampRowsQuery_canonical (P : TannerSquarePresentation) (J : Vertex P → Space) :
    (stampRowsQuery ((vertexInputList P).map (fun v => (v,J v)))).1 = incomingRows P J := by
  simp only [stampRowsQuery_value,incomingRows,List.map_map,Function.comp_def]

/-- Each execution is bound once, and its actual emitted rows feed the next phase. -/
def composedStageQuery {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (I : StateRows (StagePresentation p n)) (T : StageTables p n) :
    StateRows (StagePresentation p (n+1)) × ℝ≥0∞ :=
  let perturbation := rowExecutionQuery (StagePresentation p n) I
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) T
  let replacement := materializeRows p n perturbation.1
  let wrapped := stampRowsQuery replacement.1
  (wrapped.1,perturbation.2+((replacement.2+wrapped.2 : ℕ) : ℝ≥0∞))

theorem composedStageQuery_intermediate {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (rowExecutionQuery (StagePresentation p n) (incomingRows (StagePresentation p n) J)
      (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) T).1 =
      emittedRows p n J T := by
  rw [rowExecutionQuery_embedding_rows,incomingRows_points,emittedRows_value]

theorem composedStageQuery_rows {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (composedStageQuery p n (incomingRows (StagePresentation p n) J) T).1 =
      incomingRows (StagePresentation p (n+1)) (physicalSuccessorOutput p n J T) := by
  simp only [composedStageQuery,composedStageQuery_intermediate,materializeRows_value,
    stampRowsQuery_canonical]

theorem composedStageQuery_cost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (composedStageQuery p n (incomingRows (StagePresentation p n) J) T).2 =
      jointRowStageCost p n (J,T)+
        ((materializationCost p n (J,T)+3*Fintype.card (Vertex (StagePresentation p (n+1))) : ℕ) : ℝ≥0∞) := by
  simp only [composedStageQuery,stampRowsQuery_cost,materializeRows_length,
    composedStageQuery_intermediate,jointRowStageCost,rowExecutionCost,materializationCost]

/-- Only the initial seed cache is supplied; every later cache is retained paid output. -/
def run {L : ℝ} (p : GeometricParameters L) :
    (N : ℕ) → Experiment p N → StateRows (StagePresentation p N) × ℝ≥0∞
  | 0, _ => (incomingRows _ (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)),0)
  | N+1, z => let prior := run p N z.1
              let next := composedStageQuery p N prior.1 z.2
              (next.1,prior.2+next.2)

theorem run_rows {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    (run p N z).1 = incomingRows (StagePresentation p N) (evaluate p N z) := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [run,ih,composedStageQuery_rows,evaluate_succ]

theorem run_points {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    statePoints (run p N z).1 = evaluate p N z := by
  rw [run_rows,incomingRows_points]

theorem run_labels {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    ((run p N z).1).map Prod.fst = vertexInputList (StagePresentation p N) := by
  rw [run_rows,incomingRows_labels]

def transferTotal {L : ℝ} (p : GeometricParameters L) (N : ℕ) : ℕ :=
  ∑ i : Fin N, 3*Fintype.card (Vertex (StagePresentation p (i.val+1)))

@[simp] theorem transferTotal_zero {L : ℝ} (p : GeometricParameters L) : transferTotal p 0 = 0 := by
  simp only [transferTotal,Fin.sum_univ_zero]

theorem transferTotal_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    transferTotal p (N+1) = transferTotal p N+3*Fintype.card (Vertex (StagePresentation p (N+1))) := by
  simp only [transferTotal,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]

/-- The total is the accumulated cost field of the actual recursive execution. -/
def totalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : ℝ≥0∞ :=
  (run p N z).2

@[simp] theorem totalCost_zero {L : ℝ} (p : GeometricParameters L) (z : Experiment p 0) :
    totalCost p 0 z = 0 := rfl

theorem totalCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p (N+1)) :
    totalCost p (N+1) z = totalCost p N z.1+
      jointRowStageCost p N (evaluate p N z.1,z.2)+
        ((materializationCost p N (evaluate p N z.1,z.2)+
          3*Fintype.card (Vertex (StagePresentation p (N+1))) : ℕ) : ℝ≥0∞) := by
  change (run p N z.1).2+(composedStageQuery p N (run p N z.1).1 z.2).2 = _
  rw [run_rows,composedStageQuery_cost]
  exact (add_assoc _ _ _).symm

/-- Actual execution refinement precedes every polynomial or integral bound. -/
theorem totalCost_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    totalCost p N z = rowTotalCost p N z+
      ((totalMaterializationCost p N z+transferTotal p N : ℕ) : ℝ≥0∞) := by
  induction N with
  | zero => simp only [totalCost_zero,rowTotalCost_zero,totalMaterializationCost_zero,
      transferTotal_zero,Nat.cast_zero,add_zero]
  | succ N ih =>
      rw [totalCost_succ,rowTotalCost_succ,totalMaterializationCost_succ,transferTotal_succ,ih]
      simp only [Nat.cast_add]
      ac_rfl

/-- Retained input to a stage occurrence, without reconstructing a dense-map cache. -/
def inputRows {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) (z : Experiment p N) :
    StateRows (StagePresentation p i.val) :=
  (run p i.val (experimentPrefix p i.val N (by omega) z)).1

theorem inputRows_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) (z : Experiment p N) :
    inputRows p N i z = incomingRows (StagePresentation p i.val) (stageInput p N i z) :=
  run_rows p i.val _

def stageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) (z : Experiment p N) : ℝ≥0∞ :=
  (composedStageQuery p i.val (inputRows p N i z) (tableAt p N i z)).2

theorem stageCost_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) (z : Experiment p N) :
    stageCost p N i z = rowStageCost p N i z+
      ((stageMaterializationCost p N i z+
        3*Fintype.card (Vertex (StagePresentation p (i.val+1))) : ℕ) : ℝ≥0∞) := by
  rw [stageCost,inputRows_eq,composedStageQuery_cost]
  rfl

theorem totalCost_eq_sum {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    totalCost p N z = ∑ i : Fin N, stageCost p N i z := by
  simp only [totalCost_eq,stageCost_eq,rowTotalCost,totalMaterializationCost,transferTotal,
    Nat.cast_add,Nat.cast_sum,Finset.sum_add_distrib]

theorem stageCost_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ} (h : M ≤ N)
    (i : Fin M) (z : Experiment p N) :
    stageCost p M i (experimentPrefix p M N h z) = stageCost p N (i.castLE h) z := by
  rw [stageCost_eq,stageCost_eq,rowStageCost_prefix,stageMaterializationCost_prefix]
  rfl

theorem stageCost_last {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p (N+1)) :
    stageCost p (N+1) (Fin.last N) z =
      (composedStageQuery p N (run p N z.1).1 z.2).2 := by
  simp only [stageCost,inputRows,Fin.val_last,prefix_last,tableAt_last]

theorem totalCost_one {L : ℝ} (p : GeometricParameters L) (z : Experiment p 1) :
    totalCost p 1 z = (composedStageQuery p 0
      (incomingRows _ (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p))) z.2).2 := by
  change 0+_ = _
  exact zero_add _

theorem stageCost_nonhalting {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) (h : ¬stageHalts p N i z) : stageCost p N i z = ∞ := by
  rw [stageCost_eq,rowStageCost_nonhalting p N i z h,top_add]

theorem totalCost_finite_iff {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    totalCost p N z < ∞ ↔ ∀ i : Fin N, stageHalts p N i z := by
  rw [totalCost_eq,ENNReal.add_lt_top]
  have hfinite : ((totalMaterializationCost p N z+transferTotal p N : ℕ) : ℝ≥0∞) < ∞ := by simp
  simp only [hfinite,and_true]
  exact rowTotalCost_finite_iff p N z

theorem totalCost_nonhalting {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) (h : ¬stageHalts p N i z) : totalCost p N z = ∞ := by
  rw [totalCost_eq,rowTotalCost_infinite_of_nonhalting p N i z h,top_add]

theorem measurable_stageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    Measurable (stageCost p N i) := by
  have he : stageCost p N i = fun z => rowStageCost p N i z+
      ((materializationLabelCost p i.val+
        3*Fintype.card (Vertex (StagePresentation p (i.val+1))) : ℕ) : ℝ≥0∞) := by
    funext z
    rw [stageCost_eq,stageMaterializationCost_static]
  rw [he]
  exact (measurable_rowStageCost p N i).add measurable_const

theorem measurable_totalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (totalCost p N) := by
  have he : totalCost p N = fun z => ∑ i : Fin N, stageCost p N i z :=
    funext (totalCost_eq_sum p N)
  rw [he]
  exact Finset.measurable_sum Finset.univ (fun i _ => measurable_stageCost p N i)

/-- Actual transfer cost follows from qubit growth and the already proved row count. -/
theorem transferTotal_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    transferTotal p N ≤ 195*(stageQubits p N+1)^2 := by
  have hN := stage_count_le_qubits p N
  have hi (i : Fin N) : 3*Fintype.card (Vertex (StagePresentation p (i.val+1))) ≤
      195*(stageQubits p N+1) := by
    have hv := stageVertices_le_qubits p (i.val+1)
    have hq := stageQubits_mono p (show i.val+1 ≤ N by omega)
    nlinarith
  calc
    _ ≤ ∑ _i : Fin N, 195*(stageQubits p N+1) := Finset.sum_le_sum (fun i _ => hi i)
    _ = N*(195*(stageQubits p N+1)) := by simp
    _ ≤ (stageQubits p N+1)*(195*(stageQubits p N+1)) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

private theorem integral_add_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f g : Ω → ℝ≥0∞) (hf : Measurable f) (b : ℝ≥0∞)
    (h : ∀ z, g z ≤ f z+b) : (∫⁻ z, g z ∂μ) ≤ (∫⁻ z, f z ∂μ)+b := by
  calc
    _ ≤ ∫⁻ z, f z+b ∂μ := lintegral_mono h
    _ = _ := by rw [lintegral_add_left hf]; simp

private theorem degree_bound (C q : ℕ) :
    391*C*65^10*(q+1)^12+(65536*65^2*(q+1)^3+195*(q+1)^2) ≤
      (391*C*65^10+65536*65^2+195)*(q+1)^12 := by
  have h3 : (q+1)^3 ≤ (q+1)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (q+1)^2 ≤ (q+1)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ 391*C*65^10*(q+1)^12+(65536*65^2*(q+1)^12+195*(q+1)^12) :=
      Nat.add_le_add_left (Nat.add_le_add (Nat.mul_le_mul_left _ h3) (Nat.mul_le_mul_left _ h2)) _
    _ = _ := by ring

theorem totalCost_integral_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z, totalCost p N z ∂experimentLaw p N) ≤
      (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2+195)*
        (stageQubits p N+1)^12 : ℕ) : ℝ≥0∞) := by
  have h := integral_add_bound (experimentLaw p N) (rowTotalCost p N) (totalCost p N)
    (measurable_rowTotalCost p N)
    (((65536*65^2*(stageQubits p N+1)^3+195*(stageQubits p N+1)^2 : ℕ) : ℝ≥0∞)) (by
      intro z
      rw [totalCost_eq]
      exact add_le_add le_rfl ((Nat.cast_le (α := ℝ≥0∞)).mpr
        (Nat.add_le_add (totalMaterializationCost_le p N z) (transferTotal_le p N))))
  calc
    _ ≤ (∫⁻ z, rowTotalCost p N z ∂experimentLaw p N)+
        ((65536*65^2*(stageQubits p N+1)^3+195*(stageQubits p N+1)^2 : ℕ) : ℝ≥0∞) := h
    _ ≤ (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10)*(stageQubits p N+1)^12 : ℕ) : ℝ≥0∞)+
        ((65536*65^2*(stageQubits p N+1)^3+195*(stageQubits p N+1)^2 : ℕ) : ℝ≥0∞) :=
      add_le_add (rowTotalCost_integral_le p N) le_rfl
    _ ≤ _ := by rw [← Nat.cast_add]; exact (Nat.cast_le (α := ℝ≥0∞)).mpr (degree_bound _ _)

/-- A semantic view of an actual retained stage prefix; observations do not rerun the program. -/
def stagePrefixRows {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : StateRows (StagePresentation p i.val) :=
  (rowPrefixQuery (StagePresentation p i.val) (inputRows p N i z) (anchorRadius p.m)
    p.lambda ((6*p.m+2)*p.lambda)
    (rowUniverseQuery (StagePresentation p i.val) (inputRows p N i z) (by positivity)).1
    (tableAt p N i z) time).1

theorem stagePrefixRows_rep {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) :
    StateRowsRep (StagePresentation p i.val) (tableAt p N i z)
      (stageCounters p N i time z) (stagePrefixRows p N i time z) := by
  have h := rowPrefixQuery_rep (StagePresentation p i.val) (inputRows p N i z)
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
    (tableAt p N i z) time
  have hpoints : statePoints (inputRows p N i z) = stageInput p N i z := by
    rw [inputRows_eq,incomingRows_points]
  have hcounter :
      counters (eventSupport (StagePresentation p i.val) (statePoints (inputRows p N i z)) (anchorRadius p.m))
        (eventBad (StagePresentation p i.val) (statePoints (inputRows p N i z))
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p N i z) time =
        stageCounters p N i time z := by
    unfold stageCounters
    exact congrArg (fun J : StageMaps p i.val =>
      counters (eventSupport (StagePresentation p i.val) J (anchorRadius p.m))
        (eventBad (StagePresentation p i.val) J (anchorRadius p.m) p.lambda
          ((6*p.m+2)*p.lambda)) (tableAt p N i z) time) hpoints
  rw [hcounter] at h
  simpa only [stagePrefixRows] using h

private theorem rep_read (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P))
    (R : StateRows P) (h : StateRowsRep P T c R) (v : Vertex P) :
    (stateRowQuery v R).1 = (c v,T (v,c v)) := by
  apply stateRowQuery_value v R
  · intro row hr he
    subst v
    exact h.2 row hr
  · have hv := vertexInputList_complete P v
    rw [← h.1,List.mem_map] at hv
    exact hv

/-- Both the cached sample and its exact original fresh-table address are retained. -/
theorem stagePrefix_read {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) (v : Vertex (StagePresentation p i.val)) :
    (stateRowQuery v (stagePrefixRows p N i time z)).1 =
      (stageCounters p N i time z v,(tableAt p N i z) (v,stageCounters p N i time z v)) :=
  rep_read _ _ _ _ (stagePrefixRows_rep p N i time z) v

def actualStageCounters {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : Counters (Vertex (StagePresentation p i.val)) :=
  fun v => (stateRowQuery v (stagePrefixRows p N i time z)).1.1

def actualStageSamples {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : StageMaps p i.val :=
  statePoints (stagePrefixRows p N i time z)

def actualStageSelected {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : Option (MasterEvent (StagePresentation p i.val)) :=
  ((rowScanQuery (StagePresentation p i.val) (inputRows p N i z) (anchorRadius p.m)
    p.lambda ((6*p.m+2)*p.lambda)
    (rowUniverseQuery (StagePresentation p i.val) (inputRows p N i z) (by positivity)).1
    (stagePrefixRows p N i time z)).1).map
      (eventToMaster (StagePresentation p i.val) (statePoints (inputRows p N i z)) (anchorRadius p.m))

def actualStageHalts {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : Prop :=
  Halts (eventSupport (StagePresentation p i.val) (statePoints (inputRows p N i z)) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (statePoints (inputRows p N i z))
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p N i z)

def actualStageHaltTime {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℕ :=
  haltTime (eventSupport (StagePresentation p i.val) (statePoints (inputRows p N i z)) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (statePoints (inputRows p N i z))
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p N i z)

def actualStageGeometric {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageMaps p i.val :=
  statePoints (stagePrefixRows p N i (actualStageHaltTime p N i z) z)

def actualStagePerturbed {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageMaps p i.val :=
  statePoints (stampRowsQuery
    (rowExecutionQuery (StagePresentation p i.val) (inputRows p N i z)
      (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)).1).1

def actualStagePhysical {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageMaps p (i.val+1) :=
  statePoints (composedStageQuery p i.val (inputRows p N i z) (tableAt p N i z)).1

theorem actualStageCounters_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : actualStageCounters p N i time z = stageCounters p N i time z := by
  funext v
  exact congrArg Prod.fst (stagePrefix_read p N i time z v)

theorem actualStageSamples_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) :
    actualStageSamples p N i time z = fun v => (tableAt p N i z) (v,stageCounters p N i time z v) := by
  funext v
  exact congrArg Prod.snd (stagePrefix_read p N i time z v)

theorem actualStage_address {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) (v : Vertex (StagePresentation p i.val)) :
    (v,actualStageCounters p N i time z v) = (v,stageCounters p N i time z v) ∧
      actualStageSamples p N i time z v = (tableAt p N i z) (v,actualStageCounters p N i time z v) := by
  rw [actualStageCounters_eq,actualStageSamples_eq]
  exact ⟨rfl,rfl⟩

theorem actualStageSelected_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : actualStageSelected p N i time z = stageSelected p N i time z := by
  unfold actualStageSelected stagePrefixRows
  rw [rowPrefixQuery_selected,inputRows_eq,incomingRows_points]
  rfl

theorem actualStageHalts_iff {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : actualStageHalts p N i z ↔ stageHalts p N i z := by
  unfold actualStageHalts stageHalts
  rw [inputRows_eq,incomingRows_points]

theorem actualStageHaltTime_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : actualStageHaltTime p N i z = stageHaltTime p N i z := by
  unfold actualStageHaltTime stageHaltTime
  rw [inputRows_eq,incomingRows_points]

theorem actualStageGeometric_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : actualStageGeometric p N i z = stageGeometricOutput p N i z := by
  unfold actualStageGeometric
  rw [actualStageHaltTime_eq]
  exact StateRowsRep_points _ _ _ _ (stagePrefixRows_rep p N i (stageHaltTime p N i z) z)

theorem actualStagePerturbed_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : actualStagePerturbed p N i z = stagePerturbedOutput p N i z := by
  unfold actualStagePerturbed
  rw [inputRows_eq,rowExecutionQuery_embedding_rows,incomingRows_points,
    stampRowsQuery_canonical,incomingRows_points]
  rfl

theorem actualStagePhysical_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : actualStagePhysical p N i z = stagePhysicalOutput p N i z := by
  simp only [actualStagePhysical,inputRows_eq,composedStageQuery_rows,incomingRows_points,stagePhysicalOutput]

/-- Least stopping time includes the final clean scan and all preceding first-bad scans. -/
theorem actualStage_least_stop {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) (h : actualStageHalts p N i z) :
    actualStageSelected p N i (actualStageHaltTime p N i z) z = none ∧
      ∀ time < actualStageHaltTime p N i z, actualStageSelected p N i time z ≠ none := by
  have hh := (actualStageHalts_iff p N i z).mp h
  rw [actualStageHaltTime_eq]
  constructor
  · rw [actualStageSelected_eq]
    apply (stageSelected_none_iff p N i _ z).mpr
    exact haltTime_spec _ _ _ hh
  · intro time ht hn
    have hn' := (stageSelected_none_iff p N i time z).mp
      ((actualStageSelected_eq p N i time z).symm.trans hn)
    obtain ⟨e,he⟩ := active_before_haltTime _ _ _ hh time ht
    rw [hn'] at he
    cases he

/-- Original exceptional defaults and infinite paid cost concern the very same table. -/
theorem actualStage_nonhalting_default {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) (h : ¬actualStageHalts p N i z) :
    actualStageHaltTime p N i z = 0 ∧
      actualStageGeometric p N i z = assignment (tableAt p N i z) (fun _ => 0) ∧
      stageCost p N i z = ∞ := by
  have hh : ¬stageHalts p N i z := fun ha => h ((actualStageHalts_iff p N i z).mpr ha)
  exact ⟨(actualStageHaltTime_eq p N i z).trans (stageHaltTime_of_not_halts p N i z hh),
    (actualStageGeometric_eq p N i z).trans (stageGeometricOutput_of_not_halts p N i z hh),
    stageCost_nonhalting p N i z hh⟩

/-- Labels index all clocks, cached samples and original fixed-carrier choices. -/
abbrev StageTrace {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  (ℕ → Counters (Vertex (StagePresentation p n))) ×
  (ℕ → Option (MasterEvent (StagePresentation p n))) ×
  (ℕ → StageMaps p n) × Bool × ℕ × StageMaps p n × StageMaps p n × StageMaps p (n+1)

def stageTrace {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageTrace p i.val :=
  (fun time => actualStageCounters p N i time z,
   fun time => actualStageSelected p N i time z,
   fun time => actualStageSamples p N i time z,
   if actualStageHalts p N i z then true else false,
   actualStageHaltTime p N i z,actualStageGeometric p N i z,
   actualStagePerturbed p N i z,actualStagePhysical p N i z)

def originalStageTrace {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageTrace p i.val :=
  (fun time => stageCounters p N i time z,
   fun time => stageSelected p N i time z,
   fun time v => (tableAt p N i z) (v,stageCounters p N i time z v),
   if stageHalts p N i z then true else false,
   stageHaltTime p N i z,stageGeometricOutput p N i z,
   stagePerturbedOutput p N i z,stagePhysicalOutput p N i z)

theorem stageTrace_original {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : stageTrace p N i z = originalStageTrace p N i z := by
  simp only [stageTrace,originalStageTrace,actualStageCounters_eq,actualStageSelected_eq,
    actualStageSamples_eq,actualStageHalts_iff,actualStageHaltTime_eq,actualStageGeometric_eq,
    actualStagePerturbed_eq,actualStagePhysical_eq]

private theorem measurable_stage_samples {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (time : ℕ) :
    Measurable (fun z : Experiment p N => fun v => (tableAt p N i z) (v,stageCounters p N i time z v)) := by
  apply measurable_pi_lambda
  intro v
  have lookup : Measurable (fun w : StageTables p i.val × ℕ => w.1 (v,w.2)) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply (v,k))
  exact lookup.comp ((measurable_tableAt p N i).prodMk
    ((measurable_pi_apply v).comp (measurable_stageCounters p N i time)))

theorem measurable_stageTrace {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    Measurable (stageTrace p N i) := by
  have he : stageTrace p N i = originalStageTrace p N i := funext (stageTrace_original p N i)
  rw [he]
  exact (measurable_pi_lambda _ (fun time => measurable_stageCounters p N i time)).prodMk
    ((measurable_pi_lambda _ (fun time => measurable_stageSelected p N i time)).prodMk
    ((measurable_pi_lambda _ (fun time => measurable_stage_samples p N i time)).prodMk
    ((Measurable.ite (measurableSet_stageHalts p N i) measurable_const measurable_const).prodMk
    ((measurable_stageHaltTime p N i).prodMk ((measurable_stageGeometricOutput p N i).prodMk
    ((measurable_stagePerturbedOutput p N i).prodMk (measurable_stagePhysicalOutput p N i)))))))

/-- Complete original histories and stopped traces jointly with actual paid costs. -/
abbrev Observation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :=
  ((i : Fin (N+1)) → StageMaps p i.val) ×
  ((i : Fin N) → StageTrace p i.val) × (Fin N → ℝ≥0∞) × ℝ≥0∞

def paidHistory {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N)
    (i : Fin (N+1)) : StageMaps p i.val :=
  statePoints (run p i.val (experimentPrefix p i.val N (by omega) z)).1

theorem paidHistory_original {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    paidHistory p N z = history p N z := by
  funext i
  exact run_points p i.val _

def finiteObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : Observation p N :=
  (paidHistory p N z,fun i => stageTrace p N i z,fun i => stageCost p N i z,totalCost p N z)

def originalObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : Observation p N :=
  (history p N z,fun i => originalStageTrace p N i z,fun i => stageCost p N i z,totalCost p N z)

theorem finiteObservation_original {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    finiteObservation p N z = originalObservation p N z := by
  simp only [finiteObservation,originalObservation,paidHistory_original,stageTrace_original]

theorem measurable_finiteObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (finiteObservation p N) := by
  have hh : Measurable (paidHistory p N) := by
    have he : paidHistory p N = history p N := funext (paidHistory_original p N)
    rw [he]
    exact measurable_history p N
  exact hh.prodMk ((measurable_pi_lambda _ (fun i => measurable_stageTrace p N i)).prodMk
    ((measurable_pi_lambda _ (fun i => measurable_stageCost p N i)).prodMk (measurable_totalCost p N)))

theorem stageTrace_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ} (h : M ≤ N)
    (i : Fin M) (z : Experiment p N) :
    stageTrace p M i (experimentPrefix p M N h z) = stageTrace p N (i.castLE h) z := by
  have hc time := (original_execution_prefix p h i time z).1
  have hs time := (original_execution_prefix p h i time z).2.1
  obtain ⟨_,_,hh,ht,hg,hp,hf⟩ := original_execution_prefix p h i 0 z
  rw [stageTrace_original,stageTrace_original]
  apply Prod.ext
  · exact funext hc
  · apply Prod.ext
    · exact funext hs
    · apply Prod.ext
      · funext time v
        change (tableAt p M i (experimentPrefix p M N h z))
            (v,stageCounters p M i time (experimentPrefix p M N h z) v) =
          (tableAt p N (i.castLE h) z) (v,stageCounters p N (i.castLE h) time z v)
        rw [tableAt_prefix,congrFun (hc time) v]
      · exact Prod.ext (congrArg (fun b : Prop => if b then true else false) (propext hh))
          (Prod.ext ht (Prod.ext hg (Prod.ext hp hf)))

theorem paidHistory_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ} (h : M ≤ N)
    (z : Experiment p N) (i : Fin (M+1)) :
    paidHistory p M (experimentPrefix p M N h z) i =
      paidHistory p N z (i.castLE (by omega)) := by
  rw [paidHistory_original,paidHistory_original]
  exact history_prefix p h z i

/-- Literal common-stream recursion; no new independent tables or dense input rebuilds. -/
def streamRun {L : ℝ} (p : GeometricParameters L) (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    (N : ℕ) → StateRows (StagePresentation p N) × ℝ≥0∞
  | 0 => (incomingRows _ (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)),0)
  | N+1 => let prior := streamRun p omega N
           let next := composedStageQuery p N prior.1 (omega N)
           (next.1,prior.2+next.2)

theorem streamRun_truncate {L : ℝ} (p : GeometricParameters L)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) (N : ℕ) :
    streamRun p omega N = run p N (BDL26CountableEmbeddingExperiment.truncate p N omega) := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [streamRun,run,BDL26CountableEmbeddingExperiment.truncate_succ,ih]

theorem streamRun_rows {L : ℝ} (p : GeometricParameters L)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) (N : ℕ) :
    (streamRun p omega N).1 = incomingRows (StagePresentation p N)
      (BDL26CountableEmbeddingExperiment.levelMap p omega N) := by
  rw [streamRun_truncate,run_rows]
  rfl

def streamStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : ℝ≥0∞ :=
  (composedStageQuery p n (streamRun p omega n).1 (omega n)).2

def streamTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : ℝ≥0∞ := (streamRun p omega N).2

theorem streamStageCost_finite_prefix {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamStageCost p i.val omega = stageCost p N i (BDL26CountableEmbeddingExperiment.truncate p N omega) := by
  unfold streamStageCost stageCost inputRows
  rw [BDL26CountableEmbeddingExperiment.truncate_prefix,
    BDL26CountableEmbeddingExperiment.tableAt_truncate,streamRun_truncate]

theorem streamTotalCost_finite_prefix {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamTotalCost p N omega = totalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega) :=
  congrArg Prod.snd (streamRun_truncate p omega N)

@[simp] theorem streamTotalCost_zero {L : ℝ} (p : GeometricParameters L)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : streamTotalCost p 0 omega = 0 := rfl

theorem streamTotalCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamTotalCost p (N+1) omega = streamTotalCost p N omega+streamStageCost p N omega := rfl

theorem streamTotalCost_eq_sum {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamTotalCost p N omega = ∑ i : Fin N, streamStageCost p i.val omega := by
  rw [streamTotalCost_finite_prefix,totalCost_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => (streamStageCost_finite_prefix p N i omega).symm)

theorem streamTotalCost_mono {L : ℝ} (p : GeometricParameters L)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : Monotone (fun N => streamTotalCost p N omega) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [streamTotalCost_succ]
  exact le_add_right le_rfl

/-- Every row/clock/scan here is from the retained stream rows and literal omega n. -/
def streamStageTrace {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : StageTrace p n :=
  let I := (streamRun p omega n).1
  let T := omega n
  let events := (rowUniverseQuery (StagePresentation p n) I (by positivity : (0 : ℝ) ≤ anchorRadius p.m)).1
  let rows := fun time => (rowPrefixQuery (StagePresentation p n) I (anchorRadius p.m)
    p.lambda ((6*p.m+2)*p.lambda) events T time).1
  let halt := haltTime (eventSupport (StagePresentation p n) (statePoints I) (anchorRadius p.m))
    (eventBad (StagePresentation p n) (statePoints I) (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
  (fun time v => (stateRowQuery v (rows time)).1.1,
   fun time => ((rowScanQuery (StagePresentation p n) I (anchorRadius p.m) p.lambda
      ((6*p.m+2)*p.lambda) events (rows time)).1).map
        (eventToMaster (StagePresentation p n) (statePoints I) (anchorRadius p.m)),
   fun time => statePoints (rows time),
   if Halts (eventSupport (StagePresentation p n) (statePoints I) (anchorRadius p.m))
       (eventBad (StagePresentation p n) (statePoints I) (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
     then true else false,
   halt,statePoints (rows halt),
   statePoints (stampRowsQuery (rowExecutionQuery (StagePresentation p n) I
      (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T).1).1,
   statePoints (composedStageQuery p n I T).1)

theorem streamStageTrace_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamStageTrace p n omega = stageTrace p (n+1) (Fin.last n)
      (BDL26CountableEmbeddingExperiment.truncate p (n+1) omega) := by
  have hI : inputRows p (n+1) (Fin.last n)
      (BDL26CountableEmbeddingExperiment.truncate p (n+1) omega) = (streamRun p omega n).1 := by
    change (run p n (experimentPrefix p n (n+1) (by omega)
      (BDL26CountableEmbeddingExperiment.truncate p (n+1) omega))).1 = (streamRun p omega n).1
    rw [BDL26CountableEmbeddingExperiment.truncate_prefix,streamRun_truncate]
  have hT : tableAt p (n+1) (Fin.last n)
      (BDL26CountableEmbeddingExperiment.truncate p (n+1) omega) = omega n :=
    BDL26CountableEmbeddingExperiment.tableAt_truncate p (n+1) (Fin.last n) omega
  let observe : StateRows (StagePresentation p n) × StageTables p n → StageTrace p n := fun w =>
    let I := w.1
    let T := w.2
    let events := (rowUniverseQuery (StagePresentation p n) I
      (by positivity : (0 : ℝ) ≤ anchorRadius p.m)).1
    let rows := fun time => (rowPrefixQuery (StagePresentation p n) I (anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) events T time).1
    let halt := haltTime (eventSupport (StagePresentation p n) (statePoints I) (anchorRadius p.m))
      (eventBad (StagePresentation p n) (statePoints I) (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
    (fun time v => (stateRowQuery v (rows time)).1.1,
     fun time => ((rowScanQuery (StagePresentation p n) I (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda) events (rows time)).1).map
          (eventToMaster (StagePresentation p n) (statePoints I) (anchorRadius p.m)),
     fun time => statePoints (rows time),
     if Halts (eventSupport (StagePresentation p n) (statePoints I) (anchorRadius p.m))
         (eventBad (StagePresentation p n) (statePoints I) (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
       then true else false,
     halt,statePoints (rows halt),
     statePoints (stampRowsQuery (rowExecutionQuery (StagePresentation p n) I
        (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
        p.lambda ((6*p.m+2)*p.lambda) T).1).1,
     statePoints (composedStageQuery p n I T).1)
  change observe ((streamRun p omega n).1,omega n) =
    observe (inputRows p (n+1) (Fin.last n)
        (BDL26CountableEmbeddingExperiment.truncate p (n+1) omega),
      tableAt p (n+1) (Fin.last n) (BDL26CountableEmbeddingExperiment.truncate p (n+1) omega))
  exact (congrArg observe (Prod.ext hI hT)).symm

theorem streamStageTrace_finite_prefix {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamStageTrace p i.val omega = stageTrace p N i (BDL26CountableEmbeddingExperiment.truncate p N omega) := by
  rcases i with ⟨i,hi⟩
  rw [streamStageTrace_last]
  have h := stageTrace_prefix p hi (Fin.last i)
    (BDL26CountableEmbeddingExperiment.truncate p N omega)
  rw [BDL26CountableEmbeddingExperiment.truncate_prefix] at h
  exact h

def streamObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : Observation p N :=
  (fun i => statePoints (streamRun p omega i.val).1,
   fun i => streamStageTrace p i.val omega,fun i => streamStageCost p i.val omega,streamTotalCost p N omega)

theorem streamObservation_finite {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamObservation p N omega = finiteObservation p N (BDL26CountableEmbeddingExperiment.truncate p N omega) := by
  have hh (i : Fin (N+1)) : statePoints (streamRun p omega i.val).1 =
      paidHistory p N (BDL26CountableEmbeddingExperiment.truncate p N omega) i := by
    unfold paidHistory
    rw [BDL26CountableEmbeddingExperiment.truncate_prefix,streamRun_truncate]
  simp only [streamObservation,finiteObservation,hh,streamStageTrace_finite_prefix,
    streamStageCost_finite_prefix,streamTotalCost_finite_prefix]

theorem measurable_streamStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamStageCost p n) := by
  have he : streamStageCost p n = stageCost p (n+1) (Fin.last n) ∘
      BDL26CountableEmbeddingExperiment.truncate p (n+1) :=
    funext (streamStageCost_finite_prefix p (n+1) (Fin.last n))
  rw [he]
  exact (measurable_stageCost p (n+1) (Fin.last n)).comp
    (BDL26CountableEmbeddingExperiment.measurable_truncate p (n+1))

theorem measurable_streamTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (streamTotalCost p N) := by
  have he : streamTotalCost p N = totalCost p N ∘ BDL26CountableEmbeddingExperiment.truncate p N :=
    funext (streamTotalCost_finite_prefix p N)
  rw [he]
  exact (measurable_totalCost p N).comp (BDL26CountableEmbeddingExperiment.measurable_truncate p N)

theorem measurable_streamStageTrace {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamStageTrace p n) := by
  have he : streamStageTrace p n = stageTrace p (n+1) (Fin.last n) ∘
      BDL26CountableEmbeddingExperiment.truncate p (n+1) := funext (streamStageTrace_last p n)
  rw [he]
  exact (measurable_stageTrace p (n+1) (Fin.last n)).comp
    (BDL26CountableEmbeddingExperiment.measurable_truncate p (n+1))

theorem measurable_streamObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (streamObservation p N) := by
  have he : streamObservation p N = finiteObservation p N ∘ BDL26CountableEmbeddingExperiment.truncate p N :=
    funext (streamObservation_finite p N)
  rw [he]
  exact (measurable_finiteObservation p N).comp (BDL26CountableEmbeddingExperiment.measurable_truncate p N)

theorem measurable_stream_process {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : BDL26CountableEmbeddingExperiment.Omega p =>
      (fun n => streamStageTrace p n omega,fun n => streamStageCost p n omega,
       fun N => streamTotalCost p N omega)) :=
  (measurable_pi_lambda _ (fun n => measurable_streamStageTrace p n)).prodMk
    ((measurable_pi_lambda _ (fun n => measurable_streamStageCost p n)).prodMk
      (measurable_pi_lambda _ (fun N => measurable_streamTotalCost p N)))

/-- Complete history/counter/selector/stopped/cost copula, including exceptional inputs. -/
theorem streamObservation_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (BDL26CountableEmbeddingExperiment.streamLaw p).map (streamObservation p N) =
      (experimentLaw p N).map (originalObservation p N) := by
  have he : streamObservation p N = finiteObservation p N ∘ BDL26CountableEmbeddingExperiment.truncate p N :=
    funext (streamObservation_finite p N)
  rw [he,← Measure.map_map (measurable_finiteObservation p N)
    (BDL26CountableEmbeddingExperiment.measurable_truncate p N),BDL26CountableEmbeddingExperiment.truncate_law]
  have ho : finiteObservation p N = originalObservation p N := funext (finiteObservation_original p N)
  rw [ho]

theorem streamTotalCost_integral_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, streamTotalCost p N omega ∂BDL26CountableEmbeddingExperiment.streamLaw p) =
      ∫⁻ z, totalCost p N z ∂experimentLaw p N := by
  calc
    _ = ∫⁻ omega, totalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega)
        ∂BDL26CountableEmbeddingExperiment.streamLaw p := lintegral_congr (streamTotalCost_finite_prefix p N)
    _ = ∫⁻ z, totalCost p N z ∂(BDL26CountableEmbeddingExperiment.streamLaw p).map
        (BDL26CountableEmbeddingExperiment.truncate p N) :=
      (lintegral_map (measurable_totalCost p N) (BDL26CountableEmbeddingExperiment.measurable_truncate p N)).symm
    _ = _ := by rw [BDL26CountableEmbeddingExperiment.truncate_law]

theorem streamTotalCost_integral_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, streamTotalCost p N omega ∂BDL26CountableEmbeddingExperiment.streamLaw p) ≤
      (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2+195)*
        (stageQubits p N+1)^12 : ℕ) : ℝ≥0∞) := by
  rw [streamTotalCost_integral_eq]
  exact totalCost_integral_le p N

theorem streamTotalCost_finite_iff {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamTotalCost p N omega < ∞ ↔
      ∀ i : Fin N, BDL26CountableEmbeddingExperiment.streamHalts p i.val omega := by
  rw [streamTotalCost_finite_prefix,totalCost_finite_iff]
  exact forall_congr' (fun i => (BDL26CountableEmbeddingExperiment.original_stream_prefix p N i 0 omega).2.2.1.symm)

theorem allFiniteSuccess_paid {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, streamTotalCost p N omega < ∞) ∧
      (∀ n, PhysicalSuccessorFacts p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n
        (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t :=
  ⟨fun N => (streamTotalCost_finite_iff p N omega).mpr
      (fun i => BDL26CountableEmbeddingExperiment.allFiniteSuccess_halts p h i.val),
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_stageFacts p h,
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_geometry p h⟩

theorem source_even_paid {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) (k : ℕ) :
    streamTotalCost p (2*k) omega < ∞ ∧ PhysicalGeometry (perturbationOddScale p) (2*k)
      (BDL26CountableEmbeddingExperiment.levelMap p omega (2*k)) p.t :=
  ⟨(allFiniteSuccess_paid p h).1 (2*k),(allFiniteSuccess_paid p h).2.2 (2*k)⟩

theorem common_paid_ae {L : ℝ} (p : GeometricParameters L) :
    ∀ᵐ omega ∂BDL26CountableEmbeddingExperiment.streamLaw p,
      omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p ∧
      (∀ N, streamTotalCost p N omega < ∞) ∧
      (∀ n, PhysicalSuccessorFacts p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n
        (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t := by
  filter_upwards [BDL26CountableEmbeddingExperiment.allFiniteSuccess_ae p] with omega h
  exact ⟨h,allFiniteSuccess_paid p h⟩

/-- p is fixed before all prefix lengths and every point of the original stream. -/
theorem fixed_parameters_common_paid (L : ℝ) :
    ∃ p : GeometricParameters L,
      (∀ N, Measurable (streamObservation p N) ∧
        (∫⁻ omega, streamTotalCost p N omega ∂BDL26CountableEmbeddingExperiment.streamLaw p) ≤
          (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2+195)*
            (stageQubits p N+1)^12 : ℕ) : ℝ≥0∞)) ∧
      MeasurableSet (BDL26CountableEmbeddingExperiment.allFiniteSuccess p) ∧
      BDL26CountableEmbeddingExperiment.streamLaw p (BDL26CountableEmbeddingExperiment.allFiniteSuccess p) = 1 ∧
      ∀ᵐ omega ∂BDL26CountableEmbeddingExperiment.streamLaw p,
        omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p ∧
        (∀ N, streamTotalCost p N omega < ∞) ∧
        (∀ n, PhysicalSuccessorFacts p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)) ∧
        ∀ n, PhysicalGeometry (perturbationOddScale p) n
          (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  exact ⟨p,fun N => ⟨measurable_streamObservation p N,streamTotalCost_integral_le p N⟩,
    BDL26CountableEmbeddingExperiment.measurableSet_allFiniteSuccess p,
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_measure p,common_paid_ae p⟩

end QEC.Coding.BDL26PaidRowsComposition
