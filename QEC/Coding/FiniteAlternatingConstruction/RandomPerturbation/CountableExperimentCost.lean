import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountableExperimentGeometry
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperimentCost

/-!
# Actual paid prefixes on the common fresh-table stream

Each cost is the original stopped numeric program on the original recursively
computed input and fresh table. The joint observation retains the entire finite
history and every individual cost, including exceptional nonhalting inputs.
The derived polynomial counts the existing perturbation stages only: generation
of rank dictionaries, constructor/incidence data and replacement materialization
remain outside this operation model. The infinite stream is a probability object,
not an allocated table charged at unit cost. Source: [BDL26, Section 3, randomized
embedding induction and expected-time perturbation algorithm].
-/

noncomputable section
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

/-- The same stopped program, not a polynomial budget or an independently chosen output. -/
def streamStageCost {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) : ℝ≥0∞ := jointStageCost p i (levelMap p omega i, omega i)

/-- Only the actually retained finite stages are paid. -/
def prefixStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) : ℝ≥0∞ := ∑ i : Fin N, streamStageCost p i.val omega

theorem streamStageCost_original {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) :
    streamStageCost p i omega = actualExecutionCost (StagePresentation p i)
      (levelMap p omega i) (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) (omega i) := rfl

/-- Numeric costs agree at every point, without a halting or good-input premise. -/
theorem streamStageCost_eq_stageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (omega : Omega p) :
    streamStageCost p i.val omega = stageCost p N i (truncate p N omega) := by
  exact (congrArg (jointStageCost p i.val) (stagePair_truncate p N omega i)).symm

theorem prefixStageCost_eq_totalStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) :
    prefixStageCost p N omega = totalStageCost p N (truncate p N omega) := by
  exact Finset.sum_congr rfl (fun i _ => streamStageCost_eq_stageCost p N i omega)

@[simp] theorem prefixStageCost_zero {L : ℝ} (p : GeometricParameters L)
    (omega : Omega p) : prefixStageCost p 0 omega = 0 := by
  simp only [prefixStageCost, Fin.sum_univ_zero]

theorem prefixStageCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) :
    prefixStageCost p (N+1) omega = prefixStageCost p N omega + streamStageCost p N omega := by
  simp only [prefixStageCost, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem prefixStageCost_one {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    prefixStageCost p 1 omega = jointStageCost p 0
      (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p), omega 0) := by
  rw [prefixStageCost_succ, prefixStageCost_zero, zero_add]
  rfl

theorem prefixStageCost_mono {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    Monotone (fun N => prefixStageCost p N omega) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [prefixStageCost_succ]
  exact le_add_right le_rfl

/-- Exact prefix and proof transports, retaining the original stage occurrence. -/
theorem streamStageCost_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ}
    (h : M ≤ N) (i : Fin M) (omega : Omega p) :
    stageCost p M i (experimentPrefix p M N h (truncate p N omega)) =
      streamStageCost p (i.castLE h).val omega := by
  rw [stageCost_prefix]
  exact (streamStageCost_eq_stageCost p N (i.castLE h) omega).symm

theorem streamStageCost_nonhalting {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) (h : ¬ streamHalts p i omega) : streamStageCost p i omega = ∞ := by
  have heq := streamStageCost_eq_stageCost p (i+1) (Fin.last i) omega
  simp only [Fin.val_last] at heq
  rw [heq]
  exact stageCost_nonhalting p (i+1) (Fin.last i) (truncate p (i+1) omega) h

theorem streamStageCost_finite_of_halts {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) (h : streamHalts p i omega) : streamStageCost p i omega < ∞ := by
  have heq := streamStageCost_eq_stageCost p (i+1) (Fin.last i) omega
  simp only [Fin.val_last] at heq
  rw [heq]
  exact stageCost_finite_of_halts p (i+1) (Fin.last i) (truncate p (i+1) omega) h

theorem streamStageCost_finite_iff {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) : streamStageCost p i omega < ∞ ↔ streamHalts p i omega := by
  constructor
  · intro hc
    by_contra hh
    rw [streamStageCost_nonhalting p i omega hh] at hc
    exact (lt_irrefl _ hc)
  · exact streamStageCost_finite_of_halts p i omega

theorem streamStageCost_le_prefix {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (omega : Omega p) : streamStageCost p i.val omega ≤ prefixStageCost p N omega := by
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin N => streamStageCost p j.val omega)
    (fun j _ => (show (0 : ℝ≥0∞) ≤ streamStageCost p j.val omega from bot_le))
    (Finset.mem_univ i)

/-- No geometric success assumption is needed for this exact operational equivalence. -/
theorem prefixStageCost_finite_iff {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) :
    prefixStageCost p N omega < ∞ ↔ ∀ i : Fin N, streamHalts p i.val omega := by
  constructor
  · intro h i
    exact (streamStageCost_finite_iff p i.val omega).mp
      (lt_of_le_of_lt (streamStageCost_le_prefix p N i omega) h)
  · intro h
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact streamStageCost_finite_of_halts p i.val omega (h i)

/-- Simultaneous finite-prefix finiteness is exactly simultaneous stage termination. -/
theorem all_prefixStageCost_finite_iff {L : ℝ} (p : GeometricParameters L)
    (omega : Omega p) :
    (∀ N, prefixStageCost p N omega < ∞) ↔ ∀ i, streamHalts p i omega := by
  constructor
  · intro h i
    exact (prefixStageCost_finite_iff p (i+1) omega).mp (h (i+1)) (Fin.last i)
  · intro h N
    exact (prefixStageCost_finite_iff p N omega).mpr (fun i => h i.val)

theorem prefixStageCost_nonhalting {L : ℝ} (p : GeometricParameters L) {i N : ℕ}
    (hi : i < N) (omega : Omega p) (h : ¬ streamHalts p i omega) :
    prefixStageCost p N omega = ∞ := by
  apply top_unique
  have hb := streamStageCost_le_prefix p N ⟨i,hi⟩ omega
  rw [streamStageCost_nonhalting p i omega h] at hb
  exact hb

theorem nonhalting_default_and_cost {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) (h : ¬ streamHalts p i omega) :
    streamHaltTime p i omega = 0 ∧ streamStageCost p i omega = ∞ :=
  ⟨streamHaltTime_of_not_halts p i omega h, streamStageCost_nonhalting p i omega h⟩

theorem measurable_streamStageCost {L : ℝ} (p : GeometricParameters L) (i : ℕ) :
    Measurable (streamStageCost p i) :=
  (measurable_jointStageCost p i).comp
    ((measurable_levelMap p i).prodMk (measurable_pi_apply i))

theorem measurable_prefixStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (prefixStageCost p N) :=
  Finset.measurable_sum Finset.univ (fun i _ => measurable_streamStageCost p i.val)

theorem measurable_streamCostProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun i => streamStageCost p i omega) :=
  measurable_pi_lambda _ (fun i => measurable_streamStageCost p i)

theorem measurable_prefixCostProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun N => prefixStageCost p N omega) :=
  measurable_pi_lambda _ (fun N => measurable_prefixStageCost p N)

/-- Full finite history, the labelled vector of paid costs, and their actual sum. -/
abbrev PaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :=
  ((i : Fin (N+1)) → StageMaps p i.val) × (Fin N → ℝ≥0∞) × ℝ≥0∞

def finitePaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : PaidObservation p N :=
  (history p N z, (fun i => stageCost p N i z), totalStageCost p N z)

def streamPaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) : PaidObservation p N :=
  ((fun i => levelMap p omega i.val), (fun i => streamStageCost p i.val omega),
    prefixStageCost p N omega)

theorem streamPaidObservation_original {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) :
    streamPaidObservation p N omega = finitePaidObservation p N (truncate p N omega) := by
  apply Prod.ext
  · funext i
    exact (history_truncate p N omega i).symm
  · apply Prod.ext
    · funext i
      exact streamStageCost_eq_stageCost p N i omega
    · exact prefixStageCost_eq_totalStageCost p N omega

theorem measurable_finitePaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (finitePaidObservation p N) :=
  (measurable_history p N).prodMk
    ((measurable_pi_lambda _ (fun i => measurable_stageCost p N i)).prodMk
      (measurable_totalStageCost p N))

theorem measurable_streamPaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (streamPaidObservation p N) :=
  (measurable_pi_lambda _ (fun i : Fin (N+1) => measurable_levelMap p i.val)).prodMk
    ((measurable_pi_lambda _ (fun i : Fin N => measurable_streamStageCost p i.val)).prodMk
      (measurable_prefixStageCost p N))

/-- This identifies the cost/history copula, rather than only their scalar marginals. -/
theorem streamPaidObservation_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (streamLaw p).map (streamPaidObservation p N) =
      (experimentLaw p N).map (finitePaidObservation p N) := by
  have heq : streamPaidObservation p N = finitePaidObservation p N ∘ truncate p N :=
    funext (streamPaidObservation_original p N)
  rw [heq, ← Measure.map_map (measurable_finitePaidObservation p N)
    (measurable_truncate p N), truncate_law]

/-- Incoming geometry can depend on earlier noise; only the current table is fresh. -/
theorem streamStageCost_integral_eq {L : ℝ} (p : GeometricParameters L) (i : ℕ) :
    (∫⁻ omega, streamStageCost p i omega ∂streamLaw p) =
      ∫⁻ J, ∫⁻ T, jointStageCost p i (J,T) ∂physicalTableLaw p i ∂outputLaw p i := by
  calc
    _ = ∫⁻ w, jointStageCost p i w
        ∂(streamLaw p).map (fun omega => (levelMap p omega i, omega i)) :=
      (lintegral_map (measurable_jointStageCost p i)
        ((measurable_levelMap p i).prodMk (measurable_pi_apply i))).symm
    _ = _ := by
      rw [stream_freshPair_law]
      exact lintegral_prod _ (measurable_jointStageCost p i).aemeasurable

theorem streamStageCost_integral_le {L : ℝ} (p : GeometricParameters L) (i : ℕ) :
    (∫⁻ omega, streamStageCost p i omega ∂streamLaw p) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p i+1)^10 : ℕ) : ℝ≥0∞) := by
  rw [streamStageCost_integral_eq]
  exact jointStageCost_integral_le p i

/-- Exact transport of the original total-cost integral, including exceptional inputs. -/
theorem prefixStageCost_integral_eq_finite {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) =
      ∫⁻ z, totalStageCost p N z ∂experimentLaw p N := by
  calc
    _ = ∫⁻ omega, totalStageCost p N (truncate p N omega) ∂streamLaw p := by
      apply lintegral_congr
      exact prefixStageCost_eq_totalStageCost p N
    _ = ∫⁻ z, totalStageCost p N z ∂(streamLaw p).map (truncate p N) :=
      (lintegral_map (measurable_totalStageCost p N) (measurable_truncate p N)).symm
    _ = _ := by rw [truncate_law]

theorem prefixStageCost_integral_eq_sum {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) =
      ∑ i : Fin N, ∫⁻ omega, streamStageCost p i.val omega ∂streamLaw p :=
  lintegral_finsetSum Finset.univ (fun i _ => measurable_streamStageCost p i.val)

theorem prefixStageCost_integral_le_sum {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) *
        ∑ i : Fin N, (65*stageQubits p i.val+1)^10 : ℕ) : ℝ≥0∞) := by
  rw [prefixStageCost_integral_eq_finite]
  exact totalStageCost_integral_le_sum p N

/-- The coefficient depends only on p, which is fixed before the prefix length. -/
theorem prefixStageCost_integral_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) *
        (65^10 * (stageQubits p N+1)^11) : ℕ) : ℝ≥0∞) := by
  rw [prefixStageCost_integral_eq_finite]
  exact totalStageCost_integral_le p N

/-- Every finite paid prefix is finite on the existing, unchanged success event. -/
theorem allFiniteSuccess_prefixStageCost_finite {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (N : ℕ) :
    prefixStageCost p N omega < ∞ := by
  exact (prefixStageCost_finite_iff p N omega).mpr
    (fun i => allFiniteSuccess_halts p h i.val)

/-- Operational and physical conclusions concern one and the same stream point. -/
theorem allFiniteSuccess_paid_geometry {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) :
    (∀ i, streamHalts p i omega) ∧
    (∀ N, prefixStageCost p N omega < ∞) ∧
    (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
    ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t :=
  ⟨allFiniteSuccess_halts p h, allFiniteSuccess_prefixStageCost_finite p h,
    allFiniteSuccess_stageFacts p h, allFiniteSuccess_geometry p h⟩

theorem common_paid_geometry_ae {L : ℝ} (p : GeometricParameters L) :
    ∀ᵐ omega ∂streamLaw p, omega ∈ allFiniteSuccess p ∧
      (∀ i, streamHalts p i omega) ∧
      (∀ N, prefixStageCost p N omega < ∞) ∧
      (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t := by
  filter_upwards [allFiniteSuccess_ae p] with omega h
  exact ⟨h, allFiniteSuccess_paid_geometry p h⟩

/-- All source-even levels, including the seed, share the same paid success event. -/
theorem allFiniteSuccess_paid_source_even {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (k : ℕ) :
    prefixStageCost p (2*k) omega < ∞ ∧
      PhysicalGeometry (perturbationOddScale p) (2*k) (levelMap p omega (2*k)) p.t :=
  ⟨allFiniteSuccess_prefixStageCost_finite p h (2*k), allFiniteSuccess_source_even p h k⟩

/-- This packages counted stage costs, not full uniform constructor runtime. -/
theorem fixed_parameters_common_paid_stream (L : ℝ) :
    ∃ p : GeometricParameters L,
      (∀ i, Measurable (streamStageCost p i)) ∧
      (∀ N, Measurable (prefixStageCost p N) ∧
        (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) ≤
          ((operationConstant ((6*p.m+2)*p.lambda) *
            (65^10 * (stageQubits p N+1)^11) : ℕ) : ℝ≥0∞)) ∧
      MeasurableSet (allFiniteSuccess p) ∧ streamLaw p (allFiniteSuccess p) = 1 ∧
      ∀ᵐ omega ∂streamLaw p, omega ∈ allFiniteSuccess p ∧
        (∀ i, streamHalts p i omega) ∧
        (∀ N, prefixStageCost p N omega < ∞) ∧
        (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
        ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  exact ⟨p, measurable_streamStageCost p,
    fun N => ⟨measurable_prefixStageCost p N, prefixStageCost_integral_le p N⟩,
    measurableSet_allFiniteSuccess p, allFiniteSuccess_measure p, common_paid_geometry_ae p⟩

end QEC.Coding.BDL26CountableEmbeddingExperiment
