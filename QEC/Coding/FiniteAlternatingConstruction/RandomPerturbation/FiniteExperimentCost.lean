import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperimentGeometry
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ExpectedOperationCost
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedCostMeasurability

/-!
# Counted costs on the actual finite embedding experiment

The cost is the original stopped row program, with infinity on nontermination.
It does not charge generation of the fixed rank dictionaries or the replacement
materialization; that uniform operational work remains outside this stage model.
The fixed numerical parameters precede every depth and every random input.
-/

noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

/-- Relabeling a counted scan preserves its branch-by-branch numeric cost.
Concrete uses must prove the query equality, including the cost component. -/
theorem scanQuery_map_pair {A B W : Type*} (encode : A → B)
    (qA : A → W → Bool × ℕ) (qB : B → W → Bool × ℕ)
    (hquery : ∀ a w, qB (encode a) w = qA a w) (rows : List A) (w : W) :
    scanQuery qB (rows.map encode) w =
      ((scanQuery qA rows w).1.map encode, (scanQuery qA rows w).2) := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
      simp only [List.map_cons, scanQuery, hquery]
      cases h : (qA a w).1 <;> simp [h, ih]

/-- The original numeric execution cost, on one incoming-map/current-table pair. -/
def jointStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : ℝ≥0∞ :=
  actualExecutionCost (StagePresentation p n) w.1
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
    p.lambda ((6*p.m+2)*p.lambda) w.2

/-- No fresh output is selected: both arguments are read from the original experiment. -/
def stageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : ℝ≥0∞ :=
  jointStageCost p i.val (stagePair p n i z)

/-- A finite sum of actual costs, rather than a sum of replacement budgets. -/
def totalStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p n) : ℝ≥0∞ := ∑ i : Fin n, stageCost p n i z

theorem stageCost_original {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p n) :
    stageCost p n i z = actualExecutionCost (StagePresentation p i.val)
      (stageInput p n i z) (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) (tableAt p n i z) := rfl

/-- Exact pointwise transport; no success or termination premise is needed. -/
theorem stageCost_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (z : Experiment p n) :
    stageCost p m i (experimentPrefix p m n h z) =
      stageCost p n (i.castLE h) z :=
  congrArg (jointStageCost p i.val) (stagePair_prefix p h i z)

@[simp] theorem totalStageCost_zero {L : ℝ} (p : GeometricParameters L)
    (z : Experiment p 0) : totalStageCost p 0 z = 0 := by
  simp only [totalStageCost, Fin.sum_univ_zero]

/-- The final stage reads precisely the preceding output and the last original factor. -/
theorem stageCost_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) :
    stageCost p (n+1) (Fin.last n) z =
      jointStageCost p n (evaluate p n z.1, z.2) := by
  simp only [stageCost, stagePair, stageInput, Fin.val_last, prefix_last, tableAt_last]

theorem stageCost_castSucc {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p (n+1)) :
    stageCost p (n+1) i.castSucc z = stageCost p n i z.1 := by
  have h := stageCost_prefix p (Nat.le_succ n) i z
  have hi : i.castLE (Nat.le_succ n) = i.castSucc := Fin.ext rfl
  rw [hi] at h
  simpa only [prefix_last] using h.symm

/-- Deleting a final table removes exactly its cost, including the nonhalting branch. -/
theorem totalStageCost_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) :
    totalStageCost p (n+1) z = totalStageCost p n z.1 +
      jointStageCost p n (evaluate p n z.1, z.2) := by
  simp only [totalStageCost, Fin.sum_univ_castSucc, stageCost_castSucc, stageCost_last]

/-- The single actual stage starts at the literal seed, including on exceptional tables. -/
theorem totalStageCost_one {L : ℝ} (p : GeometricParameters L)
    (z : Experiment p 1) :
    totalStageCost p 1 z = jointStageCost p 0
      (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p), z.2) := by
  rw [totalStageCost_succ, totalStageCost_zero, zero_add, evaluate_zero]

/-- Physical qubits of the selected construction, independent of geometry and randomness. -/
def stageQubits {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  Fintype.card (StagePresentation p n).Q

theorem stageQubits_double {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    2 * stageQubits p n ≤ stageQubits p (n+1) :=
  nextState_qubit_card_lower (perturbationOddScale p) n (state (perturbationOddScale p) n)

theorem stageQubits_mono {L : ℝ} (p : GeometricParameters L) :
    Monotone (stageQubits p) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := stageQubits_double p n
  omega

/-- The number of stages is bounded by the actual final number of qubits. -/
theorem stage_count_le_qubits {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    n ≤ stageQubits p n := by
  have hpow : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hp : 0 < 2 ^ k := pow_pos (by decide) k
        omega
  have hseed := state_qubit_card_lower (perturbationOddScale p) n
  change n ≤ Fintype.card (state (perturbationOddScale p) n).presentation.Q
  exact (hpow n).trans (by omega)

/-- This arithmetic is applied to the derived single-stage expectation bounds. -/
theorem stage_size_sum_le {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∑ i : Fin n, (65 * stageQubits p i.val + 1)^10) ≤
      65^10 * (stageQubits p n + 1)^11 := by
  let q := stageQubits p n
  have hmono (i : Fin n) : stageQubits p i.val ≤ q :=
    stageQubits_mono p (Nat.le_of_lt i.isLt)
  have hterm (i : Fin n) : (65 * stageQubits p i.val + 1)^10 ≤
      65^10 * (q+1)^10 := by
    calc
      _ ≤ (65 * (q+1))^10 := Nat.pow_le_pow_left (by have := hmono i; omega) 10
      _ = _ := by rw [mul_pow]
  calc
    _ ≤ ∑ _i : Fin n, 65^10 * (q+1)^10 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = n * (65^10 * (q+1)^10) := by simp
    _ ≤ (q+1) * (65^10 * (q+1)^10) :=
      Nat.mul_le_mul_right _ ((stage_count_le_qubits p n).trans (Nat.le_succ q))
    _ = _ := by dsimp only [q]; ring

/-- The original numeric cost is measurable in both incoming geometry and table. -/
theorem measurable_jointStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (jointStageCost p n) :=
  measurable_joint_actualExecutionCost (StagePresentation p n) (by positivity)
    p.lambda ((6*p.m+2)*p.lambda)

theorem measurable_stageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (stageCost p n i) :=
  (measurable_jointStageCost p i.val).comp (measurable_stagePair p n i)

theorem measurable_totalStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (totalStageCost p n) :=
  Finset.measurable_sum Finset.univ (fun i _ => measurable_stageCost p n i)

/-- Exact random-input law and Tonelli identity, with no independent-output claim. -/
theorem stageCost_integral_eq {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (∫⁻ z, stageCost p n i z ∂experimentLaw p n) =
      ∫⁻ J, ∫⁻ T, jointStageCost p i.val (J,T)
        ∂physicalTableLaw p i.val ∂outputLaw p i.val := by
  calc
    _ = ∫⁻ w, jointStageCost p i.val w
        ∂(experimentLaw p n).map (stagePair p n i) :=
      (lintegral_map (measurable_jointStageCost p i.val) (measurable_stagePair p n i)).symm
    _ = _ := by
      rw [stagePair_law]
      exact lintegral_prod _ (measurable_jointStageCost p i.val).aemeasurable

/-- The input-good condition is derived from the literal seed recursion. -/
theorem jointStageCost_integral_le {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ J, ∫⁻ T, jointStageCost p n (J,T) ∂physicalTableLaw p n ∂outputLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p n+1)^10 : ℕ) : ℝ≥0∞) := by
  have hbound : ∀ᵐ J ∂outputLaw p n,
      (∫⁻ T, jointStageCost p n (J,T) ∂physicalTableLaw p n) ≤
        ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p n+1)^10 : ℕ) : ℝ≥0∞) := by
    filter_upwards [outputLaw_good_ae p n] with J hJ
    exact geometric_expected_operations_le_qubits (StagePresentation p n) J
      (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible p hJ
      (BDL26BoundedValence.state_boundedValence (perturbationOddScale p) n)
  calc
    _ ≤ ∫⁻ _J : StageMaps p n,
        ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p n+1)^10 : ℕ) : ℝ≥0∞)
        ∂outputLaw p n := lintegral_mono_ae hbound
    _ = _ := by simp

theorem stageCost_integral_le {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (∫⁻ z, stageCost p n i z ∂experimentLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p i.val+1)^10 : ℕ) : ℝ≥0∞) := by
  rw [stageCost_integral_eq]
  exact jointStageCost_integral_le p i.val

/-- Finite additivity needs measurability, rather than independence of the costs. -/
theorem totalStageCost_integral_eq_sum {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) =
      ∑ i : Fin n, ∫⁻ z, stageCost p n i z ∂experimentLaw p n :=
  lintegral_finsetSum Finset.univ (fun i _ => measurable_stageCost p n i)

theorem totalStageCost_integral_le_sum {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) *
        ∑ i : Fin n, (65*stageQubits p i.val+1)^10 : ℕ) : ℝ≥0∞) := by
  rw [totalStageCost_integral_eq_sum]
  calc
    _ ≤ ∑ i : Fin n,
        ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p i.val+1)^10 : ℕ) : ℝ≥0∞) :=
      Finset.sum_le_sum (fun i _ => stageCost_integral_le p n i)
    _ = _ := by simp only [Finset.mul_sum, Nat.cast_sum]

/-- Degree eleven is derived from actual growth, uniformly in depth for fixed p. -/
theorem totalStageCost_integral_le {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) *
        (65^10 * (stageQubits p n+1)^11) : ℕ) : ℝ≥0∞) := by
  exact (totalStageCost_integral_le_sum p n).trans
    ((Nat.cast_le (α := ℝ≥0∞)).mpr
      (Nat.mul_le_mul_left _ (stage_size_sum_le p n)))

/-- The actual nonhalting branch is still infinite even though haltTime defaults to zero. -/
theorem stageCost_nonhalting {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) (h : ¬ stageHalts p n i z) : stageCost p n i z = ∞ := by
  rw [stageCost_original]
  exact if_neg h

theorem stageCost_finite_of_halts {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) (h : stageHalts p n i z) : stageCost p n i z < ∞ := by
  unfold stageHalts at h
  rw [stageCost_original]
  simp only [actualExecutionCost, if_pos h]
  simp

/-- Finiteness holds on exactly the existing simultaneous Halts-and-Good event. -/
theorem totalStageCost_finite_on_success {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p n) (h : z ∈ finiteSuccess p n) : totalStageCost p n z < ∞ := by
  apply ENNReal.sum_lt_top.mpr
  intro i _
  exact stageCost_finite_of_halts p n i z (h.2.1 i)

theorem finiteSuccess_and_totalStageCost_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n ∧ totalStageCost p n z < ∞ := by
  filter_upwards [finiteSuccess_ae p n] with z hz
  exact ⟨hz, totalStageCost_finite_on_success p n z hz⟩

/-- Numerical parameters are chosen before every finite depth. This is the
expected cost of the existing counted stages, not uniform constructor runtime. -/
theorem finite_stage_cost_parameters (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ n : ℕ,
      Measurable (totalStageCost p n) ∧
      (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) ≤
        ((operationConstant ((6*p.m+2)*p.lambda) *
          (65^10 * (stageQubits p n+1)^11) : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n ∧ totalStageCost p n z < ∞ := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  exact ⟨p, fun n => ⟨measurable_totalStageCost p n, totalStageCost_integral_le p n,
    finiteSuccess_and_totalStageCost_ae p n⟩⟩

end QEC.Coding.BDL26FiniteEmbeddingExperiment
