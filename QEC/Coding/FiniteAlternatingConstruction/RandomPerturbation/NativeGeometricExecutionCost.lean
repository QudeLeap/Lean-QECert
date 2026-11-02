import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeGeometricScanCost
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeGeometricExecution
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedCostMeasurability
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ExpectedOperationCost
import QEC.Coding.ProbabilisticConstruction.Resampling.StrictSlackMoments

/-!
# Counted stopping and total cost of the original native execution

The finite-fuel interpreter below performs the original paid scan before each
transition, copies the complete generated trace, and stops only on its actual
no-event result. Its terminal branch materializes the native output rows. Fuel
is a finite observation bound; no interpreter instruction calls a halt-time
oracle. The mathematical stopped cost retains infinity on nontermination.
-/
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricExecutionCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

private theorem initialized_length (S : OddScale) (n : ℕ) (T : NativeTable S n) :
    (SR.initializeQ S n T).value.length=SR.count S n := by
  simp only [SR.initialize_value,SR.rowsFor,List.length_map,
    BDL26NativeStateRows.indices_length]

private theorem refresh_length (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (U : List (SR.Index S n)) (R : SR.Rows (SR.Index S n)) :
    (SR.refreshQ T U R).value.length=R.length := by
  have h := congrArg List.length (BDL26NativeStateRows.refresh_labels T U R)
  simpa only [List.length_map] using h

private theorem prefix_value_succ (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T (m+1)).value =
      ⟨(SR.refreshQ T (chosenSupport S n J r
          (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1)
          (prefixQ S n J hr lambda K T m).value.rows).value,
        (BDL26NativeMasterCandidates.appendQ
          (prefixQ S n J hr lambda K T m).value.trace
          [(scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1]).value⟩ := by
  rfl

private theorem prefix_operations_succ (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T (m+1)).operations =
      (prefixQ S n J hr lambda K T m).operations+
        (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).2+
        (SR.refreshQ T (chosenSupport S n J r
          (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1)
          (prefixQ S n J hr lambda K T m).value.rows).operations+
        (BDL26NativeMasterCandidates.appendQ
          (prefixQ S n J hr lambda K T m).value.trace
          [(scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1]).operations+4 := by
  rfl

private theorem prefix_lengths (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T m).value.rows.length=SR.count S n ∧
      (prefixQ S n J hr lambda K T m).value.trace.length=m := by
  induction m with
  | zero => exact ⟨initialized_length S n T,rfl⟩
  | succ m ih =>
      constructor
      · exact (refresh_length S n T _ _).trans ih.1
      · change (BDL26NativeMasterCandidates.appendQ
          (prefixQ S n J hr lambda K T m).value.trace [_]).value.length=m+1
        rw [(BDL26NativeMasterCandidates.append_spec _ _).1,
          List.length_append,ih.2]
        rfl

private theorem chosenSupport_length (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ)
    (e : Option (LiveRow S n J r)) : (chosenSupport S n J r e).length ≤ 12 := by
  cases e with
  | none => simp only [chosenSupport,List.length_nil]; omega
  | some e => exact (support_complete S n J r e).2.1.le

/-- The affine term covers every paid scan and refresh; the square separately
charges the growing trace-copy spine. -/
def prefixBudget (S : OddScale) (n K m : ℕ) : ℕ :=
  incomingBudget S n+1+
    m*(scanBudget S n K (SR.count S n)+35*SR.count S n+4)+m^2

theorem native_prefix_cost_le (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T m).operations ≤ prefixBudget S n K m := by
  induction m with
  | zero =>
      change (SR.initializeQ S n T).operations+1 ≤ prefixBudget S n K 0
      rw [(BDL26NativeStateRows.initialize_cost S n T).1]
      simp [prefixBudget,incomingBudget]
  | succ m ih =>
      let prior := prefixQ S n J hr lambda K T m
      let q := scanQ S n J hr lambda K prior.value.rows
      have hl := prefix_lengths S n J hr lambda K T m
      have hs := native_scan_cost_le S n J hr lambda K prior.value.rows
      change prior.value.rows.length=SR.count S n ∧ prior.value.trace.length=m at hl
      rw [hl.1] at hs
      have hu := chosenSupport_length S n J r q.1
      have hf := (BDL26NativeStateRows.refresh_cost T
        (chosenSupport S n J r q.1) prior.value.rows).1
      rw [hl.1] at hf
      have hf' : (SR.refreshQ T (chosenSupport S n J r q.1)
          prior.value.rows).operations ≤ 35*SR.count S n := by
        have hmul := Nat.mul_le_mul_left (SR.count S n)
          (show 2*(chosenSupport S n J r q.1).length+11 ≤ 35 by omega)
        exact hf.trans (by simpa only [Nat.mul_comm] using hmul)
      have ha := (BDL26NativeMasterCandidates.append_spec prior.value.trace [q.1]).2.1
      rw [hl.2] at ha
      change prior.operations+q.2+
        (SR.refreshQ T (chosenSupport S n J r q.1) prior.value.rows).operations+
        (BDL26NativeMasterCandidates.appendQ prior.value.trace [q.1]).operations+4 ≤ _
      change prior.operations ≤ prefixBudget S n K m at ih
      dsimp only [prefixBudget] at ih ⊢
      change q.2 ≤ scanBudget S n K (SR.count S n) at hs
      nlinarith

/-- A finite execution observation contains its actual terminal state and paid
materialized output. A fuel-exhausted observation has no supplied final output. -/
structure StopObservation (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) where
  state : Prefix S n J r
  emitted : Option (List (SR.Index S n × Space))

/-- Stateful finite-fuel refinement. Fuel zero performs no query. Every positive
fuel step pays the original scan; a clean scan pays output traversal and return
bookkeeping, while an active scan pays refresh and full growing append. -/
def stopFromQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    ℕ → Prefix S n J r → PrefixRun (StopObservation S n J r)
  | 0, state => ⟨⟨state,none⟩,0⟩
  | fuel+1, state =>
      let query := scanQ S n J hr lambda K state.rows
      match query.1 with
      | none =>
          let emitted := BDL26NativeStateRows.emitQ state.rows
          ⟨⟨state,some emitted.value⟩,query.2+emitted.operations+3⟩
      | some row =>
          let refreshed := SR.refreshQ T (support S n J r row) state.rows
          let appended := BDL26NativeMasterCandidates.appendQ state.trace [some row]
          let rest := stopFromQ S n J hr lambda K T fuel ⟨refreshed.value,appended.value⟩
          ⟨rest.value,query.2+refreshed.operations+appended.operations+rest.operations+4⟩

/-- Initialization is executed once, before the finite stopping loop. -/
def stopQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (fuel : ℕ) : PrefixRun (StopObservation S n J r) :=
  let initialized := SR.initializeQ S n T
  let rest := stopFromQ S n J hr lambda K T fuel ⟨initialized.value,[]⟩
  ⟨rest.value,initialized.operations+rest.operations+1⟩

private theorem stopFrom_none (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (fuel : ℕ)
    (state : Prefix S n J r)
    (hq : (scanQ S n J hr lambda K state.rows).1=none) :
    stopFromQ S n J hr lambda K T (fuel+1) state =
      ⟨⟨state,some (BDL26NativeStateRows.emitQ state.rows).value⟩,
        (scanQ S n J hr lambda K state.rows).2+
          (BDL26NativeStateRows.emitQ state.rows).operations+3⟩ := by
  simp only [stopFromQ,hq]

private theorem stopFrom_some (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (fuel : ℕ)
    (state : Prefix S n J r) (row : LiveRow S n J r)
    (hq : (scanQ S n J hr lambda K state.rows).1=some row) :
    stopFromQ S n J hr lambda K T (fuel+1) state =
      let refreshed := SR.refreshQ T (support S n J r row) state.rows
      let appended := BDL26NativeMasterCandidates.appendQ state.trace [some row]
      let rest := stopFromQ S n J hr lambda K T fuel ⟨refreshed.value,appended.value⟩
      ⟨rest.value,(scanQ S n J hr lambda K state.rows).2+
        refreshed.operations+appended.operations+rest.operations+4⟩ := by
  simp only [stopFromQ,hq]

private theorem stop_initial_value (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (fuel : ℕ) :
    (stopQ S n J hr lambda K T fuel).value =
      (stopFromQ S n J hr lambda K T fuel (prefixQ S n J hr lambda K T 0).value).value := by
  rfl

private theorem stop_initial_operations (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (fuel : ℕ) :
    (stopQ S n J hr lambda K T fuel).operations =
      (prefixQ S n J hr lambda K T 0).operations+
        (stopFromQ S n J hr lambda K T fuel (prefixQ S n J hr lambda K T 0).value).operations := by
  change (SR.initializeQ S n T).operations+
      (stopFromQ S n J hr lambda K T fuel
        ⟨(SR.initializeQ S n T).value,[]⟩).operations+1=
    ((SR.initializeQ S n T).operations+1)+
      (stopFromQ S n J hr lambda K T fuel
        ⟨(SR.initializeQ S n T).value,[]⟩).operations
  omega

private theorem stopFrom_at_first_none (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m d : ℕ)
    (hbefore : ∀ i < d, choice S n J hr lambda K T (m+i)≠none)
    (hstop : choice S n J hr lambda K T (m+d)=none) :
    (stopFromQ S n J hr lambda K T (d+1)
      (prefixQ S n J hr lambda K T m).value).value =
        ⟨(prefixQ S n J hr lambda K T (m+d)).value,
          some (BDL26NativeStateRows.emitQ
            (prefixQ S n J hr lambda K T (m+d)).value.rows).value⟩ ∧
    (prefixQ S n J hr lambda K T m).operations+
      (stopFromQ S n J hr lambda K T (d+1)
        (prefixQ S n J hr lambda K T m).value).operations =
      (prefixQ S n J hr lambda K T (m+d)).operations+
        (scanQ S n J hr lambda K
          (prefixQ S n J hr lambda K T (m+d)).value.rows).2+
        (BDL26NativeStateRows.emitQ
          (prefixQ S n J hr lambda K T (m+d)).value.rows).operations+3 := by
  induction d generalizing m with
  | zero =>
      have hs : (scanQ S n J hr lambda K
          (prefixQ S n J hr lambda K T m).value.rows).1=none := by
        simpa only [choice,Nat.add_zero] using hstop
      rw [stopFrom_none S n J hr lambda K T 0 _ hs]
      constructor
      · rfl
      · dsimp only [Nat.add_zero]
        change (prefixQ S n J hr lambda K T m).operations+
            ((scanQ S n J hr lambda K
                (prefixQ S n J hr lambda K T m).value.rows).2+
              (BDL26NativeStateRows.emitQ
                (prefixQ S n J hr lambda K T m).value.rows).operations+3)=
          (prefixQ S n J hr lambda K T m).operations+
            (scanQ S n J hr lambda K
              (prefixQ S n J hr lambda K T m).value.rows).2+
            (BDL26NativeStateRows.emitQ
              (prefixQ S n J hr lambda K T m).value.rows).operations+3
        omega
  | succ d ih =>
      have hs : (scanQ S n J hr lambda K
          (prefixQ S n J hr lambda K T m).value.rows).1≠none := by
        simpa only [choice,Nat.add_zero] using hbefore 0 (Nat.zero_lt_succ d)
      cases hq : (scanQ S n J hr lambda K
          (prefixQ S n J hr lambda K T m).value.rows).1 with
      | none => exact (hs hq).elim
      | some row =>
          have hb : ∀ i < d, choice S n J hr lambda K T (m+1+i)≠none := by
            intro i hi
            rw [show m+1+i=m+(i+1) by omega]
            exact hbefore (i+1) (by omega)
          have ht : choice S n J hr lambda K T (m+1+d)=none := by
            rw [show m+1+d=m+(d+1) by omega]
            exact hstop
          have hrec := ih (m+1) hb ht
          have hm : m+(d+1)=m+1+d := by omega
          have hn : (prefixQ S n J hr lambda K T (m+1)).value =
              ⟨(SR.refreshQ T (support S n J r row)
                (prefixQ S n J hr lambda K T m).value.rows).value,
                (BDL26NativeMasterCandidates.appendQ
                  (prefixQ S n J hr lambda K T m).value.trace [some row]).value⟩ := by
            simp only [prefix_value_succ,hq,chosenSupport]
          have hp := prefix_operations_succ S n J hr lambda K T m
          rw [hq] at hp
          change (prefixQ S n J hr lambda K T (m+1)).operations =
            (prefixQ S n J hr lambda K T m).operations+
              (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).2+
              (SR.refreshQ T (support S n J r row)
                (prefixQ S n J hr lambda K T m).value.rows).operations+
              (BDL26NativeMasterCandidates.appendQ
                (prefixQ S n J hr lambda K T m).value.trace [some row]).operations+4 at hp
          rw [stopFrom_some S n J hr lambda K T (d+1) _ row hq]
          dsimp only
          rw [←hn,hm]
          exact ⟨hrec.1,by omega⟩

/-- The finite-fuel program returns precisely the first no-event state and
generated trace. Its exact numeric cost includes the terminal scan and emitter. -/
theorem native_stopping_refinement (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : NativeHalts S n J hr lambda K T) :
    let m := nativeHaltTime S n J hr lambda K T
    (stopQ S n J hr lambda K T (m+1)).value =
      ⟨(prefixQ S n J hr lambda K T m).value,
        some (BDL26NativeStateRows.emitQ
          (prefixQ S n J hr lambda K T m).value.rows).value⟩ ∧
    (stopQ S n J hr lambda K T (m+1)).operations =
      (prefixQ S n J hr lambda K T m).operations+
        (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).2+
        5*SR.count S n+3 := by
  have ht : nativeHaltTime S n J hr lambda K T=Nat.find h := by
    simp only [nativeHaltTime,dif_pos h]
  have hb : ∀ i < Nat.find h, choice S n J hr lambda K T (0+i)≠none := by
    intro i hi
    simpa only [Nat.zero_add] using Nat.find_min h hi
  have hs : choice S n J hr lambda K T (0+Nat.find h)=none := by
    simpa only [Nat.zero_add] using Nat.find_spec h
  have hf := stopFrom_at_first_none S n J hr lambda K T 0 (Nat.find h) hb hs
  simp only [Nat.zero_add] at hf
  rw [←ht] at hf
  constructor
  · rw [stop_initial_value]
    exact hf.1
  · rw [stop_initial_operations,hf.2]
    have he := (BDL26NativeStateRows.emit_cost
      (prefixQ S n J hr lambda K T (nativeHaltTime S n J hr lambda K T)).value.rows).1
    rw [(prefix_lengths S n J hr lambda K T _).1] at he
    rw [he]

/-- The cost of the actual stopped finite-fuel program; a genuinely infinite
execution has infinite operation cost while its original output default remains
the column-zero assignment. -/
def nativeOperationCost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℝ≥0∞ :=
  if NativeHalts S n J hr lambda K T then
    ((stopQ S n J hr lambda K T
      (nativeHaltTime S n J hr lambda K T+1)).operations : ℝ≥0∞)
  else ∞

def executionBudget (S : OddScale) (n K m : ℕ) : ℕ :=
  prefixBudget S n K m+scanBudget S n K (SR.count S n)+5*SR.count S n+3

theorem native_stopped_cost_le (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : NativeHalts S n J hr lambda K T) :
    nativeOperationCost S n J hr lambda K T ≤
      (executionBudget S n K (nativeHaltTime S n J hr lambda K T) : ℕ) := by
  rw [nativeOperationCost,if_pos h,(native_stopping_refinement S n J hr lambda K T h).2]
  apply (Nat.cast_le (α := ℝ≥0∞)).mpr
  have hp := native_prefix_cost_le S n J hr lambda K T (nativeHaltTime S n J hr lambda K T)
  have hs := native_scan_cost_le S n J hr lambda K
    (prefixQ S n J hr lambda K T (nativeHaltTime S n J hr lambda K T)).value.rows
  rw [(prefix_lengths S n J hr lambda K T _).1] at hs
  dsimp only [executionBudget]
  omega

private theorem native_steps_decoded (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) :
    nativeTotalSteps S n J hr lambda K =
      totalSteps (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n J r) (B S n J r lambda K) ∘ decodedTable S n := by
  funext T
  have h := totalSteps_original S n J hr lambda K (decodedTable S n T)
  rw [encoded_decoded] at h
  exact h

/-- Strict slack is proved for the actual keyed supports and original product
law before the merged second-moment theorem is applied. -/
theorem native_expected_steps_sq (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ T, (nativeTotalSteps S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T)^2 ∂nativeTableMeasure S n p) ≤
        (2*(Fintype.card (Triangle (Presentation S n)))^8*
          (dependencyBound p.M+2)^2 : ℕ) := by
  let P := Presentation S n
  let ν := vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  have hbad := measurableSet_keyBad P (NC.nativeKey S n) (NC.nativeKey_injective S n)
    J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
  have hdegree : ∀ e : Event S n J (anchorRadius p.m),
      ((supportGraph (U S n J (anchorRadius p.m))).neighborFinset e).card ≤
        dependencyBound p.M := by
    intro e
    exact key_event_degree_le_of_density P (NC.nativeKey S n)
      (NC.nativeKey_injective S n) J (anchorRadius p.m) p.M p.t hJ
      (state_boundedValence S n) p.pool e
  have hprob : ∀ e : Event S n J (anchorRadius p.m),
      eventProbability (U S n J (anchorRadius p.m)) ν
        (B S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e ≤
          1/(4*((dependencyBound p.M : ℝ)+1)) := by
    intro e
    have h := key_probability_real_bound P (NC.nativeKey S n)
      (NC.nativeKey_injective S n) J p e
    simpa only [eventProbability,measureReal_def] using h.trans p.probability_ratio
  have hs := expected_totalSteps_sq_le (X := fun _ : Vertex P => Space)
    (U S n J (anchorRadius p.m))
    (B S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) ν
    hbad (dependencyBound p.M) hdegree hprob
  have hi : (∫⁻ T, (nativeTotalSteps S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T)^2 ∂nativeTableMeasure S n p) =
      ∫⁻ T, (totalSteps (X := fun _ : Vertex P => Space)
        (U S n J (anchorRadius p.m))
        (B S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)^2
        ∂tableMeasure P p := by
    rw [native_steps_decoded,←decoded_table_law S n p]
    exact (lintegral_map ((measurable_totalSteps (X := fun _ : Vertex P => Space)
      _ _ hbad).pow_const 2) hd).symm
  rw [hi]
  apply hs.trans
  apply (Nat.cast_le (α := ℝ≥0∞)).mpr
  have hc := keyEvent_card_le P (NC.nativeKey S n) (NC.nativeKey_injective S n)
    J (anchorRadius p.m)
  have hp := Nat.pow_le_pow_left hc 2
  calc
    2*(Fintype.card (Event S n J (anchorRadius p.m)))^2*(dependencyBound p.M+2)^2
      ≤ 2*((Fintype.card (Triangle P))^4)^2*(dependencyBound p.M+2)^2 := by gcongr
    _ = 2*(Fintype.card (Triangle P))^8*(dependencyBound p.M+2)^2 := by
      rw [←pow_mul]

private theorem native_halts_ae (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    ∀ᵐ T ∂nativeTableMeasure S n p,
      NativeHalts S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T := by
  filter_upwards [(native_execution_geometry_ae S n J p hJ).2] with T hT
  exact hT.1

private theorem native_steps_haltTime (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : NativeHalts S n J hr lambda K T) :
    nativeTotalSteps S n J hr lambda K T=
      (nativeHaltTime S n J hr lambda K T : ℝ≥0∞) := by
  have hh : Halts (X := fun _ : Vertex (Presentation S n) => Space)
      (U S n J r) (B S n J r lambda K) (decodedTable S n T) := by
    apply (halts_original S n J hr lambda K _).mp
    simpa only [encoded_decoded] using h
  have he := totalSteps_original S n J hr lambda K (decodedTable S n T)
  have ht := haltTime_original S n J hr lambda K (decodedTable S n T)
  rw [encoded_decoded] at he ht
  rw [he,totalSteps_eq_haltTime _ _ _ hh,ht]

/-- Data-independent constant and affine coefficients; the final square retains
the true growing append cost rather than charging it to the first moment. -/
def operationConstantTerm (S : OddScale) (n K : ℕ) : ℕ :=
  incomingBudget S n+scanBudget S n K (SR.count S n)+5*SR.count S n+4

def operationLinearTerm (S : OddScale) (n K : ℕ) : ℕ :=
  scanBudget S n K (SR.count S n)+35*SR.count S n+4

private theorem operation_quadratic_envelope (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : NativeHalts S n J hr lambda K T) :
    nativeOperationCost S n J hr lambda K T ≤
      (operationConstantTerm S n K : ℝ≥0∞)+
        (operationLinearTerm S n K : ℝ≥0∞)*nativeTotalSteps S n J hr lambda K T+
        (nativeTotalSteps S n J hr lambda K T)^2 := by
  rw [native_steps_haltTime S n J hr lambda K T h]
  apply (native_stopped_cost_le S n J hr lambda K T h).trans
  have he : executionBudget S n K (nativeHaltTime S n J hr lambda K T)=
      operationConstantTerm S n K+operationLinearTerm S n K*
        nativeHaltTime S n J hr lambda K T+(nativeHaltTime S n J hr lambda K T)^2 := by
    dsimp only [executionBudget,prefixBudget,operationConstantTerm,operationLinearTerm]
    ring
  rw [he]
  push_cast
  exact le_rfl

private instance liveRowFinite (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    Finite (LiveRow S n J r) :=
  Finite.of_injective (event S n J r) (event_injective S n J r)

private instance liveRowMeasurable (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    MeasurableSpace (LiveRow S n J r) := ⊤

private instance liveRowSingleton (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    MeasurableSingletonClass (LiveRow S n J r) := ⟨fun _ => trivial⟩

private def readLabelCost {A : Type*} [DecidableEq A] (a : A) : List A → ℕ
  | [] => 1
  | b::L => if b=a then 2 else readLabelCost a L+2

private theorem read_cost_labels {A : Type*} [DecidableEq A] (a : A)
    (R : BDL26NativeStateRows.Rows A) :
    (BDL26NativeStateRows.readQ a R).operations=readLabelCost a (R.map Prod.fst) := by
  induction R with
  | nil => rfl
  | cons row R ih =>
      by_cases h : row.1=a <;>
        simp only [BDL26NativeStateRows.readQ,List.map_cons,readLabelCost,h,if_true,if_false,ih]

private def refreshLabelCost {A : Type*} [DecidableEq A] (U : List A) : List A → ℕ
  | [] => 0
  | a::L => (BDL26NativeStateRows.memberQ a U).operations+
      (if (BDL26NativeStateRows.memberQ a U).value then 7 else 1)+
      refreshLabelCost U L+3

private theorem refresh_cost_labels {A : Type*} [DecidableEq A]
    (T : BDL26NativeStateRows.Samples A) (U : List A)
    (R : BDL26NativeStateRows.Rows A) :
    (BDL26NativeStateRows.refreshQ T U R).operations=
      refreshLabelCost U (R.map Prod.fst) := by
  change (BDL26NativeStateRows.mapQ (BDL26NativeStateRows.refreshRowQ T U) R).operations = _
  induction R with
  | nil => rfl
  | cons row R ih =>
      cases h : (BDL26NativeStateRows.memberQ row.1 U).value <;>
        simp only [BDL26NativeStateRows.mapQ,BDL26NativeStateRows.refreshRowQ,
          h,Bool.false_eq_true,if_false,if_true,List.map_cons,refreshLabelCost,ih]

private theorem prefix_labels (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T m).value.rows.map Prod.fst=SR.indices (SR.count S n) := by
  induction m with
  | zero => exact BDL26NativeStateRows.initialize_order S n T
  | succ m ih =>
      exact (BDL26NativeStateRows.refresh_labels T _ _).trans ih

private theorem measurable_native_point (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) (a : SR.Index S n) :
    Measurable (fun T : NativeTable S n => pointQ S n lambda (incomingQ S n J).value
      (prefixQ S n J hr lambda K T m).value.rows a) := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  have hbad := measurableSet_keyBad (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) J r lambda K
  have hcounters := measurable_counters (X := fun _ : Vertex (Presentation S n) => Space)
    (U S n J r) (B S n J r lambda K) hbad m
  have hm : Measurable (fun T : NativeTable S n =>
      assignment (X := fun _ : Vertex (Presentation S n) => Space)
        (decodedTable S n T)
        (counters (X := fun _ : Vertex (Presentation S n) => Space)
          (U S n J r) (B S n J r lambda K) (decodedTable S n T) m) (SR.decode S n a)) :=
    (measurable_pi_apply (SR.decode S n a)).comp ((measurable_assignment hcounters).comp hd)
  have hp : Measurable (fun T : NativeTable S n =>
      (pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows a).1) := by
    have he : (fun T : NativeTable S n =>
        (pointQ S n lambda (incomingQ S n J).value
          (prefixQ S n J hr lambda K T m).value.rows a).1) =
        (fun T : NativeTable S n => lambda • ((1/2 : ℝ) • J (SR.decode S n a))+
          assignment (X := fun _ : Vertex (Presentation S n) => Space)
            (decodedTable S n T)
            (counters (X := fun _ : Vertex (Presentation S n) => Space)
              (U S n J r) (B S n J r lambda K) (decodedTable S n T) m) (SR.decode S n a)) := by
      funext T
      rw [point_actual]
      have he := prefix_assignment S n J hr lambda K (decodedTable S n T) m
      rw [encoded_decoded] at he
      rw [he]
    rw [he]
    exact measurable_const.add hm
  have hc : ∀ T : NativeTable S n,
      (pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows a).2=
      (SR.readQ a (incomingQ S n J).value).operations+
        readLabelCost a (SR.indices (SR.count S n))+24+2 := by
    intro T
    simp only [pointQ,pointSnapshotQuery_cost,read_cost_labels,prefix_labels]
  have he : (fun T : NativeTable S n =>
      pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows a) =
      (fun T : NativeTable S n =>
        ((pointQ S n lambda (incomingQ S n J).value
          (prefixQ S n J hr lambda K T m).value.rows a).1,
          (SR.readQ a (incomingQ S n J).value).operations+
            readLabelCost a (SR.indices (SR.count S n))+24+2)) := by
    funext T
    exact Prod.ext (by rfl) (hc T)
  rw [he]
  exact hp.prodMk measurable_const

private theorem measurable_native_triangle (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) (c : MD.Code) (center : Space) :
    Measurable (fun T : NativeTable S n => triangleCodeQ S n J lambda
      (prefixQ S n J hr lambda K T m).value.rows c center) := by
  cases hf : (MD.atlasReadQ c (MD.atlasQ S n).value).value with
  | none => simp only [triangleCodeQ,hf]; exact measurable_const
  | some v =>
      let x := fun T : NativeTable S n => pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows v.1
      let y := fun T : NativeTable S n => pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows v.2.1
      let z := fun T : NativeTable S n => pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows v.2.2
      have hx : Measurable x := measurable_native_point S n J hr lambda K m v.1
      have hy : Measurable y := measurable_native_point S n J hr lambda K m v.2.1
      have hz : Measurable z := measurable_native_point S n J hr lambda K m v.2.2
      have hq : Measurable (fun T : NativeTable S n =>
          triangleQuery ![(x T).1,(y T).1,(z T).1] center 2) := by
        refine measurable_triangleQuery
          (fun T : NativeTable S n => ![(x T).1,(y T).1,(z T).1])
          (fun _ => center) (fun _ => (2 : ℝ)) ?_ ?_ measurable_const
        · intro i j
          fin_cases i
          · change Measurable (fun T : NativeTable S n => (x T).1 j)
            exact (PiLp.continuous_apply (2 : ℝ≥0∞)
              (fun _ : Fin 3 => ℝ) j).measurable.comp hx.fst
          · change Measurable (fun T : NativeTable S n => (y T).1 j)
            exact (PiLp.continuous_apply (2 : ℝ≥0∞)
              (fun _ : Fin 3 => ℝ) j).measurable.comp hy.fst
          · change Measurable (fun T : NativeTable S n => (z T).1 j)
            exact (PiLp.continuous_apply (2 : ℝ≥0∞)
              (fun _ : Fin 3 => ℝ) j).measurable.comp hz.fst
        · intro j
          exact measurable_const
      have hc : Measurable (fun T : NativeTable S n =>
          (MD.atlasQ S n).operations+(MD.atlasReadQ c (MD.atlasQ S n).value).operations+
          (incomingQ S n J).operations+(x T).2+(y T).2+(z T).2+
          (triangleQuery ![(x T).1,(y T).1,(z T).1] center 2).2+4) :=
        (((((measurable_const.add hx.snd).add hy.snd).add hz.snd).add hq.snd).add measurable_const)
      have he : (fun T : NativeTable S n => triangleCodeQ S n J lambda
          (prefixQ S n J hr lambda K T m).value.rows c center) =
          (fun T : NativeTable S n =>
            ((triangleQuery ![(x T).1,(y T).1,(z T).1] center 2).1,
              (MD.atlasQ S n).operations+(MD.atlasReadQ c (MD.atlasQ S n).value).operations+
                (incomingQ S n J).operations+(x T).2+(y T).2+(z T).2+
                (triangleQuery ![(x T).1,(y T).1,(z T).1] center 2).2+4)) := by
        funext T
        simp only [triangleCodeQ,hf,x,y,z]
      rw [he]
      exact hq.fst.prodMk hc

private theorem measurable_native_event_query (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) (row : LiveRow S n J r) :
    Measurable (fun T : NativeTable S n => eventQueryQ S n J r lambda K row
      (prefixQ S n J hr lambda K T m).value.rows) := by
  have hq := measurable_listAnyQuery (fun g : Grid K => fun T : NativeTable S n =>
    let center := centerQ S n J lambda K row.val.val.1 g
    let triangles := listAllQuery (fun c => triangleCodeQ S n J lambda
      (prefixQ S n J hr lambda K T m).value.rows c center.1) (MC.codeList row.val.val.1)
    (triangles.1,center.2+triangles.2+2)) (by
      intro g
      have ht := measurable_listAllQuery
        (fun c => fun T : NativeTable S n => triangleCodeQ S n J lambda
          (prefixQ S n J hr lambda K T m).value.rows c
          (centerQ S n J lambda K row.val.val.1 g).1)
        (fun c => measurable_native_triangle S n J hr lambda K m c _)
        (MC.codeList row.val.val.1)
      exact ht.fst.prodMk ((measurable_const.add ht.snd).add measurable_const))
    (gridListQuery K).1
  exact hq.fst.prodMk ((measurable_const.add hq.snd).add measurable_const)

private theorem scan_pair (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    scanQ S n J hr lambda K R =
      ((scanQuery (eventQueryQ S n J r lambda K) (universeQ S n J hr).1 R).1,
        (universeQ S n J hr).2+
          (scanQuery (eventQueryQ S n J r lambda K) (universeQ S n J hr).1 R).2+1) := by
  rfl

private theorem scanQuery_precompose {A W Ω : Type*}
    (q : A → W → Bool × ℕ) (f : Ω → W) (L : List A) (w : Ω) :
    scanQuery (fun a t => q a (f t)) L w=scanQuery q L (f w) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [scanQuery,ih]

private theorem measurable_scanQuery_precompose {A W Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace (Option A)]
    (q : A → W → Bool × ℕ) (f : Ω → W)
    (hq : ∀ a, Measurable (fun w => q a (f w))) (L : List A) :
    Measurable (fun w => scanQuery q L (f w)) := by
  have he : (fun w => scanQuery q L (f w))=
      scanQuery (fun a t => q a (f t)) L := by
    funext w
    exact (scanQuery_precompose q f L w).symm
  rw [he]
  exact measurable_scanQuery (fun a t => q a (f t)) hq L

private theorem measurable_native_scan (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) :
    Measurable (fun T : NativeTable S n => scanQ S n J hr lambda K
      (prefixQ S n J hr lambda K T m).value.rows) := by
  have hs := measurable_scanQuery_precompose
    (eventQueryQ S n J r lambda K)
    (fun T : NativeTable S n => (prefixQ S n J hr lambda K T m).value.rows)
    (fun row => measurable_native_event_query S n J hr lambda K m row)
    (universeQ S n J hr).1
  simp_rw [scan_pair]
  exact hs.fst.prodMk ((measurable_const.add hs.snd).add measurable_const)

private theorem measurable_native_prefix_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) :
    Measurable (fun T : NativeTable S n => (prefixQ S n J hr lambda K T m).operations) := by
  induction m with
  | zero =>
      have he : (fun T : NativeTable S n => (prefixQ S n J hr lambda K T 0).operations)=
          (fun _ => incomingBudget S n+1) := by
        funext T
        exact congrArg (fun k => k+1) (BDL26NativeStateRows.initialize_cost S n T).1
      rw [he]
      exact measurable_const
  | succ m ih =>
      have hs := measurable_native_scan S n J hr lambda K m
      have hf : Measurable (fun T : NativeTable S n =>
          (SR.refreshQ T (chosenSupport S n J r
            (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1)
            (prefixQ S n J hr lambda K T m).value.rows).operations) := by
        simp only [refresh_cost_labels,prefix_labels]
        exact (measurable_of_countable (fun e : Option (LiveRow S n J r) =>
          refreshLabelCost (chosenSupport S n J r e) (SR.indices (SR.count S n)))).comp hs.fst
      have ha : ∀ T : NativeTable S n,
          (BDL26NativeMasterCandidates.appendQ
            (prefixQ S n J hr lambda K T m).value.trace
            [(scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1]).operations=2*m+1 := by
        intro T
        rw [(BDL26NativeMasterCandidates.append_spec _ _).2.1,
          (prefix_lengths S n J hr lambda K T m).2]
      simp_rw [prefix_operations_succ,ha]
      have hm : Measurable (fun T : NativeTable S n =>
          (prefixQ S n J hr lambda K T m).operations+
            (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).2+
            (SR.refreshQ T (chosenSupport S n J r
              (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1)
              (prefixQ S n J hr lambda K T m).value.rows).operations+
            (2*m+1)+4) := by
        have hc : Measurable (fun _ : NativeTable S n => 2*m+1) := measurable_const
        have hd : Measurable (fun _ : NativeTable S n => (4 : ℕ)) := measurable_const
        convert ((((ih.add hs.snd).add hf).add hc).add hd) using 1 <;> rfl
      exact hm

private theorem measurable_native_clock (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) : Measurable (nativeHaltTime S n J hr lambda K) := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  have hm := (measurable_haltTime (X := fun _ : Vertex (Presentation S n) => Space)
    (U S n J r) (B S n J r lambda K) (measurableSet_keyBad _ _ _ _ _ _ _)).comp hd
  convert hm using 1
  funext T
  have h := haltTime_original S n J hr lambda K (decodedTable S n T)
  change nativeHaltTime S n J hr lambda K T=
    haltTime (X := fun _ : Vertex (Presentation S n) => Space)
      (U S n J r) (B S n J r lambda K) (decodedTable S n T)
  simpa only [encoded_decoded] using h

private theorem measurableSet_native_halts (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) :
    MeasurableSet {T : NativeTable S n | NativeHalts S n J hr lambda K T} := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  convert (measurableSet_halts (X := fun _ : Vertex (Presentation S n) => Space)
    (U S n J r) (B S n J r lambda K) (measurableSet_keyBad _ _ _ _ _ _ _)).preimage hd using 1
  ext T
  have h := halts_original S n J hr lambda K (decodedTable S n T)
  change NativeHalts S n J hr lambda K T ↔
    Halts (X := fun _ : Vertex (Presentation S n) => Space)
      (U S n J r) (B S n J r lambda K) (decodedTable S n T)
  simpa only [encoded_decoded] using h

/-- Actual arithmetic branch costs, selected refreshes and generated append costs
are measurable before stopping at the original measurable first-no-event clock. -/
theorem measurable_nativeOperationCost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) : Measurable (nativeOperationCost S n J hr lambda K) := by
  classical
  have hp : Measurable (fun z : NativeTable S n × ℕ =>
      (prefixQ S n J hr lambda K z.1 z.2).operations) :=
    measurable_from_prod_countable_left (fun m => measurable_native_prefix_cost S n J hr lambda K m)
  have hs : Measurable (fun z : NativeTable S n × ℕ =>
      (scanQ S n J hr lambda K (prefixQ S n J hr lambda K z.1 z.2).value.rows).2) :=
    measurable_from_prod_countable_left (fun m => (measurable_native_scan S n J hr lambda K m).snd)
  have ht := measurable_id.prodMk (measurable_native_clock S n J hr lambda K)
  have hc : Measurable (fun T : NativeTable S n =>
      (((prefixQ S n J hr lambda K T (nativeHaltTime S n J hr lambda K T)).operations+
        (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T
          (nativeHaltTime S n J hr lambda K T)).value.rows).2+5*SR.count S n+3 : ℕ) : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      ((((hp.comp ht).add (hs.comp ht)).add measurable_const).add measurable_const)
  convert Measurable.ite (measurableSet_native_halts S n J hr lambda K) hc
    (measurable_const : Measurable (fun _ : NativeTable S n => (∞ : ℝ≥0∞))) using 1
  funext T
  by_cases h : NativeHalts S n J hr lambda K T
  · simp only [nativeOperationCost,if_pos h,
      (native_stopping_refinement S n J hr lambda K T h).2]
  · simp only [nativeOperationCost,if_neg h]
  exact fun T => Classical.propDecidable (NativeHalts S n J hr lambda K T)

/-- The emitter materializes every original vertex value in native address
order; the generated trace and every original counter are retained as well. -/
theorem native_stopping_original (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : OriginalTable S n)
    (h : NativeHalts S n J hr lambda K (SR.encodeSamples S n T)) :
    let m := nativeHaltTime S n J hr lambda K (SR.encodeSamples S n T)
    let stopped := (stopQ S n J hr lambda K (SR.encodeSamples S n T) (m+1)).value
    stopped.emitted=some ((SR.indices (SR.count S n)).map (fun a =>
      (a,returned S n J hr lambda K (SR.encodeSamples S n T) (SR.decode S n a)))) ∧
    stopped.state.trace.map (Option.map (event S n J r))=originalTrace S n J r lambda K T m ∧
    ∀ v : Vertex (Presentation S n),
      (SR.readQ ((SR.decode S n).symm v) stopped.state.rows).value=
        (counters (X := fun _ : Vertex (Presentation S n) => Space)
            (U S n J r) (B S n J r lambda K) T m v,
          returned S n J hr lambda K (SR.encodeSamples S n T) v) := by
  dsimp only
  rw [(native_stopping_refinement S n J hr lambda K (SR.encodeSamples S n T) h).1]
  dsimp only
  refine ⟨?_,prefix_trace S n J hr lambda K T _,?_⟩
  · congr 1
    rw [prefix_rows,BDL26NativeStateRows.emit_value]
    apply List.map_congr_left
    intro a ha
    refine Prod.ext (by rfl) ?_
    have hp := prefix_assignment S n J hr lambda K T
      (nativeHaltTime S n J hr lambda K (SR.encodeSamples S n T))
    change T (SR.decode S n a,_)=_
    change _=originalPoints S n (prefixQ S n J hr lambda K
      (SR.encodeSamples S n T) (nativeHaltTime S n J hr lambda K
        (SR.encodeSamples S n T))).value.rows (SR.decode S n a)
    rw [hp]
    rfl
  · intro v
    rw [prefix_read]
    refine Prod.ext (by rfl) ?_
    have hp := prefix_assignment S n J hr lambda K T
      (nativeHaltTime S n J hr lambda K (SR.encodeSamples S n T))
    exact (congrFun hp v).symm

/-- Exceptional nontermination keeps the original output default, with infinite
paid execution cost rather than the zero mathematical default clock. -/
theorem native_nontermination_cost_default (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : OriginalTable S n)
    (h : ¬NativeHalts S n J hr lambda K (SR.encodeSamples S n T)) :
    nativeOperationCost S n J hr lambda K (SR.encodeSamples S n T)=∞ ∧
    returned S n J hr lambda K (SR.encodeSamples S n T)=(fun v => T (v,0)) := by
  exact ⟨by simp only [nativeOperationCost,if_neg h],
    (nonhalting_default S n J hr lambda K T h).2.1⟩

private theorem native_first_moment (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ T, nativeTotalSteps S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p) ≤
        (Fintype.card (Triangle (Presentation S n))^4 : ℕ) := by
  apply (native_expected_steps S n J p hJ).1.trans
  have hw : lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)) ≤ 1 := by
    simpa only [resamplingBudget] using
      (lll_resampling_budget_le_one (I := Unit) (dependencyBound p.M) ())
  calc
    _ ≤ ENNReal.ofReal ((Fintype.card (Triangle (Presentation S n)) : ℝ)^4*1) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw (by positivity))
    _ = _ := by simp

/-- Explicit finite scalar expected cost, with both actual resampling moments. -/
def expectedOperationBudget (S : OddScale) (n K D : ℕ) : ℕ :=
  operationConstantTerm S n K+
    operationLinearTerm S n K*(Fintype.card (Triangle (Presentation S n)))^4+
    2*(Fintype.card (Triangle (Presentation S n)))^8*(D+2)^2

/-- Expected TOTAL paid operations for the unchanged native master-row process.
Halting, product law, first and strict second moments are all derived internally. -/
theorem native_expected_operations (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ T, nativeOperationCost S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p) ≤
        (expectedOperationBudget S n ((6*p.m+2)*p.lambda) (dependencyBound p.M) : ℕ) := by
  let K := (6*p.m+2)*p.lambda
  let A := operationConstantTerm S n K
  let C := operationLinearTerm S n K
  let steps := nativeTotalSteps S n J (radius_nonneg p) p.lambda K
  let μ := nativeTableMeasure S n p
  letI (a : SR.Index S n) := vertexLaw_probability (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 (SR.decode S n a)
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (tableLaw (fun a : SR.Index S n =>
      vertexLaw (Presentation S n) ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m) (SR.decode S n a)))
    infer_instance
  have hm : Measurable steps := by
    rw [show steps=totalSteps (X := fun _ : Vertex (Presentation S n) => Space)
      (U S n J (anchorRadius p.m))
      (B S n J (anchorRadius p.m) p.lambda K) ∘ decodedTable S n from
        native_steps_decoded S n J (radius_nonneg p) p.lambda K]
    exact (measurable_totalSteps (X := fun _ : Vertex (Presentation S n) => Space)
      _ _ (measurableSet_keyBad _ _ _ _ _ _ _)).comp
        (Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n))
  have hfirst := native_first_moment S n J p hJ
  have hsecond := native_expected_steps_sq S n J p hJ
  calc
    _ ≤ ∫⁻ T, (A : ℝ≥0∞)+(C : ℝ≥0∞)*steps T+(steps T)^2 ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [native_halts_ae S n J p hJ] with T hT
      exact operation_quadratic_envelope S n J (radius_nonneg p) p.lambda K T hT
    _ = (A : ℝ≥0∞)+(C : ℝ≥0∞)*(∫⁻ T, steps T ∂μ)+
        (∫⁻ T, (steps T)^2 ∂μ) := by
      have hconst : Measurable (fun _ : NativeTable S n => (A : ℝ≥0∞)) := measurable_const
      have hmul : Measurable (fun T : NativeTable S n => (C : ℝ≥0∞)*steps T) :=
        (measurable_const : Measurable (fun _ : NativeTable S n => (C : ℝ≥0∞))).mul hm
      have hadd : Measurable (fun T : NativeTable S n => (A : ℝ≥0∞)+(C : ℝ≥0∞)*steps T) :=
        hconst.add hmul
      rw [lintegral_add_left hadd,lintegral_add_left hconst,
        lintegral_const_mul' (μ := μ) (C : ℝ≥0∞) steps (by simp)]
      simp
    _ ≤ (A : ℝ≥0∞)+(C : ℝ≥0∞)*(Fintype.card (Triangle (Presentation S n))^4 : ℕ)+
        (2*(Fintype.card (Triangle (Presentation S n)))^8*(dependencyBound p.M+2)^2 : ℕ) :=
      add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hfirst)) hsecond
    _ = _ := by
      dsimp only [A,C,expectedOperationBudget]
      push_cast
      rfl

/-- Finite expected operations imply integrability of this actual cost's real
value; nontermination remains infinite in the underlying extended cost. -/
theorem native_operation_cost_integrable (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    Integrable (fun T => (nativeOperationCost S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T).toReal) (nativeTableMeasure S n p) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact (measurable_nativeOperationCost S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda)).aemeasurable
  · exact ne_of_lt ((native_expected_operations S n J p hJ).trans_lt (by simp))

/-- A fixed exponent, independent of scale, depth, geometry and random table. -/
def nativeOperationDegree : ℕ := 1772

/-- This finite natural coefficient depends only on the jointly fixed grid and
strict dependency parameters. Its large exponent retains the existing complete
native presentation generator, including all dense tables. -/
def nativeOperationCoefficient (K D : ℕ) : ℕ :=
  (scanPolynomialConstant K+28)*132^1768+
    (scanPolynomialConstant K+39)*132^1768*65^4+2*65^8*(D+2)^2

private theorem weighted_power_product (a b c r u v : ℕ) :
    (a*(b*r^u))*(c*r^v)=(a*b*c)*r^(u+v) := by
  rw [pow_add]
  ac_rfl

private theorem weighted_product_swap (a b c d : ℕ) :
    a*(b*c)*d=(a*b*d)*c := by
  ac_rfl

private theorem weighted_mul_mono (a b c d : ℕ) (h : c ≤ d) :
    a*(b*c) ≤ (a*b)*d := by
  calc
    a*(b*c) = (a*b)*c := (Nat.mul_assoc a b c).symm
    _ ≤ (a*b)*d := Nat.mul_le_mul_left (a*b) h

private theorem expected_budget_qubit_polynomial (S : OddScale) (n K D : ℕ) :
    expectedOperationBudget S n K D ≤ nativeOperationCoefficient K D*
      (Fintype.card (Presentation S n).Q+1)^nativeOperationDegree := by
  let q := Fintype.card (Presentation S n).Q
  let r := q+1
  let x := qubitRadius S n
  let C := scanPolynomialConstant K
  have hr : 1 ≤ r := by dsimp only [r]; omega
  have hx : 1 ≤ x := by
    change 1 ≤ (132*r)^221
    exact one_le_pow₀ (by omega)
  have hx2 : x^2 ≤ x^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hx1 : x ≤ x^8 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 0 < x by omega) (show 1 ≤ 8 by decide))
  have hx0 : 1 ≤ x^8 := by
    simpa only [pow_zero] using
      (Nat.pow_le_pow_right (show 0 < x by omega) (show 0 ≤ 8 by decide))
  have hb := native_scalar_budgets_qubit S n K
  change incomingBudget S n ≤ 19*x^2 ∧
    scanBudget S n K (SR.count S n) ≤ C*x^8 ∧ SR.count S n ≤ x at hb
  have hA : operationConstantTerm S n K ≤ (C+28)*x^8 := by
    dsimp only [operationConstantTerm]
    nlinarith [hb.1,hb.2.1,hb.2.2]
  have hB : operationLinearTerm S n K ≤ (C+39)*x^8 := by
    dsimp only [operationLinearTerm]
    nlinarith [hb.2.1,hb.2.2]
  have hsize := operation_input_size_le_qubits (Presentation S n)
    (BDL26DecodingGraph.state S n).admissible.toTannerSquareAdmissible
    (state_boundedValence S n)
  have hT : Fintype.card (Triangle (Presentation S n)) ≤ 65*r := by
    dsimp only [r,q]
    omega
  have hX : x^8=132^1768*r^1768 := by
    change ((132*r)^221)^8=132^1768*r^1768
    rw [←pow_mul,mul_pow]
  have hp1768 : r^1768 ≤ r^1772 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp8 : r^8 ≤ r^1772 := Nat.pow_le_pow_right (by omega) (by decide)
  have hA' : operationConstantTerm S n K ≤
      ((C+28)*132^1768)*r^1772 := by
    apply hA.trans
    rw [hX]
    exact weighted_mul_mono (C+28) (132^1768) (r^1768) (r^1772) hp1768
  have hB' : operationLinearTerm S n K*(Fintype.card (Triangle (Presentation S n)))^4 ≤
      ((C+39)*132^1768*65^4)*r^1772 := by
    calc
      _ ≤ ((C+39)*x^8)*(65*r)^4 := Nat.mul_le_mul hB (Nat.pow_le_pow_left hT 4)
      _ = _ := by
        rw [hX,mul_pow]
        exact weighted_power_product (C+39) (132^1768) (65^4) r 1768 4
  have hM : 2*(Fintype.card (Triangle (Presentation S n)))^8*(D+2)^2 ≤
      (2*65^8*(D+2)^2)*r^1772 := by
    calc
      _ ≤ 2*(65*r)^8*(D+2)^2 := by gcongr
      _ = (2*65^8*(D+2)^2)*r^8 := by
        rw [mul_pow]
        exact weighted_product_swap 2 (65^8) (r^8) ((D+2)^2)
      _ ≤ _ := Nat.mul_le_mul_left _ hp8
  calc
    _ ≤ ((C+28)*132^1768)*r^1772+
        ((C+39)*132^1768*65^4)*r^1772+(2*65^8*(D+2)^2)*r^1772 :=
      Nat.add_le_add (Nat.add_le_add hA' hB') hM
    _ = _ := by
      rw [←add_mul,←add_mul]
      rfl

/-- Finite expected TOTAL paid native primitive operations in actual qubits.
The coefficient depends only on p; S, n, J and the random table do not occur in
it. This remains an internal single-perturbation theorem, not recursive output
independence or the public recursive embedding bound. -/
theorem native_expected_operations_qubits (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ T, nativeOperationCost S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p) ≤
        (nativeOperationCoefficient ((6*p.m+2)*p.lambda) (dependencyBound p.M)*
          (Fintype.card (Presentation S n).Q+1)^nativeOperationDegree : ℕ) :=
  (native_expected_operations S n J p hJ).trans
    ((Nat.cast_le (α := ℝ≥0∞)).mpr (expected_budget_qubit_polynomial S n _ _))

end QEC.Coding.BDL26NativeGeometricExecutionCost
