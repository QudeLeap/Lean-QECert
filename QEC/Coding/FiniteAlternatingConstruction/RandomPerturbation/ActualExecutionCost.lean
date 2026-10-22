import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.StateEventQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventPreprocessingCost

/-! # Actual finite-row execution and its counted operation cost

The state is a stored finite list of counter/sample rows. Every lookup and refresh
traversal is charged by its current input length. This length is invariant at
every finite prefix, so no bound on a second resampling-time moment is needed.
Exact real arithmetic/comparison and a fresh continuous cap draw are the primitive
model; no finite-bit complexity claim is made.
-/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

noncomputable def actualScanQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r)) (R : StateRows P) : Option (Event P J r) × ℕ :=
  scanQuery (fun e R => stateEventQuery P J r lambda K e R) events R

noncomputable def actualStepQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) : StateRows P × ℕ :=
  let scan := actualScanQuery P J r lambda K events R
  match scan.1 with
  | none => (R,scan.2)
  | some e => let update := refreshStateRowsQuery P J r e T R
              (update.1,scan.2+update.2)

noncomputable def actualPrefixQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r))
    (T : Table (X := fun _ : Vertex P => Space)) : ℕ → StateRows P × ℕ
  | 0 => initialRowsQuery P T
  | n+1 => let priorRun := actualPrefixQuery P J r lambda K events T n
           let next := actualStepQuery P J r lambda K events T priorRun.1
           (next.1,priorRun.2+next.2)

theorem actualScanQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P)) (R : StateRows P)
    (hR : StateRowsRep P T c R) :
    (actualScanQuery P J r lambda K (eventUniverseQuery P J hr).1 R).1 =
      select (localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K)) (assignment T c) := by
  let q := fun e R => stateEventQuery P J r lambda K e R
  let B := fun e => {R : StateRows P | statePoints R ∈ localEvent
    (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K) e}
  letI : ∀ e : Event P J r, DecidablePred (· ∈ B e) := fun e R =>
    if h : (q e R).1 = true then isTrue ((stateEventQuery_correct P J r lambda K e R).mp h)
    else isFalse (fun hb => h ((stateEventQuery_correct P J r lambda K e R).mpr hb))
  have hs := scanQuery_value q B (stateEventQuery_correct P J r lambda K)
    (eventUniverseQuery P J hr).1 R
  have hp (L : List (Event P J r)) : firstBadFrom B L R =
      firstBadFrom (localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r lambda K)) L (assignment T c) := by
    induction L with
    | nil => rfl
    | cons e L ih =>
      have hb : R ∈ B e ↔ assignment T c ∈ localEvent (X := fun _ : Vertex P => Space)
          (eventSupport P J r) (eventBad P J r lambda K) e := by
        change statePoints R ∈ localEvent (X := fun _ : Vertex P => Space)
            (eventSupport P J r) (eventBad P J r lambda K) e ↔
          assignment T c ∈ localEvent (X := fun _ : Vertex P => Space)
            (eventSupport P J r) (eventBad P J r lambda K) e
        rw [StateRowsRep_points P T c R hR]
      by_cases h : R ∈ B e
      · simp only [firstBadFrom,if_pos h,if_pos (hb.mp h)]
      · have hn : assignment T c ∉ localEvent (X := fun _ : Vertex P => Space)
            (eventSupport P J r) (eventBad P J r lambda K) e := fun ht => h (hb.mpr ht)
        simp only [firstBadFrom,if_neg h,if_neg hn,ih]
  rw [actualScanQuery]
  exact hs.trans ((hp _).trans (by rw [eventUniverseQuery_value]; rfl))

theorem actualStepQuery_rep (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P)) (R : StateRows P)
    (hR : StateRowsRep P T c R) :
    StateRowsRep P T (step (eventSupport P J r) (eventBad P J r lambda K) T c)
      (actualStepQuery P J r lambda K (eventUniverseQuery P J hr).1 T R).1 := by
  have hs := actualScanQuery_value P J hr lambda K T c R hR
  have hcore : step (eventSupport P J r) (eventBad P J r lambda K) T c =
      (match select (localEvent (X := fun _ : Vertex P => Space)
          (eventSupport P J r) (eventBad P J r lambda K)) (assignment T c) with
       | none => c
       | some e => advance (eventSupport P J r) e c) := by
    have hd :
        (decidableLocalEvents (X := fun _ : Vertex P => Space)
          (eventSupport P J r) (eventBad P J r lambda K) :
          ∀ e : Event P J r, DecidablePred (· ∈ localEvent
            (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K) e)) =
        geometricGlobalBadDecidable P J r lambda K := Subsingleton.elim _ _
    unfold step select
    rw [hd]
    cases hchoice : select (localEvent (X := fun _ : Vertex P => Space)
      (eventSupport P J r) (eventBad P J r lambda K)) (assignment T c) <;>
      simp only [select] at hchoice <;> simp only [hchoice]
  cases he : select (localEvent (X := fun _ : Vertex P => Space)
      (eventSupport P J r) (eventBad P J r lambda K)) (assignment T c) with
  | none =>
    rw [hcore,he]
    simp only [actualStepQuery,hs,he]
    exact hR
  | some e =>
    rw [hcore,he]
    simp only [actualStepQuery,hs,he]
    exact refreshStateRowsQuery_rep P J r e T c R hR

/-- The exact stored counter and sample address agree with core1447 at every finite prefix. -/
theorem actualPrefixQuery_rep (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    StateRowsRep P T (counters (eventSupport P J r) (eventBad P J r lambda K) T n)
      (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T n).1 := by
  induction n with
  | zero => exact initialRowsQuery_rep P T
  | succ n ih =>
    simpa only [actualPrefixQuery,counters] using actualStepQuery_rep P J hr lambda K T _ _ ih

theorem actualPrefixQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    statePoints (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T n).1 =
      assignment T (counters (eventSupport P J r) (eventBad P J r lambda K) T n) :=
  StateRowsRep_points P T _ _ (actualPrefixQuery_rep P J hr lambda K T n)

theorem actualScanQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r)) (R : StateRows P) :
    (actualScanQuery P J r lambda K events R).2 ≤
      events.length*(stateQueryBudget (Fintype.card (Triangle P)) R.length K+1) := by
  induction events with
  | nil => simp [actualScanQuery,scanQuery]
  | cons e events ih =>
    have hq := stateEventQuery_cost_le P J r lambda K e R
    simp only [actualScanQuery] at ih
    simp only [actualScanQuery,scanQuery,List.length_cons]
    split_ifs <;> nlinarith

theorem actualStepQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) :
    (actualStepQuery P J r lambda K events T R).2 ≤
      events.length*(stateQueryBudget (Fintype.card (Triangle P)) R.length K+1)+378+32*R.length := by
  have hs := actualScanQuery_cost_le P J r lambda K events R
  cases hscan : (actualScanQuery P J r lambda K events R).1 with
  | none =>
    simp only [actualStepQuery,hscan]
    omega
  | some e =>
    have hu := refreshStateRowsQuery_cost_le P J r e T R
    simp only [actualStepQuery,hscan]
    omega

theorem actualPrefixQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T n).2 ≤ 5*Fintype.card (Vertex P)+
      n*((eventUniverseQuery P J hr).1.length*(stateQueryBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P)) K+1)+378+32*Fintype.card (Vertex P)) := by
  induction n with
  | zero => simpa only [actualPrefixQuery,Nat.zero_mul,Nat.add_zero] using initialRowsQuery_cost_le P T
  | succ n ih =>
    have hn := actualStepQuery_cost_le P J r lambda K (eventUniverseQuery P J hr).1 T
      (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T n).1
    have hlen := StateRowsRep_length P T _ _ (actualPrefixQuery_rep P J hr lambda K T n)
    rw [hlen] at hn
    dsimp only [actualPrefixQuery]
    nlinarith

open scoped Classical in
noncomputable def actualExecutionCost (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) : ℝ≥0∞ :=
  if Halts (eventSupport P J r) (eventBad P J r lambda K) T then
    let eventRows := eventUniverseQuery P J hr
    let priorRun := actualPrefixQuery P J r lambda K eventRows.1 T
      (haltTime (eventSupport P J r) (eventBad P J r lambda K) T)
    let finalScan := actualScanQuery P J r lambda K eventRows.1 priorRun.1
    let result := outputStateRowsQuery P J lambda priorRun.1
    (eventRows.2+priorRun.2+finalScan.2+result.2 : ℕ)
  else ∞

/-- This bound is derived from the counted program, not stored as an execution field. -/
theorem actualExecutionCost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space))
    (hT : Halts (eventSupport P J r) (eventBad P J r lambda K) T) :
    actualExecutionCost P J hr lambda K T ≤
      (eventUniverseBudget (Fintype.card (Triangle P))+54*Fintype.card (Vertex P)+
        Fintype.card (Triangle P)^4*(stateQueryBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P)) K+1) : ℕ)+
      ((Fintype.card (Triangle P)^4*(stateQueryBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P)) K+1)+378+32*Fintype.card (Vertex P) : ℕ) : ℝ≥0∞)*
        totalSteps (eventSupport P J r) (eventBad P J r lambda K) T := by
  let N := haltTime (eventSupport P J r) (eventBad P J r lambda K) T
  have hp := actualPrefixQuery_cost_le P J hr lambda K T N
  have hlen := StateRowsRep_length P T _ _ (actualPrefixQuery_rep P J hr lambda K T N)
  have hs := actualScanQuery_cost_le P J r lambda K (eventUniverseQuery P J hr).1
    (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T N).1
  rw [hlen] at hs
  have ho := outputStateRowsQuery_cost_le P J lambda
    (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T N).1
  rw [hlen] at ho
  have hu := eventUniverseQuery_cost_le P J hr
  have hl : (eventUniverseQuery P J hr).1.length ≤ Fintype.card (Triangle P)^4 := by
    rw [eventUniverseQuery_value,Finset.length_sort,Finset.card_univ]
    exact event_card_le P J r
  have hlen := Nat.mul_le_mul_right (stateQueryBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P)) K+1) hl
  rw [actualExecutionCost,if_pos hT,totalSteps_eq_haltTime _ _ T hT]
  dsimp only [N] at hp hs ho
  dsimp only
  norm_cast
  nlinarith [Nat.mul_le_mul_left (haltTime (eventSupport P J r) (eventBad P J r lambda K) T) hlen]

end QEC.Coding.BDL26RandomPerturbation
