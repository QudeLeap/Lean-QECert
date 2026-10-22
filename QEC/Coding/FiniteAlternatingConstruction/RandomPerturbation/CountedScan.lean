import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Execution
import QEC.Coding.ProbabilisticConstruction.Resampling.Cost

/-! # Counted first-failed scans consume the actual finite geometric query -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

/-- Stop exactly at the first true counted predicate. The final clean scan is included. -/
def scanQuery {I Ω : Type*} (q : I → Ω → Bool × ℕ) : List I → Ω → Option I × ℕ
  | [], _ => (none,0)
  | i::L, ω => let qi := q i ω
               if qi.1 then (some i,qi.2+1) else
                 let tail := scanQuery q L ω
                 (tail.1,qi.2+tail.2+1)

theorem scanQuery_value {I Ω : Type*} (q : I → Ω → Bool × ℕ)
    (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
    (h : ∀ i ω, (q i ω).1 = true ↔ ω ∈ B i) (L : List I) (ω : Ω) :
    (scanQuery q L ω).1 = firstBadFrom B L ω := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    by_cases hi : ω ∈ B i
    · have hq := (h i ω).mpr hi
      simp [scanQuery,firstBadFrom,hi,hq]
    · have hq : (q i ω).1 = false := Bool.eq_false_iff.mpr (fun ht => hi ((h i ω).mp ht))
      simp [scanQuery,firstBadFrom,hi,hq,ih]

theorem scanQuery_cost_le {I Ω : Type*} (q : I → Ω → Bool × ℕ)
    (C : ℕ) (h : ∀ i ω, (q i ω).2 ≤ C) (L : List I) (ω : Ω) :
    (scanQuery q L ω).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [scanQuery]
  | cons i L ih =>
    have hi := h i ω
    simp only [scanQuery,List.length_cons]
    split_ifs <;> nlinarith

noncomputable def geometricGlobalQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (p : Vertex P → Space) : Bool × ℕ :=
  fullEventQuery P J r lambda K e (fun v => p v.val)

theorem geometricGlobalQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (p : Vertex P → Space) :
    (geometricGlobalQuery P J r lambda K e p).1 = true ↔
      p ∈ localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K) e :=
  fullEventQuery_correct P J r lambda K e _

noncomputable instance geometricGlobalBadDecidable (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ) :
    ∀ e : Event P J r, DecidablePred (· ∈ localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K) e) :=
  fun e p => if h : (geometricGlobalQuery P J r lambda K e p).1 = true then
    isTrue ((geometricGlobalQuery_correct P J r lambda K e p).mp h)
  else isFalse (fun hp => h ((geometricGlobalQuery_correct P J r lambda K e p).mpr hp))

theorem geometric_scan_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (p : Vertex P → Space) :
    (scanQuery (geometricGlobalQuery P J r lambda K)
      ((Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r)) p).1 =
      select (localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K)) p :=
  scanQuery_value _ _ (geometricGlobalQuery_correct P J r lambda K) _ p

theorem geometric_scan_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (p : Vertex P → Space) :
    (scanQuery (geometricGlobalQuery P J r lambda K)
      ((Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r)) p).2 ≤
      Fintype.card (Event P J r)*(fullQueryBudget (Fintype.card (Triangle P)) K+1) := by
  have h := scanQuery_cost_le (geometricGlobalQuery P J r lambda K)
    (fullQueryBudget (Fintype.card (Triangle P)) K)
    (fun e p => fullEventQuery_cost_le P J r lambda K e _) ((Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r)) p
  simpa only [Finset.length_sort,Finset.card_univ] using h

end QEC.Coding.BDL26RandomPerturbation
