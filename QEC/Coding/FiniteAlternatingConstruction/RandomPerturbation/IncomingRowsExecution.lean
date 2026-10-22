import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperimentCost
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountableExperimentGeometry

/-!
# The original perturbation execution with paid incoming coordinate rows

Every old-coordinate read scans the supplied finite row data. Original input
ranks, event priority, fresh-table addresses and finite histories are retained.
The underlying noncomputable rank-list generation, constructor/incidence
representation, incoming-cache construction and setup costs remain separate.
This is an internal exact-real primitive-cost result for [BDL26, Section 3,
random embedding construction and Theorem 1(1)], not a finite-bit runtime claim.
-/
noncomputable section
namespace QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

-- These original Main instances apply only to countable label lists.
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton

/-- Representation in the original fixed label order; this does not charge its construction. -/
def incomingRows (P : TannerSquarePresentation) (J : Vertex P → Space) : StateRows P :=
  (vertexInputList P).map (fun v => (v,0,J v))

@[simp] theorem incomingRows_labels (P : TannerSquarePresentation) (J : Vertex P → Space) :
    (incomingRows P J).map Prod.fst = vertexInputList P := by
  simp [incomingRows,List.map_map,Function.comp_def]

@[simp] theorem incomingRows_length (P : TannerSquarePresentation) (J : Vertex P → Space) :
    (incomingRows P J).length = Fintype.card (Vertex P) := by
  simp only [incomingRows,List.length_map,vertexInputList_length]

@[simp] theorem incomingRows_points (P : TannerSquarePresentation) (J : Vertex P → Space) :
    statePoints (incomingRows P J) = J := by
  funext v
  have hm : ∃ row ∈ incomingRows P J, row.1=v :=
    ⟨(v,0,J v),List.mem_map.mpr ⟨v,vertexInputList_complete P v,rfl⟩,rfl⟩
  have hv := stateRowQuery_value v (incomingRows P J) (0,J v) (by
    intro row hr he
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
    change u = v at he
    subst v
    rfl) hm
  exact congrArg Prod.snd hv

/-- Only the actual row scan supplies an incoming point; missing labels return zero. -/
def incomingRead (P : TannerSquarePresentation) (I : StateRows P) (v : Vertex P) : Space × ℕ :=
  let q := stateRowQuery v I
  (q.1.2,q.2)

@[simp] theorem incomingRead_value (P : TannerSquarePresentation) (I : StateRows P)
    (v : Vertex P) : (incomingRead P I v).1 = statePoints I v := rfl

theorem incomingRead_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (v : Vertex P) : (incomingRead P I v).2 ≤ 2*I.length := stateRowQuery_cost_le v I

@[simp] theorem incomingRead_empty (P : TannerSquarePresentation) (v : Vertex P) :
    incomingRead P [] v = (0,0) := rfl

@[simp] theorem incomingRead_head (P : TannerSquarePresentation) (v : Vertex P)
    (c : ℕ) (x : Space) (I : StateRows P) : incomingRead P ((v,c,x)::I) v = (x,2) := by
  simp [incomingRead,stateRowQuery]

/-- A derived conservative multiplier for at most three incoming vector scans. -/
def accessMultiplier {P : TannerSquarePresentation} (I : StateRows P) : ℕ := 6*I.length+1

theorem accessMultiplier_pos {P : TannerSquarePresentation} (I : StateRows P) :
    1 ≤ accessMultiplier I := by simp only [accessMultiplier]; omega

private theorem self_le_scale (d n : ℕ) (hd : 1 ≤ d) : n ≤ d*n := by
  have h := Nat.mul_le_mul_right n hd
  simpa only [Nat.one_mul] using h

private theorem extra_le_scale (m c e : ℕ) (hc : 1 ≤ c) (he : e ≤ 6*m) :
    c+e ≤ (6*m+1)*c := by
  have h := Nat.mul_le_mul_left (6*m) hc
  nlinarith

private def Sim {A : Type*} (d : ℕ) (x y : A × ℕ) : Prop :=
  x.1=y.1 ∧ x.2 ≤ d*y.2

private theorem map_sim {A B : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → B × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (mapQuery q' L) (mapQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [mapQuery]⟩
  | cons a L ih =>
      have ha := h a
      constructor
      · simp only [mapQuery,ha.1,ih.1]
      · dsimp only [mapQuery]
        nlinarith [ha.2,ih.2]

private theorem all_sim {A : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → Bool × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (listAllQuery q' L) (listAllQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [listAllQuery]⟩
  | cons a L ih =>
      have ha := h a
      constructor
      · simp only [listAllQuery,ha.1,ih.1]
      · dsimp only [listAllQuery]
        nlinarith [ha.2,ih.2]

private theorem any_sim {A : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → Bool × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (listAnyQuery q' L) (listAnyQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [listAnyQuery]⟩
  | cons a L ih =>
      have ha := h a
      constructor
      · simp only [listAnyQuery,ha.1,ih.1]
      · dsimp only [listAnyQuery]
        nlinarith [ha.2,ih.2]

private theorem filter_sim {A B : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → Option B × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (filterMapQuery q' L) (filterMapQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [filterMapQuery]⟩
  | cons a L ih =>
      have ha := h a
      constructor
      · simp only [filterMapQuery,ha.1,ih.1]
      · dsimp only [filterMapQuery]
        nlinarith [ha.2,ih.2]

private theorem scan_sim {A W : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → W → Bool × ℕ) (h : ∀ a w, Sim d (q' a w) (q a w))
    (L : List A) (w : W) : Sim d (scanQuery q' L w) (scanQuery q L w) := by
  induction L with
  | nil => exact ⟨rfl,by simp [scanQuery]⟩
  | cons a L ih =>
      have ha := h a w
      cases hv : (q a w).1 <;>
        simp only [Sim,scanQuery,ha.1,hv,Bool.false_eq_true,if_false,if_true]
      · exact ⟨ih.1,by nlinarith [ha.2,ih.2]⟩
      · exact ⟨True.intro,by nlinarith [ha.2]⟩

private theorem all_value_congr {A : Type*} (q q' : A → Bool × ℕ)
    (h : ∀ a, (q' a).1=(q a).1) (L : List A) :
    (listAllQuery q' L).1=(listAllQuery q L).1 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [listAllQuery,h,ih]

private theorem any_value_congr {A : Type*} (q q' : A → Bool × ℕ)
    (h : ∀ a, (q' a).1=(q a).1) (L : List A) :
    (listAnyQuery q' L).1=(listAnyQuery q L).1 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [listAnyQuery,h,ih]

private theorem map_cost_add {A B C : Type*} (q : A → B × ℕ) (q' : A → C × ℕ)
    (e : A → ℕ) (h : ∀ a, (q' a).2=(q a).2+e a) (L : List A) :
    (mapQuery q' L).2 = (mapQuery q L).2+(L.map e).sum := by
  induction L with
  | nil => simp [mapQuery]
  | cons a L ih => simp only [mapQuery,h,ih,List.map_cons,List.sum_cons]; omega

private theorem all_cost_add {A : Type*} (q q' : A → Bool × ℕ)
    (e : A → ℕ) (h : ∀ a, (q' a).2=(q a).2+e a) (L : List A) :
    (listAllQuery q' L).2 = (listAllQuery q L).2+(L.map e).sum := by
  induction L with
  | nil => simp [listAllQuery]
  | cons a L ih => simp only [listAllQuery,h,ih,List.map_cons,List.sum_cons]; omega

private theorem any_cost_add {A : Type*} (q q' : A → Bool × ℕ)
    (e : A → ℕ) (h : ∀ a, (q' a).2=(q a).2+e a) (L : List A) :
    (listAnyQuery q' L).2 = (listAnyQuery q L).2+(L.map e).sum := by
  induction L with
  | nil => simp [listAnyQuery]
  | cons a L ih => simp only [listAnyQuery,h,ih,List.map_cons,List.sum_cons]; omega

private theorem filter_cost_add {A B C : Type*} (q : A → Option B × ℕ)
    (q' : A → Option C × ℕ) (e : A → ℕ)
    (h : ∀ a, (q' a).2=(q a).2+e a) (L : List A) :
    (filterMapQuery q' L).2 = (filterMapQuery q L).2+(L.map e).sum := by
  induction L with
  | nil => simp [filterMapQuery]
  | cons a L ih => simp only [filterMapQuery,h,ih,List.map_cons,List.sum_cons]; omega

/-- Geometry eligibility reads both original X anchors from the supplied rows. -/
def rowAnchorCloseQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : Bool × ℕ :=
  let x := incomingRead P I (.x (P.faceX a.1))
  let y := incomingRead P I (.x (P.faceX b.1))
  let q := anchorCloseProgram.run (fun _ => y.1) x.1 r
  (q.1,q.2+x.2+y.2)

theorem rowAnchorCloseQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) :
    (rowAnchorCloseQuery P I r a b).1=(anchorCloseQuery P (statePoints I) r a b).1 := rfl

theorem rowAnchorCloseQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) :
    (rowAnchorCloseQuery P I r a b).2=(anchorCloseQuery P (statePoints I) r a b).2+
      (incomingRead P I (.x (P.faceX a.1))).2+(incomingRead P I (.x (P.faceX b.1))).2 := rfl

theorem rowAnchorCloseQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : (rowAnchorCloseQuery P I r a b).2 ≤
      accessMultiplier I*(anchorCloseQuery P (statePoints I) r a b).2 := by
  have hx := incomingRead_cost_le P I (.x (P.faceX a.1))
  have hy := incomingRead_cost_le P I (.x (P.faceX b.1))
  have hp : 1 ≤ (anchorCloseQuery P (statePoints I) r a b).2 := by
    dsimp only [anchorCloseQuery,anchorCloseProgram,RealTest.run]
    omega
  rw [rowAnchorCloseQuery_cost]
  have h := extra_le_scale I.length _
    ((incomingRead P I (.x (P.faceX a.1))).2+(incomingRead P I (.x (P.faceX b.1))).2)
    hp (by omega)
  simpa only [accessMultiplier,Nat.add_assoc] using h

def rowEligiblePairQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : Bool × ℕ :=
  let color := colorMatchQuery P a b
  let close := rowAnchorCloseQuery P I r a b
  (color.1 && close.1,color.2+close.2+1)

private theorem pair_sim (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : Sim (accessMultiplier I)
    (rowEligiblePairQuery P I r a b) (eligiblePairQuery P (statePoints I) r a b) := by
  have hc := rowAnchorCloseQuery_cost_le P I r a b
  have hs := self_le_scale (accessMultiplier I) (colorMatchQuery P a b).2 (accessMultiplier_pos I)
  have hd := accessMultiplier_pos I
  constructor
  · exact congrArg (fun flag => (colorMatchQuery P a b).1 && flag)
      (rowAnchorCloseQuery_value P I r a b)
  · dsimp only [rowEligiblePairQuery,eligiblePairQuery]
    nlinarith

theorem rowEligiblePairQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) :
    (rowEligiblePairQuery P I r a b).1=(eligiblePairQuery P (statePoints I) r a b).1 :=
  (pair_sim P I r a b).1

theorem rowEligiblePairQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : (rowEligiblePairQuery P I r a b).2 ≤
      accessMultiplier I*(eligiblePairQuery P (statePoints I) r a b).2 := (pair_sim P I r a b).2

def rowEligibleListQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (Finset (Triangle P) × Bool) × ℕ := by
  let unique := dedupQuery (triangleLabelEqQuery P) L
  let s : Finset (Triangle P) := ⟨↑unique.1,by
    rw [dedupQuery_value _ (triangleLabelEqQuery_correct P)]
    exact List.nodup_dedup L⟩
  let pairs := listAllQuery (fun a => listAllQuery (rowEligiblePairQuery P I r a) unique.1) unique.1
  exact ((s,decide (unique.1.length=4) && pairs.1),unique.2+pairs.2+unique.1.length+2)

private theorem eligible_sim (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : Sim (accessMultiplier I)
    (rowEligibleListQuery P I r L) (eligibleListQuery P (statePoints I) r L) := by
  let U := (dedupQuery (triangleLabelEqQuery P) L).1
  have hp := all_sim (accessMultiplier I) (accessMultiplier_pos I) _ _
    (fun a => all_sim (accessMultiplier I) (accessMultiplier_pos I) _ _ (pair_sim P I r a) U) U
  have hs := self_le_scale (accessMultiplier I)
    ((dedupQuery (triangleLabelEqQuery P) L).2+U.length+2) (accessMultiplier_pos I)
  constructor
  · dsimp only [rowEligibleListQuery,eligibleListQuery]
    rw [hp.1]
  · dsimp only [rowEligibleListQuery,eligibleListQuery]
    dsimp only [U] at hp hs
    nlinarith [hp.2]

theorem rowEligibleListQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) :
    (rowEligibleListQuery P I r L).1=(eligibleListQuery P (statePoints I) r L).1 :=
  (eligible_sim P I r L).1

theorem rowEligibleListQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (rowEligibleListQuery P I r L).2 ≤
      accessMultiplier I*(eligibleListQuery P (statePoints I) r L).2 := (eligible_sim P I r L).2

def rowCandidateQuery (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) : Option (Event P (statePoints I) r) × ℕ :=
  let q := rowEligibleListQuery P I r L
  if h : q.1.2=true then
    (some ⟨q.1.1,by
      rw [rowEligibleListQuery_value]
      exact (eligibleListQuery_correct P (statePoints I) hr L).mp
        (by simpa only [q,rowEligibleListQuery_value] using h)⟩,q.2+1)
  else (none,q.2+1)

private theorem candidate_sim (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) : Sim (accessMultiplier I)
    (rowCandidateQuery P I hr L) (candidateEventQuery P (statePoints I) hr L) := by
  have hv := rowEligibleListQuery_value P I r L
  have hc := rowEligibleListQuery_cost_le P I r L
  have hd := accessMultiplier_pos I
  constructor
  · simp only [rowCandidateQuery,candidateEventQuery,hv]
    split_ifs <;> rfl
  · dsimp only [rowCandidateQuery,candidateEventQuery]
    split_ifs <;> nlinarith

theorem rowCandidateQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) :
    (rowCandidateQuery P I hr L).1=(candidateEventQuery P (statePoints I) hr L).1 :=
  (candidate_sim P I hr L).1

theorem rowCandidateQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) : (rowCandidateQuery P I hr L).2 ≤
      accessMultiplier I*(candidateEventQuery P (statePoints I) hr L).2 := (candidate_sim P I hr L).2

def rowRawUniverseQuery (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : List (Event P (statePoints I) r) × ℕ :=
  let tuples := fourTuplesQuery (triangleInputList P)
  let events := filterMapQuery (rowCandidateQuery P I hr) tuples.1
  (events.1,tuples.2+events.2)

private theorem raw_sim (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : Sim (accessMultiplier I)
    (rowRawUniverseQuery P I hr) (rawEventUniverseQuery P (statePoints I) hr) := by
  have h := filter_sim (accessMultiplier I) (accessMultiplier_pos I) _ _
    (candidate_sim P I hr) (fourTuplesQuery (triangleInputList P)).1
  have hs := self_le_scale (accessMultiplier I) (fourTuplesQuery (triangleInputList P)).2
    (accessMultiplier_pos I)
  exact ⟨h.1,by dsimp only [rowRawUniverseQuery,rawEventUniverseQuery]; nlinarith [h.2]⟩

def rowUniverseQuery (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : List (Event P (statePoints I) r) × ℕ :=
  let raw := rowRawUniverseQuery P I hr
  let unique := dedupQuery (eventEqQuery P (statePoints I) r) raw.1
  let sorted := sortQuery (eventCompareQuery P (statePoints I) r) unique.1
  (sorted.1,raw.2+unique.2+sorted.2)

private theorem universe_sim (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : Sim (accessMultiplier I)
    (rowUniverseQuery P I hr) (eventUniverseQuery P (statePoints I) hr) := by
  have h := raw_sim P I hr
  have hs := self_le_scale (accessMultiplier I)
    ((dedupQuery (eventEqQuery P (statePoints I) r) (rawEventUniverseQuery P (statePoints I) hr).1).2+
      (sortQuery (eventCompareQuery P (statePoints I) r)
        (dedupQuery (eventEqQuery P (statePoints I) r) (rawEventUniverseQuery P (statePoints I) hr).1).1).2)
    (accessMultiplier_pos I)
  constructor
  · dsimp only [rowUniverseQuery,eventUniverseQuery]; rw [h.1]
  · dsimp only [rowUniverseQuery,eventUniverseQuery]; rw [h.1]; nlinarith [h.2]

theorem rowUniverseQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) :
    (rowUniverseQuery P I hr).1=(eventUniverseQuery P (statePoints I) hr).1 := (universe_sim P I hr).1

theorem rowUniverseQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : (rowUniverseQuery P I hr).2 ≤
      accessMultiplier I*(eventUniverseQuery P (statePoints I) hr).2 := (universe_sim P I hr).2

/-- At a missing anchor there is no incoming lookup, just the original zero branch. -/
def rowCenterQuery (P : TannerSquarePresentation) (I : StateRows P) (lambda : ℝ)
    (K : ℕ) (a : Option (Triangle P)) (g : Grid K) : Space × ℕ :=
  match a with
  | none => (0,1)
  | some t => let old := incomingRead P I (.x (P.faceX t.1))
              let grid := gridPointQuery K g
              let point := pointSnapshotQuery lambda old.1 grid.1
              (point.1,grid.2+point.2+2+old.2)

def centerExtra (P : TannerSquarePresentation) (I : StateRows P) : Option (Triangle P) → ℕ
  | none => 0
  | some t => (incomingRead P I (.x (P.faceX t.1))).2

theorem rowCenterQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (K : ℕ) (a : Option (Triangle P)) (g : Grid K) :
    (rowCenterQuery P I lambda K a g).1=(fullCenterQuery P (statePoints I) lambda K a g).1 := by
  cases a <;> rfl

theorem rowCenterQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (K : ℕ) (a : Option (Triangle P)) (g : Grid K) :
    (rowCenterQuery P I lambda K a g).2=(fullCenterQuery P (statePoints I) lambda K a g).2+
      centerExtra P I a := by cases a <;> rfl

theorem rowCenterQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (K : ℕ) (a : Option (Triangle P)) (g : Grid K) :
    (rowCenterQuery P I lambda K a g).2 ≤
      accessMultiplier I*(fullCenterQuery P (statePoints I) lambda K a g).2 := by
  cases a with
  | none => simpa only [rowCenterQuery,fullCenterQuery,Nat.mul_one] using accessMultiplier_pos I
  | some t =>
      rw [rowCenterQuery_cost]
      apply extra_le_scale I.length
      · dsimp only [fullCenterQuery]; omega
      · have h := incomingRead_cost_le P I (.x (P.faceX t.1)); exact h.trans (by omega)

def triangleExtra (P : TannerSquarePresentation) (I : StateRows P) (t : Triangle P) : ℕ :=
  (incomingRead P I (triangleVertex P t 0)).2+
  (incomingRead P I (triangleVertex P t 1)).2+
  (incomingRead P I (triangleVertex P t 2)).2

def rowTrianglePointsQuery (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) : (Fin 3 → Space) × ℕ :=
  let o0 := incomingRead P I (triangleVertex P t 0)
  let o1 := incomingRead P I (triangleVertex P t 1)
  let o2 := incomingRead P I (triangleVertex P t 2)
  let r0 := stateRowQuery (triangleVertex P t 0) R
  let r1 := stateRowQuery (triangleVertex P t 1) R
  let r2 := stateRowQuery (triangleVertex P t 2) R
  let q0 := pointSnapshotQuery lambda o0.1 r0.1.2
  let q1 := pointSnapshotQuery lambda o1.1 r1.1.2
  let q2 := pointSnapshotQuery lambda o2.1 r2.1.2
  (![q0.1,q1.1,q2.1],r0.2+r1.2+r2.2+q0.2+q1.2+q2.2+18+o0.2+o1.2+o2.2)

theorem rowTrianglePointsQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) :
    (rowTrianglePointsQuery P I lambda t R).1=
      (stateTrianglePointsQuery P (statePoints I) lambda t R).1 := rfl

theorem rowTrianglePointsQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) :
    (rowTrianglePointsQuery P I lambda t R).2=
      (stateTrianglePointsQuery P (statePoints I) lambda t R).2+triangleExtra P I t := by
  dsimp only [rowTrianglePointsQuery,stateTrianglePointsQuery,triangleExtra,incomingRead,statePoints]
  omega

theorem rowTrianglePointsQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) :
    (rowTrianglePointsQuery P I lambda t R).2 ≤
      accessMultiplier I*(stateTrianglePointsQuery P (statePoints I) lambda t R).2 := by
  rw [rowTrianglePointsQuery_cost]
  apply extra_le_scale I.length
  · dsimp only [stateTrianglePointsQuery]; omega
  · have h0 := incomingRead_cost_le P I (triangleVertex P t 0)
    have h1 := incomingRead_cost_le P I (triangleVertex P t 1)
    have h2 := incomingRead_cost_le P I (triangleVertex P t 2)
    dsimp only [triangleExtra]; omega

def rowTriangleQuery (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) : Bool × ℕ :=
  let points := rowTrianglePointsQuery P I lambda t R
  let query := triangleQuery points.1 z 2
  (query.1,points.2+query.2)

theorem rowTriangleQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) :
    (rowTriangleQuery P I lambda t R z).1=(stateTriangleQuery P (statePoints I) lambda t R z).1 := by
  simp only [rowTriangleQuery,stateTriangleQuery,rowTrianglePointsQuery_value]

theorem rowTriangleQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) :
    (rowTriangleQuery P I lambda t R z).2=(stateTriangleQuery P (statePoints I) lambda t R z).2+
      triangleExtra P I t := by
  simp only [rowTriangleQuery,stateTriangleQuery,rowTrianglePointsQuery_value,rowTrianglePointsQuery_cost]
  omega

theorem rowTriangleQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) :
    (rowTriangleQuery P I lambda t R z).2 ≤
      accessMultiplier I*(stateTriangleQuery P (statePoints I) lambda t R z).2 := by
  have hp := rowTrianglePointsQuery_cost_le P I lambda t R
  have hs := self_le_scale (accessMultiplier I)
    (triangleQuery (stateTrianglePointsQuery P (statePoints I) lambda t R).1 z 2).2
    (accessMultiplier_pos I)
  dsimp only [rowTriangleQuery,stateTriangleQuery]
  rw [rowTrianglePointsQuery_value]
  nlinarith

theorem rowRawUniverseQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) :
    (rowRawUniverseQuery P I hr).1=(rawEventUniverseQuery P (statePoints I) hr).1 := (raw_sim P I hr).1

theorem rowRawUniverseQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : (rowRawUniverseQuery P I hr).2 ≤
      accessMultiplier I*(rawEventUniverseQuery P (statePoints I) hr).2 := (raw_sim P I hr).2

def rowStateEventQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (e : Event P (statePoints I) r) (R : StateRows P) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := eventAnchorQuery P (statePoints I) r e
  let query := listAnyQuery (fun g : Grid K =>
    let center := rowCenterQuery P I lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      rowTriangleQuery P I lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) net.1
  (query.1,net.2+anchor.2+query.2+1)

private theorem event_sim (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (e : Event P (statePoints I) r) (R : StateRows P) :
    Sim (accessMultiplier I) (rowStateEventQuery P I r lambda K e R)
      (stateEventQuery P (statePoints I) r lambda K e R) := by
  let anchor := (eventAnchorQuery P (statePoints I) r e).1
  let old := fun g : Grid K =>
    let center := fullCenterQuery P (statePoints I) lambda K anchor g
    let triangles := listAllQuery (fun a : e.val =>
      stateTriangleQuery P (statePoints I) lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)
  let new := fun g : Grid K =>
    let center := rowCenterQuery P I lambda K anchor g
    let triangles := listAllQuery (fun a : e.val =>
      rowTriangleQuery P I lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)
  have hg (g : Grid K) : Sim (accessMultiplier I) (new g) (old g) := by
    have hc := rowCenterQuery_cost_le P I lambda K anchor g
    have ht := all_sim (accessMultiplier I) (accessMultiplier_pos I) _ _
      (fun a : e.val => ⟨rowTriangleQuery_value P I lambda a.val R
        (fullCenterQuery P (statePoints I) lambda K anchor g).1,
        rowTriangleQuery_cost_le P I lambda a.val R
          (fullCenterQuery P (statePoints I) lambda K anchor g).1⟩)
      (Finset.univ.toList : List e.val)
    dsimp only [new,old]
    rw [rowCenterQuery_value]
    exact ⟨ht.1,by nlinarith [ht.2,accessMultiplier_pos I]⟩
  have h := any_sim (accessMultiplier I) (accessMultiplier_pos I) old new hg (gridListQuery K).1
  have hs := self_le_scale (accessMultiplier I)
    ((gridListQuery K).2+(eventAnchorQuery P (statePoints I) r e).2+1) (accessMultiplier_pos I)
  exact ⟨h.1,by dsimp only [rowStateEventQuery,stateEventQuery]; nlinarith [h.2]⟩

theorem rowStateEventQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (e : Event P (statePoints I) r) (R : StateRows P) :
    (rowStateEventQuery P I r lambda K e R).1=(stateEventQuery P (statePoints I) r lambda K e R).1 :=
  (event_sim P I r lambda K e R).1

theorem rowStateEventQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (e : Event P (statePoints I) r) (R : StateRows P) :
    (rowStateEventQuery P I r lambda K e R).2 ≤
      accessMultiplier I*(stateEventQuery P (statePoints I) r lambda K e R).2 := (event_sim P I r lambda K e R).2

def rowScanQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (R : StateRows P) : Option (Event P (statePoints I) r) × ℕ :=
  scanQuery (rowStateEventQuery P I r lambda K) events R

private theorem row_scan_sim (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r)) (R : StateRows P) :
    Sim (accessMultiplier I) (rowScanQuery P I r lambda K events R)
      (actualScanQuery P (statePoints I) r lambda K events R) :=
  scan_sim _ (accessMultiplier_pos I) _ _ (event_sim P I r lambda K) events R

theorem rowScanQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r)) (R : StateRows P) :
    (rowScanQuery P I r lambda K events R).1=(actualScanQuery P (statePoints I) r lambda K events R).1 :=
  (row_scan_sim P I r lambda K events R).1

theorem rowScanQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r)) (R : StateRows P) :
    (rowScanQuery P I r lambda K events R).2 ≤
      accessMultiplier I*(actualScanQuery P (statePoints I) r lambda K events R).2 :=
  (row_scan_sim P I r lambda K events R).2

def rowStepQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) : StateRows P × ℕ :=
  let scan := rowScanQuery P I r lambda K events R
  match scan.1 with
  | none => (R,scan.2)
  | some e => let update := refreshStateRowsQuery P (statePoints I) r e T R
              (update.1,scan.2+update.2)

private theorem step_sim (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) :
    Sim (accessMultiplier I) (rowStepQuery P I r lambda K events T R)
      (actualStepQuery P (statePoints I) r lambda K events T R) := by
  have h := row_scan_sim P I r lambda K events R
  cases he : (actualScanQuery P (statePoints I) r lambda K events R).1 with
  | none =>
      simp only [Sim,rowStepQuery,actualStepQuery,h.1,he]
      exact ⟨True.intro,h.2⟩
  | some e =>
      have hu := self_le_scale (accessMultiplier I)
        (refreshStateRowsQuery P (statePoints I) r e T R).2 (accessMultiplier_pos I)
      simp only [Sim,rowStepQuery,actualStepQuery,h.1,he]
      exact ⟨True.intro,by nlinarith [h.2]⟩

theorem rowStepQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) :
    (rowStepQuery P I r lambda K events T R).1=(actualStepQuery P (statePoints I) r lambda K events T R).1 :=
  (step_sim P I r lambda K events T R).1

theorem rowStepQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) :
    (rowStepQuery P I r lambda K events T R).2 ≤
      accessMultiplier I*(actualStepQuery P (statePoints I) r lambda K events T R).2 :=
  (step_sim P I r lambda K events T R).2

def rowPrefixQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) : ℕ → StateRows P × ℕ
  | 0 => initialRowsQuery P T
  | s+1 => let prior := rowPrefixQuery P I r lambda K events T s
           let next := rowStepQuery P I r lambda K events T prior.1
           (next.1,prior.2+next.2)

private theorem prefix_sim (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (s : ℕ) :
    Sim (accessMultiplier I) (rowPrefixQuery P I r lambda K events T s)
      (actualPrefixQuery P (statePoints I) r lambda K events T s) := by
  induction s with
  | zero => exact ⟨rfl,self_le_scale _ _ (accessMultiplier_pos I)⟩
  | succ s ih =>
      have hn := step_sim P I r lambda K events T
        (actualPrefixQuery P (statePoints I) r lambda K events T s).1
      constructor
      · simp only [rowPrefixQuery,actualPrefixQuery,ih.1,hn.1]
      · dsimp only [rowPrefixQuery,actualPrefixQuery]
        rw [ih.1]
        nlinarith [ih.2,hn.2]

theorem rowPrefixQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (s : ℕ) :
    (rowPrefixQuery P I r lambda K events T s).1=
      (actualPrefixQuery P (statePoints I) r lambda K events T s).1 := (prefix_sim P I r lambda K events T s).1

theorem rowPrefixQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (s : ℕ) :
    (rowPrefixQuery P I r lambda K events T s).2 ≤
      accessMultiplier I*(actualPrefixQuery P (statePoints I) r lambda K events T s).2 :=
  (prefix_sim P I r lambda K events T s).2

/-- Counters and every retained fresh-table address are literally the old ones. -/
theorem rowPrefixQuery_rep (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (s : ℕ) :
    StateRowsRep P T (counters (eventSupport P (statePoints I) r)
      (eventBad P (statePoints I) r lambda K) T s)
      (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 T s).1 := by
  rw [rowUniverseQuery_value,rowPrefixQuery_value]
  exact actualPrefixQuery_rep P (statePoints I) hr lambda K T s

def rowOutputQuery (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (R : StateRows P) : List (Vertex P × Space) × ℕ :=
  mapQuery (fun row => let old := incomingRead P I row.1
                      let q := pointSnapshotQuery lambda old.1 row.2.2
                      ((row.1,q.1),q.2+3+old.2)) R

theorem rowOutputQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (R : StateRows P) :
    (rowOutputQuery P I lambda R).1=(outputStateRowsQuery P (statePoints I) lambda R).1 := by
  simp only [rowOutputQuery,outputStateRowsQuery,mapQuery_value,incomingRead_value]

theorem rowOutputQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (R : StateRows P) :
    (rowOutputQuery P I lambda R).2=(outputStateRowsQuery P (statePoints I) lambda R).2+
      (R.map (fun row => (incomingRead P I row.1).2)).sum :=
  map_cost_add _ _ _ (fun _ => rfl) R

theorem rowOutputQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (R : StateRows P) :
    (rowOutputQuery P I lambda R).2 ≤ accessMultiplier I*(outputStateRowsQuery P (statePoints I) lambda R).2 := by
  apply (map_sim (accessMultiplier I) (accessMultiplier_pos I) _ _ ?_ R).2
  intro row
  refine ⟨rfl,?_⟩
  have h := incomingRead_cost_le P I row.1
  exact extra_le_scale I.length _ _ (by omega) (by omega)

/-- The universe, finite run, final scan and emission are retained once. -/
def rowExecutionQuery (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) : List (Vertex P × Space) × ℝ≥0∞ :=
  let eventsRun := rowUniverseQuery P I hr
  let prior := rowPrefixQuery P I r lambda K eventsRun.1 T
    (haltTime (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T)
  let final := rowScanQuery P I r lambda K eventsRun.1 prior.1
  let out := rowOutputQuery P I lambda prior.1
  (out.1,if Halts (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T
    then ((eventsRun.2+prior.2+final.2+out.2 : ℕ) : ℝ≥0∞) else ∞)

def rowExecutionCost (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) : ℝ≥0∞ :=
  (rowExecutionQuery P I hr lambda K T).2

theorem rowExecutionQuery_rows (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) :
    (rowExecutionQuery P I hr lambda K T).1 =
      (outputStateRowsQuery P (statePoints I) lambda
        (actualPrefixQuery P (statePoints I) r lambda K (eventUniverseQuery P (statePoints I) hr).1 T
          (haltTime (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T)).1).1 := by
  simp only [rowExecutionQuery,rowUniverseQuery_value,rowPrefixQuery_value,rowOutputQuery_value]

theorem rowExecutionQuery_embedding_rows (P : TannerSquarePresentation) (I : StateRows P)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) :
    (rowExecutionQuery P I (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T).1 =
      (vertexInputList P).map (fun v => (v,perturbationEmbeddingOutput P (statePoints I) p T v)) := by
  rw [rowExecutionQuery_rows]
  exact actual_emitted_embedding_rows P (statePoints I) p T

theorem rowExecutionCost_nonhalting (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space))
    (h : ¬Halts (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T) :
    rowExecutionCost P I hr lambda K T=∞ := by
  simp only [rowExecutionCost,rowExecutionQuery,if_neg h]

theorem rowExecutionCost_finite_of_halts (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space))
    (h : Halts (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T) :
    rowExecutionCost P I hr lambda K T<∞ := by
  simp only [rowExecutionCost,rowExecutionQuery,if_pos h]
  simp

theorem rowExecutionCost_le (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) :
    rowExecutionCost P I hr lambda K T ≤
      (accessMultiplier I : ℝ≥0∞)*actualExecutionCost P (statePoints I) hr lambda K T := by
  by_cases h : Halts (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T
  · let s := haltTime (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T
    let events := (eventUniverseQuery P (statePoints I) hr).1
    let R := (actualPrefixQuery P (statePoints I) r lambda K events T s).1
    have hu := rowUniverseQuery_cost_le P I hr
    have hp := rowPrefixQuery_cost_le P I r lambda K events T s
    have hs := rowScanQuery_cost_le P I r lambda K events R
    have ho := rowOutputQuery_cost_le P I lambda R
    simp only [rowExecutionCost,rowExecutionQuery,actualExecutionCost,if_pos h,
      rowUniverseQuery_value,rowPrefixQuery_value]
    rw [← Nat.cast_mul]
    apply (Nat.cast_le (α := ℝ≥0∞)).mpr
    dsimp only [events,R,s] at hu hp hs ho
    nlinarith
  · rw [rowExecutionCost_nonhalting P I hr lambda K T h]
    simp only [actualExecutionCost,if_neg h]
    have hd : (accessMultiplier I : ℝ≥0∞)≠0 := by
      exact_mod_cast (Nat.ne_of_gt (accessMultiplier_pos I))
    simp [hd]

/-- Actual eligibility overhead depends only on the scanned incoming labels. -/
def pairExtra (P : TannerSquarePresentation) (I : StateRows P) (a b : Triangle P) : ℕ :=
  (incomingRead P I (.x (P.faceX a.1))).2+(incomingRead P I (.x (P.faceX b.1))).2

def eligibilityExtra (P : TannerSquarePresentation) (I : StateRows P) (L : List (Triangle P)) : ℕ :=
  let U := (dedupQuery (triangleLabelEqQuery P) L).1
  (U.map (fun a => (U.map (pairExtra P I a)).sum)).sum

private theorem eligible_pair_cost_add (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (a b : Triangle P) : (rowEligiblePairQuery P I r a b).2=
      (eligiblePairQuery P (statePoints I) r a b).2+pairExtra P I a b := by
  simp only [rowEligiblePairQuery,eligiblePairQuery,rowAnchorCloseQuery_cost,pairExtra]
  omega

theorem rowEligibleListQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (rowEligibleListQuery P I r L).2=
      (eligibleListQuery P (statePoints I) r L).2+eligibilityExtra P I L := by
  let U := (dedupQuery (triangleLabelEqQuery P) L).1
  have h := all_cost_add
    (fun a => listAllQuery (eligiblePairQuery P (statePoints I) r a) U)
    (fun a => listAllQuery (rowEligiblePairQuery P I r a) U)
    (fun a => (U.map (pairExtra P I a)).sum)
    (fun a => all_cost_add _ _ _ (eligible_pair_cost_add P I r a) U) U
  dsimp only [rowEligibleListQuery,eligibleListQuery,eligibilityExtra]
  dsimp only [U] at h
  omega

def universeExtra (P : TannerSquarePresentation) (I : StateRows P) : ℕ :=
  ((fourTuplesQuery (triangleInputList P)).1.map (eligibilityExtra P I)).sum

theorem rowRawUniverseQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : (rowRawUniverseQuery P I hr).2=
      (rawEventUniverseQuery P (statePoints I) hr).2+universeExtra P I := by
  have hc (L : List (Triangle P)) : (rowCandidateQuery P I hr L).2=
      (candidateEventQuery P (statePoints I) hr L).2+eligibilityExtra P I L := by
    dsimp only [rowCandidateQuery,candidateEventQuery]
    split_ifs <;>
      nlinarith [rowEligibleListQuery_cost P I r L]
  have h := filter_cost_add _ _ _ hc (fourTuplesQuery (triangleInputList P)).1
  dsimp only [rowRawUniverseQuery,rawEventUniverseQuery,universeExtra]
  omega

theorem rowUniverseQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : (rowUniverseQuery P I hr).2=
      (eventUniverseQuery P (statePoints I) hr).2+universeExtra P I := by
  dsimp only [rowUniverseQuery,eventUniverseQuery]
  rw [rowRawUniverseQuery_value,rowRawUniverseQuery_cost]
  omega

/-- Fixed-carrier candidate construction still filters before the scan. -/
def rowMasterCandidateQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : Option (MasterEvent P) × ℕ :=
  let q := rowEligibleListQuery P I r L
  if hc : L.toFinset.card=4 then
    (if q.1.2 then some ⟨L.toFinset,hc⟩ else none,q.2+1)
  else (none,q.2+1)

private theorem master_candidate_value (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (rowMasterCandidateQuery P I r L).1=
      (countedMasterCandidateQuery P (statePoints I) r L).1 := by
  simp only [rowMasterCandidateQuery,countedMasterCandidateQuery,rowEligibleListQuery_value]
  split_ifs <;> rfl

private theorem master_candidate_cost (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (rowMasterCandidateQuery P I r L).2=
      (countedMasterCandidateQuery P (statePoints I) r L).2+eligibilityExtra P I L := by
  dsimp only [rowMasterCandidateQuery,countedMasterCandidateQuery]
  split_ifs <;> nlinarith [rowEligibleListQuery_cost P I r L]

def rowMasterUniverseQuery (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) : List (MasterEvent P) × ℕ :=
  let tuples := fourTuplesQuery (triangleInputList P)
  let events := filterMapQuery (rowMasterCandidateQuery P I r) tuples.1
  let raw := (events.1,tuples.2+events.2)
  let unique := dedupQuery (countedMasterEqQuery P) raw.1
  let sorted := sortQuery (countedMasterCompareQuery P) unique.1
  (sorted.1,raw.2+unique.2+sorted.2)

private theorem master_universe_eq (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) : rowMasterUniverseQuery P I r =
      ((countedMasterUniverseQuery P (statePoints I) r).1,
       (countedMasterUniverseQuery P (statePoints I) r).2+universeExtra P I) := by
  have hv : (filterMapQuery (rowMasterCandidateQuery P I r)
      (fourTuplesQuery (triangleInputList P)).1).1=
      (filterMapQuery (countedMasterCandidateQuery P (statePoints I) r)
        (fourTuplesQuery (triangleInputList P)).1).1 := by
    simp only [filterMapQuery_value,master_candidate_value]
  have hc := filter_cost_add _ _ _ (master_candidate_cost P I r)
    (fourTuplesQuery (triangleInputList P)).1
  apply Prod.ext
  · dsimp only [rowMasterUniverseQuery,countedMasterUniverseQuery,countedMasterRawUniverseQuery]
    rw [hv]
  · dsimp only [rowMasterUniverseQuery,countedMasterUniverseQuery,countedMasterRawUniverseQuery]
    rw [hv]
    dsimp only [universeExtra] at hc ⊢
    omega

/-- Conjugacy includes both original priority and every new numeric lookup cost. -/
theorem rowMasterUniverseQuery_original (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : rowMasterUniverseQuery P I r=
      ((rowUniverseQuery P I hr).1.map (eventToMaster P (statePoints I) r),
       (rowUniverseQuery P I hr).2) := by
  rw [master_universe_eq,countedMasterUniverseQuery_original P (statePoints I) hr]
  apply Prod.ext
  · rw [rowUniverseQuery_value]
  · rw [rowUniverseQuery_cost]

/-- Extra reads for one actual event: eager grid and triangle loops are retained. -/
def eventExtra (P : TannerSquarePresentation) (I : StateRows P) (K : ℕ) (e : MasterEvent P) : ℕ :=
  ((gridListQuery K).1.map (fun _ => centerExtra P I (countedMasterAnchorQuery P e).1+
    ((Finset.univ.toList : List e.val).map (fun a => triangleExtra P I a.val)).sum)).sum

def rowMasterStateEventQuery (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (K : ℕ) (e : MasterEvent P) (R : StateRows P) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := countedMasterAnchorQuery P e
  let query := listAnyQuery (fun g : Grid K =>
    let center := rowCenterQuery P I lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      rowTriangleQuery P I lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)) net.1
  (query.1,net.2+anchor.2+query.2+1)

theorem rowMasterStateEventQuery_original (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (e : Event P (statePoints I) r) (R : StateRows P) :
    rowMasterStateEventQuery P I lambda K (eventToMaster P (statePoints I) r e) R=
      rowStateEventQuery P I r lambda K e R := rfl

private theorem master_event_eq (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (K : ℕ) (e : MasterEvent P) (R : StateRows P) :
    rowMasterStateEventQuery P I lambda K e R=
      ((countedMasterStateEventQuery P (statePoints I) lambda K e R).1,
       (countedMasterStateEventQuery P (statePoints I) lambda K e R).2+eventExtra P I K e) := by
  let anchor := (countedMasterAnchorQuery P e).1
  let old := fun g : Grid K =>
    let center := fullCenterQuery P (statePoints I) lambda K anchor g
    let triangles := listAllQuery (fun a : e.val =>
      stateTriangleQuery P (statePoints I) lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)
  let new := fun g : Grid K =>
    let center := rowCenterQuery P I lambda K anchor g
    let triangles := listAllQuery (fun a : e.val =>
      rowTriangleQuery P I lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1,center.2+triangles.2+8)
  have hv (g : Grid K) : (new g).1=(old g).1 := by
    dsimp only [new,old]
    rw [rowCenterQuery_value]
    exact all_value_congr _ _
      (fun a : e.val => rowTriangleQuery_value P I lambda a.val R
        (fullCenterQuery P (statePoints I) lambda K anchor g).1) _
  have hc (g : Grid K) : (new g).2=(old g).2+
      (centerExtra P I anchor+((Finset.univ.toList : List e.val).map (fun a => triangleExtra P I a.val)).sum) := by
    have ht := all_cost_add _ _ _
      (fun a : e.val => rowTriangleQuery_cost P I lambda a.val R
        (fullCenterQuery P (statePoints I) lambda K anchor g).1)
      (Finset.univ.toList : List e.val)
    dsimp only [new,old]
    rw [rowCenterQuery_value,rowCenterQuery_cost]
    omega
  have hall : (listAnyQuery new (gridListQuery K).1).1=(listAnyQuery old (gridListQuery K).1).1 :=
    any_value_congr old new hv (gridListQuery K).1
  have hcost := any_cost_add old new _ hc (gridListQuery K).1
  apply Prod.ext
  · exact hall
  · dsimp only [rowMasterStateEventQuery,countedMasterStateEventQuery]
    dsimp only [old,new,anchor] at hcost
    dsimp only [eventExtra,anchor]
    omega

/-- Lookup cost depends only on labels, independently of stored points and counters. -/
theorem incomingRead_cost_map (P : TannerSquarePresentation) (v : Vertex P)
    (L : List (Vertex P)) (f g : Vertex P → ℕ × Space) :
    (incomingRead P (L.map (fun u => (u,f u))) v).2=
      (incomingRead P (L.map (fun u => (u,g u))) v).2 := by
  induction L with
  | nil => rfl
  | cons u L ih =>
      change (stateRowQuery v (L.map (fun u => (u,f u)))).2=
        (stateRowQuery v (L.map (fun u => (u,g u)))).2 at ih
      by_cases h : u=v
      · simp only [incomingRead,List.map_cons,stateRowQuery,if_pos h]
      · simp only [incomingRead,List.map_cons,stateRowQuery,if_neg h,ih]

theorem incomingRows_read_cost (P : TannerSquarePresentation) (J : Vertex P → Space)
    (v : Vertex P) : (incomingRead P (incomingRows P J) v).2=
      (incomingRead P (incomingRows P (fun _ => 0)) v).2 :=
  incomingRead_cost_map P v (vertexInputList P) (fun u => (0,J u)) (fun _ => (0,0))

private theorem universe_extra_static (P : TannerSquarePresentation) (J : Vertex P → Space) :
    universeExtra P (incomingRows P J)=universeExtra P (incomingRows P (fun _ => 0)) := by
  have hp : pairExtra P (incomingRows P J) = pairExtra P (incomingRows P (fun _ => 0)) := by
    funext a b
    simp only [pairExtra,incomingRows_read_cost]
  have he : eligibilityExtra P (incomingRows P J) =
      eligibilityExtra P (incomingRows P (fun _ => 0)) := by
    funext L
    simp only [eligibilityExtra,hp]
  simp only [universeExtra,he]

private theorem event_extra_static (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (e : MasterEvent P) : eventExtra P (incomingRows P J) K e=
      eventExtra P (incomingRows P (fun _ => 0)) K e := by
  have hc (a : Option (Triangle P)) : centerExtra P (incomingRows P J) a=
      centerExtra P (incomingRows P (fun _ => 0)) a := by
    cases a <;> simp only [centerExtra,incomingRows_read_cost]
  simp only [eventExtra,hc,triangleExtra,incomingRows_read_cost]

/-- The fixed-carrier query is measurable with its actual new cost. -/
theorem measurable_rowMasterUniverseQuery (P : TannerSquarePresentation) (r : ℝ) :
    Measurable (fun J : Vertex P → Space => rowMasterUniverseQuery P (incomingRows P J) r) := by
  have hm := measurable_countedMasterUniverseQuery P r
  convert hm.fst.prodMk (hm.snd.add_const (universeExtra P (incomingRows P (fun _ => 0)))) using 1
  funext J
  rw [master_universe_eq,incomingRows_points,universe_extra_static]

theorem measurable_rowMasterStateEventQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (K : ℕ) (e : MasterEvent P)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ v, Measurable (f v)) :
    Measurable (fun w => rowMasterStateEventQuery P (incomingRows P (J w)) lambda K e
      (L.map (fun v => (v,f v w)))) := by
  have hm := measurable_countedMasterStateEventQuery_map P lambda K e J hJ L f hf
  convert hm.fst.prodMk (hm.snd.add_const (eventExtra P (incomingRows P (fun _ => 0)) K e)) using 1
  funext w
  rw [master_event_eq,incomingRows_points,event_extra_static]

theorem rowMasterScan_original (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (R : StateRows P) :
    scanQuery (rowMasterStateEventQuery P I lambda K) (rowMasterUniverseQuery P I r).1 R=
      ((rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R).1.map
        (eventToMaster P (statePoints I) r),
       (rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R).2) := by
  rw [rowMasterUniverseQuery_original P I hr]
  exact countedScan_map_pair (eventToMaster P (statePoints I) r) _ _
    (rowMasterStateEventQuery_original P I r lambda K) _ R

theorem measurable_rowScanQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ v, Measurable (f v)) :
    Measurable (fun w =>
      let I := incomingRows P (J w)
      let R := L.map (fun v => (v,f v w))
      let q := rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R
      (q.1.map (eventToMaster P (statePoints I) r),q.2)) := by
  have hm : Measurable (fun z : Ω × List (MasterEvent P) =>
      scanQuery (fun e w => rowMasterStateEventQuery P (incomingRows P (J w)) lambda K e
        (L.map (fun v => (v,f v w)))) z.2 z.1) :=
    measurable_from_prod_countable_left fun events => measurable_scanQuery _
      (fun e => measurable_rowMasterStateEventQuery_map P lambda K e J hJ L f hf) events
  have he := hm.comp (measurable_id.prodMk ((measurable_rowMasterUniverseQuery P r).fst.comp hJ))
  convert he using 1
  funext w
  let I := incomingRows P (J w)
  let R := L.map (fun v => (v,f v w))
  have hs (events : List (MasterEvent P)) :
      scanQuery (fun e w' => rowMasterStateEventQuery P (incomingRows P (J w')) lambda K e
        (L.map (fun v => (v,f v w')))) events w=
      scanQuery (rowMasterStateEventQuery P I lambda K) events R := by
    induction events with
    | nil => rfl
    | cons e events ih => simp only [scanQuery,ih,I,R]
  simpa only [Function.comp_def,id_eq] using
    (rowMasterScan_original P I hr lambda K R).symm.trans (hs _).symm

private theorem prefix_rows_canonical (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K s : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) :
    (rowPrefixQuery P (incomingRows P J) r lambda K (rowUniverseQuery P (incomingRows P J) hr).1 T s).1=
      (vertexInputList P).map (fun v => (v,
        counters (eventSupport P J r) (eventBad P J r lambda K) T s v,
        T (v,counters (eventSupport P J r) (eventBad P J r lambda K) T s v))) := by
  have h := StateRowsRep_rows P T _ _ (rowPrefixQuery_rep P (incomingRows P J) hr lambda K T s)
  exact h.trans (congrArg (fun J' : Vertex P → Space =>
    (vertexInputList P).map (fun v => (v,
      counters (eventSupport P J' r) (eventBad P J' r lambda K) T s v,
      T (v,counters (eventSupport P J' r) (eventBad P J' r lambda K) T s v))))
    (incomingRows_points P J))

theorem measurable_rowScanQuery_prefix (P : TannerSquarePresentation) {r : ℝ}
    (hr : 0 ≤ r) (lambda : ℝ) (K s : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let I := incomingRows P w.1
      let R := (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 w.2 s).1
      let q := rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R
      (q.1.map (eventToMaster P (statePoints I) r),q.2)) := by
  let c := fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
    counters (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2 s
  have hc : Measurable c := measurable_joint_counters P r lambda K s
  have hx := measurable_parameterized_assignment hc
  have hd (v : Vertex P) : Measurable (fun w => (c w v,w.2 (v,c w v))) :=
    ((measurable_pi_apply v).comp hc).prodMk ((measurable_pi_apply v).comp hx)
  have hm := measurable_rowScanQuery_map P hr lambda K
    (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) => w.1)
    measurable_fst (vertexInputList P) (fun v w => (c w v,w.2 (v,c w v))) hd
  convert hm using 1
  funext w
  dsimp only
  rw [prefix_rows_canonical]

theorem rowStepQuery_cost_labels (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P (statePoints I) r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P)
    (hR : R.map Prod.fst=vertexInputList P) :
    (rowStepQuery P I r lambda K events T R).2=
      (rowScanQuery P I r lambda K events R).2+
        match (rowScanQuery P I r lambda K events R).1.map (eventToMaster P (statePoints I) r) with
        | none => 0
        | some e => countedMasterRefreshCost P e := by
  cases h : (rowScanQuery P I r lambda K events R).1 with
  | none => simp only [rowStepQuery,h,Option.map_none,Nat.add_zero]
  | some e =>
      simp only [rowStepQuery,h,Option.map_some]
      rw [refreshStateRowsQuery_cost_labels P (statePoints I) r e T R hR]

theorem measurable_rowStepQuery_prefix_cost (P : TannerSquarePresentation) {r : ℝ}
    (hr : 0 ≤ r) (lambda : ℝ) (K s : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let I := incomingRows P w.1
      let R := (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 w.2 s).1
      (rowStepQuery P I r lambda K (rowUniverseQuery P I hr).1 w.2 R).2) := by
  have hs := measurable_rowScanQuery_prefix P hr lambda K s
  have hm : Measurable (fun e : Option (MasterEvent P) =>
      match e with | none => 0 | some e => countedMasterRefreshCost P e) := measurable_of_countable _
  convert hs.snd.add (hm.comp hs.fst) using 1
  funext w
  exact rowStepQuery_cost_labels P (incomingRows P w.1) r lambda K _ w.2 _
    (rowPrefixQuery_rep P (incomingRows P w.1) hr lambda K w.2 s).1

theorem measurable_rowPrefixQuery_cost (P : TannerSquarePresentation) {r : ℝ}
    (hr : 0 ≤ r) (lambda : ℝ) (K s : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let I := incomingRows P w.1
      (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 w.2 s).2) := by
  induction s with
  | zero =>
      have he (T : Table (X := fun _ : Vertex P => Space)) :
          (initialRowsQuery P T).2=(vertexInputList P).length*5 :=
        mapQuery_cost_constant _ 4 (fun _ => rfl) _
      simpa only [rowPrefixQuery,he] using
        (measurable_const : Measurable (fun _ : (Vertex P → Space) ×
          Table (X := fun _ : Vertex P => Space) => (vertexInputList P).length*5))
  | succ s ih => exact ih.add (measurable_rowStepQuery_prefix_cost P hr lambda K s)

def outputExtra (P : TannerSquarePresentation) (I : StateRows P) : ℕ :=
  ((vertexInputList P).map (fun v => (incomingRead P I v).2)).sum

theorem rowOutputQuery_cost_labels (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (R : StateRows P) (hR : R.map Prod.fst=vertexInputList P) :
    (rowOutputQuery P I lambda R).2=R.length*28+outputExtra P I := by
  rw [rowOutputQuery_cost,outputStateRowsQuery_cost]
  have he : R.map (fun row => (incomingRead P I row.1).2)=
      (vertexInputList P).map (fun v => (incomingRead P I v).2) := by
    simpa only [List.map_map,Function.comp_def] using
      congrArg (fun labels : List (Vertex P) => labels.map (fun v => (incomingRead P I v).2)) hR
  exact congrArg (fun costs : List ℕ => R.length*28+costs.sum) he

private theorem output_extra_static (P : TannerSquarePresentation) (J : Vertex P → Space) :
    outputExtra P (incomingRows P J)=outputExtra P (incomingRows P (fun _ => 0)) := by
  simp only [outputExtra,incomingRows_read_cost]

/-- Joint measurability includes all original branch costs and all paid incoming scans. -/
theorem measurable_joint_rowExecutionCost (P : TannerSquarePresentation) {r : ℝ}
    (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      rowExecutionCost P (incomingRows P w.1) hr lambda K w.2) := by
  let Ω := (Vertex P → Space) × Table (X := fun _ : Vertex P => Space)
  have ht := measurable_joint_haltTime P r lambda K
  have hp : Measurable (fun z : Ω × ℕ =>
      (rowPrefixQuery P (incomingRows P z.1.1) r lambda K
        (rowUniverseQuery P (incomingRows P z.1.1) hr).1 z.1.2 z.2).2) :=
    measurable_from_prod_countable_left (fun s => measurable_rowPrefixQuery_cost P hr lambda K s)
  have hs : Measurable (fun z : Ω × ℕ =>
      (rowScanQuery P (incomingRows P z.1.1) r lambda K (rowUniverseQuery P (incomingRows P z.1.1) hr).1
        (rowPrefixQuery P (incomingRows P z.1.1) r lambda K
          (rowUniverseQuery P (incomingRows P z.1.1) hr).1 z.1.2 z.2).1).2) :=
    measurable_from_prod_countable_left (fun s => (measurable_rowScanQuery_prefix P hr lambda K s).snd)
  have hu : Measurable (fun w : Ω => (rowUniverseQuery P (incomingRows P w.1) hr).2) := by
    have hcost : (fun w : Ω => (rowUniverseQuery P (incomingRows P w.1) hr).2) =
        (fun w : Ω => (rowMasterUniverseQuery P (incomingRows P w.1) r).2) := by
      funext w
      exact (congrArg Prod.snd
        (rowMasterUniverseQuery_original P (incomingRows P w.1) hr)).symm
    rw [hcost]
    exact (measurable_rowMasterUniverseQuery P r).snd.comp measurable_fst
  have hhalts (w : Ω) :
      Halts (eventSupport P (statePoints (incomingRows P w.1)) r)
        (eventBad P (statePoints (incomingRows P w.1)) r lambda K) w.2 =
      Halts (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2 :=
    congrArg (fun J : Vertex P → Space =>
      Halts (eventSupport P J r) (eventBad P J r lambda K) w.2)
      (incomingRows_points P w.1)
  have htime (w : Ω) :
      haltTime (eventSupport P (statePoints (incomingRows P w.1)) r)
        (eventBad P (statePoints (incomingRows P w.1)) r lambda K) w.2 =
      haltTime (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2 :=
    congrArg (fun J : Vertex P → Space =>
      haltTime (eventSupport P J r) (eventBad P J r lambda K) w.2)
      (incomingRows_points P w.1)
  have hstopped := measurable_id.prodMk ht
  have hfinite : Measurable (fun w : Ω =>
      (((rowUniverseQuery P (incomingRows P w.1) hr).2+
        (rowPrefixQuery P (incomingRows P w.1) r lambda K (rowUniverseQuery P (incomingRows P w.1) hr).1 w.2
          (haltTime (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2)).2+
        (rowScanQuery P (incomingRows P w.1) r lambda K (rowUniverseQuery P (incomingRows P w.1) hr).1
          (rowPrefixQuery P (incomingRows P w.1) r lambda K
            (rowUniverseQuery P (incomingRows P w.1) hr).1 w.2
              (haltTime (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2)).1).2+
        (Fintype.card (Vertex P)*28+outputExtra P (incomingRows P (fun _ => 0))) : ℕ) : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
      (((hu.add (hp.comp hstopped)).add (hs.comp hstopped)).add_const _)
  convert Measurable.ite (measurableSet_joint_halts P r lambda K) hfinite
    (measurable_const : Measurable (fun _ : Ω => (∞ : ℝ≥0∞))) using 1
  funext w
  by_cases h : Halts (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2
  · simp only [rowExecutionCost,rowExecutionQuery,hhalts w,htime w,if_pos h,
      rowOutputQuery_cost_labels P (incomingRows P w.1) lambda _
        (rowPrefixQuery_rep P (incomingRows P w.1) hr lambda K w.2 _).1,
      StateRowsRep_length P w.2 _ _ (rowPrefixQuery_rep P (incomingRows P w.1) hr lambda K w.2 _),
      output_extra_static]
  · simp only [rowExecutionCost,rowExecutionQuery,hhalts w,if_neg h]
  exact fun w => Classical.propDecidable
    (Halts (eventSupport P w.1 r) (eventBad P w.1 r lambda K) w.2)

/-- Semantic decoding of the actual emitted rows; no replacement cost is claimed. -/
def rowPerturbationOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) : StageMaps p n :=
  statePoints ((rowExecutionQuery (StagePresentation p n) (incomingRows (StagePresentation p n) J)
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) T).1.map
      (fun row => (row.1,0,row.2)))

theorem rowPerturbationOutput_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    rowPerturbationOutput p n J T=perturbationEmbeddingOutput (StagePresentation p n) J p T := by
  unfold rowPerturbationOutput
  rw [rowExecutionQuery_embedding_rows,incomingRows_points]
  simpa only [incomingRows,List.map_map,Function.comp_def] using
    incomingRows_points (StagePresentation p n) (perturbationEmbeddingOutput (StagePresentation p n) J p T)

def rowPhysicalSuccessor {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) : StageMaps p (n+1) :=
  replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
    (rowPerturbationOutput p n J T)

theorem rowPhysicalSuccessor_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    rowPhysicalSuccessor p n J T=physicalSuccessorOutput p n J T := by
  exact congrArg
    (replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n))
    (rowPerturbationOutput_value p n J T)

/-- This recursion uses the new emitted rows and the same original table factors. -/
def rowEvaluate {L : ℝ} (p : GeometricParameters L) : (N : ℕ) → Experiment p N → StageMaps p N
  | 0, _ => BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)
  | N+1, z => rowPhysicalSuccessor p N (rowEvaluate p N z.1) z.2

theorem rowEvaluate_value {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowEvaluate p N z=evaluate p N z := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [rowEvaluate,evaluate,rowPhysicalSuccessor_value,ih]

def rowHistory {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N)
    (i : Fin (N+1)) : StageMaps p i.val :=
  rowEvaluate p i.val (experimentPrefix p i.val N (by omega) z)

theorem rowHistory_value {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowHistory p N z=history p N z := by
  funext i
  exact rowEvaluate_value p i.val _

/-- Actual old incoming-map/current-table pair, with every coordinate access paid. -/
def jointRowStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : ℝ≥0∞ :=
  rowExecutionCost (StagePresentation p n) (incomingRows (StagePresentation p n) w.1)
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) w.2

def rowStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℝ≥0∞ := jointRowStageCost p i.val (stagePair p N i z)

def rowTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : ℝ≥0∞ :=
  ∑ i : Fin N, rowStageCost p N i z

theorem measurable_jointRowStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (jointRowStageCost p n) :=
  measurable_joint_rowExecutionCost (StagePresentation p n) (by positivity)
    p.lambda ((6*p.m+2)*p.lambda)

theorem measurable_rowStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    Measurable (rowStageCost p N i) :=
  (measurable_jointRowStageCost p i.val).comp (measurable_stagePair p N i)

theorem measurable_rowTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (rowTotalCost p N) :=
  Finset.measurable_sum Finset.univ (fun i _ => measurable_rowStageCost p N i)

theorem rowStageCost_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ}
    (h : M ≤ N) (i : Fin M) (z : Experiment p N) :
    rowStageCost p M i (experimentPrefix p M N h z)=rowStageCost p N (i.castLE h) z :=
  congrArg (jointRowStageCost p i.val) (stagePair_prefix p h i z)

@[simp] theorem rowTotalCost_zero {L : ℝ} (p : GeometricParameters L)
    (z : Experiment p 0) : rowTotalCost p 0 z=0 := by
  simp only [rowTotalCost,Fin.sum_univ_zero]

theorem rowStageCost_castSucc {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p (N+1)) :
    rowStageCost p (N+1) i.castSucc z=rowStageCost p N i z.1 := by
  have h := rowStageCost_prefix p (Nat.le_succ N) i z
  have hi : i.castLE (Nat.le_succ N)=i.castSucc := Fin.ext rfl
  rw [hi] at h
  simpa only [prefix_last] using h.symm

theorem rowStageCost_last {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p (N+1)) :
    rowStageCost p (N+1) (Fin.last N) z=jointRowStageCost p N (evaluate p N z.1,z.2) := by
  simp only [rowStageCost,stagePair,stageInput,Fin.val_last,prefix_last,tableAt_last]

theorem rowTotalCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p (N+1)) : rowTotalCost p (N+1) z=rowTotalCost p N z.1+
      jointRowStageCost p N (evaluate p N z.1,z.2) := by
  simp only [rowTotalCost,Fin.sum_univ_castSucc,rowStageCost_castSucc,rowStageCost_last]

theorem rowTotalCost_one {L : ℝ} (p : GeometricParameters L) (z : Experiment p 1) :
    rowTotalCost p 1 z=jointRowStageCost p 0
      (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p),z.2) := by
  rw [rowTotalCost_succ,rowTotalCost_zero,zero_add,evaluate_zero]

theorem jointRowStageCost_le {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : jointRowStageCost p n w ≤
      ((6*Fintype.card (Vertex (StagePresentation p n))+1 : ℕ) : ℝ≥0∞)*jointStageCost p n w := by
  have h := rowExecutionCost_le (StagePresentation p n) (incomingRows (StagePresentation p n) w.1)
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) w.2
  simpa only [jointRowStageCost,jointStageCost,accessMultiplier,incomingRows_length,incomingRows_points] using h

theorem rowStageCost_nonhalting {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : ¬stageHalts p N i z) : rowStageCost p N i z=∞ := by
  apply rowExecutionCost_nonhalting
  rw [incomingRows_points]
  change ¬stageHalts p N i z
  exact h

theorem rowStageCost_finite_of_halts {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : stageHalts p N i z) : rowStageCost p N i z<∞ := by
  apply rowExecutionCost_finite_of_halts
  rw [incomingRows_points]
  change stageHalts p N i z
  exact h

theorem rowTotalCost_infinite_of_nonhalting {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : ¬stageHalts p N i z) : rowTotalCost p N z=∞ := by
  apply top_unique
  rw [← rowStageCost_nonhalting p N i z h]
  exact Finset.single_le_sum (fun (j : Fin N) (_ : j ∈ (Finset.univ : Finset (Fin N))) =>
    show (0 : ℝ≥0∞) ≤ rowStageCost p N j z from bot_le) (Finset.mem_univ i)

theorem rowTotalCost_finite_iff {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowTotalCost p N z<∞ ↔ ∀ i : Fin N, stageHalts p N i z := by
  constructor
  · intro h i
    by_contra hi
    rw [rowTotalCost_infinite_of_nonhalting p N i z hi] at h
    exact (lt_irrefl _) h
  · intro h
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact rowStageCost_finite_of_halts p N i z (h i)

theorem rowTotalCost_finite_on_success {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) (h : z ∈ finiteSuccess p N) : rowTotalCost p N z<∞ :=
  (rowTotalCost_finite_iff p N z).mpr h.2.1

/-- The row-driven history uses the original independent whole-table factors. -/
theorem rowHistory_stagePair_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    (experimentLaw p N).map (fun z =>
      (rowEvaluate p i.val (experimentPrefix p i.val N (by omega) z),tableAt p N i z))=
      (outputLaw p i.val).prod (physicalTableLaw p i.val) := by
  have he : (fun z : Experiment p N =>
      (rowEvaluate p i.val (experimentPrefix p i.val N (by omega) z),tableAt p N i z))=stagePair p N i := by
    funext z
    exact Prod.ext (rowEvaluate_value p i.val _) rfl
  rw [he]
  exact stagePair_law p N i

/-- Complete original history jointly with the new actual cost vector and total. -/
theorem rowHistory_cost_joint_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (experimentLaw p N).map (fun z => (rowHistory p N z,(fun i => rowStageCost p N i z),rowTotalCost p N z))=
      (experimentLaw p N).map (fun z => (history p N z,(fun i => rowStageCost p N i z),rowTotalCost p N z)) := by
  congr 1
  funext z
  rw [rowHistory_value]

private theorem scale_le_final {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    6*Fintype.card (Vertex (StagePresentation p i.val))+1 ≤ 391*(stageQubits p N+1) := by
  have hi := operation_input_size_le_qubits (StagePresentation p i.val)
    (state (perturbationOddScale p) i.val).admissible.toTannerSquareAdmissible
    (state_boundedValence (perturbationOddScale p) i.val)
  have hq := stageQubits_mono p (Nat.le_of_lt i.isLt)
  have hm := Nat.mul_le_mul_left 65 hq
  change Fintype.card (Vertex (StagePresentation p i.val))+Fintype.card (Triangle (StagePresentation p i.val)) ≤
    65*stageQubits p i.val at hi
  omega

theorem rowTotalCost_le_scaled {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowTotalCost p N z ≤
      ((391*(stageQubits p N+1) : ℕ) : ℝ≥0∞)*totalStageCost p N z := by
  calc
    _ ≤ ∑ i : Fin N, ((391*(stageQubits p N+1) : ℕ) : ℝ≥0∞)*stageCost p N i z := by
      apply Finset.sum_le_sum
      intro i _
      exact (jointRowStageCost_le p i.val (stagePair p N i z)).trans
        (mul_le_mul' ((Nat.cast_le (α := ℝ≥0∞)).mpr (scale_le_final p N i)) le_rfl)
    _ = _ := by simp only [totalStageCost,Finset.mul_sum]

private theorem integral_scale_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ≥0∞) (d : ℕ) (hf : Measurable f)
    (h : ∀ z, g z ≤ (d : ℝ≥0∞)*f z) :
    (∫⁻ z, g z ∂μ) ≤ (d : ℝ≥0∞)*(∫⁻ z, f z ∂μ) := by
  calc
    _ ≤ ∫⁻ z, (d : ℝ≥0∞)*f z ∂μ := lintegral_mono h
    _ = _ := lintegral_const_mul _ hf

private theorem degree_twelve_bound (a b : ℝ≥0∞) (C q : ℕ)
    (hpaid : a ≤ ((391*(q+1) : ℕ) : ℝ≥0∞)*b)
    (hold : b ≤ ((C*(65^10*(q+1)^11) : ℕ) : ℝ≥0∞)) :
    a ≤ (((391*C*65^10)*(q+1)^12 : ℕ) : ℝ≥0∞) := by
  calc
    _ ≤ ((391*(q+1) : ℕ) : ℝ≥0∞)*b := hpaid
    _ ≤ ((391*(q+1) : ℕ) : ℝ≥0∞)*((C*(65^10*(q+1)^11) : ℕ) : ℝ≥0∞) := mul_le_mul' le_rfl hold
    _ = _ := by rw [← Nat.cast_mul]; congr 1; ring

/-- The coefficient is derived from paid incoming scans and actual qubit growth. -/
theorem rowTotalCost_integral_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z, rowTotalCost p N z ∂experimentLaw p N) ≤
      (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10)*(stageQubits p N+1)^12 : ℕ) : ℝ≥0∞) := by
  exact degree_twelve_bound
    (∫⁻ z, rowTotalCost p N z ∂experimentLaw p N)
    (∫⁻ z, totalStageCost p N z ∂experimentLaw p N)
    (operationConstant ((6*p.m+2)*p.lambda)) (stageQubits p N)
    (integral_scale_bound (experimentLaw p N) (totalStageCost p N) (rowTotalCost p N)
      (391*(stageQubits p N+1)) (measurable_totalStageCost p N) (rowTotalCost_le_scaled p N))
    (totalStageCost_integral_le p N)

/-- Parameters are fixed before every prefix and every random input. -/
theorem fixed_parameters_row_execution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N,
      Measurable (rowTotalCost p N) ∧
      (∫⁻ z, rowTotalCost p N z ∂experimentLaw p N) ≤
        (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10)*(stageQubits p N+1)^12 : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ rowTotalCost p N z<∞ := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p,fun N => ⟨measurable_rowTotalCost p N,rowTotalCost_integral_le p N,?_⟩⟩
  filter_upwards [finiteSuccess_ae p N] with z h
  exact ⟨h,rowTotalCost_finite_on_success p N z h⟩

/-- Every prefix reads the literal truncation of the same original countable stream. -/
theorem common_row_execution {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, rowTotalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega)<∞) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n
        (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t :=
  ⟨fun N => rowTotalCost_finite_on_success p N _ (h N),
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_geometry p h⟩


theorem rowEligiblePairQuery_correct (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (a b : Triangle P) :
    (rowEligiblePairQuery P I r a b).1=true ↔
      triangleColor P a=triangleColor P b ∧ dist (oldAnchor P (statePoints I) a) (oldAnchor P (statePoints I) b)≤r := by
  rw [rowEligiblePairQuery_value]
  exact eligiblePairQuery_correct P (statePoints I) hr a b

theorem rowUniverseQuery_order (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : (rowUniverseQuery P I hr).1=
      (Finset.univ : Finset (Event P (statePoints I) r)).sort (eventPriorityLE P (statePoints I) r) := by
  rw [rowUniverseQuery_value]
  exact eventUniverseQuery_value P (statePoints I) hr

theorem rowStateEventQuery_correct (P : TannerSquarePresentation) (I : StateRows P)
    (r lambda : ℝ) (K : ℕ) (e : Event P (statePoints I) r) (R : StateRows P) :
    (rowStateEventQuery P I r lambda K e R).1=true ↔
      statePoints R ∈ localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) e := by
  rw [rowStateEventQuery_value]
  exact stateEventQuery_correct P (statePoints I) r lambda K e R

/-- Every finite first-bad selection, including the final clean scan, is the original one. -/
theorem rowPrefixQuery_selected (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (s : ℕ) :
    (rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1
      (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 T s).1).1=
      selected (eventSupport P (statePoints I) r) (eventBad P (statePoints I) r lambda K) T s := by
  rw [rowUniverseQuery_value,rowScanQuery_value,rowPrefixQuery_value]
  exact actualScanQuery_value P (statePoints I) hr lambda K T _ _
    (actualPrefixQuery_rep P (statePoints I) hr lambda K T s)

theorem rowMasterCandidateQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (rowMasterCandidateQuery P I r L).1=
      (countedMasterCandidateQuery P (statePoints I) r L).1 := master_candidate_value P I r L

theorem rowMasterCandidateQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (r : ℝ) (L : List (Triangle P)) : (rowMasterCandidateQuery P I r L).2=
      (countedMasterCandidateQuery P (statePoints I) r L).2+eligibilityExtra P I L :=
  master_candidate_cost P I r L

end QEC.Coding.BDL26IncomingRowsExecution
