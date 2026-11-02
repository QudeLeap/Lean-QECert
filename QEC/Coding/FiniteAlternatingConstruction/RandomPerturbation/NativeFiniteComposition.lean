import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeGeometricJointExecution
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.PaidRowsComposition

/-!
# Finite composition of the actual native-key execution

Project-derived internal/API closure for #1637. The source route is BDL26,
Section 3, paper.tex:1277–1323,1400–1428,2120–2198,2227–2238,2252–2256.
This module retains the native key, complete continuous fresh tables, first-match
row reads, actual RX/RZ interpolation and the infinity/column-zero defaults.
Seed rows are supplied data. Constructor/rank setup and finite-bit sampling are
outside the existing exact-real primitive model. No public node is promoted.
-/
noncomputable section
namespace QEC.Coding.BDL26NativeFiniteComposition
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric BDL26KeyedGeometricExecution BDL26NativeKeyExecutionBridge
open BDL26NativeGeometricExecution BDL26NativeGeometricExecutionCost
open BDL26NativeGeometricScanCost BDL26NativeGeometricJointExecution
open BDL26ReplacementMaterialization BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

local instance labelListMeasurable (A : Type*) [Countable A] :
    MeasurableSpace (List A) := ⊤
local instance labelListSingleton (A : Type*) [Countable A] :
    MeasurableSingletonClass (List A) := ⟨fun _ => trivial⟩

private theorem map_identity {A : Type*} (L : List A) :
    L.map (fun a => a) = L := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg (List.cons a) ih

/-- Reassociate the initialization fee before a native interpreter occurs. -/
private theorem initial_fee_reassociate (initial rest final : ℕ)
    (h : initial+1+rest=final) : initial+rest+1=final := by
  omega

/-- Keep the exponent symbolic, without evaluating any native coefficient. -/
private theorem paid_power_step (a b r k : ℕ) :
    (a*r)*(b*r^k) = (a*b)*r^(k+1) := by
  rw [pow_succ]
  ac_rfl

private theorem paid_power_left (a r k : ℕ) :
    r*(a*r^k) = a*r^(k+1) := by
  rw [pow_succ]
  ac_rfl

/-- Ordinary composition on abstract carriers, before actual generated types. -/
private theorem measurable_comp_pointwise {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (g : Ω → A) (out : Ω → B)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ z, out z = f (g z)) : Measurable out := by
  have hm : Measurable (f ∘ g) := hf.comp hg
  have h : out = f ∘ g := funext he
  rw [h]
  exact hm

private theorem measurableSet_pullback_pointwise {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (f : Ω → A) (s : Set A) (out : Ω → Prop)
    (hf : Measurable f) (hs : MeasurableSet s)
    (he : ∀ z, out z ↔ f z ∈ s) : MeasurableSet {z | out z} := by
  have h : {z | out z} = f ⁻¹' s := Set.ext he
  rw [h]
  exact hs.preimage hf

private theorem lintegral_affine_nat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ≥0∞)
    (hf : Measurable f) (d b : ℕ) :
    (∫⁻ z, (d : ℝ≥0∞)*f z+(b : ℝ≥0∞) ∂μ) =
      (d : ℝ≥0∞)*(∫⁻ z, f z ∂μ)+(b : ℝ≥0∞) := by
  have hm : Measurable (fun z => (d : ℝ≥0∞)*f z) := measurable_const.mul hf
  rw [lintegral_add_left hm,lintegral_const_mul' (μ := μ) (d : ℝ≥0∞) f (by simp)]
  simp

abbrev Rows (S : OddScale) (n : ℕ) := List (Vertex (Presentation S n) × Space)

def canonicalRows (S : OddScale) (n : ℕ) (J : Input S n) : Rows S n :=
  (vertexInputList (Presentation S n)).map (fun v => (v,J v))

def rowMap (S : OddScale) (n : ℕ) (I : Rows S n) : Input S n :=
  fun v => (pointRowQuery v I).1

@[simp] theorem rowMap_canonical (S : OddScale) (n : ℕ) (J : Input S n) :
    rowMap S n (canonicalRows S n J) = J := by
  funext v
  exact pointRowQuery_map J v _ (vertexInputList_complete _ v)

@[simp] theorem canonicalRows_labels (S : OddScale) (n : ℕ) (J : Input S n) :
    (canonicalRows S n J).map Prod.fst = vertexInputList (Presentation S n) := by
  simp only [canonicalRows,List.map_map,Function.comp_def]
  exact map_identity _

@[simp] theorem canonicalRows_length (S : OddScale) (n : ℕ) (J : Input S n) :
    (canonicalRows S n J).length = Fintype.card (Vertex (Presentation S n)) := by
  simp only [canonicalRows,List.length_map,vertexInputList_length]

namespace Paid
/-- The comparison is an upper bound on an independently defined interpreter,
never its definition. -/
private def Sim {A : Type*} (d : ℕ) (x y : A × ℕ) : Prop :=
  x.1=y.1 ∧ x.2 ≤ d*y.2

private theorem self_scale (d c : ℕ) (hd : 1 ≤ d) : c ≤ d*c := by
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right c hd

private theorem map_sim {A B : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → B × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (mapQuery q' L) (mapQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [mapQuery]⟩
  | cons a L ih =>
    have ha := h a
    exact ⟨by simp only [mapQuery,ha.1,ih.1],by
      dsimp only [mapQuery]; nlinarith [ha.2,ih.2]⟩

private theorem all_sim {A : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → Bool × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (listAllQuery q' L) (listAllQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [listAllQuery]⟩
  | cons a L ih =>
    have ha := h a
    exact ⟨by simp only [listAllQuery,ha.1,ih.1],by
      dsimp only [listAllQuery]; nlinarith [ha.2,ih.2]⟩

private theorem any_sim {A : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → Bool × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (listAnyQuery q' L) (listAnyQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [listAnyQuery]⟩
  | cons a L ih =>
    have ha := h a
    exact ⟨by simp only [listAnyQuery,ha.1,ih.1],by
      dsimp only [listAnyQuery]; nlinarith [ha.2,ih.2]⟩

private theorem filter_sim {A B : Type*} (d : ℕ) (hd : 1 ≤ d)
    (q q' : A → Option B × ℕ) (h : ∀ a, Sim d (q' a) (q a)) (L : List A) :
    Sim d (filterMapQuery q' L) (filterMapQuery q L) := by
  induction L with
  | nil => exact ⟨rfl,by simp [filterMapQuery]⟩
  | cons a L ih =>
    have ha := h a
    exact ⟨by simp only [filterMapQuery,ha.1,ih.1],by
      dsimp only [filterMapQuery]; nlinarith [ha.2,ih.2]⟩

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

/-- A callback read is executed at each generated incoming address. Its actual
first-match fee, six original payload operations and the three map operations
are paid. The surrounding generator/size/address program is unchanged. -/
private def initializePayload {N M : ℕ} (h : N=M)
    (read : Fin M → Space × ℕ) (L : List (Fin N)) :
    BDL26NativeStateRows.Run (SR.Rows (Fin M)) :=
  BDL26NativeStateRows.mapQ (fun i =>
    let a := Fin.cast h i
    let x := read a
    ⟨(a,0,x.1),x.2+6,1⟩) L

def incomingQ (S : OddScale) (n : ℕ) (I : Rows S n) :
    BDL26NativeStateRows.Run (SR.Rows (SR.Index S n)) :=
  let generated := BDL26NativePresentationGenerator.setupQ S n
  let size := BDL26NativeStateRows.lengthQ generated.1.data.vertices
  let addresses := BDL26NativeStateRows.indicesQ size.value
  let rows := initializePayload (BDL26NativeStateRows.length_value generated.1.data.vertices)
    (fun a => pointRowQuery (SR.decode S n a) I) addresses.value
  ⟨rows.value,generated.2+size.operations+addresses.operations+rows.operations+2,
    BDL26NativePresentationGenerator.allocatedRecords S n+
      size.allocations+addresses.allocations+rows.allocations+1⟩

private def readSum {A : Type*} (L : List A) (read : A → Space × ℕ) : ℕ :=
  (L.map (fun a => (read a).2)).sum

private theorem payload_value {N M : ℕ} (h : N=M)
    (read : Fin M → Space × ℕ) (L : List (Fin N)) :
    (initializePayload h read L).value =
      (L.map (Fin.cast h)).map (fun a => (a,0,(read a).1)) := by
  simp only [initializePayload,BDL26NativeStateRows.map_value,List.map_map,
    Function.comp_def]

private theorem payload_fee {N M : ℕ} (h : N=M)
    (read : Fin M → Space × ℕ) (L : List (Fin N)) :
    (initializePayload h read L).operations =
      9*L.length+readSum (L.map (Fin.cast h)) read := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [initializePayload,BDL26NativeStateRows.mapQ,List.length_cons,
      readSum,List.map_cons,List.sum_cons] at *
    omega

/-- Exact extra callback cost, not a polynomial envelope. -/
def incomingExtra (S : OddScale) (n : ℕ) (I : Rows S n) : ℕ :=
  readSum (SR.indices (SR.count S n)) (fun a => pointRowQuery (SR.decode S n a) I)

theorem incoming_value (S : OddScale) (n : ℕ) (I : Rows S n) :
    (incomingQ S n I).value =
      (BDL26NativeKeyExecutionBridge.incomingQ S n (rowMap S n I)).value := by
  unfold incomingQ BDL26NativeKeyExecutionBridge.incomingQ
  rw [SR.initialize_value]
  dsimp only
  rw [payload_value,BDL26NativeStateRows.indices_value]
  have he {a b : ℕ} (h : a=b) :
      (BDL26NativeStateRows.indices a).map (Fin.cast h)=BDL26NativeStateRows.indices b := by
    subst b; simp
  rw [he]
  rfl

theorem incoming_fee (S : OddScale) (n : ℕ) (I : Rows S n) :
    (incomingQ S n I).operations = incomingBudget S n+incomingExtra S n I := by
  unfold incomingQ
  dsimp only
  rw [payload_fee,BDL26NativeStateRows.indices_value]
  have he {a b : ℕ} (h : a=b) :
      (BDL26NativeStateRows.indices a).map (Fin.cast h)=BDL26NativeStateRows.indices b := by
    subst b; simp
  rw [he,BDL26NativeStateRows.indices_length]
  rw [(BDL26NativeStateRows.length_cost _).1,BDL26NativeStateRows.indices_operations,
    BDL26NativeStateRows.length_value]
  dsimp only [incomingBudget,incomingExtra,BDL26NativeStateRows.count]
  omega

def multiplier {S : OddScale} {n : ℕ} (I : Rows S n) : ℕ := 2*I.length+1

private theorem incoming_bound (S : OddScale) (n : ℕ) (I : Rows S n) :
    (incomingQ S n I).operations ≤ multiplier I*incomingBudget S n := by
  have hread : incomingExtra S n I ≤ 2*I.length*SR.count S n := by
    have hs (L : List (SR.Index S n)) :
        readSum L (fun a => pointRowQuery (SR.decode S n a) I) ≤ L.length*(2*I.length) := by
      induction L with
      | nil => simp only [readSum,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
      | cons a L ih =>
        have ha := pointRowQuery_cost_le (SR.decode S n a) I
        simp only [readSum,List.map_cons,List.sum_cons,List.length_cons] at *
        nlinarith
    simpa only [incomingExtra,BDL26NativeStateRows.indices_length,Nat.mul_comm] using
      hs (SR.indices (SR.count S n))
  have hcount : SR.count S n ≤ incomingBudget S n := by
    dsimp only [incomingBudget]; omega
  rw [incoming_fee]
  dsimp only [multiplier]
  nlinarith
def pairQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (a b : MD.Code) : Bool × ℕ :=
  let A := NC.colorOfCodeQ S n a
  let B := NC.colorOfCodeQ S n b
  match A.value, B.value with
  | some (ca, xa), some (cb, xb) =>
      let I := incomingQ S n I
      let x := SR.readQ ca.1 I.value
      let y := SR.readQ cb.1 I.value
      let close := anchorCloseProgram.run (fun _ => y.value.2) x.value.2 r
      (decide (xa = xb) && close.1,
        A.operations+B.operations+I.operations+x.operations+y.operations+close.2+5)
  | _, _ => (false, A.operations+B.operations+2)

def eligibleQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (codes : MD.FourCodes) : Bool × ℕ :=
  listAllQuery (fun a => listAllQuery (pairQ S n I r a) (MC.codeList codes))
    (MC.codeList codes)

def codeCandidateQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (row : Code S n) : Option (Code S n) × ℕ :=
  let q := eligibleQ S n I r row.val.1
  (if q.1 then some row else none, q.2+1)

def codeRawUniverseQ (S : OddScale) (n : ℕ) (I : Rows S n) (r : ℝ) :
    List (Code S n) × ℕ :=
  let generated := MC.masterCandidatesQ S n
  let scanned := filterMapQuery (codeCandidateQ S n I r) (MC.Rows S n).attach
  (scanned.1,generated.operations+scanned.2+1)

def codeUniverseQ (S : OddScale) (n : ℕ) (I : Rows S n) (r : ℝ) :
    List (Code S n) × ℕ :=
  let raw := codeRawUniverseQ S n I r
  let sorted := sortQuery (codeCompareQ S n) raw.1
  (sorted.1,raw.2+sorted.2)

def triangleCodeQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (c : MD.Code) (center : Space) : Bool × ℕ :=
  let atlas := MD.atlasQ S n
  let found := MD.atlasReadQ c atlas.value
  match found.value with
  | none => (false,atlas.operations+found.operations+1)
  | some v =>
      let I := incomingQ S n I
      let x := pointQ S n lambda I.value R v.1
      let y := pointQ S n lambda I.value R v.2.1
      let z := pointQ S n lambda I.value R v.2.2
      let q := triangleQuery ![x.1,y.1,z.1] center 2
      (q.1,atlas.operations+found.operations+I.operations+x.2+y.2+z.2+q.2+4)

def centerQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (K : ℕ) (codes : MD.FourCodes) (g : Grid K) : Space × ℕ :=
  let anchor := anchorCodeQ codes
  let atlas := MD.atlasQ S n
  let found := MD.atlasReadQ anchor.1 atlas.value
  match found.value with
  | none => (0,anchor.2+atlas.operations+found.operations+1)
  | some v =>
      let I := incomingQ S n I
      let j := SR.readQ v.1 I.value
      let grid := gridPointQuery K g
      let point := pointSnapshotQuery lambda j.value.2 grid.1
      (point.1,anchor.2+atlas.operations+found.operations+I.operations+j.operations+grid.2+point.2+3)

def codeEventQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (K : ℕ) (row : Code S n)
    (R : SR.Rows (SR.Index S n)) : Bool × ℕ :=
  let net := gridListQuery K
  let query := listAnyQuery (fun g =>
    let center := centerQ S n I lambda K row.val.1 g
    let triangles := listAllQuery (fun c => triangleCodeQ S n I lambda R c center.1)
      (MC.codeList row.val.1)
    (triangles.1,center.2+triangles.2+2)) net.1
  (query.1,net.2+query.2+1)

def codeScanQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    Option (Code S n) × ℕ :=
  let candidates := codeUniverseQ S n I r
  let scan := scanQuery (codeEventQ S n I lambda K) candidates.1 R
  (scan.1,candidates.2+scan.2+1)

private theorem multiplier_one {S : OddScale} {n : ℕ} (I : Rows S n) :
    1 ≤ multiplier I := by dsimp only [multiplier]; omega

private theorem incoming_original_fee (S : OddScale) (n : ℕ) (J : Input S n) :
    (BDL26NativeKeyExecutionBridge.incomingQ S n J).operations=incomingBudget S n :=
  (BDL26NativeStateRows.initialize_cost S n _).1

private theorem pair_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (a b : MD.Code) :
    Sim (multiplier I) (pairQ S n I r a b)
      (BDL26NativeKeyExecutionBridge.pairQ S n (rowMap S n I) r a b) := by
  have hd := multiplier_one I
  have hi := incoming_bound S n I
  cases ha : (NC.colorOfCodeQ S n a).value with
  | none =>
    simp only [pairQ,BDL26NativeKeyExecutionBridge.pairQ,ha,Sim]
    exact ⟨True.intro,self_scale _ _ hd⟩
  | some A =>
    cases hb : (NC.colorOfCodeQ S n b).value with
    | none =>
      simp only [pairQ,BDL26NativeKeyExecutionBridge.pairQ,ha,hb,Sim]
      exact ⟨True.intro,self_scale _ _ hd⟩
    | some B =>
      simp only [pairQ,BDL26NativeKeyExecutionBridge.pairQ,ha,hb,incoming_value,
        incoming_original_fee,Sim]
      exact ⟨True.intro,by nlinarith⟩

private theorem eligible_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (codes : MD.FourCodes) :
    Sim (multiplier I) (eligibleQ S n I r codes)
      (BDL26NativeKeyExecutionBridge.eligibleQ S n (rowMap S n I) r codes) := by
  exact all_sim _ (multiplier_one I) _ _
    (fun a => all_sim _ (multiplier_one I) _ _ (pair_sim S n I r a) _) _

private theorem candidate_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (row : Code S n) :
    Sim (multiplier I) (codeCandidateQ S n I r row)
      (BDL26NativeGeometricJointExecution.codeCandidateQ S n (rowMap S n I) r row) := by
  have h := eligible_sim S n I r row.val.1
  have hd := multiplier_one I
  simp only [codeCandidateQ,BDL26NativeGeometricJointExecution.codeCandidateQ,h.1,Sim]
  exact ⟨True.intro,by nlinarith [h.2]⟩

private theorem raw_sim (S : OddScale) (n : ℕ) (I : Rows S n) (r : ℝ) :
    Sim (multiplier I) (codeRawUniverseQ S n I r)
      (BDL26NativeGeometricJointExecution.codeRawUniverseQ S n (rowMap S n I) r) := by
  have h := filter_sim _ (multiplier_one I) _ _ (candidate_sim S n I r) (MC.Rows S n).attach
  have hd := multiplier_one I
  simp only [codeRawUniverseQ,BDL26NativeGeometricJointExecution.codeRawUniverseQ,h.1,Sim]
  exact ⟨True.intro,by nlinarith [h.2]⟩

private theorem universe_sim (S : OddScale) (n : ℕ) (I : Rows S n) (r : ℝ) :
    Sim (multiplier I) (codeUniverseQ S n I r)
      (BDL26NativeGeometricJointExecution.codeUniverseQ S n (rowMap S n I) r) := by
  have h := raw_sim S n I r
  have hd := multiplier_one I
  simp only [codeUniverseQ,BDL26NativeGeometricJointExecution.codeUniverseQ,h.1,Sim]
  exact ⟨True.intro,by nlinarith [h.2]⟩

private theorem center_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (K : ℕ) (codes : MD.FourCodes) (g : Grid K) :
    Sim (multiplier I) (centerQ S n I lambda K codes g)
      (BDL26NativeKeyExecutionBridge.centerQ S n (rowMap S n I) lambda K codes g) := by
  have hi := incoming_bound S n I
  have hd := multiplier_one I
  cases hf : (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).value with
  | none =>
    simp only [centerQ,BDL26NativeKeyExecutionBridge.centerQ,hf,Sim]
    exact ⟨True.intro,self_scale _ _ hd⟩
  | some v =>
    simp only [centerQ,BDL26NativeKeyExecutionBridge.centerQ,hf,incoming_value,
      incoming_original_fee,Sim]
    exact ⟨True.intro,by nlinarith⟩

private theorem triangle_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (code : MD.Code) (center : Space) :
    Sim (multiplier I) (triangleCodeQ S n I lambda R code center)
      (BDL26NativeKeyExecutionBridge.triangleCodeQ S n (rowMap S n I) lambda R code center) := by
  have hi := incoming_bound S n I
  have hd := multiplier_one I
  cases hf : (MD.atlasReadQ code (MD.atlasQ S n).value).value with
  | none =>
    simp only [triangleCodeQ,BDL26NativeKeyExecutionBridge.triangleCodeQ,hf,Sim]
    exact ⟨True.intro,self_scale _ _ hd⟩
  | some v =>
    simp only [triangleCodeQ,BDL26NativeKeyExecutionBridge.triangleCodeQ,hf,incoming_value,
      incoming_original_fee,Sim]
    exact ⟨True.intro,by nlinarith⟩

private theorem event_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (K : ℕ) (row : Code S n) (R : SR.Rows (SR.Index S n)) :
    Sim (multiplier I) (codeEventQ S n I lambda K row R)
      (BDL26NativeGeometricJointExecution.codeEventQ S n (rowMap S n I) lambda K row R) := by
  have hd := multiplier_one I
  have hg (g : Grid K) : Sim (multiplier I)
      (let c := centerQ S n I lambda K row.val.1 g
       let q := listAllQuery (fun a => triangleCodeQ S n I lambda R a c.1) (MC.codeList row.val.1)
       (q.1,c.2+q.2+2))
      (let c := BDL26NativeKeyExecutionBridge.centerQ S n (rowMap S n I) lambda K row.val.1 g
       let q := listAllQuery (fun a => BDL26NativeKeyExecutionBridge.triangleCodeQ S n
         (rowMap S n I) lambda R a c.1) (MC.codeList row.val.1)
       (q.1,c.2+q.2+2)) := by
    have hc := center_sim S n I lambda K row.val.1 g
    have ht := all_sim _ hd _ _ (fun a => triangle_sim S n I lambda R a
      (BDL26NativeKeyExecutionBridge.centerQ S n (rowMap S n I) lambda K row.val.1 g).1)
      (MC.codeList row.val.1)
    simp only [hc.1,Sim]
    exact ⟨ht.1,by nlinarith [hc.2,ht.2]⟩
  have h := any_sim _ hd _ _ hg (gridListQuery K).1
  simp only [codeEventQ,BDL26NativeGeometricJointExecution.codeEventQ,Sim]
  exact ⟨h.1,by nlinarith [h.2]⟩

theorem scan_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    (codeScanQ S n I r lambda K R).1 =
      (BDL26NativeGeometricJointExecution.codeScanQ S n (rowMap S n I) r lambda K R).1 ∧
    (codeScanQ S n I r lambda K R).2 ≤ multiplier I*
      (BDL26NativeGeometricJointExecution.codeScanQ S n (rowMap S n I) r lambda K R).2 := by
  have hu := universe_sim S n I r
  have hs := scan_sim _ (multiplier_one I) _ _ (event_sim S n I lambda K)
    (BDL26NativeGeometricJointExecution.codeUniverseQ S n (rowMap S n I) r).1 R
  have hd := multiplier_one I
  simp only [codeScanQ,BDL26NativeGeometricJointExecution.codeScanQ,hu.1]
  exact ⟨hs.1,by nlinarith [hu.2,hs.2]⟩


private theorem incoming_lower (S : OddScale) (n : ℕ) (I : Rows S n) :
    incomingBudget S n≤(incomingQ S n I).operations := by
  rw [incoming_fee]; omega

private theorem lower_pair_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (a b : MD.Code) :
    Sim (1) (BDL26NativeKeyExecutionBridge.pairQ S n (rowMap S n I) r a b)
      (pairQ S n I r a b) := by
  have hd := (by decide : 1 ≤ 1)
  have hi := incoming_lower S n I
  cases ha : (NC.colorOfCodeQ S n a).value with
  | none =>
    simp only [pairQ,BDL26NativeKeyExecutionBridge.pairQ,ha,Sim]
    exact ⟨True.intro,self_scale _ _ hd⟩
  | some A =>
    cases hb : (NC.colorOfCodeQ S n b).value with
    | none =>
      simp only [pairQ,BDL26NativeKeyExecutionBridge.pairQ,ha,hb,Sim]
      exact ⟨True.intro,self_scale _ _ hd⟩
    | some B =>
      simp only [pairQ,BDL26NativeKeyExecutionBridge.pairQ,ha,hb,incoming_value,
        incoming_original_fee,Sim]
      exact ⟨True.intro,by nlinarith⟩

private theorem lower_eligible_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (codes : MD.FourCodes) :
    Sim (1) (BDL26NativeKeyExecutionBridge.eligibleQ S n (rowMap S n I) r codes)
      (eligibleQ S n I r codes) := by
  exact all_sim _ ((by decide : 1 ≤ 1)) _ _
    (fun a => all_sim _ ((by decide : 1 ≤ 1)) _ _ (lower_pair_sim S n I r a) _) _

private theorem lower_candidate_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (row : Code S n) :
    Sim (1) (BDL26NativeGeometricJointExecution.codeCandidateQ S n (rowMap S n I) r row)
      (codeCandidateQ S n I r row) := by
  have h := lower_eligible_sim S n I r row.val.1
  have hd := (by decide : 1 ≤ 1)
  simp only [codeCandidateQ,BDL26NativeGeometricJointExecution.codeCandidateQ,h.1,Sim]
  exact ⟨True.intro,by nlinarith [h.2]⟩

private theorem lower_raw_sim (S : OddScale) (n : ℕ) (I : Rows S n) (r : ℝ) :
    Sim (1) (BDL26NativeGeometricJointExecution.codeRawUniverseQ S n (rowMap S n I) r)
      (codeRawUniverseQ S n I r) := by
  have h := filter_sim _ ((by decide : 1 ≤ 1)) _ _ (lower_candidate_sim S n I r) (MC.Rows S n).attach
  have hd := (by decide : 1 ≤ 1)
  simp only [codeRawUniverseQ,BDL26NativeGeometricJointExecution.codeRawUniverseQ,h.1,Sim]
  exact ⟨True.intro,by nlinarith [h.2]⟩

private theorem lower_universe_sim (S : OddScale) (n : ℕ) (I : Rows S n) (r : ℝ) :
    Sim (1) (BDL26NativeGeometricJointExecution.codeUniverseQ S n (rowMap S n I) r)
      (codeUniverseQ S n I r) := by
  have h := lower_raw_sim S n I r
  have hd := (by decide : 1 ≤ 1)
  simp only [codeUniverseQ,BDL26NativeGeometricJointExecution.codeUniverseQ,h.1,Sim]
  exact ⟨True.intro,by nlinarith [h.2]⟩

private theorem lower_center_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (K : ℕ) (codes : MD.FourCodes) (g : Grid K) :
    Sim (1) (BDL26NativeKeyExecutionBridge.centerQ S n (rowMap S n I) lambda K codes g)
      (centerQ S n I lambda K codes g) := by
  have hi := incoming_lower S n I
  have hd := (by decide : 1 ≤ 1)
  cases hf : (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).value with
  | none =>
    simp only [centerQ,BDL26NativeKeyExecutionBridge.centerQ,hf,Sim]
    exact ⟨True.intro,self_scale _ _ hd⟩
  | some v =>
    simp only [centerQ,BDL26NativeKeyExecutionBridge.centerQ,hf,incoming_value,
      incoming_original_fee,Sim]
    exact ⟨True.intro,by nlinarith⟩

private theorem lower_triangle_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (code : MD.Code) (center : Space) :
    Sim (1) (BDL26NativeKeyExecutionBridge.triangleCodeQ S n (rowMap S n I) lambda R code center)
      (triangleCodeQ S n I lambda R code center) := by
  have hi := incoming_lower S n I
  have hd := (by decide : 1 ≤ 1)
  cases hf : (MD.atlasReadQ code (MD.atlasQ S n).value).value with
  | none =>
    simp only [triangleCodeQ,BDL26NativeKeyExecutionBridge.triangleCodeQ,hf,Sim]
    exact ⟨True.intro,self_scale _ _ hd⟩
  | some v =>
    simp only [triangleCodeQ,BDL26NativeKeyExecutionBridge.triangleCodeQ,hf,incoming_value,
      incoming_original_fee,Sim]
    exact ⟨True.intro,by nlinarith⟩

private theorem lower_event_sim (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (K : ℕ) (row : Code S n) (R : SR.Rows (SR.Index S n)) :
    Sim (1) (BDL26NativeGeometricJointExecution.codeEventQ S n (rowMap S n I) lambda K row R)
      (codeEventQ S n I lambda K row R) := by
  have hd := (by decide : 1 ≤ 1)
  have hg (g : Grid K) : Sim (1)
      (let c := BDL26NativeKeyExecutionBridge.centerQ S n (rowMap S n I) lambda K row.val.1 g
       let q := listAllQuery (fun a => BDL26NativeKeyExecutionBridge.triangleCodeQ S n (rowMap S n I) lambda R a c.1) (MC.codeList row.val.1)
       (q.1,c.2+q.2+2))
      (let c := centerQ S n I lambda K row.val.1 g
       let q := listAllQuery (fun a => triangleCodeQ S n I lambda R a c.1)
         (MC.codeList row.val.1)
       (q.1,c.2+q.2+2)) := by
    have hc := lower_center_sim S n I lambda K row.val.1 g
    have ht := all_sim _ hd _ _ (fun a => lower_triangle_sim S n I lambda R a
      (centerQ S n I lambda K row.val.1 g).1)
      (MC.codeList row.val.1)
    simp only [hc.1,Sim]
    exact ⟨ht.1,by nlinarith [hc.2,ht.2]⟩
  have h := any_sim _ hd _ _ hg (gridListQuery K).1
  simp only [codeEventQ,BDL26NativeGeometricJointExecution.codeEventQ,Sim]
  exact ⟨h.1,by nlinarith [h.2]⟩

theorem lower_scan_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    (BDL26NativeGeometricJointExecution.codeScanQ S n (rowMap S n I) r lambda K R).1 =
      (codeScanQ S n I r lambda K R).1 ∧
    (BDL26NativeGeometricJointExecution.codeScanQ S n (rowMap S n I) r lambda K R).2 ≤ 1*
      (codeScanQ S n I r lambda K R).2 := by
  have hu := lower_universe_sim S n I r
  have hs := scan_sim _ ((by decide : 1 ≤ 1)) _ _ (lower_event_sim S n I lambda K)
    (codeUniverseQ S n I r).1 R
  have hd := (by decide : 1 ≤ 1)
  simp only [codeScanQ,BDL26NativeGeometricJointExecution.codeScanQ,hu.1]
  exact ⟨hs.1,by nlinarith [hu.2,hs.2]⟩

/-- The actual row labels fix the lookup fees; coordinates retain their Borel
structure. No discrete measurable structure is imposed on spatial rows. -/
def canonicalExtra (S : OddScale) (n : ℕ) : ℕ :=
  incomingExtra S n (canonicalRows S n (fun _ => 0))

private theorem canonical_extra (S : OddScale) (n : ℕ) (J : Input S n) :
    incomingExtra S n (canonicalRows S n J)=canonicalExtra S n := by
  unfold incomingExtra canonicalExtra readSum
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [pointRowQuery_cost_labels,pointRowQuery_cost_labels,
    canonicalRows_labels,canonicalRows_labels]

private theorem canonical_incoming_fee (S : OddScale) (n : ℕ) (J : Input S n) :
    (incomingQ S n (canonicalRows S n J)).operations=
      incomingBudget S n+canonicalExtra S n := by
  rw [incoming_fee,canonical_extra]

private theorem incoming_read (S : OddScale) (n : ℕ) (J : Input S n)
    (a : SR.Index S n) :
    (SR.readQ a (incomingQ S n (canonicalRows S n J)).value).value.2 =
      J (SR.decode S n a) := by
  rw [incoming_value,rowMap_canonical]
  exact BDL26NativeKeyExecutionBridge.incoming_read S n J a

private theorem incoming_labels (S : OddScale) (n : ℕ) (J : Input S n) :
    (incomingQ S n (canonicalRows S n J)).value.map Prod.fst=SR.indices (SR.count S n) := by
  rw [incoming_value,rowMap_canonical]
  exact BDL26NativeStateRows.initialize_order S n _

private def readFee {A : Type*} [DecidableEq A] (a : A) : List A → ℕ
  | [] => 1
  | b::L => if b=a then 2 else readFee a L+2

private theorem read_fee {A : Type*} [DecidableEq A] (a : A)
    (R : BDL26NativeStateRows.Rows A) :
    (BDL26NativeStateRows.readQ a R).operations = readFee a (R.map Prod.fst) := by
  induction R with
  | nil => rfl
  | cons row R ih =>
      by_cases h : row.1=a <;>
        simp only [BDL26NativeStateRows.readQ,List.map_cons,readFee,h,if_true,if_false,ih]

private theorem sample_labels (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (c : SR.Index S n → ℕ) :
    (sampleRows S n T c).map Prod.fst = SR.indices (SR.count S n) := by
  simp only [sampleRows,BDL26NativeStateRows.rowsFor,List.map_map,Function.comp_def]
  have hid (L : List (SR.Index S n)) : L.map (fun a => a) = L := by
    induction L with
    | nil => rfl
    | cons a L ih => exact congrArg (List.cons a) ih
  exact hid _

private theorem sample_point (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (c : SR.Index S n → ℕ) (a : SR.Index S n) :
    originalPoints S n (sampleRows S n T c) (SR.decode S n a) = T (a,c a) := by
  simp only [originalPoints,BDL26NativeStateRows.points,Equiv.symm_apply_apply,sampleRows]
  rw [SR.read_rowsFor _ _ _ _ (SR.indices_complete _ _)]

private theorem measurable_point (S : OddScale) (n : ℕ) (lambda : ℝ)
    (c : SR.Index S n → ℕ) (a : SR.Index S n) :
    Measurable (fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n (canonicalRows S n z.1)).value (sampleRows S n z.2 c) a) := by
  have he : (fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n (canonicalRows S n z.1)).value (sampleRows S n z.2 c) a) =
      (fun z : JointInput S n =>
        (lambda • ((1/2 : ℝ) • z.1 (SR.decode S n a))+z.2 (a,c a),
          readFee a (SR.indices (SR.count S n))+
            readFee a (SR.indices (SR.count S n))+24+2)) := by
    funext z
    apply Prod.ext
    · rw [incoming_value,rowMap_canonical,point_actual,sample_point]
    · simp only [pointQ,pointSnapshotQuery_cost,read_fee,incoming_labels,sample_labels]
  rw [he]
  have hJ : Measurable (fun z : JointInput S n => z.1 (SR.decode S n a)) :=
    (measurable_pi_apply _).comp measurable_fst
  have hT : Measurable (fun z : JointInput S n => z.2 (a,c a)) :=
    (measurable_pi_apply _).comp measurable_snd
  exact (((hJ.const_smul (1/2 : ℝ)).const_smul lambda).add hT).prodMk measurable_const

private theorem measurable_pair (S : OddScale) (n : ℕ) (r : ℝ)
    (a b : MD.Code) : Measurable (fun J : Input S n => pairQ S n (canonicalRows S n J) r a b) := by
  cases ha : (NC.colorOfCodeQ S n a).value with
  | none => simp only [pairQ,ha]; exact measurable_const
  | some A =>
    cases hb : (NC.colorOfCodeQ S n b).value with
    | none => simp only [pairQ,ha,hb]; exact measurable_const
    | some B =>
      have hq : Measurable (fun J : Input S n =>
          anchorCloseProgram.run (fun _ => J (SR.decode S n B.1.1))
            (J (SR.decode S n A.1.1)) r) := by
        apply measurable_realTest_run
        · intro i j
          exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
            (measurable_pi_apply _)
        · intro j
          exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
            (measurable_pi_apply _)
        · exact measurable_const
      have hm : Measurable (fun q : Bool × ℕ =>
          (decide (A.2=B.2) && q.1,
            (NC.colorOfCodeQ S n a).operations+(NC.colorOfCodeQ S n b).operations+
              (incomingBudget S n+canonicalExtra S n)+readFee A.1.1 (SR.indices (SR.count S n))+
              readFee B.1.1 (SR.indices (SR.count S n))+q.2+5)) :=
        measurable_of_countable _
      simpa only [pairQ,ha,hb,incoming_read,canonical_incoming_fee,read_fee,incoming_labels,
        Function.comp_def] using hm.comp hq

private theorem measurable_eligible (S : OddScale) (n : ℕ) (r : ℝ)
    (codes : MD.FourCodes) : Measurable (fun J : Input S n => eligibleQ S n (canonicalRows S n J) r codes) :=
  measurable_listAllQuery _
    (fun a => measurable_listAllQuery _ (measurable_pair S n r a) (MC.codeList codes))
    (MC.codeList codes)

/-- Expose only the outer preprocessing composition. The full generated
candidate list remains an uninterpreted argument to the same filter and sort. -/
private theorem codeUniverse_factor (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    codeUniverseQ S n (canonicalRows S n J) r =
      (let q := filterMapQuery (codeCandidateQ S n (canonicalRows S n J) r) (MC.Rows S n).attach
       let sorted := sortQuery (codeCompareQ S n) q.1
       (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) := by
  rfl

private theorem measurable_universe (S : OddScale) (n : ℕ) (r : ℝ) :
    Measurable (fun J : Input S n => codeUniverseQ S n (canonicalRows S n J) r) := by
  have hc (row : Code S n) : Measurable (fun J : Input S n => codeCandidateQ S n (canonicalRows S n J) r row) :=
    (measurable_of_countable (fun q : Bool × ℕ =>
      (if q.1 then some row else none,q.2+1))).comp (measurable_eligible S n r row.val.1)
  have hr := measurable_filterMapQuery (fun row J => codeCandidateQ S n (canonicalRows S n J) r row)
    hc (MC.Rows S n).attach
  have hm : Measurable (fun q : List (Code S n) × ℕ =>
      let sorted := sortQuery (codeCompareQ S n) q.1
      (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) :=
    measurable_of_countable _
  have he : (fun J : Input S n => codeUniverseQ S n (canonicalRows S n J) r) =
      (fun J : Input S n =>
        let q := filterMapQuery (codeCandidateQ S n (canonicalRows S n J) r) (MC.Rows S n).attach
        let sorted := sortQuery (codeCompareQ S n) q.1
        (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) := by
    funext J
    exact codeUniverse_factor S n J r
  rw [he]
  exact hm.comp hr

private theorem measurable_center (S : OddScale) (n : ℕ) (lambda : ℝ)
    (K : ℕ) (codes : MD.FourCodes) (g : Grid K) :
    Measurable (fun J : Input S n => centerQ S n (canonicalRows S n J) lambda K codes g) := by
  cases hf : (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).value with
  | none => simp only [centerQ,hf]; exact measurable_const
  | some v =>
    have hp := measurable_pointSnapshotQuery lambda
      (fun J : Input S n => J (SR.decode S n v.1))
      (fun _ : Input S n => (gridPointQuery K g).1)
      (measurable_pi_apply _) measurable_const
    have he : (fun J : Input S n => centerQ S n (canonicalRows S n J) lambda K codes g) =
        (fun J : Input S n =>
          ((pointSnapshotQuery lambda (J (SR.decode S n v.1)) (gridPointQuery K g).1).1,
            (anchorCodeQ codes).2+(MD.atlasQ S n).operations+
              (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).operations+
              (incomingBudget S n+canonicalExtra S n)+readFee v.1 (SR.indices (SR.count S n))+
              (gridPointQuery K g).2+24+3)) := by
      funext J
      simp only [centerQ,hf,incoming_read,canonical_incoming_fee,read_fee,incoming_labels,
        pointSnapshotQuery_cost]
    rw [he]
    exact hp.fst.prodMk measurable_const

private theorem measurable_triangle (S : OddScale) (n : ℕ) (lambda : ℝ)
    (c : SR.Index S n → ℕ) (code : MD.Code)
    (center : JointInput S n → Space) (hc : Measurable center) :
    Measurable (fun z : JointInput S n =>
      triangleCodeQ S n (canonicalRows S n z.1) lambda (sampleRows S n z.2 c) code (center z)) := by
  cases hf : (MD.atlasReadQ code (MD.atlasQ S n).value).value with
  | none => simp only [triangleCodeQ,hf]; exact measurable_const
  | some v =>
    let x := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n (canonicalRows S n z.1)).value (sampleRows S n z.2 c) v.1
    let y := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n (canonicalRows S n z.1)).value (sampleRows S n z.2 c) v.2.1
    let z' := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n (canonicalRows S n z.1)).value (sampleRows S n z.2 c) v.2.2
    have hx : Measurable x := measurable_point S n lambda c v.1
    have hy : Measurable y := measurable_point S n lambda c v.2.1
    have hz : Measurable z' := measurable_point S n lambda c v.2.2
    have hq : Measurable (fun z : JointInput S n =>
        triangleQuery ![(x z).1,(y z).1,(z' z).1] (center z) 2) := by
      apply measurable_triangleQuery
      · intro i j
        fin_cases i
        · exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hx.fst
        · exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hy.fst
        · exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hz.fst
      · intro j
        exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hc
      · exact measurable_const
    have hcost : Measurable (fun z : JointInput S n =>
        (MD.atlasQ S n).operations+(MD.atlasReadQ code (MD.atlasQ S n).value).operations+
          (incomingBudget S n+canonicalExtra S n)+(x z).2+(y z).2+(z' z).2+
          (triangleQuery ![(x z).1,(y z).1,(z' z).1] (center z) 2).2+4) :=
      (((((measurable_const.add hx.snd).add hy.snd).add hz.snd).add hq.snd).add measurable_const)
    convert hq.fst.prodMk hcost using 1
    funext z
    simp only [triangleCodeQ,hf,canonical_incoming_fee,x,y,z']

/-- Generic full grid/triangle paid fold. Spatial measurability is proved by
its supplied individual query proofs; only Bool/Nat postprocessing is discrete. -/
private theorem measurable_paid_event_fold {Ω G A : Type*} [MeasurableSpace Ω]
    (grid : List G) (gridCost : ℕ) (codes : List A)
    (center : G → Ω → Space × ℕ) (triangle : A → Ω → Space → Bool × ℕ)
    (hc : ∀ g, Measurable (center g))
    (ht : ∀ g a, Measurable (fun z => triangle a z (center g z).1)) :
    Measurable (fun z : Ω =>
      let query := listAnyQuery (fun g =>
        let c := center g z
        let tests := listAllQuery (fun a => triangle a z c.1) codes
        (tests.1,c.2+tests.2+2)) grid
      (query.1,gridCost+query.2+1)) := by
  have hg (g : G) : Measurable (fun z : Ω =>
      let c := center g z
      let tests := listAllQuery (fun a => triangle a z c.1) codes
      (tests.1,c.2+tests.2+2)) := by
    have hall : Measurable (fun z : Ω =>
        listAllQuery (fun a => triangle a z (center g z).1) codes) :=
      measurable_listAllQuery (fun a z => triangle a z (center g z).1) (ht g) codes
    have hp : Measurable (fun v : (Bool × ℕ) × ℕ =>
        (v.1.1,v.2+v.1.2+2)) := measurable_of_countable _
    exact hp.comp (hall.prodMk (hc g).snd)
  have hq := measurable_listAnyQuery _ hg grid
  have hp : Measurable (fun v : Bool × ℕ => (v.1,gridCost+v.2+1)) :=
    measurable_of_countable _
  exact hp.comp hq

private theorem measurable_codeEvent (S : OddScale) (n : ℕ) (lambda : ℝ)
    (K : ℕ) (c : SR.Index S n → ℕ) (row : Code S n) :
    Measurable (fun z : JointInput S n =>
      codeEventQ S n (canonicalRows S n z.1) lambda K row (sampleRows S n z.2 c)) := by
  let center : Grid K → JointInput S n → Space × ℕ :=
    fun g z => centerQ S n (canonicalRows S n z.1) lambda K row.val.1 g
  let triangle : MD.Code → JointInput S n → Space → Bool × ℕ :=
    fun a z w => triangleCodeQ S n (canonicalRows S n z.1) lambda (sampleRows S n z.2 c) a w
  have hc (g : Grid K) : Measurable (center g) :=
    (measurable_center S n lambda K row.val.1 g).comp
      (measurable_fst : Measurable (fun z : JointInput S n => z.1))
  have ht (g : Grid K) (a : MD.Code) :
      Measurable (fun z : JointInput S n => triangle a z (center g z).1) :=
    measurable_triangle S n lambda c a _ (hc g).fst
  have hm := measurable_paid_event_fold (gridListQuery K).1 (gridListQuery K).2
    (MC.codeList row.val.1) center triangle hc ht
  have he : (fun z : JointInput S n =>
      codeEventQ S n (canonicalRows S n z.1) lambda K row (sampleRows S n z.2 c)) =
      (fun z : JointInput S n =>
        let query := listAnyQuery (fun g =>
          let w := center g z
          let tests := listAllQuery (fun a => triangle a z w.1) (MC.codeList row.val.1)
          (tests.1,w.2+tests.2+2)) (gridListQuery K).1
        (query.1,(gridListQuery K).2+query.2+1)) := by
    funext z
    rfl
  rw [he]
  exact hm

private theorem scan_curry {A W Ω : Type*}
    (q : Ω → A → W → Bool × ℕ) (f : Ω → W) (L : List A) (z : Ω) :
    scanQuery (fun a w => q w a (f w)) L z = scanQuery (q z) L (f z) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [scanQuery,ih]

/-- Prove dependent-input scan measurability with abstract label/state types.
Only the already proved paid geometric-query measurability is substituted later. -/
private theorem measurable_scan_curry {A W Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace (Option A)]
    (q : Ω → A → W → Bool × ℕ) (f : Ω → W)
    (hq : ∀ a, Measurable (fun z => q z a (f z))) (L : List A) :
    Measurable (fun z => scanQuery (q z) L (f z)) := by
  have he : (fun z => scanQuery (q z) L (f z)) =
      scanQuery (fun a z => q z a (f z)) L := by
    funext z
    exact (scan_curry q f L z).symm
  rw [he]
  exact measurable_scanQuery (fun a z => q z a (f z)) hq L

/-- Countable candidate-list selection plus its original preprocessing charge,
proved before any concrete generated-row carrier or geometric interpreter. -/
private theorem measurable_paid_scan {Ω A W : Type*} [MeasurableSpace Ω]
    [Countable A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (Option A)] [MeasurableSingletonClass (Option A)]
    (q : Ω → A → W → Bool × ℕ) (f : Ω → W)
    (hq : ∀ a, Measurable (fun z => q z a (f z)))
    (candidates : Ω → List A × ℕ) (hu : Measurable candidates) :
    Measurable (fun z : Ω =>
      let scan := scanQuery (q z) (candidates z).1 (f z)
      (scan.1,(candidates z).2+scan.2+1)) := by
  have hscan (L : List A) : Measurable (fun z : Ω => scanQuery (q z) L (f z)) :=
    measurable_scan_curry q f hq L
  have hm : Measurable (fun z : Ω × List A => scanQuery (q z.1) z.2 (f z.1)) :=
    measurable_from_prod_countable_left hscan
  have hs := hm.comp (measurable_id.prodMk hu.fst)
  have hp : Measurable (fun v : (Option A × ℕ) × ℕ =>
      (v.1.1,v.2+v.1.2+1)) := measurable_of_countable _
  exact hp.comp (hs.prodMk hu.snd)

private theorem measurable_codeScan (S : OddScale) (n : ℕ) (r lambda : ℝ)
    (K : ℕ) (c : SR.Index S n → ℕ) :
    Measurable (fun z : JointInput S n =>
      codeScanQ S n (canonicalRows S n z.1) r lambda K (sampleRows S n z.2 c)) := by
  let q : JointInput S n → Code S n → SR.Rows (SR.Index S n) → Bool × ℕ :=
    fun z => codeEventQ S n (canonicalRows S n z.1) lambda K
  let f : JointInput S n → SR.Rows (SR.Index S n) := fun z => sampleRows S n z.2 c
  let candidates : JointInput S n → List (Code S n) × ℕ :=
    fun z => codeUniverseQ S n (canonicalRows S n z.1) r
  have hq (a : Code S n) : Measurable (fun z : JointInput S n => q z a (f z)) :=
    measurable_codeEvent S n lambda K c a
  have hu : Measurable candidates :=
    (measurable_universe S n r).comp
      (measurable_fst : Measurable (fun z : JointInput S n => z.1))
  have hm := measurable_paid_scan q f hq candidates hu
  have he : (fun z : JointInput S n =>
      codeScanQ S n (canonicalRows S n z.1) r lambda K (sampleRows S n z.2 c)) =
      (fun z : JointInput S n =>
        let scan := scanQuery (q z) (candidates z).1 (f z)
        (scan.1,(candidates z).2+scan.2+1)) := by
    funext z
    rfl
  rw [he]
  exact hm

private def refreshFee {A : Type*} [DecidableEq A] (U : List A) : List A → ℕ
  | [] => 0
  | a::L => (BDL26NativeStateRows.memberQ a U).operations+
      (if (BDL26NativeStateRows.memberQ a U).value then 7 else 1)+refreshFee U L+3

private theorem refresh_fee {A : Type*} [DecidableEq A]
    (T : BDL26NativeStateRows.Samples A) (U : List A)
    (R : BDL26NativeStateRows.Rows A) :
    (BDL26NativeStateRows.refreshQ T U R).operations = refreshFee U (R.map Prod.fst) := by
  change (BDL26NativeStateRows.mapQ (BDL26NativeStateRows.refreshRowQ T U) R).operations = _
  induction R with
  | nil => rfl
  | cons row R ih =>
      cases h : (BDL26NativeStateRows.memberQ row.1 U).value <;>
        simp only [BDL26NativeStateRows.mapQ,BDL26NativeStateRows.refreshRowQ,h,
          Bool.false_eq_true,if_false,if_true,List.map_cons,refreshFee,ih]


abbrev State (S : OddScale) (n : ℕ) := SR.Rows (SR.Index S n) × Trace S n

/-- Every prefix executes actual scans, actual native refresh, and paid growing
append. Incoming rows are retained, not reconstructed from a caller history. -/
def prefixQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ → PrefixRun (State S n)
  | 0 => let q := SR.initializeQ S n T; ⟨(q.value,[]),q.operations+1⟩
  | m+1 =>
    let prior := prefixQ S n I r lambda K T m
    let chosen := codeScanQ S n I r lambda K prior.value.1
    let updated := SR.refreshQ T (codeSupport S n chosen.1) prior.value.1
    let appended := BDL26NativeMasterCandidates.appendQ prior.value.2 [chosen.1]
    ⟨(updated.value,appended.value),
      prior.operations+chosen.2+updated.operations+appended.operations+4⟩

/-- Countable image of the actual prefix, with its own actual numeric cost. -/
def countedPrefix (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ → CountState S n
  | 0 => ((fun _ => 0),[],incomingBudget S n+1)
  | m+1 =>
    let prior := countedPrefix S n I r lambda K T m
    let chosen := codeScanQ S n I r lambda K (sampleRows S n T prior.1)
    (SR.advanceList (codeSupport S n chosen.1) prior.1,
      prior.2.1++[chosen.1],
      prior.2.2+chosen.2+refreshFee (codeSupport S n chosen.1)
        (SR.indices (SR.count S n))+(2*prior.2.1.length+1)+4)

theorem prefix_counted (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n I r lambda K T m).value.1 =
      sampleRows S n T (countedPrefix S n I r lambda K T m).1 ∧
    (prefixQ S n I r lambda K T m).value.2 =
      (countedPrefix S n I r lambda K T m).2.1 ∧
    (prefixQ S n I r lambda K T m).operations =
      (countedPrefix S n I r lambda K T m).2.2 := by
  induction m with
  | zero =>
    exact ⟨SR.initialize_value S n T,rfl,
      congrArg (fun k => k+1) (BDL26NativeStateRows.initialize_cost S n T).1⟩
  | succ m ih =>
    refine ⟨?_,?_,?_⟩
    · change (SR.refreshQ T _ _).value = _
      rw [ih.1]
      exact SR.refresh_value T _ _ _
    · change (BDL26NativeMasterCandidates.appendQ _ [_]).value = _
      rw [(BDL26NativeMasterCandidates.append_spec _ _).1,ih.2.1,ih.1]
      rfl
    · change (prefixQ S n I r lambda K T m).operations+_+_+_+4 = _
      rw [ih.2.2,refresh_fee,ih.1,sample_labels,
        (BDL26NativeMasterCandidates.append_spec _ _).2.1,ih.2.1]
      rfl

/-- Same native row state and same stable code trace, including bad inputs. -/
theorem prefix_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n I r lambda K T m).value.1 =
      (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m).value.rows ∧
    (prefixQ S n I r lambda K T m).value.2 =
      (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m).value.trace.map
        (eraseChoice S n (rowMap S n I) r) ∧
    (prefixQ S n I r lambda K T m).operations ≤ multiplier I*
      (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m).operations := by
  induction m with
  | zero =>
    exact ⟨rfl,rfl,self_scale _ _ (multiplier_one I)⟩
  | succ m ih =>
    let old := BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m
    let q := BDL26NativeKeyExecutionBridge.scanQ S n (rowMap S n I) hr lambda K old.value.rows
    have hs := scan_refinement S n I r lambda K old.value.rows
    rw [BDL26NativeGeometricJointExecution.code_scan_refinement S n (rowMap S n I) hr] at hs
    have hu : codeSupport S n (eraseChoice S n (rowMap S n I) r q.1) =
        chosenSupport S n (rowMap S n I) r q.1 := by cases q.1 <;> rfl
    have hd := multiplier_one I
    have hl := congrArg List.length ih.2.1
    simp only [List.length_map] at hl
    refine ⟨?_,?_,?_⟩
    · change (SR.refreshQ T _ _).value = _
      rw [ih.1,hs.1,hu]
      rfl
    · change (BDL26NativeMasterCandidates.appendQ _ [_]).value =
        (BDL26NativeMasterCandidates.appendQ old.value.trace [q.1]).value.map _
      rw [(BDL26NativeMasterCandidates.append_spec _ _).1,
        (BDL26NativeMasterCandidates.append_spec _ _).1,List.map_append,
        ih.2.1,ih.1,hs.1]
      rfl
    · change (prefixQ S n I r lambda K T m).operations+_+_+_+4 ≤
        multiplier I*(old.operations+q.2+
          (SR.refreshQ T (chosenSupport S n (rowMap S n I) r q.1) old.value.rows).operations+
          (BDL26NativeMasterCandidates.appendQ old.value.trace [q.1]).operations+4)
      rw [ih.1,hs.1,hu,(BDL26NativeMasterCandidates.append_spec _ _).2.1,
        (BDL26NativeMasterCandidates.append_spec _ _).2.1,hl]
      nlinarith [ih.2.2,hs.2]


/-- Finite-fuel implementation. Fuel is observational; its branches inspect
actual paid scans and never invoke the mathematical halt-time function. -/
def stopFromQ (S : OddScale) (n : ℕ) (I : Rows S n) (r lambda : ℝ) (K : ℕ)
    (T : NativeTable S n) : ℕ → State S n →
      PrefixRun (State S n × Option (List (SR.Index S n × Space)))
  | 0,state => ⟨(state,none),0⟩
  | fuel+1,state =>
    let query := codeScanQ S n I r lambda K state.1
    match query.1 with
    | none =>
      let out := BDL26NativeStateRows.emitQ state.1
      ⟨(state,some out.value),query.2+out.operations+3⟩
    | some row =>
      let refreshed := SR.refreshQ T (codeSupport S n (some row)) state.1
      let appended := BDL26NativeMasterCandidates.appendQ state.2 [some row]
      let rest := stopFromQ S n I r lambda K T fuel (refreshed.value,appended.value)
      ⟨rest.value,query.2+refreshed.operations+appended.operations+rest.operations+4⟩

def stopQ (S : OddScale) (n : ℕ) (I : Rows S n) (r lambda : ℝ) (K : ℕ)
    (T : NativeTable S n) (fuel : ℕ) :=
  let init := SR.initializeQ S n T
  let rest := stopFromQ S n I r lambda K T fuel (init.value,[])
  (⟨rest.value,init.operations+rest.operations+1⟩ :
    PrefixRun (State S n × Option (List (SR.Index S n × Space))))

def choice (S : OddScale) (n : ℕ) (I : Rows S n) (r lambda : ℝ) (K : ℕ)
    (T : NativeTable S n) (m : ℕ) : Option (Code S n) :=
  (codeScanQ S n I r lambda K (prefixQ S n I r lambda K T m).value.1).1

private theorem choice_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0≤r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    choice S n I r lambda K T m = eraseChoice S n (rowMap S n I) r
      (BDL26NativeGeometricExecution.choice S n (rowMap S n I) hr lambda K T m) := by
  unfold choice BDL26NativeGeometricExecution.choice
  rw [(prefix_refinement S n I hr lambda K T m).1,
    (scan_refinement S n I r lambda K _).1,
    BDL26NativeGeometricJointExecution.code_scan_refinement]

/-- First-hit recursion proved on abstract state/output carriers. The premises
are the actual defining equations of the interpreter, not a halting certificate. -/
private theorem first_none_loop {A C B : Type*}
    (statesAt : ℕ → A) (fee : ℕ → ℕ) (query : A → Option C × ℕ)
    (advance : A → C → A) (advanceFee : A → C → ℕ)
    (emit : A → B) (emitFee : A → ℕ)
    (stop : ℕ → A → PrefixRun (A × Option B))
    (hprefix : ∀ m row, (query (statesAt m)).1 = some row →
      statesAt (m+1) = advance (statesAt m) row)
    (hfee : ∀ m row, (query (statesAt m)).1 = some row →
      fee (m+1) = fee m+(query (statesAt m)).2+advanceFee (statesAt m) row+4)
    (hnone : ∀ fuel state, (query state).1 = none →
      stop (fuel+1) state = ⟨(state,some (emit state)),(query state).2+emitFee state+3⟩)
    (hsome : ∀ fuel state row, (query state).1 = some row →
      stop (fuel+1) state =
        ⟨(stop fuel (advance state row)).value,
          (query state).2+advanceFee state row+(stop fuel (advance state row)).operations+4⟩)
    (d : ℕ) : ∀ m,
      (∀ i<d, (query (statesAt (m+i))).1 ≠ none) →
      (query (statesAt (m+d))).1 = none →
      (stop (d+1) (statesAt m)).value = (statesAt (m+d),some (emit (statesAt (m+d)))) ∧
      fee m+(stop (d+1) (statesAt m)).operations =
        fee (m+d)+(query (statesAt (m+d))).2+emitFee (statesAt (m+d))+3 := by
  induction d with
  | zero =>
      intro m hb hs
      simp only [Nat.add_zero] at hs ⊢
      rw [hnone 0 (statesAt m) hs]
      constructor
      · rfl
      · change fee m+((query (statesAt m)).2+emitFee (statesAt m)+3) =
          fee m+(query (statesAt m)).2+emitFee (statesAt m)+3
        simp only [Nat.add_assoc]
  | succ d ih =>
      intro m hb hs
      have hne := hb 0 (by omega)
      simp only [Nat.add_zero] at hne
      cases hq : (query (statesAt m)).1 with
      | none => exact False.elim (hne hq)
      | some row =>
          have hb' : ∀ i<d, (query (statesAt (m+1+i))).1 ≠ none := by
            intro i hi
            simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hb (i+1) (by omega)
          have hs' : (query (statesAt (m+1+d))).1 = none := by
            simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hs
          have hrec := ih (m+1) hb' hs'
          have hm : m+1+d=m+(d+1) := by omega
          rw [hm] at hrec
          rw [hsome (d+1) (statesAt m) row hq,←hprefix m row hq]
          have hf := hfee m row hq
          refine ⟨hrec.1,?_⟩
          dsimp only
          omega

/-- Reassociate fees on abstract values, before native rows or scans occur.
This changes no interpreter operation; both constructors retain the same value. -/
private theorem prefixRun_fee_group {A : Type*} (rest : PrefixRun A)
    (query refresh append : ℕ) :
    (⟨rest.value,query+refresh+append+rest.operations+4⟩ : PrefixRun A) =
      ⟨rest.value,query+(refresh+append)+rest.operations+4⟩ := by
  have h : query+refresh+append+rest.operations+4 =
      query+(refresh+append)+rest.operations+4 := by omega
  exact congrArg (fun fee : ℕ => (⟨rest.value,fee⟩ : PrefixRun A)) h

private theorem stop_at_first_none (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (d : ℕ) :
    ∀ m : ℕ,
      (∀ i<d,choice S n I r lambda K T (m+i)≠none) →
      choice S n I r lambda K T (m+d)=none →
      (stopFromQ S n I r lambda K T (d+1) (prefixQ S n I r lambda K T m).value).value =
        ((prefixQ S n I r lambda K T (m+d)).value,
          some (BDL26NativeStateRows.emitQ
            (prefixQ S n I r lambda K T (m+d)).value.1).value) ∧
      (prefixQ S n I r lambda K T m).operations+
        (stopFromQ S n I r lambda K T (d+1) (prefixQ S n I r lambda K T m).value).operations =
        (prefixQ S n I r lambda K T (m+d)).operations+
          (codeScanQ S n I r lambda K (prefixQ S n I r lambda K T (m+d)).value.1).2+
          (BDL26NativeStateRows.emitQ
            (prefixQ S n I r lambda K T (m+d)).value.1).operations+3 := by
  let query : State S n → Option (Code S n) × ℕ :=
    fun state => codeScanQ S n I r lambda K state.1
  let advance : State S n → Code S n → State S n := fun state row =>
    ((SR.refreshQ T (codeSupport S n (some row)) state.1).value,
      (BDL26NativeMasterCandidates.appendQ state.2 [some row]).value)
  let advanceFee : State S n → Code S n → ℕ := fun state row =>
    (SR.refreshQ T (codeSupport S n (some row)) state.1).operations+
      (BDL26NativeMasterCandidates.appendQ state.2 [some row]).operations
  have hp : ∀ m row, (query (prefixQ S n I r lambda K T m).value).1=some row →
      (prefixQ S n I r lambda K T (m+1)).value=
        advance (prefixQ S n I r lambda K T m).value row := by
    intro m row hq
    dsimp only [query] at hq
    simp only [prefixQ,query,advance,hq]
  have hc : ∀ m row, (query (prefixQ S n I r lambda K T m).value).1=some row →
      (prefixQ S n I r lambda K T (m+1)).operations=
        (prefixQ S n I r lambda K T m).operations+
          (query (prefixQ S n I r lambda K T m).value).2+
          advanceFee (prefixQ S n I r lambda K T m).value row+4 := by
    intro m row hq
    dsimp only [query] at hq
    simp only [prefixQ,hq,query,advanceFee]
    omega
  have hn : ∀ fuel state, (query state).1=none →
      stopFromQ S n I r lambda K T (fuel+1) state =
        ⟨(state,some (BDL26NativeStateRows.emitQ state.1).value),
          (query state).2+(BDL26NativeStateRows.emitQ state.1).operations+3⟩ := by
    intro fuel state hq
    dsimp only [query] at hq
    simp only [stopFromQ,hq,query]
  have hs : ∀ fuel state row, (query state).1=some row →
      stopFromQ S n I r lambda K T (fuel+1) state =
        ⟨(stopFromQ S n I r lambda K T fuel (advance state row)).value,
          (query state).2+advanceFee state row+
            (stopFromQ S n I r lambda K T fuel (advance state row)).operations+4⟩ := by
    intro fuel state row hq
    dsimp only [query] at hq
    simp only [stopFromQ,hq]
    exact prefixRun_fee_group
      (stopFromQ S n I r lambda K T fuel (advance state row))
      (query state).2
      (SR.refreshQ T (codeSupport S n (some row)) state.1).operations
      (BDL26NativeMasterCandidates.appendQ state.2 [some row]).operations
  exact first_none_loop
    (A := State S n) (C := Code S n) (B := List (SR.Index S n × Space))
    (fun m => (prefixQ S n I r lambda K T m).value)
    (fun m => (prefixQ S n I r lambda K T m).operations)
    query advance advanceFee
    (fun state => (BDL26NativeStateRows.emitQ state.1).value)
    (fun state => (BDL26NativeStateRows.emitQ state.1).operations)
    (stopFromQ S n I r lambda K T) hp hc hn hs d

/-- Terminal emission is the native emitter. Nontermination retains the original
column-zero value; its mathematical paid cost is infinite. -/
def emitted (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : List (SR.Index S n × Space) :=
  (BDL26NativeStateRows.emitQ
    (prefixQ S n I r lambda K T
      (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value.1).value

def stoppedOperations (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ :=
  let prior := prefixQ S n I r lambda K T (nativeHaltTime S n (rowMap S n I) hr lambda K T)
  let terminal := codeScanQ S n I r lambda K prior.value.1
  let out := BDL26NativeStateRows.emitQ prior.value.1
  prior.operations+terminal.2+out.operations+3

/-- The wrapper retains the exact initial state; no scan is unfolded. -/
private theorem stop_initial_value (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (fuel : ℕ) :
    (stopQ S n I r lambda K T fuel).value =
      (stopFromQ S n I r lambda K T fuel
        (prefixQ S n I r lambda K T 0).value).value := by
  rfl

/-- The initialization charge is exactly the original fee plus one. -/
private theorem stop_initial_operations (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (fuel : ℕ) :
    (stopQ S n I r lambda K T fuel).operations =
      (prefixQ S n I r lambda K T 0).operations+
        (stopFromQ S n I r lambda K T fuel
          (prefixQ S n I r lambda K T 0).value).operations := by
  change (SR.initializeQ S n T).operations+
      (stopFromQ S n I r lambda K T fuel
        ((SR.initializeQ S n T).value,[])).operations+1 =
    ((SR.initializeQ S n T).operations+1)+
      (stopFromQ S n I r lambda K T fuel
        ((SR.initializeQ S n T).value,[])).operations
  exact initial_fee_reassociate _ _ _ rfl

/-- The charged stopped-prefix formula is exactly the cost of the finite-fuel
program stopped by its first actual no-event branch. -/
theorem stopping_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0≤r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : NativeHalts S n (rowMap S n I) hr lambda K T) :
    (stopQ S n I r lambda K T (nativeHaltTime S n (rowMap S n I) hr lambda K T+1)).value =
      ((prefixQ S n I r lambda K T (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value,
        some (emitted S n I hr lambda K T)) ∧
    (stopQ S n I r lambda K T (nativeHaltTime S n (rowMap S n I) hr lambda K T+1)).operations =
      stoppedOperations S n I hr lambda K T := by
  have ht : nativeHaltTime S n (rowMap S n I) hr lambda K T=Nat.find h := by
    simp only [nativeHaltTime,dif_pos h]
  have hb : ∀ i<Nat.find h,choice S n I r lambda K T (0+i)≠none := by
    intro i hi hn
    rw [Nat.zero_add,choice_refinement S n I hr,eraseChoice,Option.map_eq_none_iff] at hn
    exact Nat.find_min h hi hn
  have hs : choice S n I r lambda K T (0+Nat.find h)=none := by
    rw [Nat.zero_add,choice_refinement S n I hr,eraseChoice,Option.map_eq_none_iff]
    exact Nat.find_spec h
  have hf := stop_at_first_none S n I r lambda K T (Nat.find h) 0 hb hs
  simp only [Nat.zero_add] at hf
  rw [←ht] at hf
  constructor
  · rw [stop_initial_value]
    simpa only [emitted] using hf.1
  · rw [stop_initial_operations]
    simpa only [stoppedOperations] using hf.2

def operationCost (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℝ≥0∞ :=
  if NativeHalts S n (rowMap S n I) hr lambda K T then
    (stoppedOperations S n I hr lambda K T : ℝ≥0∞) else ∞

theorem operationCost_bound (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    operationCost S n I hr lambda K T ≤
      (multiplier I : ℝ≥0∞)*nativeOperationCost S n (rowMap S n I) hr lambda K T := by
  by_cases h : NativeHalts S n (rowMap S n I) hr lambda K T
  · rw [operationCost,if_pos h,nativeOperationCost,if_pos h,
      (native_stopping_refinement S n (rowMap S n I) hr lambda K T h).2,←Nat.cast_mul]
    apply (Nat.cast_le (α := ℝ≥0∞)).mpr
    have hp := prefix_refinement S n I hr lambda K T
      (nativeHaltTime S n (rowMap S n I) hr lambda K T)
    have hs := scan_refinement S n I r lambda K
      (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T
        (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value.rows
    rw [BDL26NativeGeometricJointExecution.code_scan_refinement S n (rowMap S n I) hr] at hs
    have hl : (prefixQ S n I r lambda K T
        (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value.1.length=SR.count S n := by
      rw [(prefix_counted S n I r lambda K T _).1]
      simp only [sampleRows,BDL26NativeStateRows.rowsFor,List.length_map,
        BDL26NativeStateRows.indices_length]
    have he := (BDL26NativeStateRows.emit_cost
      (prefixQ S n I r lambda K T
        (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value.1).1
    rw [hl] at he
    dsimp only [stoppedOperations]
    rw [he,hp.1]
    have hd := multiplier_one I
    nlinarith [hp.2.2,hs.2]
  · rw [operationCost,if_neg h,nativeOperationCost,if_neg h]
    have hd : (1 : ℝ≥0∞) ≤ (multiplier I : ℝ≥0∞) := by
      exact_mod_cast multiplier_one I
    calc
      (∞ : ℝ≥0∞) = (1 : ℝ≥0∞)*∞ := (one_mul _).symm
      _ ≤ (multiplier I : ℝ≥0∞)*∞ := mul_le_mul' hd le_rfl
private theorem measurable_counted_step {A B : Type*} [Fintype A] [DecidableEq A]
    [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace (Option B)] [MeasurableSingletonClass (Option B)]
    (support : Option B → List A) (addresses : List A) :
    Measurable (fun w : ((A → ℕ) × List (Option B) × ℕ) × (Option B × ℕ) =>
      (SR.advanceList (support w.2.1) w.1.1,
        w.1.2.1++[w.2.1],
        w.1.2.2+w.2.2+refreshFee (support w.2.1) addresses+
          (2*w.1.2.1.length+1)+4)) :=
  measurable_of_countable _

/-- Compose the paid transition while the address and label carriers are abstract.
The successor equality is checked separately, without unfolding its actual scan. -/
private theorem measurable_counted_transition {Ω A B : Type*} [MeasurableSpace Ω]
    [Fintype A] [DecidableEq A]
    [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace (Option B)] [MeasurableSingletonClass (Option B)]
    (support : Option B → List A) (addresses : List A)
    (prior next : Ω → (A → ℕ) × List (Option B) × ℕ)
    (chosen : Ω → Option B × ℕ)
    (hp : Measurable prior) (hq : Measurable chosen)
    (he : ∀ z, next z =
      (SR.advanceList (support (chosen z).1) (prior z).1,
        (prior z).2.1++[(chosen z).1],
        (prior z).2.2+(chosen z).2+refreshFee (support (chosen z).1) addresses+
          (2*(prior z).2.1.length+1)+4)) : Measurable next := by
  have hm := measurable_counted_step support addresses
  have hc : Measurable (fun z : Ω =>
      (SR.advanceList (support (chosen z).1) (prior z).1,
        (prior z).2.1++[(chosen z).1],
        (prior z).2.2+(chosen z).2+refreshFee (support (chosen z).1) addresses+
          (2*(prior z).2.1.length+1)+4)) := hm.comp (hp.prodMk hq)
  have heq : next = (fun z : Ω =>
      (SR.advanceList (support (chosen z).1) (prior z).1,
        (prior z).2.1++[(chosen z).1],
        (prior z).2.2+(chosen z).2+refreshFee (support (chosen z).1) addresses+
          (2*(prior z).2.1.length+1)+4)) := funext he
  rw [heq]
  exact hc

private theorem countedPrefix_succ_pair (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    countedPrefix S n I r lambda K T (m+1) =
      (let prior := countedPrefix S n I r lambda K T m
       let chosen := codeScanQ S n I r lambda K (sampleRows S n T prior.1)
       (SR.advanceList (codeSupport S n chosen.1) prior.1,
         prior.2.1++[chosen.1],
         prior.2.2+chosen.2+refreshFee (codeSupport S n chosen.1)
           (SR.indices (SR.count S n))+(2*prior.2.1.length+1)+4)) := by
  rfl

/-- Compose a scan with the measurable counter projection on abstract carriers.
The chosen function is identified pointwise, before concrete native types occur. -/
private theorem measurable_prior_fst_query {Ω R E C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace E] [MeasurableSpace C]
    (prior : Ω → R × E) (query : Ω × R → C) (chosen : Ω → C)
    (hp : Measurable prior) (hq : Measurable query)
    (he : ∀ z, chosen z = query (z,(prior z).1)) : Measurable chosen := by
  have hm : Measurable (fun z : Ω => query (z,(prior z).1)) :=
    hq.comp (measurable_id.prodMk hp.fst)
  have heq : chosen = (fun z : Ω => query (z,(prior z).1)) := funext he
  rw [heq]
  exact hm

private theorem measurable_countedPrefix (S : OddScale) (n : ℕ)
    (r lambda : ℝ) (K m : ℕ) : Measurable (fun z : JointInput S n =>
      countedPrefix S n (canonicalRows S n z.1) r lambda K z.2 m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    let prior : JointInput S n → CountState S n :=
      fun z => countedPrefix S n (canonicalRows S n z.1) r lambda K z.2 m
    let chosen : JointInput S n → Option (Code S n) × ℕ :=
      fun z => codeScanQ S n (canonicalRows S n z.1) r lambda K (sampleRows S n z.2 (prior z).1)
    have hs : Measurable (fun w : JointInput S n × (SR.Index S n → ℕ) =>
        codeScanQ S n (canonicalRows S n w.1.1) r lambda K (sampleRows S n w.1.2 w.2)) :=
      measurable_from_prod_countable_left (measurable_codeScan S n r lambda K)
    have hp : Measurable prior := ih
    have hq : Measurable chosen :=
      measurable_prior_fst_query
        (Ω := JointInput S n) (R := SR.Index S n → ℕ)
        (E := Trace S n × ℕ) (C := Option (Code S n) × ℕ)
        prior
        (fun w : JointInput S n × (SR.Index S n → ℕ) =>
          codeScanQ S n (canonicalRows S n w.1.1) r lambda K (sampleRows S n w.1.2 w.2))
        chosen hp hs (fun _ => rfl)
    exact measurable_counted_transition (codeSupport S n) (SR.indices (SR.count S n))
      prior (fun z => countedPrefix S n (canonicalRows S n z.1) r lambda K z.2 (m+1)) chosen hp hq
      (fun z => countedPrefix_succ_pair S n (canonicalRows S n z.1) r lambda K z.2 m)

private theorem measurable_paid_selection (S : OddScale) (n : ℕ)
    (r lambda : ℝ) (K m : ℕ) : Measurable (fun z : JointInput S n =>
      codeScanQ S n (canonicalRows S n z.1) r lambda K
        (prefixQ S n (canonicalRows S n z.1) r lambda K z.2 m).value.1) := by
  have hp := measurable_countedPrefix S n r lambda K m
  have hs : Measurable (fun w : JointInput S n × (SR.Index S n → ℕ) =>
      codeScanQ S n (canonicalRows S n w.1.1) r lambda K
        (sampleRows S n w.1.2 w.2)) :=
    measurable_from_prod_countable_left (measurable_codeScan S n r lambda K)
  exact measurable_prior_fst_query
    (Ω := JointInput S n) (R := SR.Index S n → ℕ)
    (E := Trace S n × ℕ) (C := Option (Code S n) × ℕ)
    (fun z => countedPrefix S n (canonicalRows S n z.1) r lambda K z.2 m)
    (fun w : JointInput S n × (SR.Index S n → ℕ) =>
      codeScanQ S n (canonicalRows S n w.1.1) r lambda K (sampleRows S n w.1.2 w.2))
    (fun z => codeScanQ S n (canonicalRows S n z.1) r lambda K
      (prefixQ S n (canonicalRows S n z.1) r lambda K z.2 m).value.1)
    hp hs (fun z => by rw [(prefix_counted S n (canonicalRows S n z.1) r lambda K z.2 m).1])

theorem measurable_operationCost (S : OddScale) (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) : Measurable (fun z : JointInput S n =>
      operationCost S n (canonicalRows S n z.1) hr lambda K z.2) := by
  classical
  have hp : Measurable (fun w : JointInput S n × ℕ =>
      (countedPrefix S n (canonicalRows S n w.1.1) r lambda K w.1.2 w.2).2.2) :=
    measurable_from_prod_countable_left
      (fun m => (measurable_countedPrefix S n r lambda K m).snd.snd)
  have hq : Measurable (fun w : JointInput S n × ℕ =>
      (codeScanQ S n (canonicalRows S n w.1.1) r lambda K
        (prefixQ S n (canonicalRows S n w.1.1) r lambda K w.1.2 w.2).value.1).2) :=
    measurable_from_prod_countable_left
      (fun m => (measurable_paid_selection S n r lambda K m).snd)
  have hs := measurable_id.prodMk
    (BDL26NativeGeometricJointExecution.measurable_native_clock S n hr lambda K)
  have hfinite : Measurable (fun z : JointInput S n =>
      (((countedPrefix S n (canonicalRows S n z.1) r lambda K z.2
        (nativeHaltTime S n z.1 hr lambda K z.2)).2.2+
      (codeScanQ S n (canonicalRows S n z.1) r lambda K
        (prefixQ S n (canonicalRows S n z.1) r lambda K z.2
          (nativeHaltTime S n z.1 hr lambda K z.2)).value.1).2+
      5*SR.count S n+3 : ℕ) : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      ((((hp.comp hs).add (hq.comp hs)).add_const _).add_const _)
  letI haltDecidable : DecidablePred (fun z : JointInput S n =>
      NativeHalts S n z.1 hr lambda K z.2) := fun z => Classical.propDecidable _
  have hbranch : Measurable (fun z : JointInput S n =>
      if NativeHalts S n z.1 hr lambda K z.2 then
        (((countedPrefix S n (canonicalRows S n z.1) r lambda K z.2
          (nativeHaltTime S n z.1 hr lambda K z.2)).2.2+
        (codeScanQ S n (canonicalRows S n z.1) r lambda K
          (prefixQ S n (canonicalRows S n z.1) r lambda K z.2
            (nativeHaltTime S n z.1 hr lambda K z.2)).value.1).2+
        5*SR.count S n+3 : ℕ) : ℝ≥0∞)
      else ∞) :=
    Measurable.ite
      (BDL26NativeGeometricJointExecution.measurableSet_native_halts S n hr lambda K)
      hfinite (measurable_const (a := (∞ : ℝ≥0∞)))
  convert hbranch using 1
  funext z
  have he := prefix_counted S n (canonicalRows S n z.1) r lambda K z.2
    (nativeHaltTime S n z.1 hr lambda K z.2)
  have hl : (prefixQ S n (canonicalRows S n z.1) r lambda K z.2
      (nativeHaltTime S n z.1 hr lambda K z.2)).value.1.length=SR.count S n := by
    rw [he.1]
    simp only [sampleRows,BDL26NativeStateRows.rowsFor,List.length_map,
      BDL26NativeStateRows.indices_length]
  simp only [operationCost,stoppedOperations,rowMap_canonical,he.2.2,
    (BDL26NativeStateRows.emit_cost _).1,hl]

private theorem prefix_original_cost_le (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m).operations ≤
      (prefixQ S n I r lambda K T m).operations := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    have hp := prefix_refinement S n I hr lambda K T m
    have hs := lower_scan_refinement S n I r lambda K
      (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m).value.rows
    rw [BDL26NativeGeometricJointExecution.code_scan_refinement S n (rowMap S n I) hr] at hs
    have hu : ∀ q, codeSupport S n (eraseChoice S n (rowMap S n I) r q)=
        chosenSupport S n (rowMap S n I) r q := by intro q; cases q <;> rfl
    have hl := congrArg List.length hp.2.1
    simp only [List.length_map] at hl
    simp only [Nat.one_mul] at hs
    change _+_+_+_+4≤(prefixQ S n I r lambda K T m).operations+_+_+_+4
    rw [hp.1,←hs.1,hu,(BDL26NativeMasterCandidates.append_spec _ _).2.1,
      (BDL26NativeMasterCandidates.append_spec _ _).2.1,hl]
    omega

private theorem stopped_original_cost_le (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : NativeHalts S n (rowMap S n I) hr lambda K T) :
    (BDL26NativeGeometricExecutionCost.stopQ S n (rowMap S n I) hr lambda K T
      (nativeHaltTime S n (rowMap S n I) hr lambda K T+1)).operations ≤
      stoppedOperations S n I hr lambda K T := by
  have hp := prefix_refinement S n I hr lambda K T
    (nativeHaltTime S n (rowMap S n I) hr lambda K T)
  have hc := prefix_original_cost_le S n I hr lambda K T
    (nativeHaltTime S n (rowMap S n I) hr lambda K T)
  have hs := lower_scan_refinement S n I r lambda K
    (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T
      (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value.rows
  rw [BDL26NativeGeometricJointExecution.code_scan_refinement S n (rowMap S n I) hr] at hs
  simp only [Nat.one_mul] at hs
  have hl : (prefixQ S n I r lambda K T
      (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value.1.length=SR.count S n := by
    rw [(prefix_counted S n I r lambda K T _).1]
    simp only [sampleRows,BDL26NativeStateRows.rowsFor,List.length_map,
      BDL26NativeStateRows.indices_length]
  rw [(native_stopping_refinement S n (rowMap S n I) hr lambda K T h).2]
  dsimp only [stoppedOperations]
  rw [(BDL26NativeStateRows.emit_cost _).1,hl,hp.1]
  omega

/-- The exact nonnegative residual is derived from the two actual interpreters.
It contains precisely the extra incoming callback-read charges, whose primitive
decomposition is incoming_fee. No upper bound is used as a runtime cost. -/
def additionalIncomingCost (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℝ≥0∞ :=
  if NativeHalts S n (rowMap S n I) hr lambda K T then
    ((stoppedOperations S n I hr lambda K T-
      (BDL26NativeGeometricExecutionCost.stopQ S n (rowMap S n I) hr lambda K T
        (nativeHaltTime S n (rowMap S n I) hr lambda K T+1)).operations : ℕ) : ℝ≥0∞)
  else 0

theorem operationCost_decomposition (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    operationCost S n I hr lambda K T =
      nativeOperationCost S n (rowMap S n I) hr lambda K T+
        additionalIncomingCost S n I hr lambda K T := by
  by_cases h : NativeHalts S n (rowMap S n I) hr lambda K T
  · have he := Nat.add_sub_of_le (stopped_original_cost_le S n I hr lambda K T h)
    simp only [operationCost,nativeOperationCost,additionalIncomingCost,if_pos h]
    rw [←Nat.cast_add,he]
  · simp only [operationCost,nativeOperationCost,additionalIncomingCost,if_neg h,add_zero]

end Paid

private theorem native_count_card (S : OddScale) (n : ℕ) :
    SR.count S n=Fintype.card (Vertex (Presentation S n)) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (SR.decode S n)

private theorem emitted_rows (S : OddScale) (n : ℕ) (I : Rows S n)
    {L : ℝ} (p : GeometricParameters L) (T : NativeTable S n) :
    Paid.emitted S n I (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T =
      (SR.indices (SR.count S n)).map (fun a =>
        (a,nativeOutput S n (rowMap S n I) p T (SR.decode S n a))) := by
  let m := nativeHaltTime S n (rowMap S n I) (radius_nonneg p)
    p.lambda ((6*p.m+2)*p.lambda) T
  let c := (Paid.countedPrefix S n I (anchorRadius p.m) p.lambda
    ((6*p.m+2)*p.lambda) T m).1
  have he := Paid.prefix_counted S n I (anchorRadius p.m) p.lambda
    ((6*p.m+2)*p.lambda) T m
  have hn := Paid.prefix_refinement S n I (radius_nonneg p) p.lambda
    ((6*p.m+2)*p.lambda) T m
  unfold Paid.emitted
  rw [he.1]
  change (BDL26NativeStateRows.emitQ (SR.rowsFor _ _ _)).value = _
  rw [BDL26NativeStateRows.emit_value]
  apply List.map_congr_left
  intro a ha
  apply congrArg (fun w : Space => (a,w))
  change T (a,c a) = originalPoints S n
    (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda) T m).value.rows (SR.decode S n a)
  rw [←hn.1,he.1]
  exact (Paid.sample_point S n T c a).symm

/-- Both incoming and native-returned assignments are read by first-match
queries, then the original counted affine snapshot is evaluated. -/
def perturbRowsQ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (I : Rows (perturbationOddScale p) n)
    (W : List (SR.Index (perturbationOddScale p) n × Space)) :
    Rows (perturbationOddScale p) n × ℕ :=
  mapQuery (fun v =>
    let j := pointRowQuery v I
    let w := pointRowQuery ((SR.decode (perturbationOddScale p) n).symm v) W
    let q := pointSnapshotQuery p.lambda j.1 w.1
    ((v,q.1),j.2+w.2+q.2+3)) (vertexInputList (Presentation (perturbationOddScale p) n))

def nativePerturbed {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : NativeTable (perturbationOddScale p) n) : StageMaps p n :=
  perturbedMap (Presentation (perturbationOddScale p) n) J p.lambda
    (nativeOutput (perturbationOddScale p) n J p T)

def successor {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : NativeTable (perturbationOddScale p) n) : StageMaps p (n+1) :=
  replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
    (nativePerturbed p n J T)

private theorem perturbRows_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (I : Rows (perturbationOddScale p) n) (T : NativeTable (perturbationOddScale p) n) :
    (perturbRowsQ p n I (Paid.emitted _ n I (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T)).1 =
    canonicalRows (perturbationOddScale p) n
      (nativePerturbed p n (rowMap _ n I) T) := by
  rw [perturbRowsQ,mapQuery_value,emitted_rows]
  apply List.map_congr_left
  intro v hv
  have hw := pointRowQuery_map
    (fun a => nativeOutput (perturbationOddScale p) n (rowMap _ n I) p T
      (SR.decode (perturbationOddScale p) n a))
    ((SR.decode (perturbationOddScale p) n).symm v)
    (SR.indices (SR.count (perturbationOddScale p) n)) (SR.indices_complete _ _)
  simp only [hw,pointSnapshotQuery_value,Equiv.apply_symm_apply,nativePerturbed,
    perturbedMap,rowMap,canonicalRows]

private theorem materialize_canonical_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) :
    (materializeRows p n (canonicalRows (perturbationOddScale p) n J)).1 =
      canonicalRows (perturbationOddScale p) (n+1)
        (replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n) J) := by
  rw [materializeRows,mapQuery_value]
  apply List.map_congr_left
  intro v hv
  change (v,(PointCode.run (canonicalRows (perturbationOddScale p) n J)
    (successorCode p n v)).1) =
      (v,replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n) J v)
  exact congrArg (fun w : Space => (v,w))
    ((PointCode.run_value J _ (vertexInputList_complete _) (successorCode p n v)).trans
      (successorCode_value p n J v))

private theorem materialize_canonical_fee {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) :
    (materializeRows p n (canonicalRows (perturbationOddScale p) n J)).2 =
      materializationLabelCost p n := by
  apply BDL26ReplacementMaterialization.mapQuery_cost_congr
  intro v
  simp only [PointCode.run_cost_labels,canonicalRows_labels]

/-- This is the exact list-program cost with static labels, not its bound. -/
def perturbLabelCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  (mapQuery (fun v : Vertex (StagePresentation p n) =>
    ((),labelReadCost v (vertexInputList (StagePresentation p n))+
      labelReadCost ((SR.decode (perturbationOddScale p) n).symm v)
        (SR.indices (SR.count (perturbationOddScale p) n))+24+3))
    (vertexInputList (StagePresentation p n))).2

private theorem perturb_canonical_fee {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : NativeTable (perturbationOddScale p) n) :
    (perturbRowsQ p n (canonicalRows (perturbationOddScale p) n J)
      (Paid.emitted _ n (canonicalRows _ n J) (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) T)).2 = perturbLabelCost p n := by
  unfold perturbRowsQ perturbLabelCost
  apply BDL26ReplacementMaterialization.mapQuery_cost_congr
  intro v
  dsimp only
  rw [pointRowQuery_cost_labels,canonicalRows_labels,pointRowQuery_cost_labels,
    emitted_rows]
  simp only [List.map_map,Function.comp_def,map_identity,pointSnapshotQuery_cost]

def deterministicCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  perturbLabelCost p n+materializationLabelCost p n

/-- The execution retains the actual emitted assignment, performs paid row
reads/affine perturbation, then runs the original replacement interpreter.
No decoded-reference execution is used to compute its value or paid cost. -/
def stageQuery {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (I : Rows (perturbationOddScale p) n) (T : NativeTable (perturbationOddScale p) n) :
    Rows (perturbationOddScale p) (n+1) × ℝ≥0∞ :=
  let emitted := Paid.emitted _ n I (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T
  let perturbed := perturbRowsQ p n I emitted
  let materialized := materializeRows p n perturbed.1
  (materialized.1,Paid.operationCost _ n I (radius_nonneg p) p.lambda
    ((6*p.m+2)*p.lambda) T+(perturbed.2 : ℝ≥0∞)+(materialized.2 : ℝ≥0∞))

theorem stageQuery_rows {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (I : Rows (perturbationOddScale p) n) (T : NativeTable (perturbationOddScale p) n) :
    (stageQuery p n I T).1 = canonicalRows (perturbationOddScale p) (n+1)
      (successor p n (rowMap _ n I) T) := by
  change (materializeRows p n _).1 = _
  rw [perturbRows_value,materialize_canonical_value]
  rfl

theorem stageQuery_cost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : NativeTable (perturbationOddScale p) n) :
    (stageQuery p n (canonicalRows _ n J) T).2 =
      Paid.operationCost _ n (canonicalRows _ n J) (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) T+(deterministicCost p n : ℝ≥0∞) := by
  change _+_+_ = _
  rw [perturb_canonical_fee,perturbRows_value,materialize_canonical_fee,
    deterministicCost,Nat.cast_add,add_assoc]

private theorem measurable_nativePerturbed {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun z : JointInput (perturbationOddScale p) n => nativePerturbed p n z.1 z.2) := by
  apply measurable_pi_lambda
  intro v
  exact ((((measurable_pi_apply v).comp measurable_fst).const_smul (1/2 : ℝ)).const_smul
    (p.lambda : ℝ)).add ((measurable_pi_apply v).comp (measurable_joint_nativeOutput _ n p))

theorem measurable_successor {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun z : JointInput (perturbationOddScale p) n => successor p n z.1 z.2) :=
  (continuous_replacementOutput _ n (state _ n)).measurable.comp (measurable_nativePerturbed p n)

def jointStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : JointInput (perturbationOddScale p) n) : ℝ≥0∞ :=
  (stageQuery p n (canonicalRows _ n z.1) z.2).2

theorem measurable_jointStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (jointStageCost p n) := by
  have he : jointStageCost p n = fun z =>
      Paid.operationCost _ n (canonicalRows _ n z.1) (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) z.2+(deterministicCost p n : ℝ≥0∞) :=
    funext (fun z => stageQuery_cost p n z.1 z.2)
  rw [he]
  exact (Paid.measurable_operationCost _ n (radius_nonneg p) p.lambda
    ((6*p.m+2)*p.lambda)).add measurable_const

-- The generic finite-product mechanics are instantiated with whole native factors.
abbrev StageMaps {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Vertex (state (perturbationOddScale p) n).presentation → Space

abbrev StageTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  NativeTable (perturbationOddScale p) n

/-- Exactly one independent whole table factor is appended at each stage. -/
def Experiment {L : ℝ} (p : GeometricParameters L) : ℕ → Type
  | 0 => Unit
  | n+1 => Experiment p n × StageTables p n

instance experimentMeasurableSpace {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → MeasurableSpace (Experiment p n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => (experimentMeasurableSpace p n).prod inferInstance

/-- Retain the first `m` actual stage factors, by deleting later factors. -/
def experimentPrefix {L : ℝ} (p : GeometricParameters L) (m : ℕ) :
    (n : ℕ) → m ≤ n → Experiment p n → Experiment p m
  | 0, h, z => by
      have hm : m = 0 := by omega
      subst m
      exact z
  | n+1, h, z =>
      if he : m = n+1 then he.symm ▸ z
      else experimentPrefix p m n (by omega) z.1

@[simp] theorem prefix_self {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (h : n ≤ n) (z : Experiment p n) : experimentPrefix p n n h z = z := by
  cases n with
  | zero => rfl
  | succ n => simp [experimentPrefix]

theorem prefix_proof_irrel {L : ℝ} (p : GeometricParameters L) (m n : ℕ)
    (h h' : m ≤ n) : experimentPrefix p m n h = experimentPrefix p m n h' := rfl

@[simp] theorem prefix_zero {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (h : 0 ≤ n) (z : Experiment p n) : experimentPrefix p 0 n h z = () := by
  change (experimentPrefix p 0 n h z : Unit) = ()
  exact @Subsingleton.elim Unit inferInstance (experimentPrefix p 0 n h z) ()

/-- Deleting a final stage does not inspect its table. -/
theorem prefix_succ {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (z : Experiment p (n+1)) :
    experimentPrefix p m (n+1) (by omega) z = experimentPrefix p m n h z.1 := by
  have he : ¬m = n+1 := by omega
  simp only [experimentPrefix, dif_neg he]

@[simp] theorem prefix_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) : experimentPrefix p n (n+1) (by omega) z = z.1 := by
  rw [prefix_succ p (le_refl n), prefix_self]

/-- Prefix composition is a pointwise identity, without an almost-everywhere restriction. -/
theorem prefix_comp {L : ℝ} (p : GeometricParameters L) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (z : Experiment p n) :
    experimentPrefix p l m hlm (experimentPrefix p m n hmn z) = experimentPrefix p l n (hlm.trans hmn) z := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      have hl : l = 0 := by omega
      subst m
      subst l
      rfl
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        rw [prefix_self]
      · have hmn' : m ≤ n := by omega
        have hln : l ≤ n := hlm.trans hmn'
        rw [prefix_succ p hmn', prefix_succ p hln]
        exact ih hlm hmn' z.1

/-- The actual factor at stage `i`, read from the prefix ending at `i+1`. -/
def tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageTables p i.val :=
  fun z => (experimentPrefix p (i.val+1) n i.isLt z).2

@[simp] theorem tableAt_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) : tableAt p (n+1) (Fin.last n) z = z.2 := by
  simp only [tableAt, Fin.val_last, prefix_self]

theorem tableAt_castSucc {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p (n+1)) :
    tableAt p (n+1) i.castSucc z = tableAt p n i z.1 := by
  simp only [tableAt, Fin.coe_castSucc]
  rw [prefix_succ p i.isLt]

theorem tableAt_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (z : Experiment p n) :
    tableAt p m i (experimentPrefix p m n h z) = tableAt p n (i.castLE h) z := by
  simp only [tableAt, Fin.val_castLE]
  rw [prefix_comp]

/-- Evaluate the literal selected successor, including its original total default. -/
def evaluate {L : ℝ} (p : GeometricParameters L) : (n : ℕ) → Experiment p n → StageMaps p n
  | 0, _ => BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)
  | n+1, z => successor p n (evaluate p n z.1) z.2

@[simp] theorem evaluate_zero {L : ℝ} (p : GeometricParameters L) (z : Experiment p 0) :
    evaluate p 0 z = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) := rfl

@[simp] theorem evaluate_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) :
    evaluate p (n+1) z = successor p n (evaluate p n z.1) z.2 := rfl

def history {L : ℝ} (p : GeometricParameters L) (n : ℕ) (z : Experiment p n)
    (i : Fin (n+1)) : StageMaps p i.val :=
  evaluate p i.val (experimentPrefix p i.val n (by omega) z)

def stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val :=
  fun z => evaluate p i.val (experimentPrefix p i.val n (by omega) z)

def stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val × StageTables p i.val :=
  fun z => (stageInput p n i z, tableAt p n i z)

theorem evaluate_prefix_succ {L : ℝ} (p : GeometricParameters L) {i n : ℕ}
    (hi : i < n) (z : Experiment p n) :
    evaluate p (i+1) (experimentPrefix p (i+1) n hi z) =
      successor p i (stageInput p n ⟨i,hi⟩ z) (tableAt p n ⟨i,hi⟩ z) := by
  rw [evaluate_succ]
  congr 1
  unfold stageInput
  congr 1
  rw [← prefix_last p i, prefix_comp]

theorem history_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (z : Experiment p n) (i : Fin (m+1)) :
    history p m (experimentPrefix p m n h z) i =
      history p n z (i.castLE (by omega)) := by
  simp only [history, Fin.val_castLE]
  rw [prefix_comp]

theorem stagePair_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (z : Experiment p n) :
    stagePair p m i (experimentPrefix p m n h z) = stagePair p n (i.castLE h) z := by
  apply Prod.ext
  · simp only [stagePair, stageInput, Fin.val_castLE]
    rw [prefix_comp]
  · exact tableAt_prefix p h i z

theorem measurable_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) : Measurable (experimentPrefix p m n h) := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact measurable_id
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        simpa only [show experimentPrefix p (n+1) (n+1) h = id from funext (prefix_self p _ h)]
          using measurable_id
      · have hmn : m ≤ n := by omega
        have heq : experimentPrefix p m (n+1) h = (experimentPrefix p m n hmn) ∘ Prod.fst :=
          funext (prefix_succ p hmn)
        rw [heq]
        exact (ih hmn).comp measurable_fst

theorem measurable_tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (tableAt p n i) :=
  measurable_snd.comp (measurable_prefix p i.isLt)

theorem measurable_evaluate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (evaluate p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun z : Experiment p n × StageTables p n =>
        successor p n (evaluate p n z.1) z.2)
      have hleft : Measurable (fun z : Experiment p n × StageTables p n =>
          evaluate p n z.1) := ih.comp measurable_fst
      have hright : Measurable (fun z : Experiment p n × StageTables p n => z.2) :=
        measurable_snd
      have hpair : Measurable (fun z : Experiment p n × StageTables p n =>
          (evaluate p n z.1, z.2)) := hleft.prodMk hright
      have hsuccessor : Measurable (fun w : StageMaps p n × StageTables p n =>
          successor p n w.1 w.2) := measurable_successor p n
      exact @Measurable.comp
        (Experiment p n × StageTables p n) (StageMaps p n × StageTables p n) (StageMaps p (n+1))
        inferInstance inferInstance inferInstance
        (fun w : StageMaps p n × StageTables p n => successor p n w.1 w.2)
        (fun z : Experiment p n × StageTables p n => (evaluate p n z.1, z.2))
        hsuccessor hpair

theorem measurable_history {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (history p n) := by
  apply measurable_pi_lambda _
  intro i
  exact (measurable_evaluate p i.val).comp (measurable_prefix p (by omega))

theorem measurable_stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (stageInput p n i) :=
  (measurable_evaluate p i.val).comp (measurable_prefix p (by omega))

theorem measurable_stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (stagePair p n i) :=
  (measurable_stageInput p n i).prodMk (measurable_tableAt p n i)


def freshLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageTables p n) :=
  nativeTableMeasure (perturbationOddScale p) n p

instance freshLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (freshLaw p n) :=
  inferInstanceAs (IsProbabilityMeasure (nativeTableMeasure (perturbationOddScale p) n p))

def experimentLaw {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → Measure (Experiment p n)
  | 0 => Measure.dirac ()
  | n+1 => (experimentLaw p n).prod (freshLaw p n)

instance experimentLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (experimentLaw p n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure ((experimentLaw p n).prod (freshLaw p n))
      infer_instance

theorem measurePreserving_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    MeasurePreserving (experimentPrefix p m n h) (experimentLaw p n) (experimentLaw p m) := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact MeasurePreserving.id _
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        simpa only [show experimentPrefix p (n+1) (n+1) h = id from funext (prefix_self p _ h)]
          using MeasurePreserving.id (experimentLaw p (n+1))
      · have hmn : m ≤ n := by omega
        have heq : experimentPrefix p m (n+1) h = (experimentPrefix p m n hmn) ∘ Prod.fst :=
          funext (prefix_succ p hmn)
        rw [heq]
        exact (ih hmn).comp measurePreserving_fst

theorem measurePreserving_tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    MeasurePreserving (tableAt p n i) (experimentLaw p n) (freshLaw p i.val) :=
  measurePreserving_snd.comp (measurePreserving_prefix p i.isLt)

theorem tableAt_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (experimentLaw p n).map (tableAt p n i) = freshLaw p i.val :=
  (measurePreserving_tableAt p n i).map_eq

theorem tableAt_preimage {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (B : Set (StageTables p i.val)) (hB : MeasurableSet B) :
    experimentLaw p n (tableAt p n i ⁻¹' B) = freshLaw p i.val B := by
  rw [← Measure.map_apply (measurable_tableAt p n i) hB, tableAt_law]

/-- The full dependent rectangle splits into the preceding rectangle and final table set. -/
theorem full_rectangle_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin (n+1)) → Set (StageTables p i.val)) :
    {z : Experiment p (n+1) | ∀ i, tableAt p (n+1) i z ∈ B i} =
      {z : Experiment p n | ∀ i : Fin n, tableAt p n i z ∈ B i.castSucc} ×ˢ
        B (Fin.last n) := by
  ext z
  constructor
  · intro hz
    exact ⟨fun i => by simpa only [tableAt_castSucc] using hz i.castSucc,
      by simpa only [tableAt_last] using hz (Fin.last n)⟩
  · rintro ⟨hfirst, hlast⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [tableAt_last] using hlast
    · simpa only [tableAt_castSucc] using hfirst j

/-- Arbitrary table rectangles have the actual product probability, including zero stages. -/
theorem full_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n {z | ∀ i, tableAt p n i z ∈ B i} =
      ∏ i : Fin n, freshLaw p i.val (B i) := by
  induction n with
  | zero =>
      have heq : {z : Experiment p 0 | ∀ i : Fin 0, tableAt p 0 i z ∈ B i} = Set.univ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro i
        exact Fin.elim0 i
      rw [heq]
      simp only [Fin.prod_univ_zero]
      exact measure_univ
  | succ n ih =>
      rw [full_rectangle_succ]
      change (experimentLaw p n).prod (freshLaw p n) _ = _
      rw [Measure.prod_prod, ih, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]

/-- Every selected finite rectangle factors; unused factors remain the original whole laws. -/
theorem finite_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (A : Finset (Fin n)) (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n (⋂ i ∈ A, tableAt p n i ⁻¹' B i) =
      ∏ i ∈ A, freshLaw p i.val (B i) := by
  let full : (i : Fin n) → Set (StageTables p i.val) :=
    fun i => if i ∈ A then B i else Set.univ
  have hset : {z : Experiment p n | ∀ i, tableAt p n i z ∈ full i} =
      ⋂ i ∈ A, tableAt p n i ⁻¹' B i := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i hi
      simpa only [full, if_pos hi] using h i
    · intro h i
      by_cases hi : i ∈ A
      · simpa only [full, if_pos hi] using h i hi
      · simp only [full, if_neg hi, Set.mem_univ]
  rw [← hset, full_rectangle_probability]
  calc
    (∏ i : Fin n, freshLaw p i.val (full i)) =
        ∏ i ∈ A, freshLaw p i.val (full i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ A)
      intro i _ hi
      simp only [full, if_neg hi, measure_univ]
    _ = ∏ i ∈ A, freshLaw p i.val (B i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [full, if_pos hi]

theorem tableAt_iIndepFun {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    iIndepFun (tableAt p n) (experimentLaw p n) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hB
  rw [finite_rectangle_probability]
  apply Finset.prod_congr rfl
  intro i hi
  exact (tableAt_preimage p n i (B i) (hB i hi)).symm

def outputLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageMaps p n) :=
  (experimentLaw p n).map (evaluate p n)

instance outputLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (outputLaw p n) :=
  Measure.isProbabilityMeasure_map (measurable_evaluate p n).aemeasurable

@[simp] theorem outputLaw_zero {L : ℝ} (p : GeometricParameters L) :
    outputLaw p 0 = Measure.dirac (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)) := by
  change (Measure.dirac (() : Experiment p 0)).map (evaluate p 0) = _
  exact Measure.map_dirac' (measurable_evaluate p 0) ()

def freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Experiment p (n+1) → StageMaps p n × StageTables p n :=
  fun z => (evaluate p n z.1, z.2)

theorem measurable_freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (freshPair p n) :=
  ((measurable_evaluate p n).comp measurable_fst).prodMk measurable_snd

theorem freshPair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (experimentLaw p (n+1)).map (freshPair p n) =
      (outputLaw p n).prod (freshLaw p n) := by
  have hid : Measurable (id : StageTables p n → StageTables p n) := measurable_id
  have h : (outputLaw p n).prod ((freshLaw p n).map (id : StageTables p n → StageTables p n)) =
      ((experimentLaw p n).prod (freshLaw p n)).map
        (Prod.map (evaluate p n) (id : StageTables p n → StageTables p n)) :=
    Measure.map_prod_map (experimentLaw p n) (freshLaw p n) (measurable_evaluate p n) hid
  rw [Measure.map_id] at h
  have hfun : Prod.map (evaluate p n) (id : StageTables p n → StageTables p n) = freshPair p n := by
    funext z
    rcases z with ⟨x,T⟩
    rfl
  rw [hfun] at h
  exact h.symm

theorem stagePair_eq_freshPair_prefix {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    stagePair p n i = (freshPair p i.val) ∘ experimentPrefix p (i.val+1) n i.isLt := by
  funext z
  apply Prod.ext
  · change evaluate p i.val (experimentPrefix p i.val n (by omega) z) =
      evaluate p i.val (experimentPrefix p (i.val+1) n i.isLt z).1
    congr 1
    rw [← prefix_last p i.val, prefix_comp]
  · rfl

theorem stagePair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (experimentLaw p n).map (stagePair p n i) =
      (outputLaw p i.val).prod (freshLaw p i.val) := by
  rw [stagePair_eq_freshPair_prefix, ← Measure.map_map
    (measurable_freshPair p i.val) (measurable_prefix p i.isLt),
    (measurePreserving_prefix p i.isLt).map_eq, freshPair_law]

theorem prefix_output_law {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    (experimentLaw p n).map ((evaluate p m) ∘ experimentPrefix p m n h) = outputLaw p m := by
  rw [← Measure.map_map (measurable_evaluate p m) (measurable_prefix p h),
    (measurePreserving_prefix p h).map_eq]
  rfl


theorem outputLaw_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    outputLaw p (n+1) = ((outputLaw p n).prod (freshLaw p n)).map
      (fun z => successor p n z.1 z.2) := by
  rw [←freshPair_law,Measure.map_map (measurable_successor p n) (measurable_freshPair p n)]
  rfl

/-- The operational recursion carries its literal retained rows and cumulative
extended paid cost. The zero-depth seed rows are supplied data. -/
def run {L : ℝ} (p : GeometricParameters L) : (N : ℕ) → Experiment p N →
    Rows (perturbationOddScale p) N × ℝ≥0∞
  | 0, _ => (canonicalRows (perturbationOddScale p) 0 (BDL26RandomSeedEmbedding.seedPoint _),0)
  | N+1,z =>
    let prior := run p N z.1
    let next := stageQuery p N prior.1 z.2
    (next.1,prior.2+next.2)

theorem run_rows {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    (run p N z).1 = canonicalRows (perturbationOddScale p) N (evaluate p N z) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change (stageQuery p N (run p N z.1).1 z.2).1 = _
    rw [ih,stageQuery_rows,rowMap_canonical]
    rfl

def inputRows {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : Rows (perturbationOddScale p) i.val :=
  (run p i.val (experimentPrefix p i.val N (by omega) z)).1

theorem inputRows_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : inputRows p N i z =
      canonicalRows (perturbationOddScale p) i.val (stageInput p N i z) :=
  run_rows p i.val _

def stageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℝ≥0∞ :=
  (stageQuery p i.val (inputRows p N i z) (tableAt p N i z)).2

def totalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : ℝ≥0∞ :=
  (run p N z).2

theorem stageCost_joint {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    stageCost p N i = jointStageCost p i.val ∘ stagePair p N i := by
  funext z
  rw [stageCost,inputRows_eq]
  rfl

/-- Normalize the last finite index before rewriting a dependent prefix.
The actual final table and preceding experiment factors remain unchanged. -/
private theorem stageCost_last {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p (N+1)) :
    stageCost p (N+1) (Fin.last N) z =
      (stageQuery p N (run p N z.1).1 z.2).2 := by
  change (stageQuery p N
    (run p N (experimentPrefix p N (N+1) (by omega) z)).1
    (tableAt p (N+1) (Fin.last N) z)).2 = _
  rw [prefix_last p N z,tableAt_last p N z]

theorem totalCost_sum {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    totalCost p N z = ∑ i : Fin N, stageCost p N i z := by
  induction N with
  | zero => simp only [totalCost,run,Fin.sum_univ_zero]
  | succ N ih =>
    change totalCost p N z.1+(stageQuery p N (run p N z.1).1 z.2).2 = _
    rw [ih,Fin.sum_univ_castSucc]
    apply congrArg₂ (fun a b : ℝ≥0∞ => a+b)
    · apply Finset.sum_congr rfl
      intro i hi
      unfold stageCost inputRows
      rw [prefix_succ p (by omega),tableAt_castSucc]
      rfl
    · exact (stageCost_last p N z).symm

theorem measurable_stageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    Measurable (stageCost p N i) := by
  rw [stageCost_joint]
  exact (measurable_jointStageCost p i.val).comp (measurable_stagePair p N i)

theorem measurable_totalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (totalCost p N) := by
  have he : totalCost p N = fun z => ∑ i : Fin N, stageCost p N i z :=
    funext (totalCost_sum p N)
  rw [he]
  exact Finset.measurable_sum _ (fun i hi => measurable_stageCost p N i)

private theorem successor_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (ν : Measure (StageMaps p n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (StagePresentation p n) J p.t) :
    ∀ᵐ z ∂ν.prod (freshLaw p n),
      IsBoundedDensityLocalMap (StagePresentation p (n+1)) (successor p n z.1 z.2) p.t := by
  filter_upwards [native_random_input_geometry_ae (perturbationOddScale p) n p ν hν]
    with z hz
  exact replacementOutput_localMap p n (state (perturbationOddScale p) n) _
    (state_boundedValence _ n) hz.2.2.1 hz.2.2.2

theorem outputLaw_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ J ∂outputLaw p n, IsBoundedDensityLocalMap (StagePresentation p n) J p.t := by
  induction n with
  | zero =>
    apply (ae_map_iff (measurable_evaluate p 0).aemeasurable
      (measurableSet_boundedDensityLocalMap _ p.t)).mpr
    exact Filter.Eventually.of_forall (fun _ => BDL26RandomSeedEmbedding.seed_parameter_localMap p)
  | succ n ih =>
    rw [outputLaw_succ]
    exact (ae_map_iff (measurable_successor p n).aemeasurable
      (measurableSet_boundedDensityLocalMap _ p.t)).mpr
      (successor_good_ae p n (outputLaw p n) ih)

def stageHalts {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : Prop :=
  NativeHalts (perturbationOddScale p) i.val (stageInput p N i z) (radius_nonneg p)
    p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)

def stageGood {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : Prop :=
  nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z) ∈
    BDL26NativeGeometricAvoidance.NativeGood (perturbationOddScale p) i.val
      (stageInput p N i z) p

theorem measurableSet_stageHalts {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    MeasurableSet {z | stageHalts p N i z} := by
  exact measurableSet_pullback_pointwise
    (Ω := Experiment p N) (A := JointInput (perturbationOddScale p) i.val)
    (stagePair p N i)
    {w | NativeHalts (perturbationOddScale p) i.val w.1 (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda) w.2}
    (stageHalts p N i) (measurable_stagePair p N i)
    (BDL26NativeGeometricJointExecution.measurableSet_native_halts _ i.val (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda)) (fun _ => Iff.rfl)

theorem measurableSet_stageGood {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    MeasurableSet {z | stageGood p N i z} := by
  have hout : Measurable (fun z : Experiment p N =>
      nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z)) :=
    measurable_comp_pointwise
      (Ω := Experiment p N) (A := JointInput (perturbationOddScale p) i.val)
      (B := Input (perturbationOddScale p) i.val)
      (fun w => nativeOutput (perturbationOddScale p) i.val w.1 p w.2)
      (stagePair p N i) _ (measurable_joint_nativeOutput _ i.val p)
      (measurable_stagePair p N i) (fun _ => rfl)
  exact measurableSet_pullback_pointwise
    (Ω := Experiment p N)
    (A := Input (perturbationOddScale p) i.val × Input (perturbationOddScale p) i.val)
    (fun z => (stageInput p N i z,
      nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z)))
    {w | w.2 ∈ BDL26NativeGeometricAvoidance.NativeGood (perturbationOddScale p) i.val w.1 p}
    (stageGood p N i) ((measurable_stageInput p N i).prodMk hout)
    (measurableSet_joint_nativeGood _ i.val p) (fun _ => Iff.rfl)

theorem stage_success_ae {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    ∀ᵐ z ∂experimentLaw p N, stageHalts p N i z ∧ stageGood p N i z := by
  have h := native_random_input_geometry_ae (perturbationOddScale p) i.val p
    (outputLaw p i.val) (outputLaw_good_ae p i.val)
  change ∀ᵐ z ∂(outputLaw p i.val).prod (freshLaw p i.val), _ at h
  rw [←stagePair_law p N i] at h
  filter_upwards [ae_of_ae_map (measurable_stagePair p N i).aemeasurable h] with z hz
  exact ⟨hz.1,hz.2.1⟩

theorem history_good_ae {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin (N+1)) :
    ∀ᵐ z ∂experimentLaw p N,
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p N z i) p.t := by
  have h := outputLaw_good_ae p i.val
  rw [←prefix_output_law p (show i.val ≤ N by omega)] at h
  exact ae_of_ae_map ((measurable_evaluate p i.val).comp
    (measurable_prefix p (show i.val ≤ N by omega))).aemeasurable h

/-- A finite Borel event retains actual halting, actual NativeGood outputs and
all incoming/replacement local maps. No good history is a caller hypothesis. -/
def finiteSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) : Set (Experiment p N) :=
  {z | (∀ i : Fin N, stageHalts p N i z ∧ stageGood p N i z) ∧
    ∀ i : Fin (N+1), IsBoundedDensityLocalMap (StagePresentation p i.val) (history p N z i) p.t}

theorem measurableSet_finiteSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    MeasurableSet (finiteSuccess p N) := by
  have hs : MeasurableSet {z | ∀ i : Fin N, stageHalts p N i z ∧ stageGood p N i z} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i =>
      (measurableSet_stageHalts p N i).inter (measurableSet_stageGood p N i))
  have hg : MeasurableSet {z | ∀ i : Fin (N+1),
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p N z i) p.t} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i =>
      (measurableSet_boundedDensityLocalMap _ p.t).preimage
        ((measurable_pi_apply i).comp (measurable_history p N)))
  exact hs.inter hg

theorem finiteSuccess_ae {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N := by
  filter_upwards [ae_all_iff.mpr (stage_success_ae p N),
    ae_all_iff.mpr (history_good_ae p N)] with z hs hg
  exact ⟨hs,hg⟩

theorem finiteSuccess_geometry {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : Experiment p N} (hz : z ∈ finiteSuccess p N) (i : Fin (N+1)) :
    PhysicalGeometry (perturbationOddScale p) i.val (history p N z i) p.t :=
  physicalGeometry_of_localMap _ _ _ (hz.2 i)

/-- Original NativeGood yields the original incoming-face and labelled-triangle
handoff, on the same full history and the same native table. -/
theorem finiteSuccess_handoff {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : Experiment p N} (hz : z ∈ finiteSuccess p N) (i : Fin N) :
    IncomingFaceGeometry (StagePresentation p i.val) (perturbationOddScale p)
      (nativePerturbed p i.val (stageInput p N i z) (tableAt p N i z))
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ center, ((familyHits (oldTriangleImage (StagePresentation p i.val)
      (nativePerturbed p i.val (stageInput p N i z) (tableAt p N i z)))
      (Metric.closedBall center 1)).card : ℝ) ≤ triangleDensityBound := by
  have hJ : IsBoundedDensityLocalMap (StagePresentation p i.val) (stageInput p N i z) p.t :=
    hz.2 ⟨i.val,by omega⟩
  exact (BDL26NativeGeometricAvoidance.native_supported_avoidance
    (perturbationOddScale p) i.val (stageInput p N i z) p hJ).2.2 _ (hz.1 i).2

@[simp] theorem history_last {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : history p N z (Fin.last N)=evaluate p N z := by
  simp only [history,Fin.val_last,prefix_self]

theorem zero_experiment_seed {L : ℝ} (p : GeometricParameters L) (z : Experiment p 0) :
    evaluate p 0 z = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) ∧
    totalCost p 0 z=0 ∧ PhysicalGeometry (perturbationOddScale p) 0 (evaluate p 0 z) p.t :=
  ⟨rfl,rfl,BDL26RandomSeedEmbedding.seed_physicalGeometry p⟩

private theorem perturbLabelCost_bound {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    perturbLabelCost p n ≤ 32*(Fintype.card (Vertex (StagePresentation p n))+1)^2 := by
  let I := canonicalRows (perturbationOddScale p) n (fun _ => 0)
  let W := Paid.emitted (perturbationOddScale p) n I (radius_nonneg p) p.lambda
    ((6*p.m+2)*p.lambda) (fun _ => 0)
  let v := Fintype.card (Vertex (StagePresentation p n))
  have hI : I.length=v := canonicalRows_length _ n _
  have hW : W.length=v := by
    dsimp only [W]
    rw [emitted_rows,List.length_map,BDL26NativeStateRows.indices_length,native_count_card]
  have hq (a : Vertex (StagePresentation p n)) :
      (pointRowQuery a I).2+
        (pointRowQuery ((SR.decode (perturbationOddScale p) n).symm a) W).2+
        (pointSnapshotQuery p.lambda (pointRowQuery a I).1
          (pointRowQuery ((SR.decode (perturbationOddScale p) n).symm a) W).1).2+3 ≤
      4*v+27 := by
    rw [pointSnapshotQuery_cost]
    have h1 := pointRowQuery_cost_le a I
    have h2 := pointRowQuery_cost_le ((SR.decode (perturbationOddScale p) n).symm a) W
    rw [hI] at h1
    rw [hW] at h2
    omega
  have h := mapQuery_cost_le
    (fun a : Vertex (StagePresentation p n) =>
      let j := pointRowQuery a I
      let w := pointRowQuery ((SR.decode (perturbationOddScale p) n).symm a) W
      let q := pointSnapshotQuery p.lambda j.1 w.1
      ((a,q.1),j.2+w.2+q.2+3))
    (vertexInputList (StagePresentation p n)) (4*v+27) (fun a _ => hq a)
  rw [vertexInputList_length] at h
  have he := perturb_canonical_fee p n (fun _ => 0) (fun _ => 0)
  change (perturbRowsQ p n I W).2=perturbLabelCost p n at he
  rw [←he]
  exact h.trans (by dsimp only [v]; nlinarith)

private theorem materializationLabelCost_bound {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    materializationLabelCost p n ≤
      65536*(Fintype.card (Vertex (StagePresentation p n))+1)*
        Fintype.card (Vertex (StagePresentation p (n+1))) := by
  rw [←materialize_canonical_fee p n (fun _ => 0)]
  exact (materializeRows_cost_le p n (canonicalRows _ n (fun _ => 0))).trans_eq
    (by rw [canonicalRows_length])

def nativeCoefficient {L : ℝ} (p : GeometricParameters L) : ℕ :=
  nativeOperationCoefficient ((6*p.m+2)*p.lambda) (dependencyBound p.M)

/-- Exact stage-sum coefficient: native read multiplier times the unchanged
1772 bound, plus the actual static affine/replacement interpreter costs. -/
def stageBudget {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  (2*Fintype.card (Vertex (StagePresentation p n))+1)*
    (nativeCoefficient p*(stageQubits p n+1)^1772)+deterministicCost p n

theorem jointStageCost_integral_le {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ z, jointStageCost p n z ∂(outputLaw p n).prod (freshLaw p n)) ≤
      (stageBudget p n : ℝ≥0∞) := by
  let f := fun z : JointInput (perturbationOddScale p) n =>
    nativeOperationCost _ n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2
  let d := 2*Fintype.card (Vertex (StagePresentation p n))+1
  have hf : Measurable f := measurable_joint_nativeOperationCost _ n (radius_nonneg p)
    p.lambda ((6*p.m+2)*p.lambda)
  have hb : ∀ z, jointStageCost p n z ≤
      (d : ℝ≥0∞)*f z+(deterministicCost p n : ℝ≥0∞) := by
    intro z
    rw [jointStageCost,stageQuery_cost]
    have h := Paid.operationCost_bound _ n (canonicalRows _ n z.1) (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda) z.2
    rw [rowMap_canonical,Paid.multiplier,canonicalRows_length] at h
    exact add_le_add h le_rfl
  calc
    _ ≤ ∫⁻ z, (d : ℝ≥0∞)*f z+(deterministicCost p n : ℝ≥0∞)
        ∂(outputLaw p n).prod (freshLaw p n) := lintegral_mono hb
    _ = (d : ℝ≥0∞)*(∫⁻ z,f z ∂(outputLaw p n).prod (freshLaw p n))+
        (deterministicCost p n : ℝ≥0∞) := by
      exact lintegral_affine_nat ((outputLaw p n).prod (freshLaw p n)) f hf d
        (deterministicCost p n)
    _ ≤ (d : ℝ≥0∞)*(nativeCoefficient p*(stageQubits p n+1)^1772 : ℕ)+
        (deterministicCost p n : ℝ≥0∞) :=
      add_le_add (mul_le_mul' le_rfl
        (native_random_input_total_cost (perturbationOddScale p) n p (outputLaw p n)
          (outputLaw_good_ae p n))) le_rfl
    _ = _ := by dsimp only [d,stageBudget]; push_cast; rfl

theorem stageCost_integral_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    (∫⁻ z,stageCost p N i z ∂experimentLaw p N) ≤ (stageBudget p i.val : ℝ≥0∞) := by
  rw [stageCost_joint]
  change (∫⁻ z, jointStageCost p i.val (stagePair p N i z) ∂experimentLaw p N) ≤ _
  rw [←lintegral_map (measurable_jointStageCost p i.val)
    (measurable_stagePair p N i),stagePair_law]
  exact jointStageCost_integral_le p i.val

theorem totalCost_integral_le_sum {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z,totalCost p N z ∂experimentLaw p N) ≤
      ((∑ i : Fin N,stageBudget p i.val : ℕ) : ℝ≥0∞) := by
  have he : totalCost p N = fun z => ∑ i : Fin N,stageCost p N i z :=
    funext (totalCost_sum p N)
  rw [he,lintegral_finsetSum Finset.univ (fun i _ => measurable_stageCost p N i),Nat.cast_sum]
  exact Finset.sum_le_sum (fun i _ => stageCost_integral_le p N i)

/-- A concrete natural coefficient depending only on the fixed legal parameters. -/
def totalCoefficient {L : ℝ} (p : GeometricParameters L) : ℕ :=
  131*nativeCoefficient p+65568*66^2

private theorem deterministicCost_le_final {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) : deterministicCost p i.val ≤ 65568*66^2*(stageQubits p N+1)^2 := by
  have hv0 := (stageVertices_le_qubits p i.val).trans
    (Nat.mul_le_mul_left 65 (stageQubits_mono p (Nat.le_of_lt i.isLt)))
  have hv1 := (stageVertices_le_qubits p (i.val+1)).trans
    (Nat.mul_le_mul_left 65 (stageQubits_mono p (show i.val+1≤N by omega)))
  have hp := perturbLabelCost_bound p i.val
  have hm := materializationLabelCost_bound p i.val
  dsimp only [deterministicCost]
  have hpow : (Fintype.card (Vertex (StagePresentation p i.val))+1)^2 ≤
      (66*(stageQubits p N+1))^2 := Nat.pow_le_pow_left (by omega) 2
  calc
    _ ≤ 32*(66*(stageQubits p N+1))^2+
        65536*(66*(stageQubits p N+1))*(66*(stageQubits p N+1)) :=
      Nat.add_le_add (hp.trans (Nat.mul_le_mul_left 32 hpow))
        (hm.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)))
    _ = _ := by ring

private theorem stageBudget_le_final {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) : stageBudget p i.val ≤ totalCoefficient p*(stageQubits p N+1)^1773 := by
  let r := stageQubits p N+1
  have hr : 1≤r := by dsimp only [r]; omega
  have hq := stageQubits_mono p (Nat.le_of_lt i.isLt)
  have hv := stageVertices_le_qubits p i.val
  have hd : 2*Fintype.card (Vertex (StagePresentation p i.val))+1≤131*r := by
    dsimp only [r]; nlinarith
  have hp : (stageQubits p i.val+1)^1772≤r^1772 :=
    Nat.pow_le_pow_left (by dsimp only [r]; omega) _
  have h2 : r^2≤r^1773 := Nat.pow_le_pow_right hr (by decide)
  calc
    _ ≤ (131*r)*(nativeCoefficient p*r^1772)+65568*66^2*r^2 :=
      Nat.add_le_add (Nat.mul_le_mul hd (Nat.mul_le_mul_left _ hp))
        (deterministicCost_le_final p N i)
    _ ≤ (131*r)*(nativeCoefficient p*r^1772)+65568*66^2*r^1773 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _
    _ = _ := by
      change (131*r)*(nativeCoefficient p*r^1772)+65568*66^2*r^1773 =
        (131*nativeCoefficient p+65568*66^2)*r^1773
      rw [paid_power_step,←Nat.add_mul]

/-- Degree1774 accounts for paid first-match accesses and all finite levels.
No independence between different adaptive costs is used in finite additivity. -/
theorem totalCost_integral_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z,totalCost p N z ∂experimentLaw p N) ≤
      (totalCoefficient p*(stageQubits p N+1)^1774 : ℕ) := by
  apply (totalCost_integral_le_sum p N).trans
  apply (Nat.cast_le (α := ℝ≥0∞)).mpr
  have hN := stage_count_le_qubits p N
  calc
    _ ≤ ∑ _i : Fin N,totalCoefficient p*(stageQubits p N+1)^1773 :=
      Finset.sum_le_sum (fun i _ => stageBudget_le_final p N i)
    _ = N*(totalCoefficient p*(stageQubits p N+1)^1773) := by simp
    _ ≤ (stageQubits p N+1)*(totalCoefficient p*(stageQubits p N+1)^1773) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := paid_power_left (totalCoefficient p) (stageQubits p N+1) 1773

theorem totalCost_integrable {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z,totalCost p N z ∂experimentLaw p N)<∞ ∧
    Integrable (fun z => (totalCost p N z).toReal) (experimentLaw p N) := by
  have hf := (totalCost_integral_le p N).trans_lt (ENNReal.natCast_lt_top _)
  refine ⟨hf,?_⟩
  exact integrable_toReal_of_lintegral_ne_top (measurable_totalCost p N).aemeasurable (ne_of_lt hf)

theorem stageCost_nonhalting {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) (h : ¬stageHalts p N i z) : stageCost p N i z=∞ := by
  unfold stageHalts at h
  rw [stageCost,inputRows_eq,stageQuery_cost,Paid.operationCost,rowMap_canonical,if_neg h]
  simp

theorem stageCost_finite_of_halts {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) (h : stageHalts p N i z) : stageCost p N i z<∞ := by
  unfold stageHalts at h
  rw [stageCost,inputRows_eq,stageQuery_cost,Paid.operationCost,rowMap_canonical,if_pos h]
  simp

theorem totalCost_finite_on_success {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) (hz : z ∈ finiteSuccess p N) : totalCost p N z<∞ := by
  rw [totalCost_sum]
  exact ENNReal.sum_lt_top.mpr (fun i hi => stageCost_finite_of_halts p N i z (hz.1 i).1)

theorem fixed_parameters_all_finite (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N : ℕ,
      Measurable (history p N) ∧ Measurable (totalCost p N) ∧
      (∫⁻ z,totalCost p N z ∂experimentLaw p N) ≤
        (totalCoefficient p*(stageQubits p N+1)^1774 : ℕ) ∧
      Integrable (fun z => (totalCost p N z).toReal) (experimentLaw p N) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ totalCost p N z<∞ ∧
        ∀ i : Fin (N+1), PhysicalGeometry (perturbationOddScale p) i.val (history p N z i) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p,fun N => ⟨measurable_history p N,measurable_totalCost p N,
    totalCost_integral_le p N,(totalCost_integrable p N).2,?_⟩⟩
  filter_upwards [finiteSuccess_ae p N] with z hz
  exact ⟨hz,totalCost_finite_on_success p N z hz,finiteSuccess_geometry p N hz⟩

theorem source_even_geometry_cost {L : ℝ} (p : GeometricParameters L) (k : ℕ) :
    (∫⁻ z,totalCost p (2*k) z ∂experimentLaw p (2*k)) ≤
      (totalCoefficient p*(stageQubits p (2*k)+1)^1774 : ℕ) ∧
    ∀ᵐ z ∂experimentLaw p (2*k),
      PhysicalGeometry (perturbationOddScale p) (2*k) (evaluate p (2*k) z) p.t := by
  refine ⟨totalCost_integral_le p (2*k),?_⟩
  filter_upwards [finiteSuccess_ae p (2*k)] with z hz
  simpa only [history_last,Fin.val_last] using finiteSuccess_geometry p (2*k) hz (Fin.last (2*k))

namespace Decoded
/-- This reference uses the identical native key/order. It is deliberately not
identified with the older arbitrary-key finite experiment. -/
def successor {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : BDL26FiniteEmbeddingExperiment.StageMaps p n)
    (T : OriginalTable (perturbationOddScale p) n) :
    BDL26FiniteEmbeddingExperiment.StageMaps p (n+1) :=
  replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
    (perturbedMap (Presentation (perturbationOddScale p) n) J p.lambda
      (result (Presentation (perturbationOddScale p) n)
        (NC.nativeKey (perturbationOddScale p) n)
        (NC.nativeKey_injective (perturbationOddScale p) n) J p T))

private theorem successor_encoded {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : BDL26FiniteEmbeddingExperiment.StageMaps p n)
    (T : OriginalTable (perturbationOddScale p) n) :
    successor p n J T = BDL26NativeFiniteComposition.successor p n J
      (SR.encodeSamples (perturbationOddScale p) n T) := by
  have hd : decodedTable (perturbationOddScale p) n
      (SR.encodeSamples (perturbationOddScale p) n T) = T :=
    Resampling.VariableRelabeling.decode_encode_table (SR.decode (perturbationOddScale p) n) T
  have ho := nativeOutput_decoded (perturbationOddScale p) n J p
    (SR.encodeSamples (perturbationOddScale p) n T)
  have he : nativeOutput (perturbationOddScale p) n J p
      (SR.encodeSamples (perturbationOddScale p) n T) =
      result (Presentation (perturbationOddScale p) n)
        (NC.nativeKey (perturbationOddScale p) n)
        (NC.nativeKey_injective (perturbationOddScale p) n) J p T :=
    ho.trans (congrArg (fun t => result (Presentation (perturbationOddScale p) n)
      (NC.nativeKey (perturbationOddScale p) n)
      (NC.nativeKey_injective (perturbationOddScale p) n) J p t) hd)
  exact congrArg (fun out : Input (perturbationOddScale p) n =>
    replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
      (perturbedMap (Presentation (perturbationOddScale p) n) J p.lambda out)) he.symm

private theorem measurable_successor {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun z : Input (perturbationOddScale p) n × OriginalTable (perturbationOddScale p) n =>
      successor p n z.1 z.2) := by
  have he : (fun z : Input (perturbationOddScale p) n × OriginalTable (perturbationOddScale p) n =>
      successor p n z.1 z.2) = (fun z => BDL26NativeFiniteComposition.successor p n z.1
        (SR.encodeSamples (perturbationOddScale p) n z.2)) :=
    funext (fun z => successor_encoded p n z.1 z.2)
  rw [he]
  exact measurable_comp_pointwise
    (Ω := Input (perturbationOddScale p) n × OriginalTable (perturbationOddScale p) n)
    (A := JointInput (perturbationOddScale p) n)
    (B := BDL26FiniteEmbeddingExperiment.StageMaps p (n+1))
    (fun w => BDL26NativeFiniteComposition.successor p n w.1 w.2)
    (fun z => (z.1,SR.encodeSamples (perturbationOddScale p) n z.2)) _
    (BDL26NativeFiniteComposition.measurable_successor p n)
    (measurable_fst.prodMk
      ((Resampling.VariableRelabeling.measurable_encodeTable (SR.decode _ n)).comp measurable_snd))
    (fun _ => rfl)

abbrev StageMaps {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Vertex (state (perturbationOddScale p) n).presentation → Space

abbrev StageTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)

/-- Exactly one independent whole table factor is appended at each stage. -/
def Experiment {L : ℝ} (p : GeometricParameters L) : ℕ → Type
  | 0 => Unit
  | n+1 => Experiment p n × StageTables p n

instance experimentMeasurableSpace {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → MeasurableSpace (Experiment p n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => (experimentMeasurableSpace p n).prod inferInstance

/-- Retain the first `m` actual stage factors, by deleting later factors. -/
def experimentPrefix {L : ℝ} (p : GeometricParameters L) (m : ℕ) :
    (n : ℕ) → m ≤ n → Experiment p n → Experiment p m
  | 0, h, z => by
      have hm : m = 0 := by omega
      subst m
      exact z
  | n+1, h, z =>
      if he : m = n+1 then he.symm ▸ z
      else experimentPrefix p m n (by omega) z.1

@[simp] theorem prefix_self {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (h : n ≤ n) (z : Experiment p n) : experimentPrefix p n n h z = z := by
  cases n with
  | zero => rfl
  | succ n => simp [experimentPrefix]

theorem prefix_proof_irrel {L : ℝ} (p : GeometricParameters L) (m n : ℕ)
    (h h' : m ≤ n) : experimentPrefix p m n h = experimentPrefix p m n h' := rfl

@[simp] theorem prefix_zero {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (h : 0 ≤ n) (z : Experiment p n) : experimentPrefix p 0 n h z = () := by
  change (experimentPrefix p 0 n h z : Unit) = ()
  exact @Subsingleton.elim Unit inferInstance (experimentPrefix p 0 n h z) ()

/-- Deleting a final stage does not inspect its table. -/
theorem prefix_succ {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (z : Experiment p (n+1)) :
    experimentPrefix p m (n+1) (by omega) z = experimentPrefix p m n h z.1 := by
  have he : ¬m = n+1 := by omega
  simp only [experimentPrefix, dif_neg he]

@[simp] theorem prefix_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) : experimentPrefix p n (n+1) (by omega) z = z.1 := by
  rw [prefix_succ p (le_refl n), prefix_self]

/-- Prefix composition is a pointwise identity, without an almost-everywhere restriction. -/
theorem prefix_comp {L : ℝ} (p : GeometricParameters L) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (z : Experiment p n) :
    experimentPrefix p l m hlm (experimentPrefix p m n hmn z) = experimentPrefix p l n (hlm.trans hmn) z := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      have hl : l = 0 := by omega
      subst m
      subst l
      rfl
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        rw [prefix_self]
      · have hmn' : m ≤ n := by omega
        have hln : l ≤ n := hlm.trans hmn'
        rw [prefix_succ p hmn', prefix_succ p hln]
        exact ih hlm hmn' z.1

/-- The actual factor at stage `i`, read from the prefix ending at `i+1`. -/
def tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageTables p i.val :=
  fun z => (experimentPrefix p (i.val+1) n i.isLt z).2

@[simp] theorem tableAt_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) : tableAt p (n+1) (Fin.last n) z = z.2 := by
  simp only [tableAt, Fin.val_last, prefix_self]

theorem tableAt_castSucc {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p (n+1)) :
    tableAt p (n+1) i.castSucc z = tableAt p n i z.1 := by
  simp only [tableAt, Fin.coe_castSucc]
  rw [prefix_succ p i.isLt]

theorem tableAt_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (z : Experiment p n) :
    tableAt p m i (experimentPrefix p m n h z) = tableAt p n (i.castLE h) z := by
  simp only [tableAt, Fin.val_castLE]
  rw [prefix_comp]

/-- Evaluate the literal selected successor, including its original total default. -/
def evaluate {L : ℝ} (p : GeometricParameters L) : (n : ℕ) → Experiment p n → StageMaps p n
  | 0, _ => BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)
  | n+1, z => successor p n (evaluate p n z.1) z.2

@[simp] theorem evaluate_zero {L : ℝ} (p : GeometricParameters L) (z : Experiment p 0) :
    evaluate p 0 z = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) := rfl

@[simp] theorem evaluate_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) :
    evaluate p (n+1) z = successor p n (evaluate p n z.1) z.2 := rfl

def history {L : ℝ} (p : GeometricParameters L) (n : ℕ) (z : Experiment p n)
    (i : Fin (n+1)) : StageMaps p i.val :=
  evaluate p i.val (experimentPrefix p i.val n (by omega) z)

def stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val :=
  fun z => evaluate p i.val (experimentPrefix p i.val n (by omega) z)

def stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val × StageTables p i.val :=
  fun z => (stageInput p n i z, tableAt p n i z)

theorem evaluate_prefix_succ {L : ℝ} (p : GeometricParameters L) {i n : ℕ}
    (hi : i < n) (z : Experiment p n) :
    evaluate p (i+1) (experimentPrefix p (i+1) n hi z) =
      successor p i (stageInput p n ⟨i,hi⟩ z) (tableAt p n ⟨i,hi⟩ z) := by
  rw [evaluate_succ]
  congr 1
  unfold stageInput
  congr 1
  rw [← prefix_last p i, prefix_comp]

theorem history_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (z : Experiment p n) (i : Fin (m+1)) :
    history p m (experimentPrefix p m n h z) i =
      history p n z (i.castLE (by omega)) := by
  simp only [history, Fin.val_castLE]
  rw [prefix_comp]

theorem stagePair_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (z : Experiment p n) :
    stagePair p m i (experimentPrefix p m n h z) = stagePair p n (i.castLE h) z := by
  apply Prod.ext
  · simp only [stagePair, stageInput, Fin.val_castLE]
    rw [prefix_comp]
  · exact tableAt_prefix p h i z

theorem measurable_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) : Measurable (experimentPrefix p m n h) := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact measurable_id
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        simpa only [show experimentPrefix p (n+1) (n+1) h = id from funext (prefix_self p _ h)]
          using measurable_id
      · have hmn : m ≤ n := by omega
        have heq : experimentPrefix p m (n+1) h = (experimentPrefix p m n hmn) ∘ Prod.fst :=
          funext (prefix_succ p hmn)
        rw [heq]
        exact (ih hmn).comp measurable_fst

theorem measurable_tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (tableAt p n i) :=
  measurable_snd.comp (measurable_prefix p i.isLt)

theorem measurable_evaluate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (evaluate p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun z : Experiment p n × StageTables p n =>
        successor p n (evaluate p n z.1) z.2)
      have hleft : Measurable (fun z : Experiment p n × StageTables p n =>
          evaluate p n z.1) := ih.comp measurable_fst
      have hright : Measurable (fun z : Experiment p n × StageTables p n => z.2) :=
        measurable_snd
      have hpair : Measurable (fun z : Experiment p n × StageTables p n =>
          (evaluate p n z.1, z.2)) := hleft.prodMk hright
      have hsuccessor : Measurable (fun w : StageMaps p n × StageTables p n =>
          successor p n w.1 w.2) := measurable_successor p n
      exact @Measurable.comp
        (Experiment p n × StageTables p n) (StageMaps p n × StageTables p n) (StageMaps p (n+1))
        inferInstance inferInstance inferInstance
        (fun w : StageMaps p n × StageTables p n => successor p n w.1 w.2)
        (fun z : Experiment p n × StageTables p n => (evaluate p n z.1, z.2))
        hsuccessor hpair

theorem measurable_history {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (history p n) := by
  apply measurable_pi_lambda _
  intro i
  exact (measurable_evaluate p i.val).comp (measurable_prefix p (by omega))

theorem measurable_stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (stageInput p n i) :=
  (measurable_evaluate p i.val).comp (measurable_prefix p (by omega))

theorem measurable_stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Measurable (stagePair p n i) :=
  (measurable_stageInput p n i).prodMk (measurable_tableAt p n i)


def freshLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageTables p n) :=
  tableMeasure (Presentation (perturbationOddScale p) n) p

instance freshLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (freshLaw p n) :=
  inferInstanceAs (IsProbabilityMeasure (tableMeasure (Presentation (perturbationOddScale p) n) p))

def experimentLaw {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → Measure (Experiment p n)
  | 0 => Measure.dirac ()
  | n+1 => (experimentLaw p n).prod (freshLaw p n)

instance experimentLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (experimentLaw p n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure ((experimentLaw p n).prod (freshLaw p n))
      infer_instance

theorem measurePreserving_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    MeasurePreserving (experimentPrefix p m n h) (experimentLaw p n) (experimentLaw p m) := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact MeasurePreserving.id _
  | succ n ih =>
      by_cases hm : m = n+1
      · subst m
        simpa only [show experimentPrefix p (n+1) (n+1) h = id from funext (prefix_self p _ h)]
          using MeasurePreserving.id (experimentLaw p (n+1))
      · have hmn : m ≤ n := by omega
        have heq : experimentPrefix p m (n+1) h = (experimentPrefix p m n hmn) ∘ Prod.fst :=
          funext (prefix_succ p hmn)
        rw [heq]
        exact (ih hmn).comp measurePreserving_fst

theorem measurePreserving_tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    MeasurePreserving (tableAt p n i) (experimentLaw p n) (freshLaw p i.val) :=
  measurePreserving_snd.comp (measurePreserving_prefix p i.isLt)

theorem tableAt_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (experimentLaw p n).map (tableAt p n i) = freshLaw p i.val :=
  (measurePreserving_tableAt p n i).map_eq

theorem tableAt_preimage {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (B : Set (StageTables p i.val)) (hB : MeasurableSet B) :
    experimentLaw p n (tableAt p n i ⁻¹' B) = freshLaw p i.val B := by
  rw [← Measure.map_apply (measurable_tableAt p n i) hB, tableAt_law]

/-- The full dependent rectangle splits into the preceding rectangle and final table set. -/
theorem full_rectangle_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin (n+1)) → Set (StageTables p i.val)) :
    {z : Experiment p (n+1) | ∀ i, tableAt p (n+1) i z ∈ B i} =
      {z : Experiment p n | ∀ i : Fin n, tableAt p n i z ∈ B i.castSucc} ×ˢ
        B (Fin.last n) := by
  ext z
  constructor
  · intro hz
    exact ⟨fun i => by simpa only [tableAt_castSucc] using hz i.castSucc,
      by simpa only [tableAt_last] using hz (Fin.last n)⟩
  · rintro ⟨hfirst, hlast⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [tableAt_last] using hlast
    · simpa only [tableAt_castSucc] using hfirst j

/-- Arbitrary table rectangles have the actual product probability, including zero stages. -/
theorem full_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n {z | ∀ i, tableAt p n i z ∈ B i} =
      ∏ i : Fin n, freshLaw p i.val (B i) := by
  induction n with
  | zero =>
      have heq : {z : Experiment p 0 | ∀ i : Fin 0, tableAt p 0 i z ∈ B i} = Set.univ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro i
        exact Fin.elim0 i
      rw [heq]
      simp only [Fin.prod_univ_zero]
      exact measure_univ
  | succ n ih =>
      rw [full_rectangle_succ]
      change (experimentLaw p n).prod (freshLaw p n) _ = _
      rw [Measure.prod_prod, ih, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]

/-- Every selected finite rectangle factors; unused factors remain the original whole laws. -/
theorem finite_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (A : Finset (Fin n)) (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n (⋂ i ∈ A, tableAt p n i ⁻¹' B i) =
      ∏ i ∈ A, freshLaw p i.val (B i) := by
  let full : (i : Fin n) → Set (StageTables p i.val) :=
    fun i => if i ∈ A then B i else Set.univ
  have hset : {z : Experiment p n | ∀ i, tableAt p n i z ∈ full i} =
      ⋂ i ∈ A, tableAt p n i ⁻¹' B i := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i hi
      simpa only [full, if_pos hi] using h i
    · intro h i
      by_cases hi : i ∈ A
      · simpa only [full, if_pos hi] using h i hi
      · simp only [full, if_neg hi, Set.mem_univ]
  rw [← hset, full_rectangle_probability]
  calc
    (∏ i : Fin n, freshLaw p i.val (full i)) =
        ∏ i ∈ A, freshLaw p i.val (full i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ A)
      intro i _ hi
      simp only [full, if_neg hi, measure_univ]
    _ = ∏ i ∈ A, freshLaw p i.val (B i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [full, if_pos hi]

theorem tableAt_iIndepFun {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    iIndepFun (tableAt p n) (experimentLaw p n) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hB
  rw [finite_rectangle_probability]
  apply Finset.prod_congr rfl
  intro i hi
  exact (tableAt_preimage p n i (B i) (hB i hi)).symm

def outputLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageMaps p n) :=
  (experimentLaw p n).map (evaluate p n)

instance outputLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (outputLaw p n) :=
  Measure.isProbabilityMeasure_map (measurable_evaluate p n).aemeasurable

@[simp] theorem outputLaw_zero {L : ℝ} (p : GeometricParameters L) :
    outputLaw p 0 = Measure.dirac (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)) := by
  change (Measure.dirac (() : Experiment p 0)).map (evaluate p 0) = _
  exact Measure.map_dirac' (measurable_evaluate p 0) ()

def freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Experiment p (n+1) → StageMaps p n × StageTables p n :=
  fun z => (evaluate p n z.1, z.2)

theorem measurable_freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (freshPair p n) :=
  ((measurable_evaluate p n).comp measurable_fst).prodMk measurable_snd

theorem freshPair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (experimentLaw p (n+1)).map (freshPair p n) =
      (outputLaw p n).prod (freshLaw p n) := by
  have hid : Measurable (id : StageTables p n → StageTables p n) := measurable_id
  have h : (outputLaw p n).prod ((freshLaw p n).map (id : StageTables p n → StageTables p n)) =
      ((experimentLaw p n).prod (freshLaw p n)).map
        (Prod.map (evaluate p n) (id : StageTables p n → StageTables p n)) :=
    Measure.map_prod_map (experimentLaw p n) (freshLaw p n) (measurable_evaluate p n) hid
  rw [Measure.map_id] at h
  have hfun : Prod.map (evaluate p n) (id : StageTables p n → StageTables p n) = freshPair p n := by
    funext z
    rcases z with ⟨x,T⟩
    rfl
  rw [hfun] at h
  exact h.symm

theorem stagePair_eq_freshPair_prefix {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    stagePair p n i = (freshPair p i.val) ∘ experimentPrefix p (i.val+1) n i.isLt := by
  funext z
  apply Prod.ext
  · change evaluate p i.val (experimentPrefix p i.val n (by omega) z) =
      evaluate p i.val (experimentPrefix p (i.val+1) n i.isLt z).1
    congr 1
    rw [← prefix_last p i.val, prefix_comp]
  · rfl

theorem stagePair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (experimentLaw p n).map (stagePair p n i) =
      (outputLaw p i.val).prod (freshLaw p i.val) := by
  rw [stagePair_eq_freshPair_prefix, ← Measure.map_map
    (measurable_freshPair p i.val) (measurable_prefix p i.isLt),
    (measurePreserving_prefix p i.isLt).map_eq, freshPair_law]

theorem prefix_output_law {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) :
    (experimentLaw p n).map ((evaluate p m) ∘ experimentPrefix p m n h) = outputLaw p m := by
  rw [← Measure.map_map (measurable_evaluate p m) (measurable_prefix p h),
    (measurePreserving_prefix p h).map_eq]
  rfl


end Decoded

def decodeExperiment {L : ℝ} (p : GeometricParameters L) :
    (N : ℕ) → Experiment p N → Decoded.Experiment p N
  | 0,_ => ()
  | N+1,z => (decodeExperiment p N z.1,decodedTable (perturbationOddScale p) N z.2)

def encodeExperiment {L : ℝ} (p : GeometricParameters L) :
    (N : ℕ) → Decoded.Experiment p N → Experiment p N
  | 0,_ => ()
  | N+1,z => (encodeExperiment p N z.1,SR.encodeSamples (perturbationOddScale p) N z.2)

theorem encode_decode {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    encodeExperiment p N (decodeExperiment p N z)=z := by
  induction N with
  | zero => change (() : Unit) = z; exact Subsingleton.elim _ _
  | succ N ih => exact Prod.ext (ih z.1) (encoded_decoded _ N z.2)

theorem decode_encode {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Decoded.Experiment p N) :
    decodeExperiment p N (encodeExperiment p N z)=z := by
  induction N with
  | zero => change (() : Unit) = z; exact Subsingleton.elim _ _
  | succ N ih =>
    exact Prod.ext (ih z.1)
      (Resampling.VariableRelabeling.decode_encode_table (SR.decode _ N) z.2)

theorem measurable_decodeExperiment {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (decodeExperiment p N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      change Measurable (fun z : Experiment p N × StageTables p N =>
        (decodeExperiment p N z.1,decodedTable (perturbationOddScale p) N z.2))
      exact (ih.comp measurable_fst).prodMk
        ((Resampling.VariableRelabeling.measurable_decodeTable (SR.decode _ N)).comp measurable_snd)

theorem measurable_encodeExperiment {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (encodeExperiment p N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      change Measurable (fun z : Decoded.Experiment p N × Decoded.StageTables p N =>
        (encodeExperiment p N z.1,SR.encodeSamples (perturbationOddScale p) N z.2))
      exact (ih.comp measurable_fst).prodMk
        ((Resampling.VariableRelabeling.measurable_encodeTable (SR.decode _ N)).comp measurable_snd)

/-- Entire product transport, with every original table factor, all columns and
all entries retained. This does not use any resampling-order invariance. -/
theorem decodeExperiment_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (experimentLaw p N).map (decodeExperiment p N)=Decoded.experimentLaw p N := by
  induction N with
  | zero => exact Measure.map_dirac' measurable_const ()
  | succ N ih =>
    have h := Measure.map_prod_map (experimentLaw p N) (freshLaw p N)
      (measurable_decodeExperiment p N)
      (Resampling.VariableRelabeling.measurable_decodeTable (SR.decode (perturbationOddScale p) N))
    change ((experimentLaw p N).map (decodeExperiment p N)).prod
      ((freshLaw p N).map (decodedTable (perturbationOddScale p) N)) =
      ((experimentLaw p N).prod (freshLaw p N)).map
        (Prod.map (decodeExperiment p N) (decodedTable (perturbationOddScale p) N)) at h
    change ((experimentLaw p N).prod (freshLaw p N)).map
      (Prod.map (decodeExperiment p N) (decodedTable (perturbationOddScale p) N)) =
        (Decoded.experimentLaw p N).prod (Decoded.freshLaw p N)
    rw [←h,ih]
    change (Decoded.experimentLaw p N).prod
      ((nativeTableMeasure (perturbationOddScale p) N p).map (decodedTable _ N)) = _
    rw [decoded_table_law]
    rfl

theorem evaluate_decoded {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    evaluate p N z=Decoded.evaluate p N (decodeExperiment p N z) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change successor p N (evaluate p N z.1) z.2 =
      Decoded.successor p N (Decoded.evaluate p N (decodeExperiment p N z.1))
        (decodedTable (perturbationOddScale p) N z.2)
    rw [←ih]
    unfold successor nativePerturbed Decoded.successor
    rw [nativeOutput_decoded]

theorem decode_prefix {L : ℝ} (p : GeometricParameters L) (m N : ℕ) (h : m≤N)
    (z : Experiment p N) : decodeExperiment p m (experimentPrefix p m N h z) =
      Decoded.experimentPrefix p m N h (decodeExperiment p N z) := by
  induction N with
  | zero =>
      have hm : m=0 := by omega
      subst m
      rfl
  | succ N ih =>
    by_cases he : m=N+1
    · subst m
      rw [prefix_self,Decoded.prefix_self]
    · have hm : m≤N := by omega
      rw [prefix_succ p hm,Decoded.prefix_succ p hm]
      exact ih hm z.1

theorem history_decoded {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    history p N z=Decoded.history p N (decodeExperiment p N z) := by
  funext i
  change evaluate p i.val (experimentPrefix p i.val N (by omega) z) = _
  rw [evaluate_decoded,decode_prefix]
  rfl

theorem tableAt_decoded {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : decodedTable (perturbationOddScale p) i.val (tableAt p N i z)=
      Decoded.tableAt p N i (decodeExperiment p N z) := by
  have h := decode_prefix p (i.val+1) N i.isLt z
  exact congrArg Prod.snd h

/-- Simultaneous whole factor/history transport, retaining the incoming map and
whole returned assignment at every stage. No adaptive-output independence. -/
theorem full_decoded_history_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (experimentLaw p N).map (fun z => (decodeExperiment p N z,history p N z)) =
      (Decoded.experimentLaw p N).map (fun z => (z,Decoded.history p N z)) := by
  have hm : Measurable (fun z : Decoded.Experiment p N => (z,Decoded.history p N z)) :=
    measurable_id.prodMk (Decoded.measurable_history p N)
  calc
    _ = (experimentLaw p N).map
        ((fun z : Decoded.Experiment p N => (z,Decoded.history p N z)) ∘ decodeExperiment p N) := by
      congr 1
      funext z
      exact Prod.ext rfl (history_decoded p N z)
    _ = _ := by rw [←Measure.map_map hm (measurable_decodeExperiment p N),decodeExperiment_law]

/-- Exact decomposition of the actual recursion: unchanged native work,
additional first-match input reads, affine row transfer, replacement work. -/
theorem totalCost_decomposition {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : totalCost p N z =
    ∑ i : Fin N,
      (nativeOperationCost (perturbationOddScale p) i.val (stageInput p N i z)
        (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)+
      Paid.additionalIncomingCost (perturbationOddScale p) i.val (inputRows p N i z)
        (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)+
      (perturbLabelCost p i.val : ℝ≥0∞)+(materializationLabelCost p i.val : ℝ≥0∞)) := by
  rw [totalCost_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [stageCost,inputRows_eq,stageQuery_cost,Paid.operationCost_decomposition,
    rowMap_canonical,deterministicCost,Nat.cast_add]
  ac_rfl

namespace Paid

def prefixObservation (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (SR.Index S n → ℕ × Space) × Trace S n × ℕ :=
  ((fun a => (SR.readQ a (prefixQ S n I r lambda K T m).value.1).value),
    (prefixQ S n I r lambda K T m).value.2,(prefixQ S n I r lambda K T m).operations)

/-- Complete actual row/counter/payload/trace/cost view. Only fixed native
labels are discrete; every point coordinate has its original Borel structure. -/
theorem measurable_prefixObservation (S : OddScale) (n : ℕ) {r : ℝ} (hr : 0≤r)
    (lambda : ℝ) (K m : ℕ) : Measurable (fun z : JointInput S n =>
      prefixObservation S n (canonicalRows S n z.1) r lambda K z.2 m) := by
  have hp := BDL26NativeGeometricJointExecution.measurable_native_prefix S n hr lambda K m
  have hc := measurable_countedPrefix S n r lambda K m
  convert hp.fst.prodMk (hp.snd.fst.prodMk hc.snd.snd) using 1
  funext z
  have h := prefix_refinement S n (canonicalRows S n z.1) hr lambda K z.2 m
  have h' := prefix_counted S n (canonicalRows S n z.1) r lambda K z.2 m
  rw [rowMap_canonical] at h
  exact Prod.ext (funext (fun a => congrArg (fun R => (SR.readQ a R).value) h.1))
    (Prod.ext h.2.1 h'.2.2)

end Paid

abbrev StageObservation {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  StageMaps p n ×
  (ℕ → (SR.Index (perturbationOddScale p) n → ℕ × Space) × Trace (perturbationOddScale p) n × ℕ) ×
  (ℕ → Option (Code (perturbationOddScale p) n)) × Bool × ℕ ×
  StageMaps p n × StageMaps p n × StageMaps p (n+1) × ℝ≥0∞

def jointObservation {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : JointInput (perturbationOddScale p) n) : StageObservation p n :=
  (z.1,
   (fun time => Paid.prefixObservation _ n (canonicalRows _ n z.1)
     (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) z.2 time),
   (fun time => BDL26NativeGeometricJointExecution.codedChoice _ n z.1
     (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 time),
   (if NativeHalts _ n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 then true else false),
   nativeHaltTime _ n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2,
   nativeOutput _ n z.1 p z.2,nativePerturbed p n z.1 z.2,successor p n z.1 z.2,
   jointStageCost p n z)

theorem measurable_jointObservation {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (jointObservation p n) := by
  have hchoice (m : ℕ) :=
    (measurable_native_selection (perturbationOddScale p) n (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda) m).fst
  exact measurable_fst.prodMk
    ((measurable_pi_lambda _ (fun time => Paid.measurable_prefixObservation _ n
      (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) time)).prodMk
    ((measurable_pi_lambda _ hchoice).prodMk
    ((Measurable.ite (BDL26NativeGeometricJointExecution.measurableSet_native_halts _ n
      (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda)) measurable_const measurable_const).prodMk
    ((BDL26NativeGeometricJointExecution.measurable_native_clock _ n (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda)).prodMk
    ((measurable_joint_nativeOutput _ n p).prodMk
    ((measurable_nativePerturbed p n).prodMk
    ((measurable_successor p n).prodMk (measurable_jointStageCost p n))))))))

abbrev Observation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :=
  ((i : Fin (N+1)) → StageMaps p i.val) ×
  ((i : Fin N) → StageObservation p i.val) × (Fin N → ℝ≥0∞) × ℝ≥0∞

def observation {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : Observation p N :=
  (history p N z,(fun i => jointObservation p i.val (stagePair p N i z)),
    (fun i => stageCost p N i z),totalCost p N z)

theorem measurable_observation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (observation p N) :=
  (measurable_history p N).prodMk
    ((measurable_pi_lambda _ (fun i => (measurable_jointObservation p i.val).comp
      (measurable_stagePair p N i))).prodMk
    ((measurable_pi_lambda _ (measurable_stageCost p N)).prodMk (measurable_totalCost p N)))

/-- All actually retained incoming and returned rows are the complete canonical
label/payload list of the measured full history, with no missing assignment. -/
theorem retained_history {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N)
    (i : Fin (N+1)) :
    (run p i.val (experimentPrefix p i.val N (by omega) z)).1 =
      canonicalRows (perturbationOddScale p) i.val (history p N z i) ∧
    rowMap (perturbationOddScale p) i.val
      (run p i.val (experimentPrefix p i.val N (by omega) z)).1=history p N z i := by
  rw [run_rows,rowMap_canonical]
  exact ⟨rfl,rfl⟩

/-- Exceptional values and infinite costs refer to the very same stage table. -/
theorem stage_nontermination_default {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : ¬stageHalts p N i z) :
    stageCost p N i z=∞ ∧
    nativeHaltTime (perturbationOddScale p) i.val (stageInput p N i z)
      (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)=0 ∧
    nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z)=
      (fun v => (tableAt p N i z) ((SR.decode (perturbationOddScale p) i.val).symm v,0)) := by
  have hdefault := joint_nontermination_default (perturbationOddScale p) i.val
    (stageInput p N i z) (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z) h
  exact ⟨stageCost_nonhalting p N i z h,hdefault.2.1,hdefault.2.2⟩

/-- Whole paid-prefix refinement to the original decoded execution with the
SAME native key, retaining generated trace, every counter and every sample. -/
theorem paid_prefix_decoded (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0≤r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (Paid.prefixQ S n I r lambda K T m).value.1 =
      sampleRows S n T (fun a => counters (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n (rowMap S n I) r) (B S n (rowMap S n I) r lambda K)
        (decodedTable S n T) m (SR.decode S n a)) ∧
    (Paid.prefixQ S n I r lambda K T m).value.2 =
      (originalTrace S n (rowMap S n I) r lambda K (decodedTable S n T) m).map
        (Option.map (originalCode S n (rowMap S n I) r)) ∧
    Paid.choice S n I r lambda K T m =
      (selected (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n (rowMap S n I) r) (B S n (rowMap S n I) r lambda K)
        (decodedTable S n T) m).map (originalCode S n (rowMap S n I) r) := by
  have h := native_prefix_original S n (rowMap S n I) hr lambda K (decodedTable S n T) m
  rw [encoded_decoded] at h
  have hp := Paid.prefix_refinement S n I hr lambda K T m
  exact ⟨hp.1.trans h.2.2,hp.2.1.trans h.2.1,
    (Paid.choice_refinement S n I hr lambda K T m).trans h.1⟩

/-- Whole product and every paid observation travel together through the
proved inverse relabeling. The decoded mathematical recursion is separately
identified by evaluate_decoded/history_decoded, using the identical key. -/
theorem full_paid_observation_decode_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (experimentLaw p N).map (fun z => (decodeExperiment p N z,observation p N z)) =
      (Decoded.experimentLaw p N).map
        (fun z => (z,observation p N (encodeExperiment p N z))) := by
  have hm : Measurable (fun z : Decoded.Experiment p N =>
      (z,observation p N (encodeExperiment p N z))) :=
    measurable_id.prodMk ((measurable_observation p N).comp (measurable_encodeExperiment p N))
  calc
    _ = (experimentLaw p N).map
        ((fun z : Decoded.Experiment p N => (z,observation p N (encodeExperiment p N z))) ∘
          decodeExperiment p N) := by
      congr 1
      funext z
      simp only [Function.comp_def,encode_decode]
    _ = _ := by rw [←Measure.map_map hm (measurable_decodeExperiment p N),decodeExperiment_law]

theorem finiteSuccess_measure {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    experimentLaw p N (finiteSuccess p N)=1 := by
  calc
    _ = experimentLaw p N Set.univ := by
      apply measure_congr
      filter_upwards [finiteSuccess_ae p N] with z hz
      exact propext (iff_true_intro hz)
    _ = 1 := measure_univ

end QEC.Coding.BDL26NativeFiniteComposition
