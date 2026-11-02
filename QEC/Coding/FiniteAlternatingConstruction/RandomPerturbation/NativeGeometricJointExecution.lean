import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeGeometricExecutionCost
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedCostMeasurability
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.GoodMapMeasurability

/-!
# Joint incoming/native-table execution and its genuine paid-cost law

The fixed labels below are the generated native master rows, not a new event
universe. Only eligibility proofs are erased. Candidate rejection, four-key
sorting, every geometric query, native refresh and growing append retain their
actual numeric costs. Spatial coordinates always have their original finite
product Borel structure. No adaptive-output independence is asserted.
-/
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

abbrev Input (S : OddScale) (n : ℕ) := Vertex (Presentation S n) → Space
abbrev JointInput (S : OddScale) (n : ℕ) := Input S n × NativeTable S n
abbrev Code (S : OddScale) (n : ℕ) := GeneratedRow S n

instance codeFintype (S : OddScale) (n : ℕ) : Fintype (Code S n) :=
  Fintype.ofEquiv (MasterEvent (Presentation S n)) (MC.masterEquiv S n).symm
/-- Countability is transported by a proved injection, so later measurability
proofs do not normalize the generated enumeration inside a Fintype witness. -/
private theorem code_countable (S : OddScale) (n : ℕ) : Countable (Code S n) :=
  (MC.masterEquiv S n).injective.countable

instance codeCountable (S : OddScale) (n : ℕ) : Countable (Code S n) :=
  code_countable S n

instance codeMeasurable (S : OddScale) (n : ℕ) : MeasurableSpace (Code S n) := ⊤
instance codeSingleton (S : OddScale) (n : ℕ) :
    MeasurableSingletonClass (Code S n) := ⟨fun _ => trivial⟩

/-- Only countable native labels receive a discrete sigma algebra. -/
abbrev Trace (S : OddScale) (n : ℕ) := List (Option (Code S n))
instance traceMeasurable (S : OddScale) (n : ℕ) : MeasurableSpace (Trace S n) := ⊤
instance traceSingleton (S : OddScale) (n : ℕ) :
    MeasurableSingletonClass (Trace S n) := ⟨fun _ => trivial⟩
local instance labelListMeasurable (A : Type*) [Countable A] :
    MeasurableSpace (List A) := ⊤
local instance labelListSingleton (A : Type*) [Countable A] :
    MeasurableSingletonClass (List A) := ⟨fun _ => trivial⟩

abbrev CountState (S : OddScale) (n : ℕ) :=
  (SR.Index S n → ℕ) × Trace S n × ℕ

def sampleRows (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (c : SR.Index S n → ℕ) : SR.Rows (SR.Index S n) :=
  SR.rowsFor (SR.indices (SR.count S n)) T c

def eraseChoice (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    Option (LiveRow S n J r) → Option (Code S n) := Option.map Subtype.val

def codeSupport (S : OddScale) (n : ℕ) : Option (Code S n) → List (SR.Index S n)
  | none => []
  | some row => row.val.2.getD []

private theorem support_erased (S : OddScale) (n : ℕ) (J : Input S n)
    (r : ℝ) (e : Option (LiveRow S n J r)) :
    codeSupport S n (eraseChoice S n J r e) = chosenSupport S n J r e := by
  cases e <;> rfl

def codeCandidateQ (S : OddScale) (n : ℕ) (J : Input S n)
    (r : ℝ) (row : Code S n) : Option (Code S n) × ℕ :=
  let q := eligibleQ S n J r row.val.1
  (if q.1 then some row else none, q.2+1)

private theorem candidate_erased (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (row : Code S n) :
    codeCandidateQ S n J r row =
      (eraseChoice S n J r (candidateQ S n J hr row).1,
        (candidateQ S n J hr row).2) := by
  by_cases h : (eligibleQ S n J r row.val.1).1 = true
  · simp only [codeCandidateQ,candidateQ,if_pos h,dif_pos h,
      eraseChoice,Option.map_some]
  · simp only [codeCandidateQ,candidateQ,if_neg h,dif_neg h,
      eraseChoice,Option.map_none]

def codeCompareQ (S : OddScale) (n : ℕ) (a b : Code S n) : Bool × ℕ :=
  let A := fourKeyQ a.val.1
  let B := fourKeyQ b.val.1
  let compared := lexLEQuery A.1 B.1
  (compared.1,A.2+B.2+compared.2+1)

def codeRawUniverseQ (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    List (Code S n) × ℕ :=
  let generated := MC.masterCandidatesQ S n
  let scanned := filterMapQuery (codeCandidateQ S n J r) (MC.Rows S n).attach
  (scanned.1,generated.operations+scanned.2+1)

private theorem raw_erased (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) :
    codeRawUniverseQ S n J r =
      ((rawUniverseQ S n J hr).1.map Subtype.val,(rawUniverseQ S n J hr).2) := by
  have h := filterMapQuery_map_pair
    (fun e : LiveRow S n J r => e.val) (candidateQ S n J hr)
    (codeCandidateQ S n J r) (candidate_erased S n J hr) (MC.Rows S n).attach
  simp only [codeRawUniverseQ,rawUniverseQ]
  rw [h]

def codeUniverseQ (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    List (Code S n) × ℕ :=
  let raw := codeRawUniverseQ S n J r
  let sorted := sortQuery (codeCompareQ S n) raw.1
  (sorted.1,raw.2+sorted.2)

private theorem universe_erased (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) :
    codeUniverseQ S n J r =
      ((universeQ S n J hr).1.map Subtype.val,(universeQ S n J hr).2) := by
  have h := sortQuery_map_pair (fun e : LiveRow S n J r => e.val)
    (compareQ S n J r) (codeCompareQ S n) (fun _ _ => rfl)
    (rawUniverseQ S n J hr).1
  simp only [codeUniverseQ,universeQ,raw_erased S n J hr]
  rw [h]

/-- Exactly the original native grid/triangle query on generated row data. -/
def codeEventQ (S : OddScale) (n : ℕ) (J : Input S n)
    (lambda : ℝ) (K : ℕ) (row : Code S n)
    (R : SR.Rows (SR.Index S n)) : Bool × ℕ :=
  let net := gridListQuery K
  let query := listAnyQuery (fun g =>
    let center := centerQ S n J lambda K row.val.1 g
    let triangles := listAllQuery (fun c => triangleCodeQ S n J lambda R c center.1)
      (MC.codeList row.val.1)
    (triangles.1,center.2+triangles.2+2)) net.1
  (query.1,net.2+query.2+1)

def codeScanQ (S : OddScale) (n : ℕ) (J : Input S n)
    (r lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    Option (Code S n) × ℕ :=
  let candidates := codeUniverseQ S n J r
  let scan := scanQuery (codeEventQ S n J lambda K) candidates.1 R
  (scan.1,candidates.2+scan.2+1)

/-- Full paid-pair conjugacy, including rejected candidates and native sorting. -/
theorem code_scan_refinement (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (R : SR.Rows (SR.Index S n)) :
    codeScanQ S n J r lambda K R =
      (eraseChoice S n J r (scanQ S n J hr lambda K R).1,
        (scanQ S n J hr lambda K R).2) := by
  have h := countedScan_map_pair (fun e : LiveRow S n J r => e.val)
    (eventQueryQ S n J r lambda K) (codeEventQ S n J lambda K)
    (fun _ _ => rfl) (universeQ S n J hr).1 R
  simp only [codeScanQ,scanQ,universe_erased S n J hr,h,eraseChoice]

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

private theorem incoming_fee (S : OddScale) (n : ℕ) (J : Input S n) :
    (incomingQ S n J).operations = incomingBudget S n :=
  (BDL26NativeStateRows.initialize_cost S n _).1

private theorem incoming_labels (S : OddScale) (n : ℕ) (J : Input S n) :
    (incomingQ S n J).value.map Prod.fst = SR.indices (SR.count S n) :=
  BDL26NativeStateRows.initialize_order S n _

private theorem sample_point (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (c : SR.Index S n → ℕ) (a : SR.Index S n) :
    originalPoints S n (sampleRows S n T c) (SR.decode S n a) = T (a,c a) := by
  simp only [originalPoints,BDL26NativeStateRows.points,Equiv.symm_apply_apply,sampleRows]
  rw [SR.read_rowsFor _ _ _ _ (SR.indices_complete _ _)]

private theorem measurable_point (S : OddScale) (n : ℕ) (lambda : ℝ)
    (c : SR.Index S n → ℕ) (a : SR.Index S n) :
    Measurable (fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) a) := by
  have he : (fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) a) =
      (fun z : JointInput S n =>
        (lambda • ((1/2 : ℝ) • z.1 (SR.decode S n a))+z.2 (a,c a),
          readFee a (SR.indices (SR.count S n))+
            readFee a (SR.indices (SR.count S n))+24+2)) := by
    funext z
    apply Prod.ext
    · rw [point_actual,sample_point]
    · simp only [pointQ,pointSnapshotQuery_cost,read_fee,incoming_labels,sample_labels]
  rw [he]
  have hJ : Measurable (fun z : JointInput S n => z.1 (SR.decode S n a)) :=
    (measurable_pi_apply _).comp measurable_fst
  have hT : Measurable (fun z : JointInput S n => z.2 (a,c a)) :=
    (measurable_pi_apply _).comp measurable_snd
  exact (((hJ.const_smul (1/2 : ℝ)).const_smul lambda).add hT).prodMk measurable_const

private theorem measurable_pair (S : OddScale) (n : ℕ) (r : ℝ)
    (a b : MD.Code) : Measurable (fun J : Input S n => pairQ S n J r a b) := by
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
              incomingBudget S n+readFee A.1.1 (SR.indices (SR.count S n))+
              readFee B.1.1 (SR.indices (SR.count S n))+q.2+5)) :=
        measurable_of_countable _
      simpa only [pairQ,ha,hb,incoming_read,incoming_fee,read_fee,incoming_labels,
        Function.comp_def] using hm.comp hq

private theorem measurable_eligible (S : OddScale) (n : ℕ) (r : ℝ)
    (codes : MD.FourCodes) : Measurable (fun J : Input S n => eligibleQ S n J r codes) :=
  measurable_listAllQuery _
    (fun a => measurable_listAllQuery _ (measurable_pair S n r a) (MC.codeList codes))
    (MC.codeList codes)

/-- Expose only the outer preprocessing composition. The full generated
candidate list remains an uninterpreted argument to the same filter and sort. -/
private theorem codeUniverse_factor (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    codeUniverseQ S n J r =
      (let q := filterMapQuery (codeCandidateQ S n J r) (MC.Rows S n).attach
       let sorted := sortQuery (codeCompareQ S n) q.1
       (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) := by
  rfl

private theorem measurable_universe (S : OddScale) (n : ℕ) (r : ℝ) :
    Measurable (fun J : Input S n => codeUniverseQ S n J r) := by
  have hc (row : Code S n) : Measurable (fun J : Input S n => codeCandidateQ S n J r row) :=
    (measurable_of_countable (fun q : Bool × ℕ =>
      (if q.1 then some row else none,q.2+1))).comp (measurable_eligible S n r row.val.1)
  have hr := measurable_filterMapQuery (fun row J => codeCandidateQ S n J r row)
    hc (MC.Rows S n).attach
  have hm : Measurable (fun q : List (Code S n) × ℕ =>
      let sorted := sortQuery (codeCompareQ S n) q.1
      (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) :=
    measurable_of_countable _
  have he : (fun J : Input S n => codeUniverseQ S n J r) =
      (fun J : Input S n =>
        let q := filterMapQuery (codeCandidateQ S n J r) (MC.Rows S n).attach
        let sorted := sortQuery (codeCompareQ S n) q.1
        (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) := by
    funext J
    exact codeUniverse_factor S n J r
  rw [he]
  exact hm.comp hr

private theorem measurable_center (S : OddScale) (n : ℕ) (lambda : ℝ)
    (K : ℕ) (codes : MD.FourCodes) (g : Grid K) :
    Measurable (fun J : Input S n => centerQ S n J lambda K codes g) := by
  cases hf : (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).value with
  | none => simp only [centerQ,hf]; exact measurable_const
  | some v =>
    have hp := measurable_pointSnapshotQuery lambda
      (fun J : Input S n => J (SR.decode S n v.1))
      (fun _ : Input S n => (gridPointQuery K g).1)
      (measurable_pi_apply _) measurable_const
    have he : (fun J : Input S n => centerQ S n J lambda K codes g) =
        (fun J : Input S n =>
          ((pointSnapshotQuery lambda (J (SR.decode S n v.1)) (gridPointQuery K g).1).1,
            (anchorCodeQ codes).2+(MD.atlasQ S n).operations+
              (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).operations+
              incomingBudget S n+readFee v.1 (SR.indices (SR.count S n))+
              (gridPointQuery K g).2+24+3)) := by
      funext J
      simp only [centerQ,hf,incoming_read,incoming_fee,read_fee,incoming_labels,
        pointSnapshotQuery_cost]
    rw [he]
    exact hp.fst.prodMk measurable_const

private theorem measurable_triangle (S : OddScale) (n : ℕ) (lambda : ℝ)
    (c : SR.Index S n → ℕ) (code : MD.Code)
    (center : JointInput S n → Space) (hc : Measurable center) :
    Measurable (fun z : JointInput S n =>
      triangleCodeQ S n z.1 lambda (sampleRows S n z.2 c) code (center z)) := by
  cases hf : (MD.atlasReadQ code (MD.atlasQ S n).value).value with
  | none => simp only [triangleCodeQ,hf]; exact measurable_const
  | some v =>
    let x := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) v.1
    let y := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) v.2.1
    let z' := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) v.2.2
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
          incomingBudget S n+(x z).2+(y z).2+(z' z).2+
          (triangleQuery ![(x z).1,(y z).1,(z' z).1] (center z) 2).2+4) :=
      (((((measurable_const.add hx.snd).add hy.snd).add hz.snd).add hq.snd).add measurable_const)
    convert hq.fst.prodMk hcost using 1
    funext z
    simp only [triangleCodeQ,hf,incoming_fee,x,y,z']

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
      codeEventQ S n z.1 lambda K row (sampleRows S n z.2 c)) := by
  let center : Grid K → JointInput S n → Space × ℕ :=
    fun g z => centerQ S n z.1 lambda K row.val.1 g
  let triangle : MD.Code → JointInput S n → Space → Bool × ℕ :=
    fun a z w => triangleCodeQ S n z.1 lambda (sampleRows S n z.2 c) a w
  have hc (g : Grid K) : Measurable (center g) :=
    (measurable_center S n lambda K row.val.1 g).comp
      (measurable_fst : Measurable (fun z : JointInput S n => z.1))
  have ht (g : Grid K) (a : MD.Code) :
      Measurable (fun z : JointInput S n => triangle a z (center g z).1) :=
    measurable_triangle S n lambda c a _ (hc g).fst
  have hm := measurable_paid_event_fold (gridListQuery K).1 (gridListQuery K).2
    (MC.codeList row.val.1) center triangle hc ht
  have he : (fun z : JointInput S n =>
      codeEventQ S n z.1 lambda K row (sampleRows S n z.2 c)) =
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
      codeScanQ S n z.1 r lambda K (sampleRows S n z.2 c)) := by
  let q : JointInput S n → Code S n → SR.Rows (SR.Index S n) → Bool × ℕ :=
    fun z => codeEventQ S n z.1 lambda K
  let f : JointInput S n → SR.Rows (SR.Index S n) := fun z => sampleRows S n z.2 c
  let candidates : JointInput S n → List (Code S n) × ℕ :=
    fun z => codeUniverseQ S n z.1 r
  have hq (a : Code S n) : Measurable (fun z : JointInput S n => q z a (f z)) :=
    measurable_codeEvent S n lambda K c a
  have hu : Measurable candidates :=
    (measurable_universe S n r).comp
      (measurable_fst : Measurable (fun z : JointInput S n => z.1))
  have hm := measurable_paid_scan q f hq candidates hu
  have he : (fun z : JointInput S n =>
      codeScanQ S n z.1 r lambda K (sampleRows S n z.2 c)) =
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

/-- The exact countable image of a native prefix. The paid-pair theorem below
identifies this image with the real interpreter; it is not a cost surrogate. -/
def countedPrefix (S : OddScale) (n : ℕ) (J : Input S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ → CountState S n
  | 0 => ((fun _ => 0),[],incomingBudget S n+1)
  | m+1 =>
      let prior := countedPrefix S n J r lambda K T m
      let chosen := codeScanQ S n J r lambda K (sampleRows S n T prior.1)
      (SR.advanceList (codeSupport S n chosen.1) prior.1,
        prior.2.1++[chosen.1],
        prior.2.2+chosen.2+refreshFee (codeSupport S n chosen.1)
          (SR.indices (SR.count S n))+(2*prior.2.1.length+1)+4)

/-- Entire rows, every stable-code trace entry, and the precise numeric cost. -/
theorem native_prefix_refinement (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T m).value.rows =
      sampleRows S n T (countedPrefix S n J r lambda K T m).1 ∧
    (prefixQ S n J hr lambda K T m).value.trace.map (eraseChoice S n J r) =
      (countedPrefix S n J r lambda K T m).2.1 ∧
    (prefixQ S n J hr lambda K T m).operations =
      (countedPrefix S n J r lambda K T m).2.2 := by
  induction m with
  | zero =>
    refine ⟨SR.initialize_value S n T,rfl,?_⟩
    exact congrArg (fun k => k+1) (BDL26NativeStateRows.initialize_cost S n T).1
  | succ m ih =>
    let prior := prefixQ S n J hr lambda K T m
    let coded := countedPrefix S n J r lambda K T m
    let q := scanQ S n J hr lambda K prior.value.rows
    let cq := codeScanQ S n J r lambda K (sampleRows S n T coded.1)
    have hs : cq = (eraseChoice S n J r q.1,q.2) := by
      dsimp only [cq,q,prior,coded]
      rw [← ih.1]
      exact code_scan_refinement S n J hr lambda K _
    have hu : codeSupport S n cq.1 = chosenSupport S n J r q.1 :=
      (congrArg (codeSupport S n) (congrArg Prod.fst hs)).trans
        (support_erased S n J r q.1)
    have hl : prior.value.trace.length = coded.2.1.length := by
      have h := congrArg List.length ih.2.1
      simpa only [List.length_map,prior,coded] using h
    refine ⟨?_,?_,?_⟩
    · change (SR.refreshQ T (chosenSupport S n J r q.1) prior.value.rows).value =
        sampleRows S n T (SR.advanceList (codeSupport S n cq.1) coded.1)
      rw [show prior.value.rows=sampleRows S n T coded.1 from ih.1,← hu]
      exact SR.refresh_value T _ _ _
    · change (BDL26NativeMasterCandidates.appendQ prior.value.trace [q.1]).value.map
        (eraseChoice S n J r) = coded.2.1++[cq.1]
      rw [(BDL26NativeMasterCandidates.append_spec _ _).1,List.map_append]
      simp only [List.map_cons,List.map_nil,show prior.value.trace.map
        (eraseChoice S n J r)=coded.2.1 from ih.2.1,hs]
    · change prior.operations+q.2+
        (SR.refreshQ T (chosenSupport S n J r q.1) prior.value.rows).operations+
        (BDL26NativeMasterCandidates.appendQ prior.value.trace [q.1]).operations+4 =
        coded.2.2+cq.2+refreshFee (codeSupport S n cq.1)
          (SR.indices (SR.count S n))+(2*coded.2.1.length+1)+4
      rw [show prior.operations=coded.2.2 from ih.2.2,refresh_fee,
        show prior.value.rows=sampleRows S n T coded.1 from ih.1,sample_labels,
        (BDL26NativeMasterCandidates.append_spec _ _).2.1,hl,← hu,hs]

/-- The countable paid transition on abstract native addresses and labels.
The support, refresh fee, trace append and cumulative cost remain exact. -/
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

private theorem countedPrefix_succ_pair (S : OddScale) (n : ℕ) (J : Input S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    countedPrefix S n J r lambda K T (m+1) =
      (let prior := countedPrefix S n J r lambda K T m
       let chosen := codeScanQ S n J r lambda K (sampleRows S n T prior.1)
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
      countedPrefix S n z.1 r lambda K z.2 m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    let prior : JointInput S n → CountState S n :=
      fun z => countedPrefix S n z.1 r lambda K z.2 m
    let chosen : JointInput S n → Option (Code S n) × ℕ :=
      fun z => codeScanQ S n z.1 r lambda K (sampleRows S n z.2 (prior z).1)
    have hs : Measurable (fun w : JointInput S n × (SR.Index S n → ℕ) =>
        codeScanQ S n w.1.1 r lambda K (sampleRows S n w.1.2 w.2)) :=
      measurable_from_prod_countable_left (measurable_codeScan S n r lambda K)
    have hp : Measurable prior := ih
    have hq : Measurable chosen :=
      measurable_prior_fst_query
        (Ω := JointInput S n) (R := SR.Index S n → ℕ)
        (E := Trace S n × ℕ) (C := Option (Code S n) × ℕ)
        prior
        (fun w : JointInput S n × (SR.Index S n → ℕ) =>
          codeScanQ S n w.1.1 r lambda K (sampleRows S n w.1.2 w.2))
        chosen hp hs (fun _ => rfl)
    exact measurable_counted_transition (codeSupport S n) (SR.indices (SR.count S n))
      prior (fun z => countedPrefix S n z.1 r lambda K z.2 (m+1)) chosen hp hq
      (fun z => countedPrefix_succ_pair S n z.1 r lambda K z.2 m)

def codedChoice (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :=
  eraseChoice S n J r (choice S n J hr lambda K T m)

private theorem measurable_choice (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K m : ℕ) :
    Measurable (fun z : JointInput S n => codedChoice S n z.1 hr lambda K z.2 m) := by
  have hp := measurable_countedPrefix S n r lambda K m
  have hs : Measurable (fun w : JointInput S n × (SR.Index S n → ℕ) =>
      codeScanQ S n w.1.1 r lambda K (sampleRows S n w.1.2 w.2)) :=
    measurable_from_prod_countable_left (measurable_codeScan S n r lambda K)
  convert (hs.comp (measurable_id.prodMk hp.fst)).fst using 1
  funext z
  change eraseChoice S n z.1 r
      (scanQ S n z.1 hr lambda K
        (prefixQ S n z.1 hr lambda K z.2 m).value.rows).1 =
    (codeScanQ S n z.1 r lambda K
      (sampleRows S n z.2 (countedPrefix S n z.1 r lambda K z.2 m).1)).1
  rw [← (native_prefix_refinement S n z.1 hr lambda K z.2 m).1,
    code_scan_refinement]

def prefixObservation (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (SR.Index S n → ℕ × Space) × Trace S n × ℕ :=
  ((fun a => (SR.readQ a (prefixQ S n J hr lambda K T m).value.rows).value),
    (prefixQ S n J hr lambda K T m).value.trace.map (eraseChoice S n J r),
    (prefixQ S n J hr lambda K T m).operations)

/-- Genuine joint measurability, with every row/counter/value and the whole
ordered stable-code trace; no discrete sigma algebra is imposed on Space. -/
theorem measurable_native_prefix (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K m : ℕ) :
    Measurable (fun z : JointInput S n => prefixObservation S n z.1 hr lambda K z.2 m) := by
  have hp := measurable_countedPrefix S n r lambda K m
  have hread : Measurable (fun z : JointInput S n => fun a : SR.Index S n =>
      ((countedPrefix S n z.1 r lambda K z.2 m).1 a,
        z.2 (a,(countedPrefix S n z.1 r lambda K z.2 m).1 a))) := by
    apply measurable_pi_lambda
    intro a
    have hc := (measurable_pi_apply a).comp hp.fst
    have lookup : Measurable (fun z : NativeTable S n × ℕ => z.1 (a,z.2)) :=
      measurable_from_prod_countable_left (fun k => measurable_pi_apply (a,k))
    exact hc.prodMk (lookup.comp (measurable_snd.prodMk hc))
  convert hread.prodMk (hp.snd.fst.prodMk hp.snd.snd) using 1
  funext z
  have he := native_prefix_refinement S n z.1 hr lambda K z.2 m
  apply Prod.ext
  · funext a
    change (SR.readQ a (prefixQ S n z.1 hr lambda K z.2 m).value.rows).value =
      ((countedPrefix S n z.1 r lambda K z.2 m).1 a,
        z.2 (a,(countedPrefix S n z.1 r lambda K z.2 m).1 a))
    rw [he.1]
    exact SR.read_rowsFor _ _ _ _ (SR.indices_complete _ _)
  · exact Prod.ext he.2.1 he.2.2

/-- All selected stable native codes, with their actual paid scan costs. -/
theorem measurable_native_selection (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K m : ℕ) : Measurable
    (fun z : JointInput S n =>
      (codedChoice S n z.1 hr lambda K z.2 m,
        (scanQ S n z.1 hr lambda K (prefixQ S n z.1 hr lambda K z.2 m).value.rows).2)) := by
  have hp := measurable_countedPrefix S n r lambda K m
  have hs : Measurable (fun w : JointInput S n × (SR.Index S n → ℕ) =>
      codeScanQ S n w.1.1 r lambda K (sampleRows S n w.1.2 w.2)) :=
    measurable_from_prod_countable_left (measurable_codeScan S n r lambda K)
  convert hs.comp (measurable_id.prodMk hp.fst) using 1
  funext z
  change (eraseChoice S n z.1 r
      (scanQ S n z.1 hr lambda K
        (prefixQ S n z.1 hr lambda K z.2 m).value.rows).1,
      (scanQ S n z.1 hr lambda K
        (prefixQ S n z.1 hr lambda K z.2 m).value.rows).2) =
    codeScanQ S n z.1 r lambda K
      (sampleRows S n z.2 (countedPrefix S n z.1 r lambda K z.2 m).1)
  rw [← (native_prefix_refinement S n z.1 hr lambda K z.2 m).1,
    code_scan_refinement]

/-- Original keyed events decode to their unique generated native master row. -/
def originalCode (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ)
    (e : Event S n J r) : Code S n :=
  (MC.masterEquiv S n).symm ⟨e.val,e.property.1⟩

private theorem originalCode_event (S : OddScale) (n : ℕ) (J : Input S n)
    (r : ℝ) (row : LiveRow S n J r) :
    originalCode S n J r (event S n J r row) = row.val := by
  simpa only [originalCode,event,master] using
    (MC.masterEquiv S n).symm_apply_apply row.val

/-- Stable codes preserve the entire original selection/trace, not only a
selected coordinate; all original counters and assignments are retained. -/
theorem native_prefix_original (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : OriginalTable S n) (m : ℕ) :
    codedChoice S n J hr lambda K (SR.encodeSamples S n T) m =
      (selected (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n J r) (B S n J r lambda K) T m).map (originalCode S n J r) ∧
    (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.trace.map
        (eraseChoice S n J r) =
      (originalTrace S n J r lambda K T m).map (Option.map (originalCode S n J r)) ∧
    (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.rows =
      sampleRows S n (SR.encodeSamples S n T)
        (fun a => counters (X := fun _ : Vertex (Presentation S n) => Space)
          (U S n J r) (B S n J r lambda K) T m (SR.decode S n a)) := by
  have hc (e : Option (LiveRow S n J r)) :
      eraseChoice S n J r e =
        (e.map (event S n J r)).map (originalCode S n J r) := by
    cases e with
    | none => rfl
    | some row => simp only [eraseChoice,Option.map_some,originalCode_event]
  refine ⟨?_,?_,prefix_rows S n J hr lambda K T m⟩
  · rw [codedChoice,hc,choice_original]
  · rw [← prefix_trace S n J hr lambda K T m,List.map_map]
    exact List.map_congr_left (fun e _ => hc e)

theorem measurableSet_native_halts (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    MeasurableSet {z : JointInput S n | NativeHalts S n z.1 hr lambda K z.2} := by
  have he : {z : JointInput S n | NativeHalts S n z.1 hr lambda K z.2} =
      ⋃ m : ℕ, {z | codedChoice S n z.1 hr lambda K z.2 m = none} := by
    ext z
    simp only [NativeHalts,codedChoice,eraseChoice,Set.mem_setOf_eq,Set.mem_iUnion,
      Option.map_eq_none_iff]
  rw [he]
  exact MeasurableSet.iUnion fun m =>
    (measurable_choice S n hr lambda K m) (measurableSet_singleton none)

/-- The original first-no-event clock, including zero on genuine nontermination. -/
theorem measurable_native_clock (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    Measurable (fun z : JointInput S n => nativeHaltTime S n z.1 hr lambda K z.2) := by
  let pred : JointInput S n → ℕ → Prop := fun z m =>
    codedChoice S n z.1 hr lambda K z.2 m = none ∨
      ¬NativeHalts S n z.1 hr lambda K z.2
  have hp : ∀ z, ∃ m, pred z m := by
    intro z
    by_cases hz : NativeHalts S n z.1 hr lambda K z.2
    · obtain ⟨m,hm⟩ := hz
      exact ⟨m,Or.inl (by simp only [codedChoice,eraseChoice,hm,Option.map_none])⟩
    · exact ⟨0,Or.inr hz⟩
  have hm : Measurable (fun z => Nat.find (hp z)) :=
    measurable_find hp fun m =>
      ((measurable_choice S n hr lambda K m) (measurableSet_singleton none)).union
        (measurableSet_native_halts S n hr lambda K).compl
  convert hm using 1
  funext z
  by_cases hz : NativeHalts S n z.1 hr lambda K z.2
  · simp only [nativeHaltTime,dif_pos hz]
    symm
    exact Nat.find_congr' (by
      intro m
      simp only [pred,hz,not_true_eq_false,or_false,codedChoice,eraseChoice,
        Option.map_eq_none_iff])
  · simp only [nativeHaltTime,dif_neg hz]
    symm
    exact (Nat.find_eq_zero (hp z)).mpr (Or.inr hz)

private theorem measurable_returned (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    Measurable (fun z : JointInput S n => returned S n z.1 hr lambda K z.2) := by
  have hp : Measurable (fun w : JointInput S n × ℕ =>
      (prefixObservation S n w.1.1 hr lambda K w.1.2 w.2).1) :=
    measurable_from_prod_countable_left
      (fun m => (measurable_native_prefix S n hr lambda K m).fst)
  have hs := hp.comp (measurable_id.prodMk (measurable_native_clock S n hr lambda K))
  apply measurable_pi_lambda
  intro v
  exact ((measurable_pi_apply ((SR.decode S n).symm v)).comp hs).snd

/-- Entire returned assignment, not merely coordinates or a separately chosen
good output. Nontermination still returns the original column-zero default. -/
theorem measurable_joint_nativeOutput (S : OddScale) (n : ℕ)
    {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun z : JointInput S n => nativeOutput S n z.1 p z.2) :=
  measurable_returned S n (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda)

/-- Joint measurability includes every actual arithmetic branch cost and infinity. -/
theorem measurable_joint_nativeOperationCost (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    Measurable (fun z : JointInput S n => nativeOperationCost S n z.1 hr lambda K z.2) := by
  have hp : Measurable (fun w : JointInput S n × ℕ =>
      (prefixQ S n w.1.1 hr lambda K w.1.2 w.2).operations) :=
    measurable_from_prod_countable_left
      (fun m => (measurable_native_prefix S n hr lambda K m).snd.snd)
  have hq : Measurable (fun w : JointInput S n × ℕ =>
      (scanQ S n w.1.1 hr lambda K
        (prefixQ S n w.1.1 hr lambda K w.1.2 w.2).value.rows).2) :=
    measurable_from_prod_countable_left
      (fun m => (measurable_native_selection S n hr lambda K m).snd)
  have hs := measurable_id.prodMk (measurable_native_clock S n hr lambda K)
  let finiteCost := fun z : JointInput S n =>
      (((prefixQ S n z.1 hr lambda K z.2 (nativeHaltTime S n z.1 hr lambda K z.2)).operations+
        (scanQ S n z.1 hr lambda K (prefixQ S n z.1 hr lambda K z.2
          (nativeHaltTime S n z.1 hr lambda K z.2)).value.rows).2+
        5*SR.count S n+3 : ℕ) : ℝ≥0∞)
  have hf : Measurable finiteCost :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      ((((hp.comp hs).add (hq.comp hs)).add_const _).add_const _)
  have he : (fun z : JointInput S n => nativeOperationCost S n z.1 hr lambda K z.2) =
      (fun z => if NativeHalts S n z.1 hr lambda K z.2 then finiteCost z else ∞) := by
    funext z
    by_cases h : NativeHalts S n z.1 hr lambda K z.2
    · simp only [nativeOperationCost,if_pos h,finiteCost,
        (native_stopping_refinement S n z.1 hr lambda K z.2 h).2]
    · simp only [nativeOperationCost,if_neg h]
  rw [he]
  exact Measurable.ite (measurableSet_native_halts S n hr lambda K) hf measurable_const

/-- No exceptional branch is silently replaced by zero cost or a chosen output. -/
theorem joint_nontermination_default (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : ¬NativeHalts S n J hr lambda K T) :
    nativeOperationCost S n J hr lambda K T = ∞ ∧
    nativeHaltTime S n J hr lambda K T = 0 ∧
    returned S n J hr lambda K T = (fun v => T ((SR.decode S n).symm v,0)) := by
  have he := native_nontermination_cost_default S n J hr lambda K (decodedTable S n T)
  have hh : ¬NativeHalts S n J hr lambda K (SR.encodeSamples S n (decodedTable S n T)) := by
    simpa only [encoded_decoded] using h
  have hc := he hh
  rw [encoded_decoded] at hc
  exact ⟨hc.1,by simp only [nativeHaltTime,dif_neg h],hc.2⟩

instance nativeTable_probability (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) : IsProbabilityMeasure (nativeTableMeasure S n p) := by
  letI (a : SR.Index S n) := vertexLaw_probability (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 (SR.decode S n a)
  change IsProbabilityMeasure (tableLaw (fun a : SR.Index S n =>
    vertexLaw (Presentation S n) ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m) (SR.decode S n a)))
  infer_instance

instance originalTable_probability (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) : IsProbabilityMeasure (tableMeasure (Presentation S n) p) := by
  letI (v : Vertex (Presentation S n)) := vertexLaw_probability (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  change IsProbabilityMeasure (tableLaw (vertexLaw (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)))
  infer_instance

/-- Genuine product decode law, retaining the incoming map coordinate. -/
theorem joint_decoded_table_law (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν] :
    (ν.prod (nativeTableMeasure S n p)).map
        (fun z : JointInput S n => (z.1,decodedTable S n z.2)) =
      ν.prod (tableMeasure (Presentation S n) p) := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  have hm : Measurable (fun z : JointInput S n => (z.1,decodedTable S n z.2)) :=
    measurable_fst.prodMk (hd.comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hm hs,Measure.prod_apply (hm hs),Measure.prod_apply hs]
  apply lintegral_congr
  intro J
  rw [← decoded_table_law S n p,Measure.map_apply hd
    ((measurable_const.prodMk measurable_id :
      Measurable (fun T : OriginalTable S n => (J,T))) hs)]
  rfl

def jointOutput (S : OddScale) (n : ℕ) {L : ℝ} (p : GeometricParameters L)
    (z : JointInput S n) : Input S n × Input S n := (z.1,nativeOutput S n z.1 p z.2)

private theorem decoded_encoded (S : OddScale) (n : ℕ) (T : OriginalTable S n) :
    decodedTable S n (SR.encodeSamples S n T) = T :=
  Resampling.VariableRelabeling.decode_encode_table (SR.decode S n) T

private theorem measurable_original_jointOutput (S : OddScale) (n : ℕ)
    {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun z : Input S n × OriginalTable S n =>
      (z.1,result (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) z.1 p z.2)) := by
  have he : Measurable (SR.encodeSamples S n) :=
    Resampling.VariableRelabeling.measurable_encodeTable (SR.decode S n)
  have hm := measurable_fst.prodMk
    ((measurable_joint_nativeOutput S n p).comp
      (measurable_fst.prodMk (he.comp measurable_snd)))
  convert hm using 1
  funext z
  change (z.1,result (Presentation S n) (NC.nativeKey S n)
      (NC.nativeKey_injective S n) z.1 p z.2) =
    (z.1,nativeOutput S n z.1 p (SR.encodeSamples S n z.2))
  apply Prod.ext
  · rfl
  · have h := nativeOutput_decoded S n z.1 p (SR.encodeSamples S n z.2)
    simpa only [decoded_encoded] using h.symm

/-- Same original decoded execution law for the entire input/output pair.
Freshness is the product draw, not independence of the adaptive final output. -/
theorem joint_native_output_law (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν] :
    (ν.prod (nativeTableMeasure S n p)).map (jointOutput S n p) =
      (ν.prod (tableMeasure (Presentation S n) p)).map
        (fun z : Input S n × OriginalTable S n =>
          (z.1,result (Presentation S n) (NC.nativeKey S n)
            (NC.nativeKey_injective S n) z.1 p z.2)) := by
  have hd : Measurable (fun z : JointInput S n => (z.1,decodedTable S n z.2)) :=
    measurable_fst.prodMk
      ((Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)).comp measurable_snd)
  rw [← joint_decoded_table_law S n p ν,
    Measure.map_map (measurable_original_jointOutput S n p) hd]
  congr 1
  funext z
  exact Prod.ext rfl (nativeOutput_decoded S n z.1 p z.2)

/-- A test assignment is inserted at every column only for recognizing the
original avoidance predicate. It does not change the execution table law. -/
private def assignmentTable (S : OddScale) (n : ℕ) (w : Input S n) : NativeTable S n :=
  fun a => w (SR.decode S n a.1)

private theorem assignmentTable_points (S : OddScale) (n : ℕ) (w : Input S n) :
    originalPoints S n (sampleRows S n (assignmentTable S n w) (fun _ => 0)) = w := by
  funext v
  have h := sample_point S n (assignmentTable S n w) (fun _ => 0) ((SR.decode S n).symm v)
  simpa only [Equiv.apply_symm_apply,assignmentTable] using h

private theorem good_scan_iff (S : OddScale) (n : ℕ)
    (J w : Input S n) {L : ℝ} (p : GeometricParameters L) :
    w ∈ BDL26NativeGeometricAvoidance.NativeGood S n J p ↔
      w ∈ geometricSupport (Presentation S n) p ∧
        (codeScanQ S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
          (sampleRows S n (assignmentTable S n w) (fun _ => 0))).1 = none := by
  have hs := scan_actual S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda)
    (sampleRows S n (assignmentTable S n w) (fun _ => 0))
  rw [assignmentTable_points] at hs
  have hn : (codeScanQ S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
      (sampleRows S n (assignmentTable S n w) (fun _ => 0))).1 = none ↔
      select (localEvent (U S n J (anchorRadius p.m))
        (B S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) w = none := by
    rw [code_scan_refinement S n J (radius_nonneg p),← hs]
    simp only [eraseChoice,Option.map_eq_none_iff]
  rw [hn]
  change (w ∈ geometricSupport (Presentation S n) p ∧
    w ∈ KeyAvoid (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J p) ↔ _
  apply and_congr_right
  intro _
  simpa only [KeyAvoid,avoid,Set.mem_setOf_eq,Finset.mem_univ,forall_const] using
    (select_none_iff (localEvent (U S n J (anchorRadius p.m))
      (B S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) w).symm

/-- Joint support and scan-none measurability is structural in its input,
table and label carriers; the concrete original good event is identified later. -/
private theorem measurableSet_support_scan_none {X T A : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace (Option A)]
    [MeasurableSingletonClass (Option A)]
    (support : Set X) (hs : MeasurableSet support)
    (table : X → T) (ht : Measurable table)
    (scan : X × T → Option A × ℕ) (hscan : Measurable scan)
    (good : X → Set X)
    (he : ∀ J w, w ∈ good J ↔ w ∈ support ∧ (scan (J,table w)).1 = none) :
    MeasurableSet {y : X × X | y.2 ∈ good y.1} := by
  have hm : Measurable (fun y : X × X => scan (y.1,table y.2)) :=
    hscan.comp (measurable_fst.prodMk (ht.comp measurable_snd))
  have heq : {y : X × X | y.2 ∈ good y.1} =
      {y : X × X | y.2 ∈ support} ∩
      {y : X × X | (scan (y.1,table y.2)).1 = none} := by
    ext y
    exact he y.1 y.2
  rw [heq]
  exact (hs.preimage (measurable_snd : Measurable (fun y : X × X => y.2))).inter
    (hm.fst (measurableSet_singleton none))

/-- The exact original support-and-avoidance event is jointly Borel. This is
the measurable event used below, before its deterministic geometry handoff. -/
theorem measurableSet_joint_nativeGood (S : OddScale) (n : ℕ)
    {L : ℝ} (p : GeometricParameters L) :
    MeasurableSet {y : Input S n × Input S n |
      y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p} := by
  have ht : Measurable (assignmentTable S n) := by
    apply measurable_pi_lambda
    intro a
    exact measurable_pi_apply (SR.decode S n a.1)
  exact measurableSet_support_scan_none
    (geometricSupport (Presentation S n) p) (measurableSet_geometricSupport (Presentation S n) p)
    (assignmentTable S n) ht
    (fun z : JointInput S n => codeScanQ S n z.1 (anchorRadius p.m) p.lambda
      ((6*p.m+2)*p.lambda) (sampleRows S n z.2 (fun _ => 0)))
    (measurable_codeScan S n (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) (fun _ => 0))
    (fun J => BDL26NativeGeometricAvoidance.NativeGood S n J p)
    (fun J w => good_scan_iff S n J w p)

private theorem measurableSet_joint_success (S : OddScale) (n : ℕ)
    {L : ℝ} (p : GeometricParameters L) :
    MeasurableSet {z : JointInput S n |
      IsBoundedDensityLocalMap (Presentation S n) z.1 p.t ∧
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 ∧
      nativeOutput S n z.1 p z.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n z.1 p} := by
  have hI : MeasurableSet {z : JointInput S n |
      IsBoundedDensityLocalMap (Presentation S n) z.1 p.t} :=
    (measurableSet_boundedDensityLocalMap (Presentation S n) p.t).preimage measurable_fst
  have hH : MeasurableSet {z : JointInput S n |
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2} :=
    measurableSet_native_halts S n (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda)
  have hm : Measurable (jointOutput S n p) :=
    measurable_fst.prodMk (measurable_joint_nativeOutput S n p)
  have he : {z : JointInput S n |
      IsBoundedDensityLocalMap (Presentation S n) z.1 p.t ∧
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 ∧
      nativeOutput S n z.1 p z.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n z.1 p} =
      {z : JointInput S n | IsBoundedDensityLocalMap (Presentation S n) z.1 p.t} ∩
        ({z : JointInput S n |
          NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2} ∩
          (jointOutput S n p) ⁻¹' {y : Input S n × Input S n |
            y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p}) := by
    ext z
    rfl
  rw [he]
  exact hI.inter (hH.inter ((measurableSet_joint_nativeGood S n p).preimage hm))

private theorem joint_success_ae (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    ∀ᵐ z ∂ν.prod (nativeTableMeasure S n p),
      IsBoundedDensityLocalMap (Presentation S n) z.1 p.t ∧
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 ∧
      nativeOutput S n z.1 p z.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n z.1 p := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_joint_success S n p)).mpr
  filter_upwards [hν] with J hJ
  filter_upwards [(native_execution_geometry_ae S n J p hJ).2] with T hT
  exact ⟨hJ,hT.1,hT.2.1⟩

/-- Fresh product sampling with arbitrary incoming probability law: actual
halting and the complete original geometric/density output handoff. -/
theorem native_random_input_geometry_ae (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    ∀ᵐ z ∂ν.prod (nativeTableMeasure S n p),
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 ∧
      nativeOutput S n z.1 p z.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n z.1 p ∧
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) z.1 p.lambda (nativeOutput S n z.1 p z.2))
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ center, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) z.1 p.lambda (nativeOutput S n z.1 p z.2)))
        (Metric.closedBall center 1)).card : ℝ) ≤ triangleDensityBound := by
  filter_upwards [joint_success_ae S n p ν hν] with z hz
  exact ⟨hz.2.1,hz.2.2,keyGood_geometry_density (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) z.1 p hz.1 (state_boundedValence S n) _ hz.2.2⟩

/-- The retained J/output assignment pushforward has the same original good
geometry; this is not an independent product distribution of final outputs. -/
theorem joint_output_geometry_ae (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    ∀ᵐ y ∂(ν.prod (nativeTableMeasure S n p)).map (jointOutput S n p),
      IsBoundedDensityLocalMap (Presentation S n) y.1 p.t ∧
      y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p ∧
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) y.1 p.lambda y.2)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ center, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) y.1 p.lambda y.2))
        (Metric.closedBall center 1)).card : ℝ) ≤ triangleDensityBound := by
  have hm : Measurable (jointOutput S n p) :=
    measurable_fst.prodMk (measurable_joint_nativeOutput S n p)
  have hs : MeasurableSet {y : Input S n × Input S n |
      IsBoundedDensityLocalMap (Presentation S n) y.1 p.t ∧
      y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p} :=
    ((measurableSet_boundedDensityLocalMap (Presentation S n) p.t).preimage measurable_fst).inter
      (measurableSet_joint_nativeGood S n p)
  have hg : ∀ᵐ y ∂(ν.prod (nativeTableMeasure S n p)).map (jointOutput S n p),
      IsBoundedDensityLocalMap (Presentation S n) y.1 p.t ∧
      y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p := by
    apply (ae_map_iff hm.aemeasurable hs).mpr
    filter_upwards [joint_success_ae S n p ν hν] with z hz
    exact ⟨hz.1,hz.2.2⟩
  filter_upwards [hg] with y hy
  exact ⟨hy.1,hy.2,keyGood_geometry_density (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) y.1 p hy.1 (state_boundedValence S n) _ hy.2⟩

/-- Tonelli is applied to the genuine jointly measurable actual native cost. -/
theorem native_random_input_cost_integral (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν] :
    (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) =
      ∫⁻ J, ∫⁻ T, nativeOperationCost S n J (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p ∂ν :=
  lintegral_prod _ (measurable_joint_nativeOperationCost S n (radius_nonneg p)
    p.lambda ((6*p.m+2)*p.lambda)).aemeasurable

/-- Abstract the finite scalar before simplifying a probability integral. No
native generator, coefficient formula, qubit carrier or power is unfolded. -/
private theorem probability_lintegral_nat_constant {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (C : ℕ) :
    (∫⁻ _ : A, (C : ℝ≥0∞) ∂μ) = (C : ℝ≥0∞) := by
  simp

/-- The SAME coefficient depends only on jointly fixed p; exponent 1772 and
the actual entire paid process are unchanged for every S,n and input law ν. -/
theorem native_random_input_total_cost (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) ≤
      (nativeOperationCoefficient ((6*p.m+2)*p.lambda) (dependencyBound p.M)*
        (Fintype.card (Presentation S n).Q+1)^nativeOperationDegree : ℕ) := by
  rw [native_random_input_cost_integral S n p ν]
  have hb : ∀ᵐ J ∂ν,
      (∫⁻ T, nativeOperationCost S n J (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p) ≤
        (nativeOperationCoefficient ((6*p.m+2)*p.lambda) (dependencyBound p.M)*
          (Fintype.card (Presentation S n).Q+1)^nativeOperationDegree : ℕ) := by
    filter_upwards [hν] with J hJ
    exact native_expected_operations_qubits S n J p hJ
  exact (lintegral_mono_ae hb).trans_eq
    (probability_lintegral_nat_constant ν
      (nativeOperationCoefficient ((6*p.m+2)*p.lambda) (dependencyBound p.M)*
        (Fintype.card (Presentation S n).Q+1)^nativeOperationDegree))

/-- Finite expectation and integrability do not alter infinity/default semantics
on the original exceptional nontermination set. -/
theorem native_random_input_cost_integrable (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) < ∞ ∧
    Integrable (fun z : JointInput S n =>
      (nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) z.2).toReal) (ν.prod (nativeTableMeasure S n p)) := by
  have hf : (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) < ∞ :=
    (native_random_input_total_cost S n p ν hν).trans_lt (ENNReal.natCast_lt_top _)
  refine ⟨hf,?_⟩
  apply integrable_toReal_of_lintegral_ne_top
  · exact (measurable_joint_nativeOperationCost S n (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda)).aemeasurable
  · exact ne_of_lt hf

end QEC.Coding.BDL26NativeGeometricJointExecution
