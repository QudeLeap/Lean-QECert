import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeKeyExecutionBridge
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ExpectedOperationCost

/-!
# Operation bounds for the actual native master-row scan

The scalar budgets expand the paid generator, rejected candidates, eager pair
eligibility, four-key sort, atlas reads, incoming cache and exact-real queries.
No operation bound or execution certificate is supplied by a caller.
-/
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricScanCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26NativeKeyExecutionBridge
open scoped Classical

-- Each budget is defined from actual retained data/component programs, never
-- accepted as a caller-supplied cost or successful-execution certificate.
def triangleCount (S : OddScale) (n : ℕ) : ℕ :=
  (BDL26NativeMasterCandidates.actualCodes S n).length

def masterCount (S : OddScale) (n : ℕ) : ℕ :=
  Nat.choose (triangleCount S n) 4

def incomingBudget (S : OddScale) (n : ℕ) : ℕ :=
  (BDL26NativePresentationGenerator.setupQ S n).2+
    2*(SR.count S n)^2+12*SR.count S n+4

def atlasReadBudget (S : OddScale) (n : ℕ) : ℕ :=
  43*triangleCount S n+1

def colorBudget (S : OddScale) (n : ℕ) : ℕ :=
  (BDL26NativeTriangleColors.colorsQ S n).operations+43*triangleCount S n+3

def pairBudget (S : OddScale) (n : ℕ) : ℕ :=
  2*colorBudget S n+incomingBudget S n+4*SR.count S n+2007

def eligibilityBudget (S : OddScale) (n : ℕ) : ℕ :=
  4*(4*(pairBudget S n+1)+1)

def preprocessingBudget (S : OddScale) (n : ℕ) : ℕ :=
  (MC.masterCandidatesQ S n).operations+
    masterCount S n*(eligibilityBudget S n+2)+1+
    (masterCount S n+1)^2*159

def pointBudget (incomingRows stateRows : ℕ) : ℕ :=
  2*incomingRows+2*stateRows+49

def triangleBudget (S : OddScale) (n stateRows : ℕ) : ℕ :=
  (MD.atlasQ S n).operations+atlasReadBudget S n+incomingBudget S n+
    3*pointBudget (SR.count S n) stateRows+200004

def centerBudget (S : OddScale) (n K : ℕ) : ℕ :=
  36+(MD.atlasQ S n).operations+atlasReadBudget S n+incomingBudget S n+
    (2*SR.count S n+1)+(3*K+9)+45+3

def gridBudget (K : ℕ) : ℕ :=
  6*(2*K+1)^3+3*(2*K+1)^2+5*(2*K+1)+1

def queryBudget (S : OddScale) (n K stateRows : ℕ) : ℕ :=
  gridBudget K+(2*K+1)^3*
    (centerBudget S n K+4*(triangleBudget S n stateRows+1)+3)+1

def scanBudget (S : OddScale) (n K stateRows : ℕ) : ℕ :=
  preprocessingBudget S n+masterCount S n*(queryBudget S n K stateRows+1)+1

private theorem codeList_length (codes : MD.FourCodes) :
    (MC.codeList codes).length=4 := rfl

private theorem incoming_length (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) :
    (incomingQ S n J).value.length=SR.count S n := by
  rw [incomingQ, SR.initialize_value]
  simp only [BDL26NativeStateRows.rowsFor, List.length_map,
    BDL26NativeStateRows.indices_length]

private theorem incoming_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) :
    (incomingQ S n J).operations=incomingBudget S n := by
  exact (BDL26NativeStateRows.initialize_cost S n
    (fun p => J (SR.decode S n p.1))).1

private theorem atlas_read_cost (S : OddScale) (n : ℕ) (c : MD.Code) :
    (MD.atlasReadQ c (MD.atlasQ S n).value).operations ≤ atlasReadBudget S n := by
  have h := (BDL26NativeSupportMetadata.atlas_read_cost c (MD.atlasQ S n).value).1
  simpa only [atlasReadBudget,triangleCount,
    BDL26NativeSupportMetadata.atlas_value,List.length_map] using h

private theorem color_cost (S : OddScale) (n : ℕ) (c : MD.Code) :
    (NC.colorOfCodeQ S n c).operations ≤ colorBudget S n := by
  exact (BDL26NativeTriangleColors.lookup_cost S n c).1

private theorem pair_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (a b : MD.Code) :
    (pairQ S n J r a b).2 ≤ pairBudget S n := by
  have hA := color_cost S n a
  have hB := color_cost S n b
  have hI := incoming_cost S n J
  cases ha : (NC.colorOfCodeQ S n a).value with
  | none =>
      simp only [pairQ, ha]
      dsimp only [pairBudget]
      omega
  | some aa =>
      rcases aa with ⟨ca,xa⟩
      cases hb : (NC.colorOfCodeQ S n b).value with
      | none =>
          simp only [pairQ, ha, hb]
          dsimp only [pairBudget]
          omega
      | some bb =>
          rcases bb with ⟨cb,xb⟩
          have hx := (BDL26NativeStateRows.read_cost ca.1 (incomingQ S n J).value).1
          have hy := (BDL26NativeStateRows.read_cost cb.1 (incomingQ S n J).value).1
          rw [incoming_length] at hx hy
          have hc := anchorCloseProgram.run_cost_le
            (fun _ => (SR.readQ cb.1 (incomingQ S n J).value).value.2)
            (SR.readQ ca.1 (incomingQ S n J).value).value.2 r
          have hp := anchorCloseProgram_cost_le
          simp only [pairQ, ha, hb]
          dsimp only [pairBudget]
          omega

private theorem eligibility_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (codes : MD.FourCodes) :
    (eligibleQ S n J r codes).2 ≤ eligibilityBudget S n := by
  have h := listAllQuery_cost_le
    (fun a => listAllQuery (pairQ S n J r a) (MC.codeList codes))
    (MC.codeList codes) (4*(pairBudget S n+1)) (by
      intro a ha
      have h := listAllQuery_cost_le (pairQ S n J r a) (MC.codeList codes)
        (pairBudget S n) (by intro b hb; exact pair_cost S n J r a b)
      simpa only [codeList_length] using h)
  simpa only [eligibleQ, eligibilityBudget, codeList_length] using h

private theorem candidate_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (row : GeneratedRow S n) :
    (candidateQ S n J hr row).2 ≤ eligibilityBudget S n+1 := by
  have h := eligibility_cost S n J r row.val.1
  unfold candidateQ
  dsimp only
  split_ifs <;> exact Nat.add_le_add_right h 1

private theorem raw_length (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (rawUniverseQ S n J hr).1.length ≤ masterCount S n := by
  have h := filterMapQuery_length_le (candidateQ S n J hr)
    (MC.masterCandidatesQ S n).value.attach
  rw [List.length_attach] at h
  change (rawUniverseQ S n J hr).1.length ≤ (MC.Rows S n).length at h
  exact h.trans_eq (BDL26NativeMasterCandidates.master_count S n)

private theorem raw_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (rawUniverseQ S n J hr).2 ≤ (MC.masterCandidatesQ S n).operations+
      masterCount S n*(eligibilityBudget S n+2)+1 := by
  have h := filterMapQuery_cost_le (candidateQ S n J hr)
    (MC.masterCandidatesQ S n).value.attach (eligibilityBudget S n+1)
    (by intro row hrow; exact candidate_cost S n J hr row)
  rw [List.length_attach] at h
  have hm : (MC.masterCandidatesQ S n).value.length=masterCount S n :=
    BDL26NativeMasterCandidates.master_count S n
  rw [hm] at h
  norm_num only [Nat.add_assoc] at h
  change (MC.masterCandidatesQ S n).operations+
    (filterMapQuery (candidateQ S n J hr) (MC.masterCandidatesQ S n).value.attach).2+1 ≤ _
  omega

private theorem universe_length (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (universeQ S n J hr).1.length ≤ masterCount S n := by
  change (sortQuery (compareQ S n J r) (rawUniverseQ S n J hr).1).1.length ≤ _
  rw [sortQuery_value (compareQ S n J r)
    (fun a b => BDL26KeyedGeometricExecution.keyPriorityLE (Presentation S n)
      (NC.nativeKey S n) (NC.nativeKey_injective S n) J r
      (event S n J r a) (event S n J r b)) (compare_actual S n J r),
    List.length_insertionSort]
  exact raw_length S n J hr

private theorem universe_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (universeQ S n J hr).2 ≤ preprocessingBudget S n := by
  have h := universe_sort_cost S n J hr
  have hraw := raw_cost S n J hr
  have hl := raw_length S n J hr
  have hs := Nat.mul_le_mul_right 159
    (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) 2)
  dsimp only [preprocessingBudget]
  omega

private theorem point_cost (S : OddScale) (n : ℕ) (lambda : ℝ)
    (I R : SR.Rows (SR.Index S n)) (a : SR.Index S n) :
    (pointQ S n lambda I R a).2 ≤ pointBudget I.length R.length := by
  have hi := (BDL26NativeStateRows.read_cost a I).1
  have hr := (BDL26NativeStateRows.read_cost a R).1
  have hp := pointSnapshotQuery_cost_le lambda
    (SR.readQ a I).value.2 (SR.readQ a R).value.2
  change (SR.readQ a I).operations+(SR.readQ a R).operations+
    (pointSnapshotQuery lambda (SR.readQ a I).value.2 (SR.readQ a R).value.2).2+2 ≤ _
  dsimp only [pointBudget]
  omega

private theorem triangle_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (lambda : ℝ)
    (R : SR.Rows (SR.Index S n)) (c : MD.Code) (center : Space) :
    (triangleCodeQ S n J lambda R c center).2 ≤ triangleBudget S n R.length := by
  have ha := atlas_read_cost S n c
  have hi := incoming_cost S n J
  cases hf : (MD.atlasReadQ c (MD.atlasQ S n).value).value with
  | none =>
      simp only [triangleCodeQ, hf]
      dsimp only [triangleBudget]
      omega
  | some v =>
      have hx := point_cost S n lambda (incomingQ S n J).value R v.1
      have hy := point_cost S n lambda (incomingQ S n J).value R v.2.1
      have hz := point_cost S n lambda (incomingQ S n J).value R v.2.2
      rw [incoming_length] at hx hy hz
      have hq := triangleQuery_cost_le ![
        (pointQ S n lambda (incomingQ S n J).value R v.1).1,
        (pointQ S n lambda (incomingQ S n J).value R v.2.1).1,
        (pointQ S n lambda (incomingQ S n J).value R v.2.2).1] center 2
      simp only [triangleCodeQ, hf]
      dsimp only [triangleBudget]
      omega

private theorem lower_cost (a b : MD.Code) : (lowerCodeQ a b).2=11 := rfl

private theorem anchor_fold_cost (a : MD.Code) (L : List MD.Code) :
    (anchorFoldQ a L).2=12*L.length := by
  induction L generalizing a with
  | nil => rfl
  | cons b L ih =>
      change (lowerCodeQ a b).2+(anchorFoldQ (lowerCodeQ a b).1 L).2+1=
        12*(L.length+1)
      rw [lower_cost, ih]
      ring

private theorem anchor_cost (codes : MD.FourCodes) : (anchorCodeQ codes).2=36 :=
  anchor_fold_cost codes.first [codes.second,codes.third,codes.fourth]

private theorem center_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (lambda : ℝ) (K : ℕ)
    (codes : MD.FourCodes) (g : Grid K) :
    (centerQ S n J lambda K codes g).2 ≤ centerBudget S n K := by
  have ha := atlas_read_cost S n (anchorCodeQ codes).1
  have hi := incoming_cost S n J
  have hc := anchor_cost codes
  cases hf : (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).value with
  | none =>
      simp only [centerQ, hf]
      dsimp only [centerBudget]
      omega
  | some v =>
      have hj := (BDL26NativeStateRows.read_cost v.1 (incomingQ S n J).value).1
      rw [incoming_length] at hj
      have hg := gridPointQuery_cost_le K g
      have hp := pointSnapshotQuery_cost_le lambda
        (SR.readQ v.1 (incomingQ S n J).value).value.2 (gridPointQuery K g).1
      simp only [centerQ, hf]
      dsimp only [centerBudget]
      omega

/-- Every grid cell and each of the four triangle queries is charged, including
repeated atlas construction and fresh incoming-cache initialization. -/
private theorem event_query_cost_le (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r lambda : ℝ) (K : ℕ)
    (row : LiveRow S n J r) (R : SR.Rows (SR.Index S n)) :
    (eventQueryQ S n J r lambda K row R).2 ≤ queryBudget S n K R.length := by
  have hg := gridListQuery_cost_le K
  have hq := listAnyQuery_cost_le (fun g : Grid K =>
    let center := centerQ S n J lambda K row.val.val.1 g
    let triangles := listAllQuery
      (fun c => triangleCodeQ S n J lambda R c center.1) (MC.codeList row.val.val.1)
    (triangles.1,center.2+triangles.2+2))
    (gridListQuery K).1
    (centerBudget S n K+4*(triangleBudget S n R.length+1)+2) (by
      intro g hgm
      have hc := center_cost S n J lambda K row.val.val.1 g
      have ht := listAllQuery_cost_le
        (fun c => triangleCodeQ S n J lambda R c
          (centerQ S n J lambda K row.val.val.1 g).1)
        (MC.codeList row.val.val.1) (triangleBudget S n R.length)
        (by intro c hcm; exact triangle_cost S n J lambda R c _)
      rw [codeList_length] at ht
      dsimp only
      omega)
  rw [gridListQuery_length] at hq
  change (gridListQuery K).2+
    (listAnyQuery _ (gridListQuery K).1).2+1 ≤ _
  dsimp only [queryBudget, gridBudget]
  norm_num only [Nat.add_assoc] at hq ⊢
  omega

-- State length is fixed in this bound, rather than assumed uniformly bounded
-- across an arbitrary input row list. The proof is valid for EVERY supplied R.
private theorem scan_list_cost {A W : Type*} (q : A → W → Bool × ℕ)
    (L : List A) (w : W) (C : ℕ) (hq : ∀ a, (q a w).2 ≤ C) :
    (scanQuery q L w).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [scanQuery]
  | cons a L ih =>
      have ha := hq a
      simp only [scanQuery, List.length_cons]
      split_ifs <;> nlinarith

/-- A derived bound on the ACTUAL paid native scan, including all generated
master rows before filtering, actual native sorting and repeated query setup.
No law, trace, cost certificate, legacy order or halting premise is an input. -/
theorem native_scan_cost_le (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    (scanQ S n J hr lambda K R).2 ≤ scanBudget S n K R.length := by
  have hu := universe_cost S n J hr
  have hl := universe_length S n J hr
  have hs := scan_list_cost (eventQueryQ S n J r lambda K)
    (universeQ S n J hr).1 R (queryBudget S n K R.length)
    (fun row => event_query_cost_le S n J r lambda K row R)
  have hm := Nat.mul_le_mul_right (queryBudget S n K R.length+1) hl
  change (universeQ S n J hr).2+
    (scanQuery (eventQueryQ S n J r lambda K) (universeQ S n J hr).1 R).2+1 ≤ _
  dsimp only [scanBudget]
  omega


/-- A closed scalar envelope, with no retained target/component operation projection. -/
def closedScanBudget (a b K z : ℕ) : ℕ :=
  let incoming := a+2*b^2+12*b+4
  let atlas := a+178*b^2+50*b+2
  let colors := a+275*b^2+103*b+4
  let pair := 2*(colors+43*b+3)+incoming+4*b+2007
  let eligible := 4*(4*(pair+1)+1)
  let masters := a+(b+1)^4*(a+178*b^2+222*b+509)+13*(b+1)^3+2
  let preprocess := masters+b^4*(eligible+2)+1+(b^4+1)^2*159
  let triangle := atlas+(43*b+1)+incoming+3*(2*b+2*z+49)+200004
  let center := 36+atlas+(43*b+1)+incoming+(2*b+1)+(3*K+9)+45+3
  let query := gridBudget K+(2*K+1)^3*(center+4*(triangle+1)+3)+1
  preprocess+b^4*(query+1)+1

/-- Every retained scalar component is replaced by its syntax-derived polynomial. -/
theorem native_scan_budget_closed_le (S : OddScale) (n K z : ℕ) :
    let a := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    let b := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    scanBudget S n K z ≤ closedScanBudget a b K z := by
  let a := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
  let b := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
  have hsetup : (BDL26NativePresentationGenerator.setupQ S n).2 ≤ a := by
    simpa only [BDL26NativePresentationGenerator.setupExponent_value] using
      BDL26NativePresentationGenerator.setup_cost S n
  have hlength := BDL26NativeSupportMetadata.metadata_lengths S n
  change triangleCount S n ≤ b ∧ _ ≤ b ∧ SR.count S n ≤ b at hlength
  rcases hlength with ⟨ht,hf,hv⟩
  have hT : (BDL26NativeSupportMetadata.T S n).length ≤ b := ht
  have hV : (BDL26NativeSupportMetadata.V S n).length ≤ b := hv
  have hmaster : masterCount S n ≤ b^4 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left ht 4)
  have hcolors := (BDL26NativeTriangleColors.colors_polynomial S n).1
  have hatlas := (BDL26NativeSupportMetadata.atlas_cost S n).1
  have hmasters := (BDL26NativeMasterCandidates.master_polynomial S n).1
  change (BDL26NativeTriangleColors.colorsQ S n).operations ≤ a+275*b^2+103*b+4 at hcolors
  change (MC.masterCandidatesQ S n).operations ≤
    a+(b+1)^4*(a+178*b^2+222*b+509)+13*(b+1)^3+2 at hmasters
  have hatlas' : (MD.atlasQ S n).operations ≤ a+178*b^2+50*b+2 := by
    apply hatlas.trans
    calc
      _ ≤ a+b*(44*b+2*b+132*b+50)+2 := by gcongr
      _ = _ := by ring
  have hincoming : incomingBudget S n ≤ a+2*b^2+12*b+4 := by
    dsimp only [incomingBudget]
    gcongr
  have hcolor : colorBudget S n ≤ a+275*b^2+103*b+4+43*b+3 := by
    dsimp only [colorBudget]
    gcongr
  have htriangle : triangleBudget S n z ≤
      (a+178*b^2+50*b+2)+(43*b+1)+(a+2*b^2+12*b+4)+
        3*(2*b+2*z+49)+200004 := by
    dsimp only [triangleBudget,atlasReadBudget,pointBudget]
    gcongr
  have hcenter : centerBudget S n K ≤
      36+(a+178*b^2+50*b+2)+(43*b+1)+(a+2*b^2+12*b+4)+
        (2*b+1)+(3*K+9)+45+3 := by
    dsimp only [centerBudget,atlasReadBudget]
    gcongr
  dsimp only [scanBudget,preprocessingBudget,eligibilityBudget,pairBudget,
    queryBudget,closedScanBudget]
  gcongr

/-- Explicit coefficient for the degree-eight diagonal of the expanded scan. -/
def scanPolynomialConstant (K : ℕ) : ℕ :=
  gridBudget K+(2*K+1)^3*(3*K+802225)+61537

private theorem closedScanBudget_mono {a b z a' b' z' : ℕ} (K : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hz : z ≤ z') :
    closedScanBudget a b K z ≤ closedScanBudget a' b' K z' := by
  dsimp only [closedScanBudget]
  gcongr

private theorem closedScanBudget_diagonal (x K : ℕ) (hx : 1 ≤ x) :
    closedScanBudget x x K x ≤ scanPolynomialConstant K*x^8 := by
  let g := gridBudget K
  let h := (2*K+1)^3
  have hp (j : ℕ) (hj : j ≤ 8) : x^j ≤ x^8 :=
    Nat.pow_le_pow_right (by omega) hj
  have h0 : 1 ≤ x^8 := by simpa only [pow_zero] using hp 0 (by decide)
  have h1 : x ≤ x^8 := by simpa only [pow_one] using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have hconstant : 685 ≤ 685*x^8 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 685 h0
  calc
    _ = 159*x^8+(900*h+9010)*x^6+(585*h+5911)*x^5+
        (g+3*h*K+800740*h+35211)*x^4+4099*x^3+4163*x^2+2299*x+685 := by
      dsimp only [closedScanBudget,g,h] <;> ring
    _ ≤ 159*x^8+(900*h+9010)*x^8+(585*h+5911)*x^8+
        (g+3*h*K+800740*h+35211)*x^8+4099*x^8+4163*x^8+2299*x^8+685*x^8 := by
      gcongr <;> assumption
    _ = _ := by dsimp only [scanPolynomialConstant,g,h] <;> ring

private theorem depth_le_qubits (S : OddScale) (n : ℕ) :
    n+1 ≤ Fintype.card (Presentation S n).Q := by
  have hp : n+1 ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; nlinarith
  have hq : 5*2^n ≤ Fintype.card (Presentation S n).Q :=
    BDL26QuantitativeBounds.state_qubit_card_lower S n
  omega

private theorem qubits_mono (S : OddScale) :
    Monotone (fun n => Fintype.card (Presentation S n).Q) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := BDL26QuantitativeBounds.nextState_qubit_card_lower S n
    (BDL26DecodingGraph.state S n)
  change 2*Fintype.card (Presentation S n).Q ≤ Fintype.card (Presentation S (n+1)).Q at h
  omega

private theorem scale_le_positive_qubits (S : OddScale) (n : ℕ) (hn : 1 ≤ n) :
    S.ell ≤ Fintype.card (Presentation S n).Q := by
  let P := BDL26DecodingGraph.baseState.presentation
  let q : P.Q := (0 : BDL26FiniteAlternatingCore.BaseQubit)
  let f : BDL26TannerLocalRegularity.QDoubleCylinderVertex P q S →
      BDL26RXLocalReplacement.RX1 P S := fun v => Sum.inr ⟨q,v⟩
  have hi : Function.Injective f := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
  have hc := Fintype.card_le_of_injective f hi
  rw [BDL26QuantitativeBounds.qDoubleCylinderVertex_card] at hc
  have he : Fintype.card (BDL26TannerLocalRegularity.QStarEdge P q)=1 := by decide
  rw [he] at hc
  have hs := S.two_half_add_one
  have hfirst : S.ell ≤ Fintype.card (Presentation S 1).Q := by
    change S.ell ≤ Fintype.card (BDL26RXLocalReplacement.RX1 P S)
    omega
  exact hfirst.trans (qubits_mono S hn)

/-- This radius has no scale parameter: at level zero the actual generator is
scale independent; at positive levels the actual qubits already dominate scale. -/
def qubitRadius (S : OddScale) (n : ℕ) : ℕ :=
  (132*(Fintype.card (Presentation S n).Q+1))^221

-- Arithmetic automation sees only abstract natural numbers in these two
-- lemmas; the native setup program and presentation cardinality stay folded.
private theorem radius_power_bounds (s q d r : ℕ)
    (hs : s ≤ q) (hd : d ≤ q) (hr : r=s+130*q+2) :
    1 ≤ (132*(q+1))^221 ∧
    d*r^220 ≤ (132*(q+1))^221 ∧
    d*r^15 ≤ (132*(q+1))^221 := by
  let R : ℕ := 132*(q+1)
  have hR : 1 ≤ R := by dsimp only [R]; omega
  have hdn : d ≤ R := by dsimp only [R]; omega
  have hrn : r ≤ R := by dsimp only [R]; omega
  refine ⟨one_le_pow₀ hR,?_,?_⟩
  · calc
      d*r^220 ≤ R*R^220 := Nat.mul_le_mul hdn (Nat.pow_le_pow_left hrn 220)
      _ = R^221 := (pow_succ' R 220).symm
  · calc
      d*r^15 ≤ R*R^15 := Nat.mul_le_mul hdn (Nat.pow_le_pow_left hrn 15)
      _ = R^16 := (pow_succ' R 15).symm
      _ ≤ R^221 := Nat.pow_le_pow_right (by omega) (by decide)

private theorem incoming_scalar_envelope (u v x : ℕ)
    (hu : u ≤ x) (hv : v ≤ x) (hx : 1 ≤ x) :
    u+2*v^2+12*v+4 ≤ 19*x^2 := by
  have hx2 : x ≤ x^2 := by nlinarith
  have h1 : 1 ≤ x^2 := by nlinarith
  calc
    u+2*v^2+12*v+4 ≤ x+2*x^2+12*x+4 := by gcongr
    _ ≤ 19*x^2 := by nlinarith

-- The bridge only composes already proved inequalities. In particular it does
-- not send actual setup/cardinality expressions to omega, ring or nlinarith.
private theorem scalar_budgets_from_power_bounds (S : OddScale) (n K x : ℕ)
    (hx : 1 ≤ x)
    (ha : (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220 ≤ x)
    (hb : (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15 ≤ x) :
    incomingBudget S n ≤ 19*x^2 ∧
    scanBudget S n K (SR.count S n) ≤ scanPolynomialConstant K*x^8 ∧
    SR.count S n ≤ x := by
  have hv : SR.count S n ≤ x :=
    (BDL26NativeStateRows.native_length_bound S n).trans hb
  have hs := BDL26NativePresentationGenerator.setup_cost S n
  rw [BDL26NativePresentationGenerator.setupExponent_value] at hs
  have hsetup := hs.trans ha
  refine ⟨?_,?_,hv⟩
  · exact incoming_scalar_envelope
      (BDL26NativePresentationGenerator.setupQ S n).2 (SR.count S n) x hsetup hv hx
  · exact (native_scan_budget_closed_le S n K (SR.count S n)).trans
      ((closedScanBudget_mono K ha hb hv).trans (closedScanBudget_diagonal x K hx))

private theorem scalar_budgets_of_scale_le (S : OddScale) (n K : ℕ)
    (hscale : S.ell ≤ Fintype.card (Presentation S n).Q) :
    incomingBudget S n ≤ 19*(qubitRadius S n)^2 ∧
    scanBudget S n K (SR.count S n) ≤ scanPolynomialConstant K*(qubitRadius S n)^8 ∧
    SR.count S n ≤ qubitRadius S n := by
  have h := radius_power_bounds S.ell (Fintype.card (Presentation S n).Q)
    (n+1) (BDL26NativePresentationGenerator.inputRadius S n)
    hscale (depth_le_qubits S n) rfl
  exact scalar_budgets_from_power_bounds S n K (qubitRadius S n) h.1 h.2.1 h.2.2

-- At level zero every actual program and carrier is the same seed. Prove
-- transport with two generic scales, before specializing either scale to 3.
-- Only the two history base equations are reduced here. Every subsequent
-- constructor is transported symbolically, without executing its list loops.
private theorem seed_setup_programs_eq (S T : OddScale) :
    BDL26NativePresentationGenerator.setupQ S 0=
      BDL26NativePresentationGenerator.setupQ T 0 ∧
    BDL26NativePresentationGenerator.allocatedRecords S 0=
      BDL26NativePresentationGenerator.allocatedRecords T 0 := by
  have hh : BDL26NativePresentationGenerator.historyQ S 0=
      BDL26NativePresentationGenerator.historyQ T 0 := by
    change ([BDL26NativePresentationGenerator.seedFrameQ.1],
      BDL26NativePresentationGenerator.seedFrameQ.2+1)=_
    exact Eq.refl _
  have ha : BDL26NativePresentationGenerator.Allocation.historyQ S 0=
      BDL26NativePresentationGenerator.Allocation.historyQ T 0 := by
    change ([BDL26NativePresentationGenerator.Allocation.seedFrameQ.1],
      BDL26NativePresentationGenerator.Allocation.seedFrameQ.2+1)=_
    exact Eq.refl _
  constructor
  · simp only [BDL26NativePresentationGenerator.setupQ,
      BDL26NativePresentationGenerator.runQ,
      BDL26NativePresentationGenerator.generateQ,hh]
  · simp only [BDL26NativePresentationGenerator.allocatedRecords,
      BDL26NativePresentationGenerator.Allocation.setupQ,
      BDL26NativePresentationGenerator.Allocation.runQ,
      BDL26NativePresentationGenerator.Allocation.generateQ,ha]

-- Outer constructors only: quadruples, endpoint/map/color loops and every
-- paid value remain the original programs, held as identical symbolic terms.
-- Prove the original observation identities with symbolic levels first.
-- The seed consumer instantiates this ordinary input-congruence theorem;
-- it never converts a level-zero native program into a local view.
private theorem component_costs_eq_of_setup_eq (S T : OddScale) (n m : ℕ)
    (hs : BDL26NativePresentationGenerator.setupQ S n=
      BDL26NativePresentationGenerator.setupQ T m)
    (ha : BDL26NativePresentationGenerator.allocatedRecords S n=
      BDL26NativePresentationGenerator.allocatedRecords T m) :
    (MC.masterCandidatesQ S n).operations=(MC.masterCandidatesQ T m).operations ∧
    (MD.atlasQ S n).operations=(MD.atlasQ T m).operations ∧
    (BDL26NativeTriangleColors.colorsQ S n).operations=
      (BDL26NativeTriangleColors.colorsQ T m).operations := by
  -- Nat-valued observations bind the generated carrier inside the lambda.
  -- Congruence therefore transports its vertex list and Fin carrier together.
  let atlasCost := fun generated :
      BDL26NativePresentationGenerator.Query BDL26NativePresentationGenerator.SetupOutput =>
    let out := BDL26NativeSupportMetadata.atlasRowsQ generated.1.data.frame
      generated.1.data.vertices generated.1.triangles
    generated.2+out.operations+2
  let colorCost := fun generated :
      BDL26NativePresentationGenerator.Query BDL26NativePresentationGenerator.SetupOutput =>
    let out := BDL26NativeSupportMetadata.atlasRowsQ generated.1.data.frame
      generated.1.data.vertices generated.1.triangles
    let rows := @BDL26NativeTriangleColors.colorRowsQ
      (Fin generated.1.data.vertices.length)
      (instDecidableEqFin generated.1.data.vertices.length) out.value
    (generated.2+out.operations+2)+rows.operations+2
  -- This proof-local observation is the delta expansion of the original
  -- master/candidate/query/atlas constructors. Every paid branch and field is
  -- retained; quadruples and all list/lookup programs remain unexpanded.
  let masterCost := fun input :
      (BDL26NativePresentationGenerator.Query BDL26NativePresentationGenerator.SetupOutput) × ℕ =>
    let generated := input.1
    let allocated := input.2
    let out := BDL26NativeSupportMetadata.atlasRowsQ generated.1.data.frame
      generated.1.data.vertices generated.1.triangles
    let atlas : BDL26NativeStateRows.Run
        (List (MD.Code × Option (BDL26NativeSupportMetadata.Triple
          (Fin generated.1.data.vertices.length)))) :=
      ⟨out.value,generated.2+out.operations+2,allocated+out.allocations+1⟩
    let query : MD.FourCodes → BDL26NativeStateRows.Run
        (Option (List (Fin generated.1.data.vertices.length))) := fun codes =>
      let a := BDL26NativeSupportMetadata.atlasReadQ codes.first atlas.value
      let b := BDL26NativeSupportMetadata.atlasReadQ codes.second atlas.value
      let c := BDL26NativeSupportMetadata.atlasReadQ codes.third atlas.value
      let d := BDL26NativeSupportMetadata.atlasReadQ codes.fourth atlas.value
      match a.value,b.value,c.value,d.value with
      | some x,some y,some z,some w =>
          let dedup := @BDL26NativeSupportMetadata.dedupQ
            (Fin generated.1.data.vertices.length)
            (instDecidableEqFin generated.1.data.vertices.length)
            (BDL26NativeSupportMetadata.twelve x y z w)
          ⟨some dedup.value,
            atlas.operations+a.operations+b.operations+c.operations+d.operations+
              dedup.operations+30,
            atlas.allocations+dedup.allocations+13⟩
      | _,_,_,_ =>
          ⟨none,atlas.operations+a.operations+b.operations+c.operations+d.operations+6,
            atlas.allocations⟩
    let candidate : MD.Code → MD.Code → MD.Code → MD.Code →
        BDL26NativeStateRows.Run
          (MD.FourCodes × Option (List (Fin generated.1.data.vertices.length))) := fun a b c d =>
      let ca := BDL26NativeMasterCandidates.copyCodeQ a
      let cb := BDL26NativeMasterCandidates.copyCodeQ b
      let cc := BDL26NativeMasterCandidates.copyCodeQ c
      let cd := BDL26NativeMasterCandidates.copyCodeQ d
      let codes := BDL26NativeMasterCandidates.pack ca.value cb.value cc.value cd.value
      let queried := query codes
      ⟨(codes,queried.value),ca.operations+cb.operations+cc.operations+cd.operations+
        queried.operations+5+3+8,
        ca.allocations+cb.allocations+cc.allocations+cd.allocations+queried.allocations+1+1⟩
    let rows := BDL26NativeMasterCandidates.quadruplesQ candidate generated.1.triangles
    generated.2+rows.operations+2
  -- Here k is a free variable, so the original history/list programs stay
  -- symbolic while definitional equality checks only their outer constructors.
  have hmaster (U : OddScale) (k : ℕ) :
      (MC.masterCandidatesQ U k).operations=
        masterCost (BDL26NativePresentationGenerator.setupQ U k,
          BDL26NativePresentationGenerator.allocatedRecords U k) := by
    dsimp only [BDL26NativeMasterCandidates.masterCandidatesQ,masterCost]
    apply congrArg (fun f : MD.Code → MD.Code → MD.Code → MD.Code →
        BDL26NativeStateRows.Run (MD.FourCodes × Option (List (SR.Index U k))) =>
      (BDL26NativePresentationGenerator.setupQ U k).2+
        (BDL26NativeMasterCandidates.quadruplesQ f
          (BDL26NativePresentationGenerator.setupQ U k).1.triangles).operations+2)
    funext a b c d
    let codes : MD.FourCodes := BDL26NativeMasterCandidates.pack
      (BDL26NativeMasterCandidates.copyCodeQ a).value
      (BDL26NativeMasterCandidates.copyCodeQ b).value
      (BDL26NativeMasterCandidates.copyCodeQ c).value
      (BDL26NativeMasterCandidates.copyCodeQ d).value
    cases h₁ : (BDL26NativeSupportMetadata.atlasReadQ codes.first
        (MD.atlasQ U k).value).value <;>
      cases h₂ : (BDL26NativeSupportMetadata.atlasReadQ codes.second
        (MD.atlasQ U k).value).value <;>
      cases h₃ : (BDL26NativeSupportMetadata.atlasReadQ codes.third
        (MD.atlasQ U k).value).value <;>
      cases h₄ : (BDL26NativeSupportMetadata.atlasReadQ codes.fourth
        (MD.atlasQ U k).value).value
    all_goals
      dsimp only [codes,BDL26NativeSupportMetadata.atlasQ] at h₁ h₂ h₃ h₄
      simp only [BDL26NativeMasterCandidates.candidateQ,
        BDL26NativeSupportMetadata.queryQ,BDL26NativeSupportMetadata.atlasQ,
        h₁,h₂,h₃,h₄] <;> congr <;> exact Subsingleton.elim _ _
  have hatlas (U : OddScale) (k : ℕ) :
      (MD.atlasQ U k).operations=
        atlasCost (BDL26NativePresentationGenerator.setupQ U k) := by
    rfl
  have hcolors (U : OddScale) (k : ℕ) :
      (BDL26NativeTriangleColors.colorsQ U k).operations=
        colorCost (BDL26NativePresentationGenerator.setupQ U k) := by
    rfl
  refine ⟨?_,?_,?_⟩
  · exact (hmaster S n).trans
      ((congrArg masterCost (Prod.ext hs ha)).trans (hmaster T m).symm)
  · exact (hatlas S n).trans ((congrArg atlasCost hs).trans (hatlas T m).symm)
  · exact (hcolors S n).trans ((congrArg colorCost hs).trans (hcolors T m).symm)

private theorem seed_component_costs_eq (S T : OddScale) :
    (MC.masterCandidatesQ S 0).operations=(MC.masterCandidatesQ T 0).operations ∧
    (MD.atlasQ S 0).operations=(MD.atlasQ T 0).operations ∧
    (BDL26NativeTriangleColors.colorsQ S 0).operations=
      (BDL26NativeTriangleColors.colorsQ T 0).operations := by
  rcases seed_setup_programs_eq S T with ⟨hs,ha⟩
  exact component_costs_eq_of_setup_eq S T 0 0 hs ha

private theorem seed_budget_transport (S T : OddScale) (K z : ℕ) :
    incomingBudget S 0=incomingBudget T 0 ∧
    scanBudget S 0 K z=scanBudget T 0 K z ∧
    SR.count S 0=SR.count T 0 ∧
    qubitRadius S 0=qubitRadius T 0 := by
  have hs := (seed_setup_programs_eq S T).1
  have hc := seed_component_costs_eq S T
  have hv : SR.count S 0=SR.count T 0 := by
    exact congrArg (fun generated => generated.1.data.vertices.length) hs
  have ht : triangleCount S 0=triangleCount T 0 := by
    exact congrArg (fun generated => generated.1.triangles.length) hs
  have hi : incomingBudget S 0=incomingBudget T 0 := by
    simp only [incomingBudget,BDL26NativeStateRows.count,hs]
  refine ⟨hi,?_,hv,?_⟩
  · simp only [scanBudget,preprocessingBudget,masterCount,eligibilityBudget,
      pairBudget,colorBudget,triangleBudget,atlasReadBudget,pointBudget,
      centerBudget,queryBudget,hc.1,hc.2.1,hc.2.2,ht,hi,hv]
  · change (132*(Fintype.card BDL26DecodingGraph.baseState.presentation.Q+1))^221=
      (132*(Fintype.card BDL26DecodingGraph.baseState.presentation.Q+1))^221
    exact Eq.refl _

/-- All actual scalar budgets are now bounded solely in the actual native qubit
count. No retained generator cost or scale/depth coefficient survives. -/
theorem native_scalar_budgets_qubit (S : OddScale) (n K : ℕ) :
    incomingBudget S n ≤ 19*(qubitRadius S n)^2 ∧
    scanBudget S n K (SR.count S n) ≤ scanPolynomialConstant K*(qubitRadius S n)^8 ∧
    SR.count S n ≤ qubitRadius S n := by
  by_cases hn : n=0
  · subst n
    let S0 : OddScale := ⟨3,rfl,by decide⟩
    have hq : 5 ≤ Fintype.card (Presentation S0 0).Q := by
      simpa only [pow_zero,Nat.mul_one] using
        BDL26QuantitativeBounds.state_qubit_card_lower S0 0
    have h0 : S0.ell ≤ Fintype.card (Presentation S0 0).Q :=
      (show 3 ≤ 5 by decide).trans hq
    have ht := seed_budget_transport S S0 K (SR.count S 0)
    rw [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
    exact scalar_budgets_of_scale_le S0 0 K h0
  · exact scalar_budgets_of_scale_le S n K
      (scale_le_positive_qubits S n (by omega))

end QEC.Coding.BDL26NativeGeometricScanCost
