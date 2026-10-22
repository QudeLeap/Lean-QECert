import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeSupportMetadata
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeTriangleKeys

/-!
# Closed paid native three-fiber colors

Project-derived internal/API realization of BDL26 paper.tex1400–1428's bounded
proper labeling. The legacy color/policy definitions are unchanged. The generic
proof policy specializes exactly to them; the closed program instead computes
the explicitly named native policy. No execution-law equality is asserted.
Costs count finite-record/cursor operations and allocations, not bit complexity.
The endpoint atlas is constructed internally, all full-code probes are paid,
and all three rank scans retain rejected branches and actual counter updates.
-/
namespace QEC.Coding.BDL26NativeTriangleColors

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence

namespace G
export BDL26NativePresentationGenerator (Code)
end G
open G
abbrev Run := BDL26NativeStateRows.Run
abbrev Triple := BDL26NativeSupportMetadata.Triple
abbrev AtlasRow (A : Type*) := Code × Option (Triple A)
abbrev ColorRow (A : Type*) := Code × Option (Triple A × Triple ℕ)

noncomputable section Semantic
variable (P : TannerSquarePresentation) (key : Triangle P → ℕ)

/-- Primitive-key semantic coloring on the original domain labels. -/
def policyColor (t : Triangle P) : Fin 3 → ℕ := by
  classical
  exact ![fiberRank key (fun u : Triangle P => P.faceX u.1) t,
    fiberRank key (fun u : Triangle P => P.faceQ u.1 u.2) t,
    fiberRank key (fun u : Triangle P => P.faceZ u.1) t]

theorem policyColor_lt (hv : BoundedValence P) (t : Triangle P) (i : Fin 3) :
    policyColor P key t i < 56 := by
  classical
  fin_cases i
  · have hr := fiberRank_lt_card key (fun u : Triangle P => P.faceX u.1) t
    have hc := xTriangles_card_le P hv (P.faceX t.1)
    simp only [XTriangles,Fintype.card_subtype] at hc
    change fiberRank key (fun u : Triangle P => P.faceX u.1) t < 56
    omega
  · have hr := fiberRank_lt_card key (fun u : Triangle P => P.faceQ u.1 u.2) t
    have hc := qTriangles_card_le P hv (P.faceQ t.1 t.2)
    simp only [QTriangles,Fintype.card_subtype] at hc
    change fiberRank key (fun u : Triangle P => P.faceQ u.1 u.2) t < 56
    omega
  · have hr := fiberRank_lt_card key (fun u : Triangle P => P.faceZ u.1) t
    have hc := zTriangles_card_le P hv (P.faceZ t.1)
    simp only [ZTriangles,Fintype.card_subtype] at hc
    change fiberRank key (fun u : Triangle P => P.faceZ u.1) t < 56
    omega

theorem policy_same_vertex (hk : Function.Injective key) {a b : Triangle P}
    (hc : policyColor P key a=policyColor P key b) {i j : Fin 3}
    (hv : triangleVertex P a i=triangleVertex P b j) : a=b := by
  classical
  fin_cases i <;> fin_cases j <;> simp [triangleVertex] at hv
  · apply fiberRank_injective_on_fiber key (fun t : Triangle P => P.faceX t.1) hk a b
    · exact hv
    · exact congrFun hc 0
  · apply fiberRank_injective_on_fiber key (fun t : Triangle P => P.faceQ t.1 t.2) hk a b
    · exact hv
    · exact congrFun hc 1
  · apply fiberRank_injective_on_fiber key (fun t : Triangle P => P.faceZ t.1) hk a b
    · exact hv
    · exact congrFun hc 2

theorem policy_support_disjoint (hk : Function.Injective key) {a b : Triangle P}
    (hne : a≠b) (hc : policyColor P key a=policyColor P key b) :
    Disjoint (triangleSupport P a) (triangleSupport P b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v ha hb
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hb
  exact hne (policy_same_vertex P key hk hc (hi.trans hj.symm))

def boundedPolicyColor (hv : BoundedValence P) (t : Triangle P) : Fin 3 → Fin 56 :=
  fun i => ⟨policyColor P key t i,policyColor_lt P key hv t i⟩

theorem palette_card : Fintype.card (Fin 3 → Fin 56)=56^3 := by simp

/-- Literal specialization; no existing definition is rewritten. -/
theorem legacy_specialization (t : Triangle P) :
    policyColor P (triangleKey P) t=triangleColor P t := rfl

theorem legacy_bounded_specialization (hv : BoundedValence P) (t : Triangle P) :
    boundedPolicyColor P (triangleKey P) hv t=boundedTriangleColor P hv t := by
  funext i
  apply Fin.ext
  rfl

private theorem vertex_rank (t : Triangle P) (i : Fin 3) :
    fiberRank key (fun u : Triangle P => triangleVertex P u i) t=policyColor P key t i := by
  classical
  fin_cases i <;> simp [fiberRank,earlierFiber,triangleVertex,policyColor]
end Semantic

/-- Fixed triple projection. This is a finite record read, not a rank oracle. -/
def tripleAt {A : Type*} (v : Triple A) (i : Fin 3) : A := ![v.1,v.2.1,v.2.2] i

/-- All ten fields are read and reconstructed; one complete record is retained. -/
def copyCodeQ (c : Code) : Run Code :=
  ⟨{family:=c.family,owner:=c.owner,copy:=c.copy,part:=c.part,p:=c.p,
    q:=c.q,i:=c.i,j:=c.j,k:=c.k,l:=c.l},21,1⟩

theorem copy_spec (c : Code) :
    (copyCodeQ c).value=c ∧ (copyCodeQ c).operations=21 ∧ (copyCodeQ c).allocations=1 :=
  ⟨rfl,rfl,rfl⟩

/-- Boolean membership of one earlier incidence fiber; used for proof counting. -/
def hit {A : Type*} [DecidableEq A] (k : ℕ) (a : A) (i : Fin 3) (r : AtlasRow A) : Bool :=
  match r.2 with
  | none => false
  | some v => decide (tripleAt v i=a) && decide (2*r.1.owner+r.1.copy<k)

/-- The counter is computed recursively. Every row reads its key, including
missing rows. Successful endpoint probes execute equality/order and count the
accepted increment; rejected comparisons retain their own paid branch. -/
def fiberScanQ {A : Type*} [DecidableEq A] (k : ℕ) (a : A) (i : Fin 3) :
    List (AtlasRow A) → Run ℕ
  | [] => ⟨0,1,0⟩
  | r::rs =>
      let key := BDL26NativeTriangleKeys.rawKeyQ r.1
      let tail := fiberScanQ k a i rs
      match r.2 with
      | none => ⟨tail.value,key.2.1+tail.operations+3,tail.allocations⟩
      | some v =>
          let eq := decide (tripleAt v i=a)
          let earlier := decide (key.1<k)
          let accept := eq && earlier
          ⟨if accept then tail.value+1 else tail.value,
            key.2.1+tail.operations+12+(if accept then 1 else 0),tail.allocations⟩

theorem scan_empty {A : Type*} [DecidableEq A] (k : ℕ) (a : A) (i : Fin 3) :
    fiberScanQ k a i []=⟨0,1,0⟩ := rfl

theorem scan_value {A : Type*} [DecidableEq A] (k : ℕ) (a : A) (i : Fin 3)
    (L : List (AtlasRow A)) : (fiberScanQ k a i L).value=L.countP (hit k a i) := by
  induction L with
  | nil => simp [fiberScanQ]
  | cons r L ih =>
      cases h : r.2 with
      | none => simp [fiberScanQ,hit,h,ih]
      | some v =>
          by_cases he : tripleAt v i=a <;>
            by_cases hk : 2*r.1.owner+r.1.copy<k <;>
              simp [fiberScanQ,hit,h,BDL26NativeTriangleKeys.rawKeyQ,he,hk,ih,
                List.countP_cons]

/-- Exact rejected/accepted accounting, including empty return and missing row. -/
theorem scan_accounting {A : Type*} [DecidableEq A] (k : ℕ) (a : A) (i : Fin 3)
    (r : AtlasRow A) (L : List (AtlasRow A)) :
    (fiberScanQ k a i (r::L)).operations=(fiberScanQ k a i L).operations+
      (match r.2 with | none => 8 | some _ => 17+(if hit k a i r then 1 else 0)) ∧
    (fiberScanQ k a i (r::L)).allocations=(fiberScanQ k a i L).allocations := by
  cases h : r.2 with
  | none =>
      constructor <;>
        simp only [fiberScanQ,hit,h,BDL26NativeTriangleKeys.rawKeyQ] <;> omega
  | some v =>
      by_cases he : tripleAt v i=a <;>
        by_cases hk : 2*r.1.owner+r.1.copy<k <;>
          constructor <;>
            simp [fiberScanQ,hit,h,BDL26NativeTriangleKeys.rawKeyQ,he,hk] <;> omega

theorem scan_cost {A : Type*} [DecidableEq A] (k : ℕ) (a : A) (i : Fin 3)
    (L : List (AtlasRow A)) :
    (fiberScanQ k a i L).operations≤18*L.length+1 ∧
      (fiberScanQ k a i L).allocations=0 := by
  induction L with
  | nil => simp [fiberScanQ]
  | cons r L ih =>
      have h := scan_accounting k a i r L
      cases hr : r.2 <;> simp only [hr,List.length_cons] at h ⊢
      · constructor <;> omega
      · split_ifs at h <;> norm_num at h <;> constructor <;> omega

/-- Revalidate the full code against the internally constructed atlas. No
success is assumed. A failed code still pays its complete scan and copy. -/
def colorRowQ {A : Type*} [DecidableEq A] (atlas : List (AtlasRow A)) (c : Code) :
    Run (ColorRow A) :=
  let copied := copyCodeQ c
  let found := BDL26NativeSupportMetadata.atlasReadQ c atlas
  match found.value with
  | none => ⟨(copied.value,none),copied.operations+found.operations+3,
      copied.allocations+1⟩
  | some v =>
      let key := BDL26NativeTriangleKeys.rawKeyQ c
      let x := fiberScanQ key.1 v.1 0 atlas
      let q := fiberScanQ key.1 v.2.1 1 atlas
      let z := fiberScanQ key.1 v.2.2 2 atlas
      ⟨(copied.value,some ((v.1,v.2.1,v.2.2),(x.value,q.value,z.value))),
        copied.operations+found.operations+key.2.1+x.operations+q.operations+z.operations+12,
        copied.allocations+found.allocations+x.allocations+q.allocations+z.allocations+8⟩

theorem row_code {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) (c : Code) :
    (colorRowQ L c).value.1=c := by
  cases h : (BDL26NativeSupportMetadata.atlasReadQ c L).value <;>
    simp [colorRowQ,h,copyCodeQ]

theorem row_failure {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) (c : Code)
    (h : (BDL26NativeSupportMetadata.atlasReadQ c L).value=none) :
    (colorRowQ L c).value=(c,none) ∧
      (colorRowQ L c).operations=(BDL26NativeSupportMetadata.atlasReadQ c L).operations+24 ∧
      (colorRowQ L c).allocations=2 := by
  constructor
  · simp only [colorRowQ,h,copyCodeQ]
  · constructor
    · simp only [colorRowQ,h,copyCodeQ]
      omega
    · simp only [colorRowQ,h,copyCodeQ]

theorem row_success_accounting {A : Type*} [DecidableEq A] (L : List (AtlasRow A))
    (c : Code) (v : Triple A)
    (h : (BDL26NativeSupportMetadata.atlasReadQ c L).value=some v) :
    (colorRowQ L c).operations=(BDL26NativeSupportMetadata.atlasReadQ c L).operations+
      (fiberScanQ (2*c.owner+c.copy) v.1 0 L).operations+
      (fiberScanQ (2*c.owner+c.copy) v.2.1 1 L).operations+
      (fiberScanQ (2*c.owner+c.copy) v.2.2 2 L).operations+38 ∧
      (colorRowQ L c).allocations=9 := by
  have ha := (BDL26NativeSupportMetadata.atlas_read_cost c L).2
  have hx := (scan_cost (2*c.owner+c.copy) v.1 (0 : Fin 3) L).2
  have hq := (scan_cost (2*c.owner+c.copy) v.2.1 (1 : Fin 3) L).2
  have hz := (scan_cost (2*c.owner+c.copy) v.2.2 (2 : Fin 3) L).2
  constructor
  · simp only [colorRowQ,h,copyCodeQ,BDL26NativeTriangleKeys.rawKeyQ]
    omega
  · simp only [colorRowQ,h,copyCodeQ,BDL26NativeTriangleKeys.rawKeyQ]
    rw [ha,hx,hq,hz]

theorem row_cost {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) (c : Code) :
    (colorRowQ L c).operations≤97*L.length+50 ∧
      (colorRowQ L c).allocations≤10 := by
  have hf := BDL26NativeSupportMetadata.atlas_read_cost c L
  cases h : (BDL26NativeSupportMetadata.atlasReadQ c L).value with
  | none => simp only [colorRowQ,h,copyCodeQ]; constructor <;> omega
  | some v =>
      have hx := scan_cost (2*c.owner+c.copy) v.1 (0 : Fin 3) L
      have hq := scan_cost (2*c.owner+c.copy) v.2.1 (1 : Fin 3) L
      have hz := scan_cost (2*c.owner+c.copy) v.2.2 (2 : Fin 3) L
      simp only [colorRowQ,h,copyCodeQ,BDL26NativeTriangleKeys.rawKeyQ]
      constructor <;> omega

def colorRowsQ {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) : Run (List (ColorRow A)) :=
  BDL26NativeStateRows.mapQ (fun r => colorRowQ L r.1) L

theorem rows_order {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) :
    (colorRowsQ L).value.map Prod.fst=L.map Prod.fst := by
  rw [colorRowsQ,BDL26NativeStateRows.map_value,List.map_map]
  apply List.map_congr_left
  intro r _
  exact row_code L r.1

theorem rows_cost {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) :
    (colorRowsQ L).operations≤L.length*(97*L.length+53) ∧
      (colorRowsQ L).allocations≤11*L.length := by
  constructor
  · exact BDL26NativeStateRows.map_operations _ L (97*L.length+50)
      (fun r _ => (row_cost L r.1).1)
  · simpa [colorRowsQ,Nat.mul_comm] using
      BDL26NativeStateRows.map_allocations (fun r => colorRowQ L r.1) L 10
        (fun r _ => (row_cost L r.1).2)

/-- Only scale/depth are runtime inputs. Generator, all endpoint construction,
full-code probes, rank scans and retained copies are charged internally. -/
def colorsQ (S : OddScale) (n : ℕ) : Run (List (ColorRow (BDL26NativeStateRows.Index S n))) :=
  let atlas := BDL26NativeSupportMetadata.atlasQ S n
  let rows := colorRowsQ atlas.value
  ⟨rows.value,atlas.operations+rows.operations+2,atlas.allocations+rows.allocations+1⟩

def colorOfCodeQ (S : OddScale) (n : ℕ) (c : Code) :
    Run (Option (Triple (BDL26NativeStateRows.Index S n) × Triple ℕ)) :=
  let rows := colorsQ S n
  let out := BDL26NativeSupportMetadata.atlasReadQ c rows.value
  ⟨out.value,rows.operations+out.operations+2,rows.allocations+out.allocations⟩

abbrev T := BDL26NativeSupportMetadata.T
abbrev V := BDL26NativeSupportMetadata.V
abbrev F := BDL26NativeSupportMetadata.F

theorem colors_value (S : OddScale) (n : ℕ) :
    (colorsQ S n).value=(T S n).map
      (fun c => (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value) := by
  change (colorRowsQ _).value=_
  rw [colorRowsQ,BDL26NativeStateRows.map_value,BDL26NativeSupportMetadata.atlas_value,
    List.map_map]
  rfl

theorem colors_order (S : OddScale) (n : ℕ) :
    (colorsQ S n).value.map Prod.fst=T S n := by
  rw [colors_value,List.map_map]
  have he : (fun c => (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value.1)=id := by
    funext c
    exact row_code _ c
  change (T S n).map
    (fun c => (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value.1)=T S n
  rw [he]
  exact List.map_id _

theorem colors_nodup (S : OddScale) (n : ℕ) : (colorsQ S n).value.Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [colors_order]
  exact (BDL26NativePresentationGenerator.output_label_nodup S n).2.2

theorem colors_count (S : OddScale) (n : ℕ) :
    (colorsQ S n).value.length=BDL26NativeTriangleKeys.triangleCount S n := by
  have h := congrArg List.length (colors_order S n)
  simpa [BDL26NativeTriangleKeys.triangleCount] using h

theorem colors_cost (S : OddScale) (n : ℕ) :
    (colorsQ S n).operations≤(BDL26NativePresentationGenerator.setupQ S n).2+
      (T S n).length*(141*(T S n).length+2*(F S n).faces.length+132*(V S n).length+103)+4 ∧
    (colorsQ S n).allocations≤BDL26NativePresentationGenerator.allocatedRecords S n+
      (T S n).length*((T S n).length+3*(V S n).length+19)+2 := by
  have ha := BDL26NativeSupportMetadata.atlas_cost S n
  have hr := rows_cost (BDL26NativeSupportMetadata.atlasQ S n).value
  have hl : (BDL26NativeSupportMetadata.atlasQ S n).value.length=(T S n).length := by
    rw [BDL26NativeSupportMetadata.atlas_value,List.length_map]
  rw [hl] at hr
  constructor <;> dsimp only [colorsQ] <;> nlinarith [ha.1,ha.2,hr.1,hr.2]

theorem colors_polynomial (S : OddScale) (n : ℕ) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (colorsQ S n).operations≤A+275*B^2+103*B+4 ∧
      (colorsQ S n).allocations≤A+4*B^2+19*B+2 := by
  have hc := colors_cost S n
  have hl := BDL26NativeSupportMetadata.metadata_lengths S n
  have hg := BDL26NativePresentationGenerator.setup_cost S n
  rw [BDL26NativePresentationGenerator.setupExponent_value] at hg
  have ha := BDL26NativePresentationGenerator.allocated_polynomial S n
  dsimp only at hl ⊢
  let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
  change (T S n).length≤B ∧ (F S n).faces.length≤B ∧ (V S n).length≤B at hl
  have ho : (T S n).length*(141*(T S n).length+2*(F S n).faces.length+132*(V S n).length+103)
      ≤B*(275*B+103) := by
    apply Nat.mul_le_mul hl.1
    dsimp only [B]
    omega
  have hs : (T S n).length*((T S n).length+3*(V S n).length+19)≤B*(4*B+19) := by
    apply Nat.mul_le_mul hl.1
    dsimp only [B]
    omega
  constructor
  · calc
      (colorsQ S n).operations ≤ (BDL26NativePresentationGenerator.setupQ S n).2+
          (T S n).length*(141*(T S n).length+2*(F S n).faces.length+
            132*(V S n).length+103)+4 := hc.1
      _ ≤ (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
          B*(275*B+103)+4 := Nat.add_le_add_right (Nat.add_le_add hg ho) 4
      _ = (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
          275*B^2+103*B+4 := by ring
  · calc
      (colorsQ S n).allocations ≤ BDL26NativePresentationGenerator.allocatedRecords S n+
          (T S n).length*((T S n).length+3*(V S n).length+19)+2 := hc.2
      _ ≤ (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
          B*(4*B+19)+2 := Nat.add_le_add_right (Nat.add_le_add ha hs) 2
      _ = (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
          4*B^2+19*B+2 := by ring

noncomputable section Actual
open scoped Classical
abbrev P := BDL26NativeTriangleKeys.P
abbrev encode := BDL26NativeTriangleKeys.encode
abbrev corners := BDL26NativeSupportMetadata.corners

def nativeKey (S : OddScale) (n : ℕ) (t : Triangle (P S n)) : ℕ :=
  (BDL26NativeTriangleKeys.nativeTriangleIndex S n t).val

theorem nativeKey_injective (S : OddScale) (n : ℕ) : Function.Injective (nativeKey S n) := by
  intro a b h
  exact (BDL26NativeTriangleKeys.nativeTriangleIndex S n).injective (Fin.ext h)

theorem native_code_readback (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    nativeKey S n t=2*(encode S n t).owner+(encode S n t).copy ∧
      BDL26NativeTriangleKeys.codeAtKey (nativeKey S n t)=encode S n t :=
  ⟨rfl,BDL26NativeTriangleKeys.encode_readback S n t⟩

def nativeColor (S : OddScale) (n : ℕ) := policyColor (P S n) (nativeKey S n)

def nativeBoundedColor (S : OddScale) (n : ℕ) : Triangle (P S n) → Fin 3 → Fin 56 :=
  boundedPolicyColor (P S n) (nativeKey S n) (state_boundedValence S n)

theorem native_rank_lt (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    nativeColor S n t i<56 := policyColor_lt _ _ (state_boundedValence S n) t i

theorem native_bounded_value (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    (nativeBoundedColor S n t i).val=nativeColor S n t i := rfl

/-- The two native copies share X, hence their X-fiber ranks strictly increase. -/
theorem copy_x_rank_strict (S : OddScale) (n : ℕ) (f : (P S n).Face) :
    nativeColor S n (f,0) 0<nativeColor S n (f,1) 0 := by
  change fiberRank (nativeKey S n) (fun t : Triangle (P S n) => (P S n).faceX t.1) (f,0)<
    fiberRank (nativeKey S n) (fun t : Triangle (P S n) => (P S n).faceX t.1) (f,1)
  apply fiberRank_strictMono (nativeKey S n)
    (fun t : Triangle (P S n) => (P S n).faceX t.1) (f,0) (f,1) rfl
  change 2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex f).val+0<
    2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex f).val+1
  omega

theorem native_same_vertex (S : OddScale) (n : ℕ) {a b : Triangle (P S n)}
    (hc : nativeColor S n a=nativeColor S n b) {i j : Fin 3}
    (hv : triangleVertex (P S n) a i=triangleVertex (P S n) b j) : a=b :=
  policy_same_vertex _ _ (nativeKey_injective S n) hc hv

theorem native_support_disjoint (S : OddScale) (n : ℕ) {a b : Triangle (P S n)}
    (hne : a≠b) (hc : nativeColor S n a=nativeColor S n b) :
    Disjoint (triangleSupport (P S n) a) (triangleSupport (P S n) b) :=
  policy_support_disjoint _ _ (nativeKey_injective S n) hne hc

private theorem corners_at (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    tripleAt (corners S n t) i=BDL26NativePresentationGenerator.generatedVertexIndex S n
      (triangleVertex (P S n) t i) := by
  fin_cases i <;> rfl

theorem actual_corner_decode (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    BDL26NativeStateRows.decode S n (tripleAt (corners S n t) i)=triangleVertex (P S n) t i := by
  rw [corners_at]
  exact Equiv.symm_apply_apply (BDL26NativePresentationGenerator.generatedVertexIndex S n) _

private theorem count_covered {U : Type*} [Fintype U] (e : U → Code)
    (he : Function.Injective e) (L : List Code) (hn : L.Nodup)
    (hL : ∀c,c∈L ↔ ∃u,e u=c) (p : Code → Bool) (q : U → Prop) [DecidablePred q]
    (hp : ∀u,p (e u)=true ↔ q u) :
    L.countP p=(Finset.univ.filter q).card := by
  classical
  have hs : (L.filter p).toFinset=(Finset.univ.filter q).image e := by
    ext c
    constructor
    · intro hc
      have hm := List.mem_filter.mp (List.mem_toFinset.mp hc)
      obtain ⟨u,hu⟩ := (hL c).mp hm.1
      apply Finset.mem_image.mpr
      refine ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hu⟩
      apply (hp u).mp
      simpa [hu] using hm.2
    · intro hc
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hc
      apply List.mem_toFinset.mpr
      exact List.mem_filter.mpr ⟨(hL (e u)).mpr ⟨u,rfl⟩,
        (hp u).mpr (Finset.mem_filter.mp hu).2⟩
  rw [List.countP_eq_length_filter,←List.toFinset_card_of_nodup (hn.filter p),hs]
  exact Finset.card_image_of_injective _ he

/-- All actual atlas rows contribute exactly their original earlier-fiber
predicate. No generator failure is filtered away in this correspondence. -/
theorem scan_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    (fiberScanQ (nativeKey S n t) (tripleAt (corners S n t) i) i
      (BDL26NativeSupportMetadata.atlasQ S n).value).value=nativeColor S n t i := by
  rw [scan_value,BDL26NativeSupportMetadata.atlas_value,List.countP_map]
  have he : ∀u : Triangle (P S n),
      hit (nativeKey S n t) (tripleAt (corners S n t) i) i
        (encode S n u,(BDL26NativeSupportMetadata.endpointQ (F S n) (V S n) (T S n)
          (encode S n u)).value)=true ↔
      triangleVertex (P S n) u i=triangleVertex (P S n) t i ∧ nativeKey S n u<nativeKey S n t := by
    intro u
    rw [show (BDL26NativeSupportMetadata.endpointQ (F S n) (V S n) (T S n)
      (encode S n u)).value=some (corners S n u) from
        BDL26NativeSupportMetadata.endpoint_actual S n u]
    simp only [hit,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨?_,h.2⟩
      exact (actual_corner_decode S n u i).symm.trans
        ((congrArg (BDL26NativeStateRows.decode S n) h.1).trans
          (actual_corner_decode S n t i))
    · intro h
      refine ⟨?_,h.2⟩
      exact (BDL26NativeStateRows.decode S n).injective
        ((actual_corner_decode S n u i).trans
          (h.1.trans (actual_corner_decode S n t i).symm))
  have hcount := count_covered (encode S n) (BDL26NativeTriangleKeys.encode_injective S n)
    (T S n) (BDL26NativePresentationGenerator.output_label_nodup S n).2.2
    (BDL26NativePresentationGenerator.triangle_labels S n)
    (fun c => hit (nativeKey S n t) (tripleAt (corners S n t) i) i
      (c,(BDL26NativeSupportMetadata.endpointQ (F S n) (V S n) (T S n) c).value))
    (fun u => triangleVertex (P S n) u i=triangleVertex (P S n) t i ∧
      nativeKey S n u<nativeKey S n t) he
  change (T S n).countP
    (fun c => hit (nativeKey S n t) (tripleAt (corners S n t) i) i
      (c,(BDL26NativeSupportMetadata.endpointQ (F S n) (V S n) (T S n) c).value))=
    nativeColor S n t i
  exact hcount.trans (vertex_rank (P S n) (nativeKey S n) t i)

def nativeRow (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    ColorRow (BDL26NativeStateRows.Index S n) :=
  (encode S n t,some (corners S n t,
    (nativeColor S n t 0,nativeColor S n t 1,nativeColor S n t 2)))

theorem row_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value (encode S n t)).value=
      nativeRow S n t := by
  have ha : (BDL26NativeSupportMetadata.atlasReadQ (encode S n t)
    (BDL26NativeSupportMetadata.atlasQ S n).value).value=some (corners S n t) :=
      BDL26NativeSupportMetadata.atlas_actual S n t
  have hx := scan_actual S n t 0
  have hq := scan_actual S n t 1
  have hz := scan_actual S n t 2
  change (fiberScanQ _ (corners S n t).1 _ _).value=_ at hx
  change (fiberScanQ _ (corners S n t).2.1 _ _).value=_ at hq
  change (fiberScanQ _ (corners S n t).2.2 _ _).value=_ at hz
  simp only [colorRowQ,ha,copyCodeQ,BDL26NativeTriangleKeys.rawKeyQ]
  change (encode S n t,some (corners S n t,(_,_,_)))=nativeRow S n t
  rw [show 2*(encode S n t).owner+(encode S n t).copy=nativeKey S n t from rfl]
  rw [hx,hq,hz]
  rfl

theorem output_readback (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (colorsQ S n).value[(BDL26NativeTriangleKeys.nativeTriangleIndex S n t).val]?=
      some (nativeRow S n t) := by
  rw [colors_value,List.getElem?_map,BDL26NativeTriangleKeys.triangle_readback,
    Option.map_some,row_actual]

theorem output_complete (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    nativeRow S n t∈(colorsQ S n).value := by
  rw [colors_value]
  exact List.mem_map.mpr ⟨encode S n t,BDL26NativeTriangleKeys.encode_member S n t,
    row_actual S n t⟩

theorem output_unique (S : OddScale) (n : ℕ)
    (r : ColorRow (BDL26NativeStateRows.Index S n)) (hr : r∈(colorsQ S n).value) :
    ∃!t : Triangle (P S n),nativeRow S n t=r := by
  rw [colors_value] at hr
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hr
  obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n c).mp hc
  refine ⟨t,?_,?_⟩
  · rw [←he,←ht]
    exact (row_actual S n t).symm
  · intro u hu
    apply BDL26NativeTriangleKeys.encode_injective S n
    have h1 := congrArg Prod.fst hu
    have h2 := congrArg Prod.fst he
    change encode S n u=r.1 at h1
    rw [row_code] at h2
    exact h1.trans (h2.symm.trans ht.symm)

/-- All rows succeed internally, preserve the full code and typed corners, and
compute all three ranks; actual valence discharges the fixed palette bounds. -/
theorem output_sound (S : OddScale) (n : ℕ)
    (r : ColorRow (BDL26NativeStateRows.Index S n)) (hr : r∈(colorsQ S n).value) :
    ∃t : Triangle (P S n),r=nativeRow S n t ∧
      ∀i : Fin 3,nativeColor S n t i<56 := by
  obtain ⟨t,ht,_⟩ := output_unique S n r hr
  exact ⟨t,ht.symm,native_rank_lt S n t⟩

private theorem colors_pairs (S : OddScale) (n : ℕ) :
    (colorsQ S n).value=(T S n).map (fun c =>
      (c,(colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value.2)) := by
  rw [colors_value]
  apply List.map_congr_left
  intro c _
  apply Prod.ext
  · exact row_code _ c
  · rfl

theorem lookup_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (colorOfCodeQ S n (encode S n t)).value=(nativeRow S n t).2 := by
  change (BDL26NativeSupportMetadata.atlasReadQ _ (colorsQ S n).value).value=_
  rw [colors_pairs,BDL26NativeSupportMetadata.atlas_read_map _ _ _
    (BDL26NativeTriangleKeys.encode_member S n t),row_actual]

theorem lookup_missing (S : OddScale) (n : ℕ) (c : Code) (hc : c∉T S n) :
    (colorOfCodeQ S n c).value=none := by
  change (BDL26NativeSupportMetadata.atlasReadQ c (colorsQ S n).value).value=none
  rw [colors_pairs]
  exact (BDL26NativeSupportMetadata.atlas_read_missing _ c (T S n) hc).1

theorem lookup_cost (S : OddScale) (n : ℕ) (c : Code) :
    (colorOfCodeQ S n c).operations≤(colorsQ S n).operations+43*(T S n).length+3 ∧
      (colorOfCodeQ S n c).allocations=(colorsQ S n).allocations := by
  have h := BDL26NativeSupportMetadata.atlas_read_cost c (colorsQ S n).value
  have hl : (colorsQ S n).value.length=(T S n).length := by
    rw [colors_value,List.length_map]
  rw [hl] at h
  constructor <;> dsimp only [colorOfCodeQ] <;> omega

theorem lookup_polynomial (S : OddScale) (n : ℕ) (c : Code) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (colorOfCodeQ S n c).operations≤A+275*B^2+146*B+7 ∧
      (colorOfCodeQ S n c).allocations≤A+4*B^2+19*B+2 := by
  have hc := colors_polynomial S n
  have hq := lookup_cost S n c
  have hl := (BDL26NativeSupportMetadata.metadata_lengths S n).1
  change (T S n).length≤(n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15 at hl
  dsimp only at hc ⊢
  constructor <;> omega

theorem lookup_failure_iff (S : OddScale) (n : ℕ) (c : Code) :
    (colorOfCodeQ S n c).value=none ↔ ¬∃t : Triangle (P S n),encode S n t=c := by
  constructor
  · intro h ⟨t,ht⟩
    rw [←ht,lookup_actual] at h
    cases h
  · intro h
    apply lookup_missing S n c
    intro hc
    exact h ((BDL26NativePresentationGenerator.triangle_labels S n c).mp hc)

theorem invalid_padding (S : OddScale) (n : ℕ) (c : Code) (hl : c.l≠0) :
    (colorOfCodeQ S n c).value=none := by
  apply (lookup_failure_iff S n c).mpr
  rintro ⟨t,ht⟩
  exact hl (congrArg (fun c : Code => c.l) ht).symm

theorem seed_count (S : OddScale) : (colorsQ S 0).value.length=8 := by
  rw [colors_count,BDL26NativeTriangleKeys.triangle_count]
  rfl

/-- Actual seed face2/copy0 has dense key4 but first rank0 in its X fiber.
The key and a bounded local color are therefore different quantities. -/
theorem seed_key_not_color (S : OddScale) :
    nativeKey S 0 ((2 : Fin 4),(0 : Fin 2))=4 ∧
      nativeColor S 0 ((2 : Fin 4),(0 : Fin 2)) 0=0 := by
  constructor
  · rfl
  · change fiberRank (fun u : Fin 4 × Fin 2 => 2*u.1.val+u.2.val)
      (fun u : Fin 4 × Fin 2 => baseFaceX u.1) ((2 : Fin 4),(0 : Fin 2))=0
    unfold fiberRank earlierFiber
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu
    rcases u with ⟨f,d⟩
    have hkey : 2*f.val+d.val<4 := hu.2
    have hf : f=(0 : Fin 4) ∨ f=(1 : Fin 4) := by
      have hval : f.val=0 ∨ f.val=1 := by omega
      rcases hval with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hf with rfl | rfl
    · have hbad : (0 : ℕ)=1 := congrArg Fin.val hu.1
      omega
    · have hbad : (0 : ℕ)=1 := congrArg Fin.val hu.1
      omega

/-- Distinct copy labels remain distinct rows, irrespective of image geometry. -/
theorem copies_distinct (S : OddScale) (n : ℕ) (f : (P S n).Face) :
    nativeRow S n (f,0)≠nativeRow S n (f,1) := by
  intro h
  have he := BDL26NativeTriangleKeys.encode_injective S n (congrArg Prod.fst h)
  have hd := congrArg (fun t : Triangle (P S n) => t.2.val) he
  norm_num at hd

end Actual
end QEC.Coding.BDL26NativeTriangleColors
