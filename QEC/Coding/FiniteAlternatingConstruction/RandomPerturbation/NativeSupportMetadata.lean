import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeStateRows

/-!
# Paid native triangle-address and support metadata

Project-derived internal refinement supporting BDL26 construction, perturbation
and replacement. The actual numeric generator supplies every atlas row. Four
complete native codes are runtime data; original event encoding is proof-only.
Original rank, colour, anchor, event-priority and selected-event ingress remain
external. Costs count finite-record/cursor operations and allocations, including
rejected full-code probes; no finite-bit or Lean/hardware runtime is asserted.
-/
namespace QEC.Coding.BDL26NativeSupportMetadata

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

namespace N
export BDL26NativePresentationGenerator (Code FaceRow Frame)
end N

open N
abbrev Run := BDL26NativeStateRows.Run
abbrev Index := BDL26NativeStateRows.Index
noncomputable abbrev P := BDL26NativeStateRows.P

/-- A bounded address is built by the visited prefix, without a free length
scan. Every probe uses the OUTER ten-field equality counter. -/
def locateQ (c : Code) : (L : List Code) → Run (Option (Fin L.length))
  | [] => ⟨none,1,0⟩
  | a::L =>
      let test := BDL26NativePresentationGenerator.equalCodeQ c a
      if test.1 then ⟨some 0,test.2+2,1⟩ else
        let rest := locateQ c L
        match rest.value with
        | none => ⟨none,test.2+rest.operations+2,rest.allocations⟩
        | some i => ⟨some i.succ,test.2+rest.operations+3,rest.allocations+1⟩

theorem locate_complete (c : Code) (L : List Code) (hc : c∈L) :
    ∃i,(locateQ c L).value=some i := by
  induction L with
  | nil => simp at hc
  | cons a L ih =>
      by_cases h : c=a
      · subst a
        exact ⟨0,by simp [locateQ,BDL26NativePresentationGenerator.equalCodeQ]⟩
      · have ht : c∈L := by simpa only [List.mem_cons,h,false_or] using hc
        obtain ⟨i,hi⟩ := ih ht
        exact ⟨i.succ,by simp [locateQ,BDL26NativePresentationGenerator.equalCodeQ,h,hi]⟩

theorem locate_missing (c : Code) (L : List Code) (hc : c∉L) :
    (locateQ c L).value=none ∧ (locateQ c L).operations=43*L.length+1 ∧
      (locateQ c L).allocations=0 := by
  induction L with
  | nil => simp [locateQ]
  | cons a L ih =>
      have h : c≠a := by intro he; exact hc (by simp [he])
      have ht : c∉L := fun hm => hc (by simp [hm])
      have hr := ih ht
      simp only [locateQ,BDL26NativePresentationGenerator.equalCodeQ,
        decide_eq_false_iff_not.mpr h,Bool.false_eq_true,if_false,hr.1,List.length_cons]
      exact ⟨trivial,by omega,hr.2.2⟩

theorem locate_cost (c : Code) (L : List Code) :
    (locateQ c L).operations≤44*L.length+1 ∧ (locateQ c L).allocations≤L.length := by
  induction L with
  | nil => simp [locateQ]
  | cons a L ih =>
      by_cases h : c=a
      · simp [locateQ,BDL26NativePresentationGenerator.equalCodeQ,h]
        omega
      · cases hr : (locateQ c L).value <;>
          simp only [locateQ,BDL26NativePresentationGenerator.equalCodeQ,
            decide_eq_false_iff_not.mpr h,Bool.false_eq_true,if_false,hr,List.length_cons] <;>
          constructor <;> omega

private theorem handle_lt_iff_mem (c : Code) (L : List Code) :
    (BDL26NativePresentationGenerator.handleQ c L).1<L.length ↔ c∈L := by
  induction L with
  | nil => simp [BDL26NativePresentationGenerator.handleQ]
  | cons a L ih =>
      by_cases h : c=a <;>
        simp [BDL26NativePresentationGenerator.handleQ,
          BDL26NativePresentationGenerator.equalCodeQ,h,ih]

theorem locate_handle (c : Code) (L : List Code) (i : Fin L.length)
    (hi : (locateQ c L).value=some i) :
    (BDL26NativePresentationGenerator.handleQ c L).1=i.val := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons a L ih =>
      by_cases h : c=a
      · have he : (0 : Fin (a::L).length)=i := by
          simpa [locateQ,BDL26NativePresentationGenerator.equalCodeQ,h] using hi
        subst i
        simp [BDL26NativePresentationGenerator.handleQ,BDL26NativePresentationGenerator.equalCodeQ,h]
      · cases hr : (locateQ c L).value with
        | none => simp [locateQ,BDL26NativePresentationGenerator.equalCodeQ,h,hr] at hi
        | some j =>
            have he : j.succ=i := by
              simpa [locateQ,BDL26NativePresentationGenerator.equalCodeQ,h,hr] using hi
            subst i
            have ht := ih j hr
            simp only [BDL26NativePresentationGenerator.handleQ,
              BDL26NativePresentationGenerator.equalCodeQ,decide_eq_false_iff_not.mpr h,
              Bool.false_eq_true,if_false]
            simpa using congrArg Nat.succ ht

abbrev Triple (A : Type*) := A × A × A

/-- Complete Code construction pays all three ten-field records. The copy bit
selects the actual Q corner; X and Z keep their different family labels. -/
def endpointQ (F : Frame) (V triangles : List Code) (c : Code) :
    Run (Option (Triple (Fin V.length))) :=
  let valid := locateQ c triangles
  match valid.value with
  | none => ⟨none,valid.operations+2,valid.allocations⟩
  | some _ =>
      let face := BDL26NativePresentationGenerator.faceAtQ F.faces c.owner
      let x := locateQ ({owner:=face.1.x} : Code) V
      let q := locateQ ({family:=1,owner:=if c.copy=0 then face.1.q0 else face.1.q1} : Code) V
      let z := locateQ ({family:=2,owner:=face.1.z} : Code) V
      match x.value,q.value,z.value with
      | some a,some b,some d =>
          ⟨some (a,b,d),valid.operations+face.2+x.operations+q.operations+z.operations+40,
            valid.allocations+x.allocations+q.allocations+z.allocations+6⟩
      | _,_,_ =>
          ⟨none,valid.operations+face.2+x.operations+q.operations+z.operations+40,
            valid.allocations+x.allocations+q.allocations+z.allocations+3⟩

theorem endpoint_missing (F : Frame) (V triangles : List Code) (c : Code)
    (hc : c∉triangles) : (endpointQ F V triangles c).value=none := by
  simp [endpointQ,(locate_missing c triangles hc).1]

theorem endpoint_cost (F : Frame) (V triangles : List Code) (c : Code) :
    (endpointQ F V triangles c).operations≤44*triangles.length+2*F.faces.length+132*V.length+45 ∧
    (endpointQ F V triangles c).allocations≤triangles.length+3*V.length+6 := by
  have hv := locate_cost c triangles
  have hf := BDL26NativePresentationGenerator.faceAtQ_cost_le F.faces c.owner
  have hx := locate_cost ({owner:=(BDL26NativePresentationGenerator.faceAtQ F.faces c.owner).1.x} : Code) V
  have hq := locate_cost ({family:=1,owner:=if c.copy=0 then
    (BDL26NativePresentationGenerator.faceAtQ F.faces c.owner).1.q0 else
    (BDL26NativePresentationGenerator.faceAtQ F.faces c.owner).1.q1} : Code) V
  have hz := locate_cost ({family:=2,owner:=(BDL26NativePresentationGenerator.faceAtQ F.faces c.owner).1.z} : Code) V
  unfold endpointQ
  dsimp only
  split
  · dsimp only
    constructor <;> omega
  · split <;> dsimp only <;> constructor <;> omega

def atlasRowsQ (F : Frame) (V triangles : List Code) :
    Run (List (Code × Option (Triple (Fin V.length)))) :=
  BDL26NativeStateRows.mapQ (fun c =>
    let out := endpointQ F V triangles c
    ⟨(c,out.value),out.operations+2,out.allocations+1⟩) triangles

theorem atlas_rows_value (F : Frame) (V triangles : List Code) :
    (atlasRowsQ F V triangles).value=
      triangles.map (fun c => (c,(endpointQ F V triangles c).value)) := by
  exact BDL26NativeStateRows.map_value _ _

theorem atlas_rows_cost (F : Frame) (V triangles : List Code) :
    (atlasRowsQ F V triangles).operations≤
      triangles.length*(44*triangles.length+2*F.faces.length+132*V.length+50) ∧
    (atlasRowsQ F V triangles).allocations≤triangles.length*(triangles.length+3*V.length+8) := by
  constructor
  · have h := BDL26NativeStateRows.map_operations
      (fun c => let out := endpointQ F V triangles c
        (⟨(c,out.value),out.operations+2,out.allocations+1⟩ :
          Run (Code × Option (Triple (Fin V.length)))) ) triangles
      (44*triangles.length+2*F.faces.length+132*V.length+47) (by
        intro c _; dsimp only; have h := (endpoint_cost F V triangles c).1; omega)
    simpa [atlasRowsQ,Nat.add_assoc] using h
  · have h := BDL26NativeStateRows.map_allocations
      (fun c => let out := endpointQ F V triangles c
        (⟨(c,out.value),out.operations+2,out.allocations+1⟩ :
          Run (Code × Option (Triple (Fin V.length)))) ) triangles
      (triangles.length+3*V.length+7) (by
        intro c _; dsimp only; have h := (endpoint_cost F V triangles c).2; omega)
    simpa [atlasRowsQ,Nat.add_assoc] using h

/-- The generator and its actual face/code tables are bound once. -/
def atlasQ (S : OddScale) (n : ℕ) : Run (List (Code × Option (Triple (Index S n)))) :=
  let generated := BDL26NativePresentationGenerator.setupQ S n
  let out := atlasRowsQ generated.1.data.frame generated.1.data.vertices generated.1.triangles
  ⟨out.value,generated.2+out.operations+2,
    BDL26NativePresentationGenerator.allocatedRecords S n+out.allocations+1⟩

/-- Atlas lookup compares the full original numeric code and returns its stored
payload, retaining first-match semantics even for generic duplicate rows. -/
def atlasReadQ {A : Type*} (c : Code) : List (Code × Option A) → Run (Option A)
  | [] => ⟨none,1,0⟩
  | row::rows =>
      let test := BDL26NativePresentationGenerator.equalCodeQ c row.1
      if test.1 then ⟨row.2,test.2+2,0⟩ else
        let rest := atlasReadQ c rows
        ⟨rest.value,test.2+rest.operations+2,rest.allocations⟩

theorem atlas_read_cost {A : Type*} (c : Code) (L : List (Code × Option A)) :
    (atlasReadQ c L).operations≤43*L.length+1 ∧ (atlasReadQ c L).allocations=0 := by
  induction L with
  | nil => simp [atlasReadQ]
  | cons row L ih =>
      by_cases h : c=row.1
      · simp [atlasReadQ,BDL26NativePresentationGenerator.equalCodeQ,h]
        omega
      · simp only [atlasReadQ,BDL26NativePresentationGenerator.equalCodeQ,
          decide_eq_false_iff_not.mpr h,Bool.false_eq_true,if_false,List.length_cons]
        exact ⟨by omega,ih.2⟩

theorem atlas_read_map {A : Type*} (f : Code → Option A) (c : Code) (L : List Code)
    (hc : c∈L) : (atlasReadQ c (L.map (fun a => (a,f a)))).value=f c := by
  induction L with
  | nil => simp at hc
  | cons a L ih =>
      by_cases h : c=a
      · subst a; simp [atlasReadQ,BDL26NativePresentationGenerator.equalCodeQ]
      · have ht : c∈L := by simpa only [List.mem_cons,h,false_or] using hc
        simpa [atlasReadQ,BDL26NativePresentationGenerator.equalCodeQ,h] using ih ht

theorem atlas_read_missing {A : Type*} (f : Code → Option A) (c : Code) (L : List Code)
    (hc : c∉L) :
    (atlasReadQ c (L.map (fun a => (a,f a)))).value=none ∧
      (atlasReadQ c (L.map (fun a => (a,f a)))).operations=43*L.length+1 := by
  induction L with
  | nil => simp [atlasReadQ]
  | cons a L ih =>
      have h : c≠a := by intro he; exact hc (by simp [he])
      have ht : c∉L := fun hm => hc (by simp [hm])
      have hr := ih ht
      simp only [List.map_cons,atlasReadQ,BDL26NativePresentationGenerator.equalCodeQ,
        decide_eq_false_iff_not.mpr h,Bool.false_eq_true,if_false,List.length_cons]
      exact ⟨hr.1,by omega⟩

/-- Deduplication pays all membership scans and each retained output cell. -/
def dedupQ {A : Type*} [DecidableEq A] : List A → Run (List A)
  | [] => ⟨[],1,0⟩
  | a::L =>
      let rest := dedupQ L
      let hit := BDL26NativeStateRows.memberQ a rest.value
      if hit.value then ⟨rest.value,rest.operations+hit.operations+3,rest.allocations⟩
      else ⟨a::rest.value,rest.operations+hit.operations+3,rest.allocations+1⟩

theorem dedup_membership {A : Type*} [DecidableEq A] (L : List A) (a : A) :
    a∈(dedupQ L).value ↔ a∈L := by
  induction L generalizing a with
  | nil => simp [dedupQ]
  | cons b L ih =>
      by_cases h : b∈(dedupQ L).value
      · have ht := (BDL26NativeStateRows.member_value b (dedupQ L).value).mpr h
        have hb := (ih b).mp h
        simp [dedupQ,ht,ih]
        rintro rfl
        exact hb
      · have ht : (BDL26NativeStateRows.memberQ b (dedupQ L).value).value=false := by
          cases he : (BDL26NativeStateRows.memberQ b (dedupQ L).value).value <;>
            simp_all [BDL26NativeStateRows.member_value]
        simp [dedupQ,ht,ih]

theorem dedup_nodup {A : Type*} [DecidableEq A] (L : List A) : (dedupQ L).value.Nodup := by
  induction L with
  | nil => simp [dedupQ]
  | cons a L ih =>
      by_cases h : a∈(dedupQ L).value
      · have ht := (BDL26NativeStateRows.member_value a (dedupQ L).value).mpr h
        simpa [dedupQ,ht] using ih
      · have ht : (BDL26NativeStateRows.memberQ a (dedupQ L).value).value=false := by
          cases he : (BDL26NativeStateRows.memberQ a (dedupQ L).value).value <;>
            simp_all [BDL26NativeStateRows.member_value]
        simp [dedupQ,ht,h,ih]

theorem dedup_length {A : Type*} [DecidableEq A] (L : List A) :
    (dedupQ L).value.length≤L.length := by
  induction L with
  | nil => simp [dedupQ]
  | cons a L ih =>
      unfold dedupQ
      dsimp only
      split_ifs <;> simp only [List.length_cons] <;> omega

theorem dedup_cost {A : Type*} [DecidableEq A] (L : List A) :
    (dedupQ L).operations≤L.length*(2*L.length+4)+1 ∧
    (dedupQ L).allocations≤L.length := by
  induction L with
  | nil => simp [dedupQ]
  | cons a L ih =>
      have hm := (BDL26NativeStateRows.member_cost a (dedupQ L).value).1
      have hl := dedup_length L
      unfold dedupQ
      dsimp only
      split_ifs <;> simp only [List.length_cons] <;> constructor <;> nlinarith [ih.1,ih.2]

structure FourCodes where
  first : Code
  second : Code
  third : Code
  fourth : Code
  deriving Repr

def twelve {A : Type*} (a b c d : Triple A) : List A :=
  [a.1,a.2.1,a.2.2,b.1,b.2.1,b.2.2,c.1,c.2.1,c.2.2,d.1,d.2.1,d.2.2]

/-- All four lookups and their rejected comparisons are paid. Twelve list
cells are allocated before dedup, and the successful Option payload is paid. -/
def queryQ (S : OddScale) (n : ℕ) (codes : FourCodes) : Run (Option (List (Index S n))) :=
  let atlas := atlasQ S n
  let a := atlasReadQ codes.first atlas.value
  let b := atlasReadQ codes.second atlas.value
  let c := atlasReadQ codes.third atlas.value
  let d := atlasReadQ codes.fourth atlas.value
  match a.value,b.value,c.value,d.value with
  | some x,some y,some z,some w =>
      let out := dedupQ (twelve x y z w)
      ⟨some out.value,atlas.operations+a.operations+b.operations+c.operations+d.operations+out.operations+30,
        atlas.allocations+out.allocations+13⟩
  | _,_,_,_ =>
      ⟨none,atlas.operations+a.operations+b.operations+c.operations+d.operations+6,atlas.allocations⟩

theorem query_support (S : OddScale) (n : ℕ) (codes : FourCodes)
    (U : List (Index S n)) (hU : (queryQ S n codes).value=some U) :
    U.Nodup ∧ U.length≤12 := by
  unfold queryQ at hU
  dsimp only at hU
  split at hU
  · have he : (dedupQ (twelve _ _ _ _)).value=U := Option.some.inj hU
    subst U
    exact ⟨dedup_nodup _,by simpa [twelve] using dedup_length (twelve _ _ _ _)⟩
  · simp at hU

abbrev V (S : OddScale) (n : ℕ) :=
  (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices
abbrev T (S : OddScale) (n : ℕ) :=
  (BDL26NativePresentationGenerator.setupQ S n).1.triangles
abbrev F (S : OddScale) (n : ℕ) :=
  (BDL26NativePresentationGenerator.setupQ S n).1.data.frame

theorem atlas_value (S : OddScale) (n : ℕ) :
    (atlasQ S n).value=(T S n).map (fun c => (c,(endpointQ (F S n) (V S n) (T S n) c).value)) :=
  atlas_rows_value _ _ _

theorem atlas_cost (S : OddScale) (n : ℕ) :
    (atlasQ S n).operations≤(BDL26NativePresentationGenerator.setupQ S n).2+
      (T S n).length*(44*(T S n).length+2*(F S n).faces.length+132*(V S n).length+50)+2 ∧
    (atlasQ S n).allocations≤BDL26NativePresentationGenerator.allocatedRecords S n+
      (T S n).length*((T S n).length+3*(V S n).length+8)+1 := by
  have h := atlas_rows_cost (F S n) (V S n) (T S n)
  constructor
  · change (BDL26NativePresentationGenerator.setupQ S n).2+
      (atlasRowsQ (F S n) (V S n) (T S n)).operations+2≤_
    exact Nat.add_le_add_right (Nat.add_le_add_left h.1 _) 2
  · change BDL26NativePresentationGenerator.allocatedRecords S n+
      (atlasRowsQ (F S n) (V S n) (T S n)).allocations+1≤_
    exact Nat.add_le_add_right (Nat.add_le_add_left h.2 _) 1

private theorem atlas_length (S : OddScale) (n : ℕ) :
    (atlasQ S n).value.length=(T S n).length := by
  rw [atlas_value,List.length_map]

theorem query_cost (S : OddScale) (n : ℕ) (codes : FourCodes) :
    (queryQ S n codes).operations≤(BDL26NativePresentationGenerator.setupQ S n).2+
      (T S n).length*(44*(T S n).length+2*(F S n).faces.length+132*(V S n).length+50)+
      172*(T S n).length+400 ∧
    (queryQ S n codes).allocations≤BDL26NativePresentationGenerator.allocatedRecords S n+
      (T S n).length*((T S n).length+3*(V S n).length+8)+26 := by
  have ha := atlas_cost S n
  have h0 := atlas_read_cost codes.first (atlasQ S n).value
  have h1 := atlas_read_cost codes.second (atlasQ S n).value
  have h2 := atlas_read_cost codes.third (atlasQ S n).value
  have h3 := atlas_read_cost codes.fourth (atlasQ S n).value
  rw [atlas_length] at h0 h1 h2 h3
  cases hA : (atlasReadQ codes.first (atlasQ S n).value).value with
  | none =>
      simp only [queryQ,hA]
      constructor <;> omega
  | some x =>
      cases hB : (atlasReadQ codes.second (atlasQ S n).value).value with
      | none =>
          simp only [queryQ,hA,hB]
          constructor <;> omega
      | some y =>
          cases hC : (atlasReadQ codes.third (atlasQ S n).value).value with
          | none =>
              simp only [queryQ,hA,hB,hC]
              constructor <;> omega
          | some z =>
              cases hD : (atlasReadQ codes.fourth (atlasQ S n).value).value with
              | none =>
                  simp only [queryQ,hA,hB,hC,hD]
                  constructor <;> omega
              | some w =>
                  have hd := dedup_cost (twelve x y z w)
                  have hlen : (twelve x y z w).length=12 := rfl
                  rw [hlen] at hd
                  simp only [queryQ,hA,hB,hC,hD]
                  constructor <;> omega

theorem query_missing (S : OddScale) (n : ℕ) (codes : FourCodes)
    (hc : codes.first∉T S n) : (queryQ S n codes).value=none := by
  have h := (atlas_read_missing
    (fun c => (endpointQ (F S n) (V S n) (T S n) c).value) codes.first (T S n) hc).1
  rw [←atlas_value] at h
  simp [queryQ,h]

/-- These are actual retained list lengths, not a caller cardinality budget. -/
theorem metadata_lengths (S : OddScale) (n : ℕ) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    (T S n).length≤B ∧ (F S n).faces.length≤B ∧ (V S n).length≤B := by
  have h := BDL26NativePresentationGenerator.retained_space S n
  unfold BDL26NativePresentationGenerator.outputRecords
    BDL26NativePresentationGenerator.frameRecords at h
  dsimp only [T,F,V]
  constructor
  · omega
  · constructor <;> omega

/-- A closed polynomial in depth and the real generator radius. Every term
comes from the actual atlas/query loops and accepted generator bounds. -/
theorem query_polynomial (S : OddScale) (n : ℕ) (codes : FourCodes) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (queryQ S n codes).operations≤A+178*B^2+222*B+400 ∧
      (queryQ S n codes).allocations≤A+4*B^2+8*B+26 := by
  have hq := query_cost S n codes
  have hl := metadata_lengths S n
  have hg := BDL26NativePresentationGenerator.setup_cost S n
  rw [BDL26NativePresentationGenerator.setupExponent_value] at hg
  have ha := BDL26NativePresentationGenerator.allocated_polynomial S n
  dsimp only at hl ⊢
  let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
  have ho : (T S n).length*(44*(T S n).length+2*(F S n).faces.length+132*(V S n).length+50)
      ≤B*(178*B+50) := by
    apply Nat.mul_le_mul hl.1
    dsimp only [B]
    omega
  have hs : (T S n).length*((T S n).length+3*(V S n).length+8)≤B*(4*B+8) := by
    apply Nat.mul_le_mul hl.1
    dsimp only [B]
    omega
  constructor <;> nlinarith [hq.1,hq.2,hl.1,hl.2.1,hl.2.2]

/-- Query metadata and independently initialize the actual cache before its
update. Prior finite support ingress is explicitly external as in #1579. No
caller supplies an initialized cache or a successful-query certificate. -/
def refreshEventQ (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (externalSupports : List (List (Index S n))) :
    Run (Option (BDL26NativeStateRows.Rows (Index S n))) :=
  let query := queryQ S n codes
  match query.value with
  | none => ⟨none,query.operations+2,query.allocations⟩
  | some U =>
      let cache := BDL26NativeStateRows.executeQ S n table externalSupports
      let out := BDL26NativeStateRows.refreshQ table U cache.value
      ⟨some out.value,query.operations+cache.operations+out.operations+4,
        query.allocations+cache.allocations+out.allocations+1⟩

theorem refresh_failure (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (trace : List (List (Index S n))) (h : (queryQ S n codes).value=none) :
    (refreshEventQ S n codes table trace).value=none ∧
    (refreshEventQ S n codes table trace).operations=(queryQ S n codes).operations+2 ∧
    (refreshEventQ S n codes table trace).allocations=(queryQ S n codes).allocations := by
  simp [refreshEventQ,h]

theorem refresh_success (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (trace : List (List (Index S n))) (U : List (Index S n))
    (h : (queryQ S n codes).value=some U) :
    (refreshEventQ S n codes table trace).value=some
      (BDL26NativeStateRows.rowsFor (BDL26NativeStateRows.indices (BDL26NativeStateRows.count S n))
        table (BDL26NativeStateRows.advanceList U
          (BDL26NativeStateRows.traceCounters trace (fun _ => 0)))) := by
  simp only [refreshEventQ,h,BDL26NativeStateRows.execute_value,
    BDL26NativeStateRows.refresh_value]

theorem refresh_cost (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (trace : List (List (Index S n))) :
    (refreshEventQ S n codes table trace).operations≤(queryQ S n codes).operations+
      (BDL26NativeStateRows.executeQ S n table trace).operations+35*BDL26NativeStateRows.count S n+4 ∧
    (refreshEventQ S n codes table trace).allocations≤(queryQ S n codes).allocations+
      (BDL26NativeStateRows.executeQ S n table trace).allocations+2*BDL26NativeStateRows.count S n+1 := by
  have hl : (BDL26NativeStateRows.executeQ S n table trace).value.length=
      BDL26NativeStateRows.count S n := by
    have h := congrArg List.length (BDL26NativeStateRows.execute_order S n table trace)
    simpa only [List.length_map,BDL26NativeStateRows.indices_length] using h
  cases h : (queryQ S n codes).value with
  | none => simp only [refreshEventQ,h]; constructor <;> omega
  | some U =>
      have hu := (query_support S n codes U h).2
      have hr := BDL26NativeStateRows.refresh_cost table U
        (BDL26NativeStateRows.executeQ S n table trace).value
      rw [hl] at hr
      have hm := Nat.mul_le_mul_left (BDL26NativeStateRows.count S n)
        (show 2*U.length+11≤35 by omega)
      simp only [refreshEventQ,h]
      constructor <;> omega

/-- The complete initialized update has a polynomial bound in actual generator
size and the explicitly external finite trace length/weight. -/
theorem refresh_polynomial (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (trace : List (List (Index S n))) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (refreshEventQ S n codes table trace).operations≤
      2*A+180*B^2+269*B+410+2*trace.length+
        B*(2*BDL26NativeStateRows.traceWeight trace+11*trace.length) ∧
    (refreshEventQ S n codes table trace).allocations≤
      2*A+5*B^2+12*B+29+2*B*trace.length := by
  have hq := query_polynomial S n codes
  have he := BDL26NativeStateRows.execute_cost S n table trace
  have hr := refresh_cost S n codes table trace
  have hl := BDL26NativeStateRows.native_length_bound S n
  dsimp only at hq ⊢
  have hs := Nat.mul_le_mul hl hl
  have hw := Nat.mul_le_mul_right
    (2*BDL26NativeStateRows.traceWeight trace+11*trace.length) hl
  have ht := Nat.mul_le_mul_right trace.length hl
  constructor <;> nlinarith [hq.1,hq.2,he.1,he.2,hr.1,hr.2]

noncomputable section
open scoped Classical

/-- Proof-only encoding through the generator's internally constructed handles. -/
def vertexCode (S : OddScale) (n : ℕ) : Vertex (P S n) → Code
  | .x x => {owner:=((BDL26NativePresentationGenerator.generatedRefines S n).xIndex x).val}
  | .q q => {family:=1,owner:=((BDL26NativePresentationGenerator.generatedRefines S n).qIndex q).val}
  | .z z => {family:=2,owner:=((BDL26NativePresentationGenerator.generatedRefines S n).zIndex z).val}

def triangleCode (S : OddScale) (n : ℕ) (t : Triangle (P S n)) : Code :=
  {family:=3,owner:=((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val,
    copy:=t.2.val}

theorem vertex_handle (S : OddScale) (n : ℕ) (v : Vertex (P S n)) :
    (BDL26NativePresentationGenerator.handleQ (vertexCode S n v) (V S n)).1=
      (BDL26NativePresentationGenerator.generatedVertexIndex S n v).val := by
  cases v <;> rfl

theorem locate_vertex (S : OddScale) (n : ℕ) (v : Vertex (P S n)) :
    (locateQ (vertexCode S n v) (V S n)).value=
      some (BDL26NativePresentationGenerator.generatedVertexIndex S n v) := by
  have hm : vertexCode S n v∈V S n := (handle_lt_iff_mem _ _).mp (by
    rw [vertex_handle]
    exact (BDL26NativePresentationGenerator.generatedVertexIndex S n v).isLt)
  obtain ⟨i,hi⟩ := locate_complete _ _ hm
  have hv := locate_handle _ _ i hi
  rw [vertex_handle] at hv
  have he : i=BDL26NativePresentationGenerator.generatedVertexIndex S n v := Fin.ext hv.symm
  exact hi.trans (congrArg (fun j : Fin (V S n).length => some j) he)

theorem triangle_member (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    triangleCode S n t∈T S n :=
  (BDL26NativePresentationGenerator.triangle_labels S n _).mpr ⟨t,rfl⟩

theorem query_invalid_padding (S : OddScale) (n : ℕ) (codes : FourCodes)
    (hl : codes.first.l≠0) : (queryQ S n codes).value=none := by
  apply query_missing S n codes
  intro hc
  obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n codes.first).mp hc
  exact hl (congrArg (fun c : Code => c.l) ht).symm

def corners (S : OddScale) (n : ℕ) (t : Triangle (P S n)) : Triple (Index S n) :=
  (BDL26NativePresentationGenerator.generatedVertexIndex S n (triangleVertex (P S n) t 0),
   BDL26NativePresentationGenerator.generatedVertexIndex S n (triangleVertex (P S n) t 1),
   BDL26NativePresentationGenerator.generatedVertexIndex S n (triangleVertex (P S n) t 2))

theorem endpoint_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (endpointQ (F S n) (V S n) (T S n) (triangleCode S n t)).value=some (corners S n t) := by
  obtain ⟨i,hi⟩ := locate_complete _ _ (triangle_member S n t)
  have hf := BDL26NativePresentationGenerator.face_endpoints S n t.1
  change (BDL26NativePresentationGenerator.faceAtQ (F S n).faces
      ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val).1.x=
      ((BDL26NativePresentationGenerator.generatedRefines S n).xIndex ((P S n).faceX t.1)).val ∧
    (BDL26NativePresentationGenerator.faceAtQ (F S n).faces
      ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val).1.z=
      ((BDL26NativePresentationGenerator.generatedRefines S n).zIndex ((P S n).faceZ t.1)).val ∧
    (BDL26NativePresentationGenerator.faceAtQ (F S n).faces
      ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val).1.q0=
      ((BDL26NativePresentationGenerator.generatedRefines S n).qIndex ((P S n).faceQ t.1 0)).val ∧
    (BDL26NativePresentationGenerator.faceAtQ (F S n).faces
      ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val).1.q1=
      ((BDL26NativePresentationGenerator.generatedRefines S n).qIndex ((P S n).faceQ t.1 1)).val at hf
  have hx := locate_vertex S n (.x ((P S n).faceX t.1))
  have hq0 := locate_vertex S n (.q ((P S n).faceQ t.1 0))
  have hq1 := locate_vertex S n (.q ((P S n).faceQ t.1 1))
  have hz := locate_vertex S n (.z ((P S n).faceZ t.1))
  simp only [vertexCode] at hx hq0 hq1 hz
  unfold endpointQ
  dsimp only
  rw [hi]
  dsimp only [triangleCode]
  rcases t with ⟨f,d⟩
  fin_cases d <;>
    simp [corners,triangleVertex,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,hx,hq0,hq1,hz]

theorem atlas_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (atlasReadQ (triangleCode S n t) (atlasQ S n).value).value=some (corners S n t) := by
  rw [atlas_value]
  exact (atlas_read_map _ _ _ (triangle_member S n t)).trans (endpoint_actual S n t)

private theorem index_eq_decode (S : OddScale) (n : ℕ) (a : Index S n)
    (v : Vertex (P S n)) :
    a=BDL26NativePresentationGenerator.generatedVertexIndex S n v ↔
      BDL26NativeStateRows.decode S n a=v := by
  constructor
  · intro h; rw [h]; exact Equiv.symm_apply_apply _ _
  · intro h
    exact (Equiv.apply_symm_apply (BDL26NativePresentationGenerator.generatedVertexIndex S n) a).symm.trans
      (congrArg (BDL26NativePresentationGenerator.generatedVertexIndex S n) h)

def tripleList {A : Type*} (x : Triple A) : List A := [x.1,x.2.1,x.2.2]

theorem corners_membership (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (a : Index S n) :
    a∈tripleList (corners S n t) ↔
      BDL26NativeStateRows.decode S n a∈triangleSupport (P S n) t := by
  change a∈[(BDL26NativePresentationGenerator.generatedVertexIndex S n) (triangleVertex (P S n) t 0),
      (BDL26NativePresentationGenerator.generatedVertexIndex S n) (triangleVertex (P S n) t 1),
      (BDL26NativePresentationGenerator.generatedVertexIndex S n) (triangleVertex (P S n) t 2)] ↔
    BDL26NativeStateRows.decode S n a∈Finset.univ.image (triangleVertex (P S n) t)
  constructor
  · intro ha
    rcases List.mem_cons.mp ha with h0|ha
    · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,((index_eq_decode S n a _).mp h0).symm⟩
    rcases List.mem_cons.mp ha with h1|ha
    · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,((index_eq_decode S n a _).mp h1).symm⟩
    rcases List.mem_cons.mp ha with h2|ha
    · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,((index_eq_decode S n a _).mp h2).symm⟩
    · cases ha
  · intro ha
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
    have he := (index_eq_decode S n a (triangleVertex (P S n) t i)).mpr hi.symm
    fin_cases i
    · exact List.mem_cons.mpr (Or.inl he)
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl he)))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl he)))))

/-- Read four labels from the event's actual four-element finite list. This
is an internal semantic encoding, not a constructed original event stream. -/
def eventLabels (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) : Triangle (P S n) × Triangle (P S n) ×
      Triangle (P S n) × Triangle (P S n) :=
  let L := e.val.toList
  have hL : L.length=4 := by simpa only [L,Finset.length_toList] using e.property.1
  (L.get ⟨0,by omega⟩,L.get ⟨1,by omega⟩,L.get ⟨2,by omega⟩,L.get ⟨3,by omega⟩)

theorem event_labels_list (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) :
    [ (eventLabels S n J r e).1,(eventLabels S n J r e).2.1,
      (eventLabels S n J r e).2.2.1,(eventLabels S n J r e).2.2.2 ]=e.val.toList := by
  have hL : e.val.toList.length=4 := by simpa using e.property.1
  obtain ⟨a,b,c,d,h⟩ := List.length_eq_four.mp hL
  simp [eventLabels,h]

def eventCodes (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) : FourCodes :=
  let t := eventLabels S n J r e
  ⟨triangleCode S n t.1,triangleCode S n t.2.1,
    triangleCode S n t.2.2.1,triangleCode S n t.2.2.2⟩

private theorem twelve_membership {A : Type*} (x y z w : Triple A) (a : A) :
    a∈twelve x y z w ↔ a∈tripleList x ∨ a∈tripleList y ∨ a∈tripleList z ∨ a∈tripleList w := by
  simp [twelve,tripleList,or_assoc]

private theorem event_support_four (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) (v : Vertex (P S n)) :
    v∈eventSupport (P S n) J r e ↔
      v∈triangleSupport (P S n) (eventLabels S n J r e).1 ∨
      v∈triangleSupport (P S n) (eventLabels S n J r e).2.1 ∨
      v∈triangleSupport (P S n) (eventLabels S n J r e).2.2.1 ∨
      v∈triangleSupport (P S n) (eventLabels S n J r e).2.2.2 := by
  have he : [ (eventLabels S n J r e).1,(eventLabels S n J r e).2.1,
      (eventLabels S n J r e).2.2.1,(eventLabels S n J r e).2.2.2 ].toFinset=e.val := by
    rw [event_labels_list,Finset.toList_toFinset]
  change v∈e.val.biUnion (triangleSupport (P S n)) ↔ _
  rw [←he]
  simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  aesop

/-- Universal exact original-event support, with no caller success/support
certificate. The same original event is encoded internally. -/
theorem query_original (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) :
    ∃U,(queryQ S n (eventCodes S n J r e)).value=some U ∧ U.Nodup ∧ U.length≤12 ∧
      ∀a,a∈U ↔ BDL26NativeStateRows.decode S n a∈eventSupport (P S n) J r e := by
  let t := eventLabels S n J r e
  let raw := twelve (corners S n t.1) (corners S n t.2.1)
    (corners S n t.2.2.1) (corners S n t.2.2.2)
  refine ⟨(dedupQ raw).value,?_,dedup_nodup _,?_,?_⟩
  · simp [queryQ,eventCodes,atlas_actual,t,raw]
  · simpa [raw,twelve] using dedup_length raw
  · intro a
    change a∈(dedupQ (twelve (corners S n t.1) (corners S n t.2.1)
      (corners S n t.2.2.1) (corners S n t.2.2.2))).value ↔ _
    rw [dedup_membership,twelve_membership]
    rw [corners_membership,corners_membership,corners_membership,corners_membership]
    exact (event_support_four S n J r e _).symm

/-- The unchanged original event increments precisely its original support;
all native cache rows are constructed inside refreshEventQ. The old selected
trace remains the same explicitly external ingress used by the parent API. -/
theorem refresh_original (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (table : BDL26NativeStateRows.Samples (Vertex (P S n)))
    (m : ℕ) (e : Event (P S n) J r) :
    (refreshEventQ S n (eventCodes S n J r e) (BDL26NativeStateRows.encodeSamples S n table)
      (BDL26NativeStateRows.originalTrace S n J r lambda K table m)).value=some
      (BDL26NativeStateRows.rowsFor (BDL26NativeStateRows.indices (BDL26NativeStateRows.count S n))
        (BDL26NativeStateRows.encodeSamples S n table)
        (fun a => advance (eventSupport (P S n) J r) e
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable table) m)
          (BDL26NativeStateRows.decode S n a))) := by
  obtain ⟨U,hU,_,_,hmem⟩ := query_original S n J r e
  rw [refresh_success S n _ _ _ U hU,BDL26NativeStateRows.original_trace_counters]
  congr 2
  funext a
  simp only [BDL26NativeStateRows.advanceList,advance,hmem]

theorem refresh_original_read (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (table : BDL26NativeStateRows.Samples (Vertex (P S n)))
    (m : ℕ) (e : Event (P S n) J r) (v : Vertex (P S n)) :
    ((refreshEventQ S n (eventCodes S n J r e) (BDL26NativeStateRows.encodeSamples S n table)
      (BDL26NativeStateRows.originalTrace S n J r lambda K table m)).value.map
      (fun rows => (BDL26NativeStateRows.readQ ((BDL26NativeStateRows.decode S n).symm v) rows).value))=
      some (advance (eventSupport (P S n) J r) e
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable table) m) v,
        table (v,advance (eventSupport (P S n) J r) e
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable table) m) v)) := by
  rw [refresh_original]
  simp only [Option.map_some]
  rw [BDL26NativeStateRows.read_rowsFor _ _ _ _ (BDL26NativeStateRows.indices_complete _ _)]
  simp only [BDL26NativeStateRows.encodeSamples,Equiv.apply_symm_apply]

theorem refresh_original_order (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (table : BDL26NativeStateRows.Samples (Vertex (P S n)))
    (m : ℕ) (e : Event (P S n) J r) :
    ((refreshEventQ S n (eventCodes S n J r e) (BDL26NativeStateRows.encodeSamples S n table)
      (BDL26NativeStateRows.originalTrace S n J r lambda K table m)).value.map
      (List.map Prod.fst))=some (BDL26NativeStateRows.indices (BDL26NativeStateRows.count S n)) := by
  rw [refresh_original]
  simp [BDL26NativeStateRows.rowsFor,List.map_map,Function.comp_def]

end
end QEC.Coding.BDL26NativeSupportMetadata
