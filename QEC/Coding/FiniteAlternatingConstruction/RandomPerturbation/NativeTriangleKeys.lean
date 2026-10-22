import QEC.Coding.FiniteAlternatingConstruction.NativePresentationGenerator

/-!
# Paid native triangle keys and full-record validated order queries

Project-derived internal/API refinement of the native triangle address space. Only the merged
native generator is used. The native dense order is a separate named relation;
legacy ranks, colors, eligibility, priorities and sampling laws are unchanged.
Costs use the generator's finite-record/cursor model, not integer bit complexity.
-/
namespace QEC.Coding.BDL26NativeTriangleKeys

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

abbrev Code := BDL26NativePresentationGenerator.Code
abbrev KRun (A : Type*) := A × ℕ × ℕ
abbrev KeyRow := Code × ℕ

def value {A : Type*} (r : KRun A) : A := r.1
def operations {A : Type*} (r : KRun A) : ℕ := r.2.1
def allocations {A : Type*} (r : KRun A) : ℕ := r.2.2

/-- Two scalar reads, multiplication, addition and return. This does not validate. -/
def rawKeyQ (c : Code) : KRun ℕ := (2*c.owner+c.copy,5,0)

/-- Retain each complete immutable Code; allocate its pair and output list cell. -/
def keyRowsQ : List Code → KRun (List KeyRow)
  | [] => ([],1,0)
  | c::cs =>
      let k := rawKeyQ c
      let tail := keyRowsQ cs
      ((c,k.1)::tail.1,k.2.1+tail.2.1+5,k.2.2+tail.2.2+2)

/-- Each failed comparison pays the outer generator's complete ten-field test. -/
def lookupRowsQ (c : Code) : List KeyRow → KRun (Option ℕ)
  | [] => (none,1,0)
  | r::rs =>
      let eq := BDL26NativePresentationGenerator.equalCodeQ c r.1
      if eq.1 then (some r.2,eq.2+2,1)
      else
        let tail := lookupRowsQ c rs
        (tail.1,eq.2+tail.2.1+2,tail.2.2)

/-- No caller atlas: the actual complete generator runs inside this entry point. -/
def keySetupQ (S : OddScale) (n : ℕ) : KRun (List KeyRow) :=
  let generated := BDL26NativePresentationGenerator.setupQ S n
  let rows := keyRowsQ generated.1.triangles
  (rows.1,generated.2+rows.2.1+2,BDL26NativePresentationGenerator.allocatedRecords S n+rows.2.2+1)

def keyOfCodeQ (S : OddScale) (n : ℕ) (c : Code) : KRun (Option ℕ) :=
  let atlas := keySetupQ S n
  let found := lookupRowsQ c atlas.1
  (found.1,atlas.2.1+found.2.1+2,atlas.2.2+found.2.2+1)

/-- Both complete closed lookups are evaluated and charged, even on failure. -/
def compareCodesQ (S : OddScale) (n : ℕ) (a b : Code) : KRun (Option Bool) :=
  let x := keyOfCodeQ S n a
  let y := keyOfCodeQ S n b
  match x.1,y.1 with
  | some i,some j => (some (decide (i≤j)),x.2.1+y.2.1+4,x.2.2+y.2.2+1)
  | _,_ => (none,x.2.1+y.2.1+2,x.2.2+y.2.2)


/-- Exact pair accounting keeps both closed lookups in every branch. -/
theorem compare_accounting (S : OddScale) (n : ℕ) (a b : Code) :
    operations (compareCodesQ S n a b)=
        operations (keyOfCodeQ S n a)+operations (keyOfCodeQ S n b)+
          (if (keyOfCodeQ S n a).1.isSome && (keyOfCodeQ S n b).1.isSome then 4 else 2) ∧
      allocations (compareCodesQ S n a b)=
        allocations (keyOfCodeQ S n a)+allocations (keyOfCodeQ S n b)+
          (if (keyOfCodeQ S n a).1.isSome && (keyOfCodeQ S n b).1.isSome then 1 else 0) := by
  cases hx : (keyOfCodeQ S n a).1 <;> cases hy : (keyOfCodeQ S n b).1 <;>
    simp [compareCodesQ,hx,hy,operations,allocations]

theorem rawKey_spec (c : Code) :
    (rawKeyQ c).1=2*c.owner+c.copy ∧ operations (rawKeyQ c)=5 ∧
      allocations (rawKeyQ c)=0 := ⟨rfl,rfl,rfl⟩

theorem keyRows_spec (cs : List Code) :
    (keyRowsQ cs).1=cs.map (fun c => (c,2*c.owner+c.copy)) ∧
      operations (keyRowsQ cs)=10*cs.length+1 ∧
      allocations (keyRowsQ cs)=2*cs.length := by
  induction cs with
  | nil => simp [keyRowsQ,operations,allocations]
  | cons c cs ih =>
      rcases ih with ⟨hv,ho,ha⟩
      simp only [keyRowsQ,rawKeyQ,List.map_cons,List.length_cons,operations,allocations] at *
      exact ⟨congrArg (List.cons _) hv,by omega,by omega⟩

theorem lookup_cost (c : Code) (rs : List KeyRow) :
    operations (lookupRowsQ c rs)≤43*rs.length+1 ∧
      allocations (lookupRowsQ c rs)≤1 := by
  induction rs with
  | nil => simp [lookupRowsQ,operations,allocations]
  | cons r rs ih =>
      by_cases h : c=r.1
      · simp [lookupRowsQ,BDL26NativePresentationGenerator.equalCodeQ,h,operations,allocations]; omega
      · simp [lookupRowsQ,BDL26NativePresentationGenerator.equalCodeQ,h,
          operations,allocations] at *
        omega

theorem lookup_empty (c : Code) : lookupRowsQ c []=(none,1,0) := rfl

theorem lookup_head (c : Code) (k : ℕ) (rs : List KeyRow) :
    lookupRowsQ c ((c,k)::rs)=(some k,43,1) := by
  simp [lookupRowsQ,BDL26NativePresentationGenerator.equalCodeQ]

theorem lookup_failure (c : Code) (rs : List KeyRow)
    (h : ∀r∈rs,r.1≠c) :
    lookupRowsQ c rs=(none,43*rs.length+1,0) := by
  induction rs with
  | nil => simp [lookupRowsQ]
  | cons r rs ih =>
      have hr : c≠r.1 := Ne.symm (h r (by simp))
      have ht := ih (fun r hr => h r (by simp [hr]))
      simp [lookupRowsQ,BDL26NativePresentationGenerator.equalCodeQ,hr,ht,List.length_cons]
      omega

open scoped Classical in
theorem lookup_rows_value (c : Code) (cs : List Code) :
    (lookupRowsQ c (keyRowsQ cs).1).1=
      if c∈cs then some (2*c.owner+c.copy) else none := by
  induction cs with
  | nil => simp [keyRowsQ,lookupRowsQ]
  | cons a cs ih =>
      by_cases h : c=a
      · subst a; simp [keyRowsQ,rawKeyQ,lookupRowsQ,BDL26NativePresentationGenerator.equalCodeQ]
      · simp [keyRowsQ,rawKeyQ,lookupRowsQ,BDL26NativePresentationGenerator.equalCodeQ,h,ih]


theorem lookup_after_rejections (c : Code) (rejected : List KeyRow) (k : ℕ)
    (tail : List KeyRow) (h : ∀r∈rejected,r.1≠c) :
    lookupRowsQ c (rejected++(c,k)::tail)=(some k,43*(rejected.length+1),1) := by
  induction rejected with
  | nil => simpa using lookup_head c k tail
  | cons r rs ih =>
      have hr : c≠r.1 := Ne.symm (h r (by simp))
      have ht := ih (fun r hr => h r (by simp [hr]))
      simp [lookupRowsQ,BDL26NativePresentationGenerator.equalCodeQ,hr,ht]
      omega

/-- Complete native face/copy list, before the generator's paid dedup. -/
def frameCodes (m : ℕ) : List Code :=
  (List.range m).flatMap (fun f =>
    [{family:=3,owner:=f,copy:=0},{family:=3,owner:=f,copy:=1}])

/-- Proof descriptor of a dense position; runtime validation uses the paid full-Code scan. -/
def codeAtKey (k : ℕ) : Code := {family:=3,owner:=k/2,copy:=k%2}

private theorem frameCodes_succ (m : ℕ) :
    frameCodes (m+1)=frameCodes m++
      [{family:=3,owner:=m,copy:=0},{family:=3,owner:=m,copy:=1}] := by
  simp [frameCodes,List.range_succ,List.flatMap_append]

/-- Ordered equality, stronger than membership or cardinality. -/
theorem frame_codes_dense (m : ℕ) :
    frameCodes m=(List.range (2*m)).map codeAtKey := by
  induction m with
  | zero => simp [frameCodes]
  | succ m ih =>
      rw [frameCodes_succ,ih]
      have h : 2*(m+1)=2*m+1+1 := by omega
      rw [h,List.range_succ,List.range_succ,List.map_append,List.map_append]
      have h0 : codeAtKey (2*m)=({family:=3,owner:=m,copy:=0} : Code) := by
        unfold codeAtKey; congr <;> omega
      have h1 : codeAtKey (2*m+1)=({family:=3,owner:=m,copy:=1} : Code) := by
        unfold codeAtKey; congr <;> omega
      simp [h0,h1,List.append_assoc]

theorem frame_keys_dense (m : ℕ) :
    (frameCodes m).map (fun c => 2*c.owner+c.copy)=List.range (2*m) := by
  rw [frame_codes_dense,List.map_map]
  have h : (fun k => 2*(codeAtKey k).owner+(codeAtKey k).copy)=id := by
    funext k; simp only [codeAtKey,id_eq]; omega
  simp only [Function.comp_def]
  rw [h,List.map_id]

private theorem frame_nodup (m : ℕ) : (frameCodes m).Nodup := by
  have h : ((frameCodes m).map (fun c => 2*c.owner+c.copy)).Nodup := by
    rw [frame_keys_dense]; exact List.nodup_range
  exact List.Nodup.of_map (fun c : Code => 2*c.owner+c.copy) h

private theorem dedup_preserves (cs : List Code) (h : cs.Nodup) :
    (BDL26NativePresentationGenerator.dedupQ cs).1=cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rcases List.nodup_cons.mp h with ⟨hn,ht⟩
      have hv := ih ht
      have hf : (BDL26NativePresentationGenerator.memCodeQ c cs).1=false := by
        apply Bool.eq_false_iff.mpr
        intro he
        exact hn ((BDL26NativePresentationGenerator.memCodeQ_correct c cs).mp he)
      simp [BDL26NativePresentationGenerator.dedupQ,hv,hf]

theorem triangle_codes (F : BDL26NativePresentationGenerator.Frame) :
    (BDL26NativePresentationGenerator.triangleCodesQ F).1=frameCodes F.nf := by
  have hraw : (BDL26NativePresentationGenerator.loopQ F.nf (fun f => BDL26NativePresentationGenerator.mapQ
      (fun d => BDL26NativePresentationGenerator.emitQ {family:=3,owner:=f,copy:=d}) [0,1])).1=
      frameCodes F.nf := by
    simp [BDL26NativePresentationGenerator.loopQ,BDL26NativePresentationGenerator.flatMapQ_value,BDL26NativePresentationGenerator.rangeQ_value,BDL26NativePresentationGenerator.mapQ_value,
      BDL26NativePresentationGenerator.emitQ,frameCodes]
  change (BDL26NativePresentationGenerator.dedupQ _).1=_
  rw [hraw]
  exact dedup_preserves _ (frame_nodup _)

theorem triangle_keys (S : OddScale) (n : ℕ) :
    ((BDL26NativePresentationGenerator.setupQ S n).1.triangles.map (fun c => 2*c.owner+c.copy))=
      List.range (2*(BDL26NativePresentationGenerator.setupQ S n).1.data.frame.nf) := by
  change ((BDL26NativePresentationGenerator.triangleCodesQ _).1.map _) = _
  rw [triangle_codes,frame_keys_dense]
  rfl

def triangleCount (S : OddScale) (n : ℕ) : ℕ :=
  (BDL26NativePresentationGenerator.setupQ S n).1.triangles.length

theorem triangle_count (S : OddScale) (n : ℕ) :
    triangleCount S n=2*(BDL26NativePresentationGenerator.setupQ S n).1.data.frame.nf := by
  have h := congrArg List.length (triangle_keys S n)
  simpa [triangleCount] using h

theorem keySetup_spec (S : OddScale) (n : ℕ) :
    (keySetupQ S n).1=(BDL26NativePresentationGenerator.setupQ S n).1.triangles.map
        (fun c => (c,2*c.owner+c.copy)) ∧
      operations (keySetupQ S n)=(BDL26NativePresentationGenerator.setupQ S n).2+10*triangleCount S n+3 ∧
      allocations (keySetupQ S n)=BDL26NativePresentationGenerator.allocatedRecords S n+2*triangleCount S n+1 := by
  have h := keyRows_spec (BDL26NativePresentationGenerator.setupQ S n).1.triangles
  dsimp only [keySetupQ,operations,allocations,triangleCount] at *
  exact ⟨h.1,by omega,by omega⟩

theorem keySetup_projections (S : OddScale) (n : ℕ) :
    ((keySetupQ S n).1.map Prod.fst)=(BDL26NativePresentationGenerator.setupQ S n).1.triangles ∧
      ((keySetupQ S n).1.map Prod.snd)=List.range (triangleCount S n) := by
  rw [(keySetup_spec S n).1]
  constructor
  · simp [List.map_map,Function.comp_def]
  · simpa only [List.map_map,Function.comp_def,triangle_count] using triangle_keys S n

theorem keySetup_nodup (S : OddScale) (n : ℕ) :
    (keySetupQ S n).1.Nodup ∧ ((keySetupQ S n).1.map Prod.snd).Nodup := by
  have hk : ((keySetupQ S n).1.map Prod.snd).Nodup := by
    rw [(keySetup_projections S n).2]; exact List.nodup_range
  exact ⟨List.Nodup.of_map Prod.snd hk,hk⟩

theorem keySetup_range (S : OddScale) (n : ℕ) (k : ℕ) :
    k∈((keySetupQ S n).1.map Prod.snd) ↔ k<triangleCount S n := by
  rw [(keySetup_projections S n).2]; exact List.mem_range


theorem seed_codes (S : OddScale) :
    (BDL26NativePresentationGenerator.setupQ S 0).1.triangles=frameCodes 4 := by
  change (BDL26NativePresentationGenerator.triangleCodesQ _).1=_
  rw [triangle_codes]
  rfl

theorem seed_keys (S : OddScale) :
    ((keySetupQ S 0).1.map Prod.snd)=List.range 8 := by
  rw [(keySetup_projections S 0).2,triangle_count]
  rfl

noncomputable section

abbrev P (S : OddScale) (n : ℕ) := (state S n).presentation

def encode (S : OddScale) (n : ℕ) (t : Triangle (P S n)) : Code :=
  {family:=3,owner:=((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val,copy:=t.2.val}

/-- Constructed face quotient/remainder index, with no chosen finite permutation. -/
def nativeTriangleIndex (S : OddScale) (n : ℕ) :
    Triangle (P S n) ≃ Fin (triangleCount S n) where
  toFun t := ⟨2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val+t.2.val,by
    rw [triangle_count]
    change _<2*(BDL26NativePresentationGenerator.generateQ S n).1.nf
    have hf := ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).isLt
    have hd := t.2.isLt
    omega⟩
  invFun k := ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex.symm ⟨k.val/2,by
      have hk : k.val<2*(BDL26NativePresentationGenerator.generateQ S n).1.nf := by
        calc
          k.val<triangleCount S n := k.isLt
          _=2*(BDL26NativePresentationGenerator.generateQ S n).1.nf := triangle_count S n
      omega⟩,⟨k.val%2,by omega⟩)
  left_inv t := by
    apply Prod.ext
    · apply (BDL26NativePresentationGenerator.generatedRefines S n).fIndex.injective
      apply Fin.ext
      simp only [Equiv.apply_symm_apply]
      have hd := t.2.isLt
      omega
    · apply Fin.ext
      change (2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val+
        t.2.val)%2=t.2.val
      have hd := t.2.isLt
      omega
  right_inv k := by
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    omega

theorem index_value (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (nativeTriangleIndex S n t).val=
      2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val+t.2.val := rfl

theorem index_inverse (S : OddScale) (n : ℕ) :
    (∀t,(nativeTriangleIndex S n).symm (nativeTriangleIndex S n t)=t) ∧
      (∀k,nativeTriangleIndex S n ((nativeTriangleIndex S n).symm k)=k) :=
  ⟨(nativeTriangleIndex S n).symm_apply_apply,(nativeTriangleIndex S n).apply_symm_apply⟩

theorem inverse_coordinates (S : OddScale) (n : ℕ) (k : Fin (triangleCount S n)) :
    ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex ((nativeTriangleIndex S n).symm k).1).val=
        k.val/2 ∧ ((nativeTriangleIndex S n).symm k).2.val=k.val%2 := by
  exact ⟨congrArg Fin.val ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex.apply_symm_apply _),rfl⟩

theorem encode_member (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    encode S n t∈(BDL26NativePresentationGenerator.setupQ S n).1.triangles :=
  (BDL26NativePresentationGenerator.triangle_labels S n _).mpr ⟨t,rfl⟩

theorem encode_injective (S : OddScale) (n : ℕ) : Function.Injective (encode S n) :=
  BDL26NativePresentationGenerator.triangles_injective S n

theorem encode_readback (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    codeAtKey (nativeTriangleIndex S n t).val=encode S n t := by
  unfold codeAtKey encode
  rw [index_value]
  have hd := t.2.isLt
  congr <;> omega

theorem triangle_readback (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (BDL26NativePresentationGenerator.setupQ S n).1.triangles[(nativeTriangleIndex S n t).val]?=
      some (encode S n t) := by
  have hk : (nativeTriangleIndex S n t).val<
      2*(BDL26NativePresentationGenerator.setupQ S n).1.data.frame.nf := by
    calc
      (nativeTriangleIndex S n t).val<triangleCount S n := (nativeTriangleIndex S n t).isLt
      _=2*(BDL26NativePresentationGenerator.setupQ S n).1.data.frame.nf := triangle_count S n
  change (BDL26NativePresentationGenerator.triangleCodesQ _).1[_]?=_
  rw [triangle_codes,frame_codes_dense]
  have hr : (nativeTriangleIndex S n t).val<
      2*(BDL26NativePresentationGenerator.runQ S n).1.frame.nf := hk
  rw [List.getElem?_map,List.getElem?_range hr,Option.map_some]
  exact congrArg some (encode_readback S n t)

theorem atlas_original_row (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (encode S n t,(nativeTriangleIndex S n t).val)∈(keySetupQ S n).1 := by
  rw [(keySetup_spec S n).1]
  apply List.mem_map.mpr
  exact ⟨encode S n t,encode_member S n t,rfl⟩

theorem atlas_original_unique (S : OddScale) (n : ℕ) (k : Fin (triangleCount S n)) :
    ∃!t : Triangle (P S n),(encode S n t,k.val)∈(keySetupQ S n).1 := by
  refine ⟨(nativeTriangleIndex S n).symm k,?_,?_⟩
  · simpa only [Equiv.apply_symm_apply] using
      atlas_original_row S n ((nativeTriangleIndex S n).symm k)
  · intro t ht
    rw [(keySetup_spec S n).1] at ht
    rcases List.mem_map.mp ht with ⟨c,hc,he⟩
    have hv : (nativeTriangleIndex S n t).val=k.val := by
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      dsimp at h1 h2
      rw [h1] at h2
      exact h2
    exact (nativeTriangleIndex S n).injective
      ((Fin.ext hv).trans ((nativeTriangleIndex S n).apply_symm_apply k).symm)

open scoped Classical in
theorem keyOfCode_value (S : OddScale) (n : ℕ) (c : Code) :
    (keyOfCodeQ S n c).1=
      if c∈(BDL26NativePresentationGenerator.setupQ S n).1.triangles then some (2*c.owner+c.copy) else none := by
  exact lookup_rows_value c _

theorem keyOfCode_original (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (keyOfCodeQ S n (encode S n t)).1=some (nativeTriangleIndex S n t).val := by
  rw [keyOfCode_value,if_pos (encode_member S n t)]
  rfl

theorem keyOfCode_success (S : OddScale) (n : ℕ) (c : Code) (k : ℕ) :
    (keyOfCodeQ S n c).1=some k ↔
      ∃!t : Triangle (P S n),encode S n t=c ∧ (nativeTriangleIndex S n t).val=k := by
  constructor
  · intro h
    rw [keyOfCode_value] at h
    split at h
    · rename_i hc
      rcases (BDL26NativePresentationGenerator.triangle_labels S n c).mp hc with ⟨t,ht⟩
      have hk : 2*c.owner+c.copy=k := Option.some.inj h
      refine ⟨t,⟨ht,?_⟩,?_⟩
      · rw [←ht] at hk; exact hk
      · intro u hu; exact encode_injective S n (hu.1.trans ht.symm)
    · contradiction
  · rintro ⟨t,⟨rfl,rfl⟩,_⟩
    exact keyOfCode_original S n t

theorem keyOfCode_failure (S : OddScale) (n : ℕ) (c : Code) :
    (keyOfCodeQ S n c).1=none ↔
      ¬∃t : Triangle (P S n),encode S n t=c := by
  rw [keyOfCode_value]
  constructor
  · intro h ⟨t,ht⟩
    have hc : c∈(BDL26NativePresentationGenerator.setupQ S n).1.triangles := ht ▸ encode_member S n t
    simp [hc] at h
  · intro h
    have hc : c∉(BDL26NativePresentationGenerator.setupQ S n).1.triangles := by
      intro hc; exact h ((BDL26NativePresentationGenerator.triangle_labels S n c).mp hc)
    simp [hc]


theorem invalid_family (S : OddScale) (n : ℕ) (c : Code) (h : c.family≠3) :
    (keyOfCodeQ S n c).1=none := by
  apply (keyOfCode_failure S n c).mpr
  rintro ⟨t,ht⟩
  exact h (congrArg (fun c : Code => c.family) ht).symm

theorem invalid_padding (S : OddScale) (n : ℕ) (c : Code) (h : c.l≠0) :
    (keyOfCodeQ S n c).1=none := by
  apply (keyOfCode_failure S n c).mpr
  rintro ⟨t,ht⟩
  exact h (congrArg (fun c : Code => c.l) ht).symm

theorem invalid_copy (S : OddScale) (n : ℕ) (c : Code) (h : 2≤c.copy) :
    (keyOfCodeQ S n c).1=none := by
  apply (keyOfCode_failure S n c).mpr
  rintro ⟨t,ht⟩
  have he := congrArg (fun c : Code => c.copy) ht
  have hd := t.2.isLt
  change t.2.val=c.copy at he
  omega

theorem invalid_owner (S : OddScale) (n : ℕ) (c : Code)
    (h : (BDL26NativePresentationGenerator.setupQ S n).1.data.frame.nf≤c.owner) :
    (keyOfCodeQ S n c).1=none := by
  apply (keyOfCode_failure S n c).mpr
  rintro ⟨t,ht⟩
  have he := congrArg (fun c : Code => c.owner) ht
  have hf := ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).isLt
  change ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val=c.owner at he
  change (BDL26NativePresentationGenerator.generateQ S n).1.nf≤c.owner at h
  omega

abbrev nativeLE (S : OddScale) (n : ℕ) (a b : Triangle (P S n)) : Prop :=
  (nativeTriangleIndex S n a).val≤(nativeTriangleIndex S n b).val

theorem native_order (S : OddScale) (n : ℕ) :
    (∀a b,nativeLE S n a b ∨ nativeLE S n b a) ∧
      (∀a b c,nativeLE S n a b → nativeLE S n b c → nativeLE S n a c) ∧
      (∀a b,nativeLE S n a b → nativeLE S n b a → a=b) := by
  refine ⟨fun a b => le_total _ _,fun a b c hab hbc => le_trans hab hbc,?_⟩
  intro a b hab hba
  apply (nativeTriangleIndex S n).injective
  exact Fin.ext (le_antisymm hab hba)

theorem compare_original (S : OddScale) (n : ℕ) (a b : Triangle (P S n)) :
    (compareCodesQ S n (encode S n a) (encode S n b)).1=
      some (decide (nativeLE S n a b)) := by
  simp only [compareCodesQ,keyOfCode_original,nativeLE]

theorem compare_failure (S : OddScale) (n : ℕ) (a b : Code) :
    (compareCodesQ S n a b).1=none ↔
      (keyOfCodeQ S n a).1=none ∨ (keyOfCodeQ S n b).1=none := by
  cases hx : (keyOfCodeQ S n a).1 <;> cases hy : (keyOfCodeQ S n b).1 <;>
    simp [compareCodesQ,hx,hy]

end

/-- Extracted from the real retained representation, without a caller budget. -/
theorem triangle_count_bound (S : OddScale) (n : ℕ) :
    triangleCount S n≤(n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15 := by
  have h := BDL26NativePresentationGenerator.retained_space S n
  unfold BDL26NativePresentationGenerator.outputRecords at h
  dsimp only [triangleCount]
  omega

theorem keyOfCode_cost (S : OddScale) (n : ℕ) (c : Code) :
    operations (keyOfCodeQ S n c)≤
        (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+53*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15)+6 ∧
      allocations (keyOfCodeQ S n c)≤
        (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+2*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15)+3 := by
  have hs := keySetup_spec S n
  have hl := lookup_cost c (keySetupQ S n).1
  have hn := triangle_count_bound S n
  have hg := BDL26NativePresentationGenerator.setup_cost S n
  rw [BDL26NativePresentationGenerator.setupExponent_value] at hg
  have ha := BDL26NativePresentationGenerator.allocated_polynomial S n
  have hlen : (keySetupQ S n).1.length=triangleCount S n := by
    rw [hs.1]; simp [triangleCount]
  rw [hlen] at hl
  dsimp only [keyOfCodeQ,operations,allocations] at *
  constructor <;> omega

theorem compare_cost (S : OddScale) (n : ℕ) (a b : Code) :
    operations (compareCodesQ S n a b)≤
        2*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220)+
          106*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15)+16 ∧
      allocations (compareCodesQ S n a b)≤
        2*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220)+
          4*((n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15)+7 := by
  have hx := keyOfCode_cost S n a
  have hy := keyOfCode_cost S n b
  cases hvx : (keyOfCodeQ S n a).1 <;> cases hvy : (keyOfCodeQ S n b).1 <;>
    simp only [compareCodesQ,hvx,hvy,operations,allocations] at * <;> omega

/-- Failure is paid by the same generator and every complete-record rejection. -/
theorem keyOfCode_miss_cost (S : OddScale) (n : ℕ) (c : Code)
    (hc : c∉(BDL26NativePresentationGenerator.setupQ S n).1.triangles) :
    (keyOfCodeQ S n c).1=none ∧
      operations (keyOfCodeQ S n c)=(BDL26NativePresentationGenerator.setupQ S n).2+53*triangleCount S n+6 ∧
      allocations (keyOfCodeQ S n c)=BDL26NativePresentationGenerator.allocatedRecords S n+2*triangleCount S n+2 := by
  have hf : ∀r∈(keySetupQ S n).1,r.1≠c := by
    intro r hr he
    have hm : r.1∈(BDL26NativePresentationGenerator.setupQ S n).1.triangles := by
      rw [←(keySetup_projections S n).1]
      exact List.mem_map.mpr ⟨r,hr,rfl⟩
    exact hc (he ▸ hm)
  have hl := lookup_failure c _ hf
  have hs := keySetup_spec S n
  have hlen : (keySetupQ S n).1.length=triangleCount S n := by
    rw [hs.1]; simp [triangleCount]
  rw [hlen] at hl
  have ho : (keySetupQ S n).2.1=
      (BDL26NativePresentationGenerator.setupQ S n).2+10*triangleCount S n+3 := hs.2.1
  have ha : (keySetupQ S n).2.2=
      BDL26NativePresentationGenerator.allocatedRecords S n+2*triangleCount S n+1 := hs.2.2
  dsimp only [keyOfCodeQ,operations,allocations]
  rw [hl]
  dsimp only
  rw [ho,ha]
  exact ⟨rfl,by omega,by omega⟩

end QEC.Coding.BDL26NativeTriangleKeys
