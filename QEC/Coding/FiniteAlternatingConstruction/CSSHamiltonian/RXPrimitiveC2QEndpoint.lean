import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks.PhysicalMarks
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RXPrimitiveFailureLocalization
import QEC.Coding.FiniteAlternatingConstruction.GlobalLookupLinearity

/-!
# Original endpoint for the primitive C2 Q-edge class

Project-derived internal analysis of BDL26 paper.tex3398–3418,3445–3480,
SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b.
The total depth and both original histories remain fixed. The complete Q-edge
star includes both Q endpoints and every mapped neighboring Z edge.
Explicit later-supported kernels normalize the original global fallback on
the detector loop. The original local-first selector is retained in both
branches; this internal class result is not a public stability theorem.
-/
noncomputable section
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26LevelTwoCode
open BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators

-- Imported definitions retain their original reducibility.  Every chart
-- normalization below is explicit and confined to the proof that needs it.
-- These are exactly the original decoder's structural encodings on the same carriers.
local instance rawOneXEncodable (S : OddScale) : Encodable (RawOne S).X :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).X)
local instance rawOneQEncodable (S : OddScale) : Encodable (RawOne S).Q :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Q)
local instance rawOneZEncodable (S : OddScale) : Encodable (RawOne S).Z :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Z)
local instance executableTransposeFaceEncodable (S : OddScale) :
    Encodable (transposePresentation (BDL26LevelTwoDecoder.executableLevelOne S)).Face :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Face)
local instance executableTransposeEdgeEncodable (S : OddScale) :
    Encodable (BDL26FiniteTannerSquare.Edge
      (transposePresentation (BDL26LevelTwoDecoder.executableLevelOne S))) := by
  letI : Encodable (transposePresentation
      (BDL26LevelTwoDecoder.executableLevelOne S)).X :=
    inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Z)
  letI : Encodable (transposePresentation
      (BDL26LevelTwoDecoder.executableLevelOne S)).Q :=
    inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  letI : Encodable (transposePresentation
      (BDL26LevelTwoDecoder.executableLevelOne S)).Z :=
    inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).X)
  dsimp only [BDL26FiniteTannerSquare.Edge,XQEdge,QZEdge]
  infer_instance

local instance baseZeroX : OfNat baseTannerSquarePresentation.X 0 :=
  inferInstanceAs (OfNat BaseX 0)

-- Expose the original executable encodings on their literal RX carriers.
local instance rawRX0Encodable (S : OddScale) :
    Encodable (RX0 baseTannerSquarePresentation S) :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).X)
local instance rawRX1Encodable (S : OddScale) :
    Encodable (RX1 baseTannerSquarePresentation S) :=
  inferInstanceAs (Encodable (BDL26LevelTwoDecoder.executableLevelOne S).Q)

local instance baseXEncodable : Encodable baseTannerSquarePresentation.X :=
  inferInstanceAs (Encodable (Fin 2))
local instance baseQEncodable : Encodable baseTannerSquarePresentation.Q :=
  inferInstanceAs (Encodable (Fin 5))
local instance baseZEncodable : Encodable baseTannerSquarePresentation.Z :=
  inferInstanceAs (Encodable (Fin 2))
local instance baseFaceEncodable : Encodable baseTannerSquarePresentation.Face :=
  inferInstanceAs (Encodable (Fin 4))

-- Typed projection views keep the original base presentation opaque in dependent grids.
private theorem base_faceX_value (f : BaseFace) :
    baseTannerSquarePresentation.faceX f=baseFaceX f := rfl

private theorem base_faceZ_value (f : BaseFace) :
    baseTannerSquarePresentation.faceZ f=baseFaceZ f := rfl

private theorem base_faceQ_value (f : BaseFace) (c : BDL26FiniteTannerSquare.Two) :
    baseTannerSquarePresentation.faceQ f c=baseFaceQ f c := rfl

private theorem base_xq_matrix_value (x : BaseX) (q : BaseQubit) :
    baseTannerSquarePresentation.xq x q=decide (baseBoundary1Matrix x q≠0) := rfl

private theorem base_qz_matrix_value (q : BaseQubit) (z : BaseZ) :
    baseTannerSquarePresentation.qz q z=decide (baseBoundary2Matrix q z≠0) := rfl

private theorem base_X_eq_value (x y : baseTannerSquarePresentation.X) :
    x=y ↔ (x : BaseX).val=(y : BaseX).val := @Fin.ext_iff 2 x y

private theorem base_Q_eq_value (q r : baseTannerSquarePresentation.Q) :
    q=r ↔ (q : BaseQubit).val=(r : BaseQubit).val := @Fin.ext_iff 5 q r

private theorem base_Z_eq_value (z w : baseTannerSquarePresentation.Z) :
    z=w ↔ (z : BaseZ).val=(w : BaseZ).val := @Fin.ext_iff 2 z w

private theorem base_face_eq_value (f g : baseTannerSquarePresentation.Face) :
    f=g ↔ (f : BaseFace).val=(g : BaseFace).val := @Fin.ext_iff 4 f g

private theorem raw_two_eq_value (a b : Fin 2) :
    a=b ↔ a.val=b.val := base_Z_eq_value a b

private theorem raw_four_eq_value (a b : Fin 4) :
    a=b ↔ a.val=b.val := base_face_eq_value a b

private theorem raw_five_eq_value (a b : Fin 5) :
    a=b ↔ a.val=b.val := base_Q_eq_value a b

private theorem star_edge_xq_view (P : TannerSquarePresentation) (x : P.X)
    (e : XQEdge P) :
    xStarEdgeMember P x (.inl e)=decide (∃ f : P.Face,
      xStarFaceMember P x f=true ∧ (e=faceXQEdge P f 0 ∨ e=faceXQEdge P f 1)) := by
  change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧
    decide (e=faceXQEdge P f 0 ∨ e=faceXQEdge P f 1)=true)=_
  apply Bool.decide_congr
  simp only [decide_eq_true_eq]

private theorem boundary_edge_qz_view (P : TannerSquarePresentation) (x : P.X)
    (e : QZEdge P) :
    xStarBoundaryEdgeMember P x (.inr e)=decide (∃ f : P.Face,
      xStarFaceMember P x f=true ∧ (e=faceQZEdge P f 0 ∨ e=faceQZEdge P f 1)) := by
  change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧
    decide (e=faceQZEdge P f 0 ∨ e=faceQZEdge P f 1)=true)=_
  apply Bool.decide_congr
  simp only [decide_eq_true_eq]

private theorem indicator_iff (p q : Prop) [Decidable p] [Decidable q]
    (h : p ↔ q) : (if p then (1:F) else 0)=(if q then (1:F) else 0) := by
  by_cases hp : p
  · simp only [if_pos hp,if_pos (h.mp hp)]
  · simp only [if_neg hp,if_neg (fun hq => hp (h.mpr hq))]

private theorem basis_value {I : Type} (i j : I) :
    canonicalBasisWord (F:=F) i j=(if j=i then 1 else 0) := by
  classical
  by_cases h : j=i
  · subst j
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord,h,Ne.symm h]

attribute [local simp] basis_value

private theorem two_indicators_zero {I : Type} (q q0 q1 : I) (c : F)
    (h0 : q≠q0) (h1 : q≠q1) :
    ((if q=q0 then (1:F) else 0)+(if q=q1 then 1 else 0))+c=c := by
  simp only [if_neg h0,if_neg h1,zero_add]

private theorem gradient_two_basis (P : TannerSquarePresentation)
    (u v : P.X) (q : P.Q) :
    tannerCoboundary0 P (canonicalBasisWord (F:=F) u+canonicalBasisWord v) q=
      (if P.xq u q=true then (1:F) else 0)+(if P.xq v q=true then 1 else 0) := by
  calc
    _ = tannerCoboundary0 P (canonicalBasisWord u) q+
        tannerCoboundary0 P (canonicalBasisWord v) q :=
      congrArg (fun w : Word F P.Q => w q) (map_add (tannerCoboundary0 P) _ _)
    _ = _ := congrArg₂ (fun a b : F => a+b)
      (tannerCoboundary0_canonicalBasis_apply P u q)
      (tannerCoboundary0_canonicalBasis_apply P v q)

private theorem two_basis_value {I : Type} (u v x : I) :
    ((canonicalBasisWord (F:=F) u+canonicalBasisWord (F:=F) v : Word F I)) x=
      (if x=u then 1 else 0)+(if x=v then 1 else 0) := by
  change canonicalBasisWord (F:=F) u x+canonicalBasisWord v x=_
  rw [basis_value,basis_value]

private theorem gradient_two_basis_second (P : TannerSquarePresentation)
    (u v : P.X) (q : P.Q)
    (hu : ¬P.xq u q=true)
    (h : tannerCoboundary0 P
      (canonicalBasisWord (F:=F) u+canonicalBasisWord v) q≠0) :
    P.xq v q=true := by
  rw [gradient_two_basis,if_neg hu,zero_add] at h
  by_contra hv
  rw [if_neg hv] at h
  exact h rfl

private theorem basis_eq_single {I : Type} [DecidableEq I] (i : I) :
    canonicalBasisWord (F:=F) i=Pi.single i 1 := by
  classical
  funext j
  by_cases h : j=i
  · subst j
    simp [basis_value]
  · simp [basis_value,Pi.single_apply,h,Ne.symm h]

private theorem word_add_eval {I : Type} (a b : Word F I) (i : I) :
    (a+b) i=a i+b i := rfl
private theorem word_smul_eval {I : Type} (c : F) (w : Word F I) (i : I) :
    (c • w) i=c*w i := rfl
private theorem word_zero_eval {I : Type} (i : I) : (0 : Word F I) i=0 := rfl
private theorem word_sum_eval {J I : Type} [Fintype J]
    (w : J → Word F I) (i : I) : (∑ j, w j) i=∑ j, w j i := by
  simp only [Finset.sum_apply]

attribute [local simp] word_add_eval word_smul_eval word_zero_eval

private theorem sigma_same_index_inj {I : Type} {A : I → Type} {i : I}
    (u v : A i) (h : (Sigma.mk i u : Sigma A)=Sigma.mk i v) : u=v := by
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

private theorem code_larger_left {I : Type} [Encodable I] (a b : I) :
    Encodable.encode a≤Encodable.encode
      (if Encodable.encode a≤Encodable.encode b then b else a) := by
  by_cases h : Encodable.encode a≤Encodable.encode b
  · rw [if_pos h]; exact h
  · rw [if_neg h]

private theorem code_larger_right {I : Type} [Encodable I] (a b : I) :
    Encodable.encode b≤Encodable.encode
      (if Encodable.encode a≤Encodable.encode b then b else a) := by
  by_cases h : Encodable.encode a≤Encodable.encode b
  · rw [if_pos h]
  · rw [if_neg h]; exact (Nat.lt_of_not_ge h).le

private theorem code_larger_upper {I : Type} [Encodable I] (a b : I) (B : Nat)
    (ha : Encodable.encode a≤B) (hb : Encodable.encode b≤B) :
    Encodable.encode (if Encodable.encode a≤Encodable.encode b then b else a)≤B := by
  by_cases h : Encodable.encode a≤Encodable.encode b
  · simpa only [if_pos h] using hb
  · simpa only [if_neg h] using ha

private theorem scalar_unit_pair {I : Type} [DecidableEq I]
    (v start finish : I) (hne : start≠finish) (p : Bool)
    (h : (if p=true then (1:F) else 0)=
      canonicalBasisWord (F:=F) v start+canonicalBasisWord (F:=F) v finish) :
    p=true ↔ v=start ∨ v=finish := by
  simp only [basis_value] at h
  constructor
  · intro hp
    by_cases hs : v=start
    · exact Or.inl hs
    · by_cases ht : v=finish
      · exact Or.inr ht
      · have bad : (1:F)=0 := by simpa [hp,hs,Ne.symm hs,ht,Ne.symm ht] using h
        exact False.elim (one_ne_zero bad)
  · rintro (rfl | rfl)
    · by_contra hp
      have bad : (0:F)=1 := by simpa [hp,hne,Ne.symm hne] using h
      exact zero_ne_one bad
    · by_contra hp
      have bad : (0:F)=1 := by simpa [hp,hne,Ne.symm hne] using h
      exact zero_ne_one bad

private theorem words_cancel_middle {I : Type} (a b : Word F I) : a+(b+a)=b := by
  rw [add_left_comm]
  have hz : a+a=0 := by funext i; exact ZModModule.add_self (a i)
  rw [hz,add_zero]

private theorem three_words_cancel {I : Type} (a b c : Word F I) :
    a+b+((c+a)+(c+b))=0 := by
  have hz (w : Word F I) : w+w=0 := by
    funext i
    exact ZModModule.add_self (w i)
  calc
    _ = (a+a)+((b+b)+(c+c)) := by abel
    _ = 0 := by rw [hz a,hz b,hz c,zero_add,zero_add]

private theorem transposed_face_member (P : TannerSquarePresentation)
    (z : P.Z) (f : P.Face) :
    xStarFaceMember (transposePresentation P) z f=true ↔ P.faceZ f=z := by
  change decide (P.data.faceZ f=z)=true ↔ P.data.faceZ f=z
  by_cases h : P.data.faceZ f=z <;> simp [h]

private theorem sum_scaled_words_apply {J I : Type} [Fintype J]
    (a : J → F) (w : J → Word F I) (q : I) :
    (∑ j, a j • w j) q=∑ j, a j*w j q := by
  erw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

private theorem collect_indicator_sums {J K I : Type} [Fintype J] [Fintype K]
    (a : J → F) (rel : J → K → Bool) (w : K → Word F I) :
    (∑ j, a j • (∑ k, if rel j k=true then w k else 0))=
      ∑ k, (∑ j, a j*(if rel j k=true then 1 else 0)) • w k := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : rel j k=true <;> simp [h]

private theorem generic_basis_plus_value {I : Type} (q target : I)
    (w : Word F I) (hw : w target=0) :
    ((canonicalBasisWord (F:=F) q+w : Word F I)) target=(if target=q then 1 else 0) := by
  calc
    _ = canonicalBasisWord (F:=F) q target+w target := rfl
    _ = _ := by rw [basis_value,hw,add_zero]

private theorem two_units_apply {I : Type} (a b q : I) (w : Word F I) :
    ((canonicalBasisWord (F:=F) a+canonicalBasisWord (F:=F) b+w : Word F I)) q=
      ((if q=a then 1 else 0)+(if q=b then 1 else 0))+w q := by
  change canonicalBasisWord (F:=F) a q+canonicalBasisWord (F:=F) b q+w q=_
  rw [basis_value,basis_value]

private theorem extend_edge_at_same (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (w : Word F (ZDoubleCylinderEdge P z S))
    (e : ZDoubleCylinderEdge P z S) : extendZEdgeWord P S z w (.inl ⟨z,e⟩)=w e := by
  simp [extendZEdgeWord]

private theorem extend_edge_at_other (P : TannerSquarePresentation) (S : OddScale)
    (z z' : P.Z) (w : Word F (ZDoubleCylinderEdge P z S))
    (e : ZDoubleCylinderEdge P z' S) (h : z'≠z) :
    extendZEdgeWord P S z w (.inl ⟨z',e⟩)=0 := by
  exact dif_neg h

private theorem extend_edge_at_port (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (w : Word F (ZDoubleCylinderEdge P z S))
    (q : P.Q) (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    extendZEdgeWord P S z w (.inr ⟨q,v⟩)=0 := rfl

private theorem conditional_word_sum_apply {J I : Type} [Fintype J]
    (condition : J → Prop) [DecidablePred condition]
    (words : ∀ j, condition j → Word F I) (q : I) :
    (∑ j, if h : condition j then words j h else 0) q=
      ∑ j, if h : condition j then words j h q else 0 := by
  erw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : condition j
  · rw [dif_pos h,dif_pos h]
  · simp only [dif_neg h,word_zero_eval]

private theorem map_conditional_word_sum {J I K : Type} [Fintype J]
    (D : Word F I →ₗ[F] Word F K)
    (condition : J → Prop) [DecidablePred condition]
    (words : ∀ j, condition j → Word F I) :
    D (∑ j, if h : condition j then words j h else 0)=
      ∑ j, if h : condition j then D (words j h) else 0 := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [map_zero]

private theorem mapped_shifted_sum_cancel {J I K : Type} [Fintype J]
    (D : Word F I →ₗ[F] Word F K) (a : Word F I)
    (condition : J → Prop) [DecidablePred condition]
    (words : ∀ j, condition j → Word F I)
    (ends mids locals : ∀ j, condition j → Word F K)
    (ha : D a=∑ j, if h : condition j then ends j h else 0)
    (he : ∀ j h, D (words j h)=(mids j h+ends j h)+locals j h) :
    D (a+∑ j, if h : condition j then words j h else 0)=
      ∑ j, if h : condition j then mids j h+locals j h else 0 := by
  rw [map_add,ha,map_conditional_word_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : condition j
  · rw [dif_pos h,dif_pos h,dif_pos h,he j h]
    calc
      _ = (ends j h+(mids j h+ends j h))+locals j h := by abel
      _ = _ := by rw [words_cancel_middle]
  · simp only [dif_neg h,zero_add]

private theorem disjoint_conditional_basis_apply {J I : Type} [Fintype J]
    (condition : J → Prop) [DecidablePred condition]
    (labels : ∀ j, condition j → I) (q : I)
    (hne : ∀ j h, q≠labels j h) :
    (∑ j, if h : condition j then canonicalBasisWord (F:=F) (labels j h) else 0) q=0 := by
  rw [conditional_word_sum_apply condition
    (fun j h => canonicalBasisWord (labels j h)) q]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : condition j
  · rw [dif_pos h,basis_value,if_neg (hne j h)]
  · rw [dif_neg h]

private theorem two_eq_zero_or_one (c : BDL26FiniteTannerSquare.Two) :
    c=0 ∨ c=1 := by fin_cases c <;> simp

private theorem support_mem_of_ne {I : Type} [Fintype I] (w : Word F I)
    (i : I) (hi : w i≠0) : i∈hammingSupport w := by
  simpa only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hi

private def finCastGrid {m : Nat} (i : Fin m) : Fin (m+1) :=
  ⟨i.val,Nat.lt_succ_of_lt i.isLt⟩

private def finSuccGrid {m : Nat} (i : Fin m) : Fin (m+1) :=
  ⟨i.val+1,by have := i.isLt; omega⟩

private theorem own_horizontal_start (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half) (row : Fin (S.half+1)) :
    subdivisionEdgeStart P x S (subdivisionHorizontalEdge P x S f i row)=
      subdivisionGridVertex P x S f (finCastGrid i) row := by
  exact (subdivisionHorizontalEdge_start P x S f i row).trans
    (congrArg (fun a : Fin (S.half+1) => subdivisionGridVertex P x S f a row) (by apply Fin.ext; rfl))

private theorem own_horizontal_end (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half) (row : Fin (S.half+1)) :
    subdivisionEdgeEnd P x S (subdivisionHorizontalEdge P x S f i row)=
      subdivisionGridVertex P x S f (finSuccGrid i) row := by
  exact (subdivisionHorizontalEdge_end P x S f i row).trans
    (congrArg (fun a : Fin (S.half+1) => subdivisionGridVertex P x S f a row) (by apply Fin.ext; rfl))

private theorem own_vertical_start (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (column : Fin (S.half+1)) (i : Fin S.half) :
    subdivisionEdgeStart P x S (subdivisionVerticalEdge P x S f column i)=
      subdivisionGridVertex P x S f column (finCastGrid i) := by
  exact (subdivisionVerticalEdge_start P x S f column i).trans
    (congrArg (fun a : Fin (S.half+1) => subdivisionGridVertex P x S f column a) (by apply Fin.ext; rfl))

private theorem own_vertical_end (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (column : Fin (S.half+1)) (i : Fin S.half) :
    subdivisionEdgeEnd P x S (subdivisionVerticalEdge P x S f column i)=
      subdivisionGridVertex P x S f column (finSuccGrid i) := by
  exact (subdivisionVerticalEdge_end P x S f column i).trans
    (congrArg (fun a : Fin (S.half+1) => subdivisionGridVertex P x S f column a) (by apply Fin.ext; rfl))

private def finInteriorGrid (S : OddScale) (i : Fin (S.half-1)) : Fin (S.half+1) :=
  ⟨i.val+1,by have := S.half_pos; have := i.isLt; omega⟩

private def finInteriorIndex (S : OddScale) (i : Fin (S.half+1))
    (h0 : i.val≠0) (hh : i.val≠S.half) : Fin (S.half-1) :=
  ⟨i.val-1,by have := i.isLt; omega⟩

private theorem horizontal_inner_start_grid (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (i : Fin S.half) (k : Fin (S.half-1)) :
    subdivisionEdgeStart P x S (.inr (.inl (f,i,k)))=
      subdivisionGridVertex P x S f (finCastGrid i) (finInteriorGrid S k) := rfl

private theorem horizontal_inner_end_grid (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (i : Fin S.half) (k : Fin (S.half-1)) :
    subdivisionEdgeEnd P x S (.inr (.inl (f,i,k)))=
      subdivisionGridVertex P x S f (finSuccGrid i) (finInteriorGrid S k) := rfl

private theorem horizontal_inner_eq (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (row : Fin (S.half+1)) (h0 : row.val≠0) (hh : row.val≠S.half) :
    subdivisionHorizontalEdge P x S f i row=
      .inr (.inl (f,i,finInteriorIndex S row h0 hh)) := by
  unfold subdivisionHorizontalEdge
  simp only [dif_neg h0,dif_neg hh]
  apply congrArg (fun k : Fin (S.half-1) =>
    (Sum.inr (Sum.inl (f,i,k)) : SubdivisionEdge P x S))
  apply Fin.ext
  rfl

private theorem horizontal_last_eq (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (row : Fin (S.half+1)) (h : row.val=S.half) :
    subdivisionHorizontalEdge P x S f i row=.inl (xStarFaceQZEdge P x f 1,i) := by
  have h0 : row.val≠0 := by have := S.half_pos; omega
  unfold subdivisionHorizontalEdge
  rw [dif_neg h0,dif_pos h]

private theorem vertical_inner_eq (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (row : Fin (S.half+1))
    (i : Fin S.half) (h0 : row.val≠0) (hh : row.val≠S.half) :
    subdivisionVerticalEdge P x S f row i=
      .inr (.inr (f,finInteriorIndex S row h0 hh,i)) := by
  unfold subdivisionVerticalEdge
  rw [dif_neg h0,dif_neg hh]
  apply congrArg (fun k : Fin (S.half-1) =>
    (Sum.inr (Sum.inr (f,k,i)) : SubdivisionEdge P x S))
  apply Fin.ext
  rfl

abbrev Seed (S : OddScale) := Σ r : (RawOne S).Q,
  Σ e : QDoubleCylinderEdge (transposePresentation (RawOne S)) r S,
    DoubleCylinderEdge (state S 2).presentation (c2QEdgeOwner S r e) S

private def extractC3 (S : OddScale) (q : Physical S 3) : Option (Seed S) :=
  match (BDL26RXDecoderAdapter.rxPhysicalQEquiv S 3 ⟨2,by omega⟩ (by decide)).symm q with
  | .inl ⟨.inl (.inr ⟨r,e⟩),d⟩ => some ⟨r,e,d⟩
  | _ => none

private theorem extractC3_seed (S : OddScale) (a : Seed S) :
    extractC3 S (c2QEdgePhysical S a.1 a.2.1 a.2.2)=some a := by
  unfold extractC3 c2QEdgePhysical
  rw [Equiv.symm_apply_apply] <;> rfl

private theorem extractC3_face (S : OddScale) (a : BDL26RXFaceEdgeTower.Seed S) :
    extractC3 S (BDL26RXFaceEdgeTower.seedPhysical S a)=none := by
  unfold extractC3 BDL26RXFaceEdgeTower.seedPhysical
  rw [Equiv.symm_apply_apply] <;> rfl

private theorem extractC3_oldX (S : OddScale) (x : (state S 1).presentation.X)
    (c : BDL26FiniteTannerSquare.Two)
    (d : DoubleCylinderEdge (state S 2).presentation (oldXOwner S 1 (by decide) x c) S) :
    extractC3 S (oldXPhysical S 1 (by decide) x c d)=none := by
  unfold extractC3 oldXPhysical
  rw [Equiv.symm_apply_apply] <;> rfl

private theorem extractC3_rx (S : OddScale) (q : Physical S 2)
    (v : QDoubleCylinderVertex (state S 2).presentation q S) :
    extractC3 S (BDL26FirstZeroQVertexTower.rxVertex S 2 (by decide) q v)=none := by
  rw [rx_vertex_chart]
  unfold extractC3
  rw [Equiv.symm_apply_apply] <;> rfl

private theorem trace_seed_leaf (S : OddScale) (a : Seed S)
    {b : Nat} {q : Physical S (b+2)} {leaf : Leaf S}
    (t : Trace S b q leaf) (hb : b=1)
    (hq : HEq q (c2QEdgePhysical S a.1 a.2.1 a.2.2)) :
    leaf=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2) := by
  cases t with
  | c2 q => omega
  | face a' =>
    have he := congrArg (extractC3 S) (eq_of_heq hq)
    rw [extractC3_face,extractC3_seed] at he
    cases he
  | rzEdge b ho z e =>
    have hb0 : b=0 := by omega
    subst b
    exact False.elim (ho (by decide))
  | higherFace j a' => omega
  | primitive p =>
    cases p with
    | c2QEdge r e d =>
      have he := congrArg (extractC3 S) (eq_of_heq hq)
      have he' : some (⟨r,e,d⟩ : Seed S)=some a := by
        change extractC3 S (c2QEdgePhysical S r e d)=some a at he
        exact (extractC3_seed S ⟨r,e,d⟩).symm.trans he
      exact congrArg (fun a : Seed S =>
        Leaf.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2)) (Option.some.inj he')
    | oldX _ ho x c d =>
      have hm : b=1 := hb
      subst b
      have he := congrArg (extractC3 S) (eq_of_heq hq)
      change extractC3 S (oldXPhysical S 1 ho x c d)=some a at he
      rw [extractC3_oldX] at he
      cases he
  | @rx b q leaf t he v =>
    have hb0 : b=0 := by omega
    subst b
    have he' := congrArg (extractC3 S) (eq_of_heq hq)
    rw [extractC3_rx,extractC3_seed] at he'
    cases he'
  | @rz b q leaf t ho v =>
    have hb0 : b=0 := by omega
    subst b
    exact False.elim (ho (by decide))
  | qEdgePair j a' t => omega

/-- The actual choice-based parser recognizes every literal C3 Q-edge seed. -/
theorem parse_seed (S : OddScale) (a : Seed S) :
    parse S 1 (c2QEdgePhysical S a.1 a.2.1 a.2.2)=
      .primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2) :=
  trace_seed_leaf S a (parsedTrace S 1 _) rfl HEq.rfl

private def extractC4 (S : OddScale) (q : Physical S 4) : Option (Physical S 3) :=
  match (BDL26RZPhysicalStarTransport.upperQChart S 4 ⟨3,by omega⟩ (by decide)).symm q with
  | .inr ⟨q,_⟩ => some q
  | .inl _ => none

private theorem extractC4_rz (S : OddScale) (q : Physical S 3)
    (v : QDoubleCylinderVertex (transposePresentation (state S 3).presentation) q S) :
    extractC4 S (BDL26FirstZeroQVertexTower.rzVertex S 3 (by decide) q v)=some q := by
  rw [rz_vertex_chart]
  unfold extractC4
  rw [Equiv.symm_apply_apply] <;> rfl

private theorem extractC4_edge (S : OddScale) (z : (state S 3).presentation.Z)
    (e : ZDoubleCylinderEdge (state S 3).presentation z S) :
    extractC4 S (BDL26RZLocalEdgeTower.rzLocalEdge S 3 (by decide) z e)=none := by
  unfold extractC4 BDL26RZLocalEdgeTower.rzLocalEdge
  rw [Equiv.symm_apply_apply] <;> rfl

private theorem trace_rz_seed_leaf (S : OddScale) (a : Seed S)
    (v : QDoubleCylinderVertex (transposePresentation (state S 3).presentation)
      (c2QEdgePhysical S a.1 a.2.1 a.2.2) S)
    {b : Nat} {q : Physical S (b+2)} {leaf : Leaf S}
    (t : Trace S b q leaf) (hb : b=2)
    (hq : HEq q (BDL26FirstZeroQVertexTower.rzVertex S 3 (by decide)
      (c2QEdgePhysical S a.1 a.2.1 a.2.2) v)) :
    leaf=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2) := by
  cases t with
  | c2 q => omega
  | face a' => omega
  | rzEdge b ho z e =>
    have hb1 : b=1 := by omega
    subst b
    have he := congrArg (extractC4 S) (eq_of_heq hq)
    rw [extractC4_edge,extractC4_rz] at he
    cases he
  | higherFace j a' => omega
  | primitive p =>
    have ho := primitive_odd p
    rw [hb] at ho
    exact False.elim (ho (by decide))
  | @rx b q leaf t he v' =>
    have hb1 : b=1 := by omega
    subst b
    have ho : ¬(3 : Nat)%2=0 := by decide
    exact False.elim (ho he)
  | @rz b q leaf t ho v' =>
    have hb1 : b=1 := by omega
    subst b
    have he := congrArg (extractC4 S) (eq_of_heq hq)
    rw [extractC4_rz,extractC4_rz] at he
    exact trace_seed_leaf S a t rfl (heq_of_eq (Option.some.inj he))
  | qEdgePair j a' t => omega

/-- Actual higher RZ Q vertices preserve the literal primitive parser class. -/
theorem parse_rz_seed (S : OddScale) (a : Seed S)
    (v : QDoubleCylinderVertex (transposePresentation (state S 3).presentation)
      (c2QEdgePhysical S a.1 a.2.1 a.2.2) S) :
    parse S 2 (BDL26FirstZeroQVertexTower.rzVertex S 3 (by decide)
      (c2QEdgePhysical S a.1 a.2.1 a.2.2) v)=
        .primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2) :=
  trace_rz_seed_leaf S a v (parsedTrace S 2 _) rfl HEq.rfl

private theorem basis_support_self {I : Type} [Fintype I] [DecidableEq I] (q : I) :
    q∈hammingSupport (canonicalBasisWord (F:=F) q) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  simpa [basis_value] using (one_ne_zero : (1:F)≠0)

private theorem seed_ambient (S : OddScale) (N : Nat) (hN : 1≤N) (a : Seed S) :
    c2QEdgePhysical S a.1 a.2.1 a.2.2=
      BDL26RXDecoderAdapter.rxPhysicalQEquiv S (N+2) (Edge N ⟨0,by omega⟩)
        (by change 2%2=0; decide) (.inl ⟨c2QEdgeOwner S a.1 a.2.1,a.2.2⟩) := by
  unfold c2QEdgePhysical BDL26RXDecoderAdapter.rxPhysicalQEquiv
  simp only [BDL26LocalizedHistoryErrorDescent.Edge,LevelTwoHistory.physicalStep,Fin.val_mk]

private theorem original_support_mem {I : Type} [Fintype I]
    (w : Word F I) (q : I) : q∈hammingSupport w ↔ w q≠0 := by
  simp only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and]

private theorem seed_parent (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (hN : 1≤N) (a : Seed S)
    (w : LocalizedWord S N sigma tau ⟨1,by omega⟩)
    (hw : w.word=canonicalBasisWord (F:=F) (c2QEdgePhysical S a.1 a.2.1 a.2.2)) :
    BDL26RXPhysicalStarTransport.parentX S (N+2) (Edge N ⟨0,by omega⟩)
      (by change 2%2=0; decide) w.center=c2QEdgeOwner S a.1 a.2.1 := by
  let originalWord := w.word
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at originalWord
  have hw3 : originalWord=canonicalBasisWord (F:=F)
      (c2QEdgePhysical S a.1 a.2.1 a.2.2) := by
    simpa only [originalWord,BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
      BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] using hw
  have hseed : c2QEdgePhysical S a.1 a.2.1 a.2.2∈
      (hammingSupport originalWord : Finset (Physical S 3)) := by
    rw [hw3]
    exact basis_support_self _
  have hs_nonzero : ∀ q, w.word q≠0 →
      q∈BDL26LocalizedHistoryErrorDescent.star S N ⟨1,by all_goals omega⟩ w.center := by
    intro q hq
    apply w.supported
    unfold hammingSupport
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel,Fin.val_mk,
    Nat.reduceAdd] at hs_nonzero
  have hnz := (original_support_mem originalWord
    (c2QEdgePhysical S a.1 a.2.1 a.2.2)).mp hseed
  have hi := hs_nonzero (c2QEdgePhysical S a.1 a.2.1 a.2.2) (by
    simpa only [originalWord] using hnz)
  dsimp only [BDL26LocalizedHistoryErrorDescent.star,
    LevelTwoHistory.physicalLevel,Fin.val_mk,Nat.reduceAdd] at hi
  erw [seed_ambient S N hN a] at hi
  exact BDL26HigherRXFaceTower.rx_local_edge_parent S (N+2) (Edge N ⟨0,by omega⟩)
    (by change 2%2=0; decide) w.center (c2QEdgeOwner S a.1 a.2.1) a.2.2 hi

private theorem seed_carrier_eq (S : OddScale) (N : Nat) (hN : 1≤N) :
    LevelTwoHistory.Suffix (BDL26IndexedDecoder.FamilyQ S (N+2))
      (⟨1,by omega⟩ : LevelIndex N)=Physical S 3 := by
  have hl : (LevelTwoHistory.physicalLevel
      (⟨1,by omega⟩ : LevelIndex N)).val=3 := by
    simp only [LevelTwoHistory.physicalLevel_val,Fin.val_mk]
  simpa only [LevelTwoHistory.Suffix,BDL26IndexedDecoder.FamilyQ,
    BDL26CSSHamiltonian.Physical,BDL26CSSHamiltonian.presentation] using
      congrArg (fun k => (state S k).presentation.Q) hl

private theorem cast_word_zero_iff {I J : Type} (h : I=J) (w : Word F I) :
    cast (congrArg (Word F) h) w=0 ↔ w=0 := by
  cases h
  rfl

private theorem seed_step_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (hN : 1≤N) (a : Seed S)
    (w : LocalizedWord S N sigma tau ⟨1,by omega⟩)
    (hw : hammingSupport w.word ⊆ {c2QEdgePhysical S a.1 a.2.1 a.2.2}) :
    hammingSupport (step S N sigma tau ⟨0,by omega⟩ w).lower.word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (c2QEdgeOwner S a.1 a.2.1) := by
  let i : StepIndex N := ⟨0,by omega⟩
  have he : (Edge N i).val%2=0 := by change 2%2=0; decide
  let originalWord := w.word
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at originalWord
  have hw3 : hammingSupport originalWord ⊆ {c2QEdgePhysical S a.1 a.2.1 a.2.2} := by
    simpa only [originalWord,BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
      BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] using hw
  let physicalWord : Word F (Physical S 3) :=
    cast (congrArg (Word F) (seed_carrier_eq S N hN)) w.word
  have hraw : HEq physicalWord w.word := cast_heq _ _
  dsimp only [BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
    BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] at hraw
  have hword : physicalWord=originalWord := eq_of_heq hraw
  have hsupport : hammingSupport physicalWord=hammingSupport originalWord := by
    ext q
    simp only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hword]
  have hpw : hammingSupport physicalWord ⊆ {c2QEdgePhysical S a.1 a.2.1 a.2.2} := by
    rw [hsupport]
    exact hw3
  obtain ⟨c,hc⟩ := @BDL26RXQEdgePairTransport.scalar_singleton (Physical S 3) _ _
    physicalWord (c2QEdgePhysical S a.1 a.2.1 a.2.2) hpw
  rcases BDL26RXQEdgePairTransport.bit_cases c with rfl | rfl
  · have hz3 : physicalWord=0 :=
      hc.trans (BDL26RXQEdgePairTransport.scalar_zero _)
    have hz : w.word=0 := (cast_word_zero_iff (seed_carrier_eq S N hN) w.word).mp hz3
    rw [BDL26RXQEdgePairTransport.step_zero S N sigma tau i w hz]
    rw [hammingSupport_zero]
    exact Finset.empty_subset _
  · have hb3 : physicalWord=canonicalBasisWord (F:=F)
        (c2QEdgePhysical S a.1 a.2.1 a.2.2) :=
      hc.trans (BDL26RXQEdgePairTransport.scalar_one _)
    have hb0 : originalWord=canonicalBasisWord (F:=F)
        (c2QEdgePhysical S a.1 a.2.1 a.2.2) := hword.symm.trans hb3
    have hp := seed_parent S N sigma tau hN a w (by
      simpa only [originalWord,BDL26CochainFamily.Cochain1,LevelTwoHistory.Suffix,
        BDL26IndexedDecoder.FamilyQ,LevelTwoHistory.physicalLevel] using hb0)
    have hs := (step S N sigma tau i w).lower.supported
    rw [step_rx S N sigma tau i he w] at hs
    change hammingSupport (BDL26RXPhysicalStarTransport.L S (N+2) (Edge N i) he
      w.center _ _) ⊆ BDL26RXPhysicalStarTransport.physicalXStar
        (state S 2).presentation
        (BDL26RXPhysicalStarTransport.parentX S (N+2) (Edge N i) he w.center) at hs
    rw [hp] at hs
    rw [step_rx S N sigma tau i he w]
    exact hs

/-- The literal parser class derives the terminal full star in the original path. -/
theorem terminal_star (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2)) :
    hammingSupport (descent S N u q).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (c2QEdgeOwner S a.1 a.2.1) := by
  have hm := parser_semantics S N u q
  rw [hp] at hm
  obtain ⟨hN,hw⟩ := hm
  have hs := seed_step_supported S N (input S N u)
    (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q)) hN a
    (BDL26BoundaryTailInvariance.snapshot S N u q ⟨1,by omega⟩) hw
  change hammingSupport (BDL26BoundaryTailInvariance.snapshot S N u q 0).word ⊆ _
  unfold BDL26BoundaryTailInvariance.snapshot at hs ⊢
  have he := path_step S N (input S N u)
    (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q))
    (BDL26BoundaryTailInvariance.physicalTop S N u q) (⟨0,by omega⟩ : StepIndex N)
  exact Eq.mpr (congrArg (fun w : LocalizedWord S N (input S N u)
      (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q)) 0 =>
      hammingSupport w.word ⊆ BDL26RXPhysicalStarTransport.physicalXStar
        (state S 2).presentation (c2QEdgeOwner S a.1 a.2.1)) he) hs

private theorem star_operations_heq {U V : TannerSquarePresentation} (h : U=V) :
    HEq (BDL26RXPhysicalStarTransport.physicalXStar U)
      (BDL26RXPhysicalStarTransport.physicalXStar V) ∧
    HEq (fun w : Word F U.Q => hammingSupport w)
      (fun w : Word F V.Q => hammingSupport w) := by
  cases h
  exact ⟨HEq.rfl,HEq.rfl⟩

/-- The complete terminal star on the literal materialized C2 carriers. -/
theorem terminal_raw_star (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2)) :
    BDL26LevelTwoLocalBranchEndpoint.supported S (.inl (.inr ⟨a.1,a.2.1⟩))
      (descent S N u q).word := by
  have hm := star_operations_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S))
  have hx : (BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation :
      (RawTwo S).X → Finset (RawTwo S).Q)=
      BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) := eq_of_heq hm.1
  have hs : ((fun w : Word F (state S 2).presentation.Q => hammingSupport w) :
      BDL26LevelTwoLocalBranchEndpoint.Error S → Finset (RawTwo S).Q)=
      (fun w : BDL26LevelTwoLocalBranchEndpoint.Error S => hammingSupport w) :=
    eq_of_heq hm.2
  have hh := terminal_star S N u q a hp
  change hammingSupport (descent S N u q).word ⊆
    BDL26RXPhysicalStarTransport.physicalXStar (RawTwo S) (.inl (.inr ⟨a.1,a.2.1⟩))
  have hhs := congrArg (fun support : BDL26LevelTwoLocalBranchEndpoint.Error S →
      Finset (RawTwo S).Q => support (descent S N u q).word) hs
  have hxs := congrArg (fun star : (RawTwo S).X → Finset (RawTwo S).Q =>
      star (.inl (.inr ⟨a.1,a.2.1⟩))) hx
  intro r hr
  exact Eq.mp (congrArg (fun t : Finset (RawTwo S).Q => r∈t) hxs)
    (hh (Eq.mpr (congrArg (fun t : Finset (RawTwo S).Q => r∈t) hhs) hr))

/-- All other preceding-Q coefficients vanish; no neighboring Z bit is dropped. -/
theorem terminal_parity_other (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (r : (RawOne S).Q) (hr : r≠a.1) :
    BDL26LevelTwoLocalBranchEndpoint.parity S (descent S N u q).word r=0 :=
  BDL26LevelTwoLocalBranchEndpoint.edge_parity_other S a.1 a.2.1 _
    (terminal_raw_star S N u q a hp) r hr

/-- Both actual tagged Q endpoints occur in the exact remaining coefficient. -/
theorem terminal_parity_self (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2)) :
    BDL26LevelTwoLocalBranchEndpoint.parity S (descent S N u q).word a.1=
      (descent S N u q).word
        (.inr ⟨a.1,qDoubleCylinderEdgeStart (transposePresentation (RawOne S)) a.1 S a.2.1⟩)+
      (descent S N u q).word
        (.inr ⟨a.1,qDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) a.1 S a.2.1⟩) :=
  BDL26LevelTwoLocalBranchEndpoint.edge_parity_self S a.1 a.2.1 _
    (terminal_raw_star S N u q a hp)

/-- Every nonzero Z-sector bit is the actual image of this same Q edge. -/
theorem terminal_Z_bit (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (z : (RawOne S).Z) (e : ZDoubleCylinderEdge (RawOne S) z S)
    (he : (descent S N u q).word (.inl ⟨z,e⟩)≠0) :
    ∃ hz : (RawOne S).qz a.1 z=true,
      qToZDoubleCylinderEdge (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible a.1 z hz S a.2.1=e := by
  have hi := (BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mp
    (terminal_raw_star S N u q a hp (support_mem_of_ne _ _ he))
  change decide (∃ hz : (RawOne S).qz a.1 z=true,
    qToZDoubleCylinderEdge (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible a.1 z hz S a.2.1=e)=true at hi
  exact of_decide_eq_true hi

/-- A one-neighbor Q edge has a derived local preimage, including every Z bit. -/
theorem degree_one_local_preimage (S : OddScale) (r : (RawOne S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (RawOne S)) r S)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hunique : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (h : BDL26LevelTwoLocalBranchEndpoint.Error S)
    (hh : BDL26LevelTwoLocalBranchEndpoint.supported S (.inl (.inr ⟨r,e⟩)) h) :
    ∃ g : BDL26LevelTwoLocalBranchEndpoint.Error S,
      BDL26LevelTwoDistance.levelTwoLocalError S g ∧
      BDL26LevelTwoLocalBranchEndpoint.delta S g=
        BDL26LevelTwoLocalBranchEndpoint.delta S h := by
  let x : (RawTwo S).X := .inl (.inr ⟨r,e⟩)
  let image := qToZDoubleCylinderEdge (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S e
  let c : F := h (.inl ⟨z,image⟩)
  let p : Word F (RawTwo S).X := c • canonicalBasisWord (F:=F) x
  let b := tannerCoboundary0 (RawTwo S) p
  have hb (q : (RawTwo S).Q) : b q=
      c*(if (RawTwo S).xq x q=true then 1 else 0) := by
    dsimp only [b,p]
    erw [map_smul,Pi.smul_apply,smul_eq_mul,tannerCoboundary0_canonicalBasis_apply]
  have houtside (q : (RawTwo S).Q) (hi : ¬(RawTwo S).xq x q=true) : h q=0 := by
    by_contra hn
    exact hi ((BDL26RXPhysicalStarTransport.mem_physicalXStar _ _ _).mp
      (hh (support_mem_of_ne _ _ hn)))
  have hZ (z' : (RawOne S).Z) (d : ZDoubleCylinderEdge (RawOne S) z' S) :
      (h+b) (.inl ⟨z',d⟩)=0 := by
    change h (.inl ⟨z',d⟩)+b (.inl ⟨z',d⟩)=0
    erw [hb]
    by_cases hi : (RawTwo S).xq x (.inl ⟨z',d⟩)=true
    · have hi' := hi
      change decide (∃ hqz : (RawOne S).qz r z'=true,
        qToZDoubleCylinderEdge (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r z' hqz S e=d)=true at hi'
      obtain ⟨hqz,hd⟩ := of_decide_eq_true hi'
      have hzz := hunique z' hqz
      subst z'
      have hd' : image=d := by simpa only [image] using hd
      subst d
      erw [if_pos hi,mul_one]
      exact ZModModule.add_self _
    · erw [houtside _ hi,if_neg hi,mul_zero,zero_add]
  have hlocal : BDL26LevelTwoDistance.levelTwoLocalError S (h+b) := by
    apply (BDL26LevelTwoDistance.levelTwoLocalError_iff_owner S (h+b)).mpr
    refine ⟨Vertex.q r,?_⟩
    intro q hq
    have hi : (RawTwo S).xq x q=true := by
      by_contra hn
      have hzero : b q=0 := by erw [hb,if_neg hn,mul_zero]
      exact hq (by change h q+b q=0; erw [houtside q hn,hzero,zero_add])
    rcases q with ⟨z',d⟩ | ⟨r',v⟩
    · exact False.elim (hq (hZ z' d))
    · change decide (∃ hr : r'=r,
        hr ▸ v=qDoubleCylinderEdgeStart (transposePresentation (RawOne S)) r S e ∨
        hr ▸ v=qDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) r S e)=true at hi
      obtain ⟨hr,_⟩ := of_decide_eq_true hi
      change Vertex.q r'=Vertex.q r
      exact congrArg Vertex.q hr
  refine ⟨h+b,hlocal,?_⟩
  have hzero : BDL26LevelTwoLocalBranchEndpoint.delta S b=0 := by
    have hc := LinearMap.congr_fun
      (BDL26LevelTwoDistance.tannerCoboundary_squared (RawTwo S)) p
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply,b] using hc
  erw [map_add,hzero,add_zero]

/-- Success is proved for the one-neighbor geometry, rather than assumed. -/
theorem degree_one_search (S : OddScale) (r : (RawOne S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (RawOne S)) r S)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hunique : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (h : BDL26LevelTwoLocalBranchEndpoint.Error S)
    (hh : BDL26LevelTwoLocalBranchEndpoint.supported S (.inl (.inr ⟨r,e⟩)) h) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S
      (BDL26LevelTwoLocalBranchEndpoint.delta S h) :=
  (BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff S _).mpr
    (degree_one_local_preimage S r e z hz hunique h hh)

/-- This geometry proves success on the original SECOND, at the original fixed depth. -/
theorem degree_one_original_search (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (hs : firstReadout S N u=0)
    (z : (RawOne S).Z) (hz : (RawOne S).qz a.1 z=true)
    (hunique : ∀ z', (RawOne S).qz a.1 z'=true → z'=z) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S N u q) := by
  rw [← BDL26FirstZeroFaceEndpoint.terminal_syndrome S N u q hs]
  exact degree_one_search S a.1 a.2.1 z hz hunique _ (terminal_raw_star S N u q a hp)

/-- The one-neighbor branch retains both base calls and the complete accumulated Phi. -/
theorem degree_one_original_endpoint (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (hs : firstReadout S N u=0)
    (z : (RawOne S).Z) (hz : (RawOne S).qz a.1 z=true)
    (hunique : ∀ z', (RawOne S).qz a.1 z'=true → z'=z) :
    ∃ (p0 : (SuffixData S N).family.Cochain0 0)
      (p : (SuffixData S N).family.Cochain0 (TopIndex N)),
      (SuffixData S N).family.coboundary0 0 p0=
        (descent S N u q).word+
          (actualBase S N).decode (actualInputs S N (input S N u) 0)+
          (actualBase S N).decode (actualInputs S N
            (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q)) 0) ∧
      p=intervalMap0 (SuffixData S N) 0 (TopIndex N) (Nat.zero_le _) p0+
        accumulated S N u q ∧
      (SuffixData S N).family.coboundary0 (TopIndex N) p=
        BDL26LogicalDefectProtection.deltaX S N u q ∧
      (SuffixData S N).family.coboundary0 (TopIndex N) p=
        BDL26ActualFailureReadout.flip S N q+xCorrection S N u+
          xCorrection S N (translateX S N u (BDL26ActualFailureReadout.flip S N q)) ∧
      BDL26LogicalDefectProtection.chiX S N u q=0 := by
  have hb := degree_one_original_search S N u q a hp hs z hz hunique
  exact ⟨BDL26LocalSearchFailureReduction.basePotential S N u q hs hb,
    BDL26LocalSearchFailureReduction.fullPotential S N u q hs hb,
    BDL26LocalSearchFailureReduction.basePotential_spec S N u q hs hb,
    BDL26LocalSearchFailureReduction.fullPotential_formula S N u q hs hb,
    BDL26LocalSearchFailureReduction.fullPotential_spec S N u q hs hb,
    BDL26LocalSearchFailureReduction.original_correction_equation S N u q hs hb,
    BDL26LocalSearchFailureReduction.successful_chiX_zero S N u q hs hb⟩

private def seedQ (j : Fin 2) : BaseQubit := ⟨j.val,by omega⟩

private def seedRadial (j : Fin 2) : XStarEdge baseTannerSquarePresentation (0 : BaseX) :=
  ⟨.inl ⟨(0,seedQ j),by fin_cases j <;> decide⟩,by fin_cases j <;> decide⟩

private def seedCenter : XStarVertex baseTannerSquarePresentation (0 : BaseX) :=
  ⟨Vertex.x 0,by decide⟩

private def seedQVertex (j : Fin 2) : XStarVertex baseTannerSquarePresentation (0 : BaseX) :=
  ⟨Vertex.q (seedQ j),by fin_cases j <;> decide⟩

private theorem seedRadial_start (j : Fin 2) :
    xStarEdgeStart _ _ (seedRadial j)=seedCenter := by fin_cases j <;> rfl

private theorem seedRadial_end (j : Fin 2) :
    xStarEdgeEnd _ _ (seedRadial j)=seedQVertex j := by fin_cases j <;> rfl

private def seedFace (j : Fin 2) : XStarFace baseTannerSquarePresentation (0 : BaseX) :=
  ⟨⟨j.val,by omega⟩,by fin_cases j <;> decide⟩

private theorem seedRadial_face_zero : ∀ (j : Fin 2)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX)),
    seedRadial j=xStarFaceXQEdge _ _ f 0 ↔ f=seedFace j := by decide

private theorem seedRadial_face_one : ∀ (j : Fin 2)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX)),
    seedRadial j≠xStarFaceXQEdge _ _ f 1 := by decide

private theorem seedRadial_ne_qz (j : Fin 2)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX))
    (c : BDL26FiniteTannerSquare.Two) : seedRadial j≠xStarFaceQZEdge _ _ f c := by
  intro h
  have hv := congrArg Subtype.val h
  cases hv

private theorem seedRadial_horizontal (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX))
    (a : Fin S.half) (b : Fin (S.half+1)) :
    (.inl (seedRadial j,i) : SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)=
        subdivisionHorizontalEdge _ _ S f a b ↔
      f=seedFace j ∧ i=a ∧ b.val=0 := by
  by_cases hb0 : b.val=0
  · simp [subdivisionHorizontalEdge,hb0,seedRadial_face_zero]
  · by_cases hbm : b.val=S.half
    · have hm0 : S.half≠0 := S.half_pos.ne'
      simp [subdivisionHorizontalEdge,hb0,hbm,hm0,seedRadial_ne_qz]
    · simp [subdivisionHorizontalEdge,hb0,hbm]

private theorem seedRadial_vertical (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (f : XStarFace baseTannerSquarePresentation (0 : BaseX))
    (a : Fin (S.half+1)) (b : Fin S.half) :
    (.inl (seedRadial j,i) : SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)≠
      subdivisionVerticalEdge _ _ S f a b := by
  unfold subdivisionVerticalEdge
  split_ifs <;> simp [seedRadial_face_one,seedRadial_ne_qz]

private theorem face_matrix_expanded (T : TannerSquarePresentation) (x : T.X)
    (S : OddScale) (e : SubdivisionEdge T x S) (f : XStarFace T x)
    (a b : Fin S.half) :
    subdivisionFaceEdgeMatrix T x S e (f,a,b)=
      (((if e=subdivisionHorizontalEdge T x S f a (finCastGrid b) then (1:F) else 0)+
        (if e=subdivisionVerticalEdge T x S f (finSuccGrid a) b then 1 else 0))+
        (if e=subdivisionHorizontalEdge T x S f a (finSuccGrid b) then 1 else 0))+
        (if e=subdivisionVerticalEdge T x S f (finCastGrid a) b then 1 else 0) := rfl

private theorem seedRadial_localMatrix (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (f : SubdivisionFace baseTannerSquarePresentation (0 : BaseX) S) :
    subdivisionFaceEdgeMatrix baseTannerSquarePresentation (0 : BaseX) S
        (.inl (seedRadial j,i)) f=
      if f=(seedFace j,i,⟨0,S.half_pos⟩) then 1 else 0 := by
  rcases f with ⟨f,a,b⟩
  have hv0 := seedRadial_vertical S j i f (finSuccGrid a) b
  have hv1 := seedRadial_vertical S j i f (finCastGrid a) b
  have ht : ¬(.inl (seedRadial j,i) :
      SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)=
        subdivisionHorizontalEdge _ _ S f a (finSuccGrid b) := by
    erw [seedRadial_horizontal]
    simp [finSuccGrid]
  have hb : ((.inl (seedRadial j,i) :
      SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)=
        subdivisionHorizontalEdge _ _ S f a (finCastGrid b)) ↔
      (f,a,b)=(seedFace j,i,⟨0,S.half_pos⟩) := by
    erw [seedRadial_horizontal]
    simp [finCastGrid,Fin.ext_iff,eq_comm,and_assoc]
  erw [face_matrix_expanded]
  simp only [if_neg hv0,if_neg ht,if_neg hv1,add_zero]
  exact indicator_iff _ _ hb

private def seedRadialCheck (S : OddScale) (j : Fin 2) (i : Fin S.half) : (RawOne S).Z :=
  .inl (.inl ⟨(0 : BaseX),.inl (0,(seedFace j,i,⟨0,S.half_pos⟩))⟩)

private theorem seedRadial_qEdge_zero (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (q : BaseQubit) (e : QDoubleCylinderEdge baseTannerSquarePresentation q S) :
    qDoubleCylinderEdgeXIncidence baseTannerSquarePresentation q 0 S
      (.inl (0,.inl (seedRadial j,i))) e=0 := by
  unfold qDoubleCylinderEdgeXIncidence
  by_cases hxq : baseTannerSquarePresentation.xq (0 : BaseX) q=true
  · erw [dif_pos hxq]
    have hn : (.inl (0,.inl (seedRadial j,i)) :
        DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S)≠
        qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation q 0 hxq S e := by
      rcases e with ⟨c,z,k⟩ | z
      · intro he
        have tag := congrArg (fun edge : DoubleCylinderEdge
            baseTannerSquarePresentation (0 : BaseX) S =>
          match edge with
          | .inl (_, .inl (a,_)) => match a.val with
              | .inl _ => true
              | .inr _ => false
          | _ => false) he
        change true=false at tag
        cases tag
      · intro he
        cases he
    erw [if_neg hn]
  · erw [dif_neg hxq]

private theorem rx_local_column_indicator (P : TannerSquarePresentation)
    (S : OddScale) (x0 : P.X) (edge : DoubleCylinderEdge P x0 S)
    (face : DoubleCylinderFace P x0 S)
    (hl : ∀ f, doubleCylinderFaceEdgeMatrix P x0 S edge f=
      if f=face then 1 else 0)
    (hq : ∀ (q : P.Q) (e : QDoubleCylinderEdge P q S),
      qDoubleCylinderEdgeXIncidence P q x0 S edge e=0) (z : RX2 P S) :
    rxBoundary2Matrix P S (.inl ⟨x0,edge⟩) z=
      if z=(.inl (.inl ⟨x0,face⟩) : RX2 P S) then 1 else 0 := by
  classical
  rcases z with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · by_cases h : x0=x
    · subst x
      simp [rxBoundary2Matrix,hl,Sigma.mk.injEq]
    · simp [rxBoundary2Matrix,h,Ne.symm h,Sigma.mk.injEq]
  · simp [rxBoundary2Matrix,hq]
  · simp [rxBoundary2Matrix]

private theorem rx_q_column_indicator (P : TannerSquarePresentation)
    (S : OddScale) (q0 : P.Q) (vertex : QDoubleCylinderVertex P q0 S)
    (edge : QDoubleCylinderEdge P q0 S)
    (hq : ∀ e, qDoubleCylinderEdgeVertexIncidence P q0 S vertex e=
      if e=edge then 1 else 0)
    (hz : ∀ z, qDoubleCylinderVertexZIncidence P q0 S vertex z=0)
    (z : RX2 P S) :
    rxBoundary2Matrix P S (.inr ⟨q0,vertex⟩) z=
      if z=(.inl (.inr ⟨q0,edge⟩) : RX2 P S) then 1 else 0 := by
  classical
  rcases z with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · simp [rxBoundary2Matrix]
  · by_cases h : q0=q
    · subst q
      simp [rxBoundary2Matrix,hq,Sigma.mk.injEq]
    · simp [rxBoundary2Matrix,h,Ne.symm h,Sigma.mk.injEq]
  · simp [rxBoundary2Matrix,hz]

private theorem raw_boundary1_view (S : OddScale) (x : (RawOne S).X)
    (r : (RawOne S).Q) :
    rxBoundary1Matrix baseTannerSquarePresentation S x r=
      if (RawOne S).xq x r=true then (1:F) else 0 := by
  exact rxPresentation_boundary1Matrix_eq baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4 S x r

private theorem raw_boundary2_view (S : OddScale) (r : (RawOne S).Q)
    (z : (RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S r z=
      if (RawOne S).qz r z=true then (1:F) else 0 := by
  exact rxPresentation_boundary2Matrix_eq baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4 S r z

private theorem seedRadial_matrix (S : OddScale) (j : Fin 2) (i : Fin S.half)
    (z : (RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S
        (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) z=
      if z=seedRadialCheck S j i then 1 else 0 := by
  have hl : ∀ f, doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation (0 : BaseX) S
      (.inl (0,.inl (seedRadial j,i))) f=
        if f=(.inl (0,(seedFace j,i,⟨0,S.half_pos⟩))) then 1 else 0 := by
    intro f
    rcases f with ⟨c,f⟩ | b
    · by_cases hc : c=0
      · subst c
        change subdivisionFaceEdgeMatrix baseTannerSquarePresentation (0 : BaseX) S
          (.inl (seedRadial j,i)) f=
            if (Sum.inl (0,f) : DoubleCylinderFace baseTannerSquarePresentation (0 : BaseX) S)=
                .inl (0,(seedFace j,i,⟨0,S.half_pos⟩)) then 1 else 0
        have hm := seedRadial_localMatrix S j i f
        apply hm.trans
        apply indicator_iff
        constructor
        · intro hf
          exact congrArg (fun g : SubdivisionFace baseTannerSquarePresentation (0 : BaseX) S =>
            (Sum.inl ((0 : BDL26FiniteTannerSquare.Two),g) :
              DoubleCylinderFace baseTannerSquarePresentation (0 : BaseX) S)) hf
        · intro he
          exact congrArg Prod.snd (Sum.inl.inj he)
      · simp only [doubleCylinderFaceEdgeMatrix,if_neg (Ne.symm hc),
          Sum.inl.injEq,Prod.mk.injEq,hc,false_and,if_false]
    · have hb : (.inl (seedRadial j,i) :
          SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)≠b.val := by
        intro he
        have hm := b.property
        erw [← he] at hm
        change xStarBoundaryEdgeMember baseTannerSquarePresentation (0 : BaseX)
          (seedRadial j).val=true at hm
        change false=true at hm
        cases hm
      simp only [doubleCylinderFaceEdgeMatrix,Sum.inr_ne_inl,if_false]
      exact if_neg hb
  have hm := rx_local_column_indicator baseTannerSquarePresentation S
    (0 : BaseX) (.inl (0,.inl (seedRadial j,i)))
    (.inl (0,(seedFace j,i,⟨0,S.half_pos⟩))) hl (seedRadial_qEdge_zero S j i) z
  convert hm using 1 <;> congr 1

private theorem seedRadial_degree_one (S : OddScale) (j : Fin 2) (i : Fin S.half) :
    (RawOne S).qz (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩)
        (seedRadialCheck S j i)=true ∧
      ∀ z : (RawOne S).Z,
        (RawOne S).qz (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) z=true →
          z=seedRadialCheck S j i := by
  have hi (z : (RawOne S).Z) := rxPresentation_boundary2Matrix_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4 S
      (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) z
  constructor
  · have ht := hi (seedRadialCheck S j i)
    change _=(if (RawOne S).qz (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) (seedRadialCheck S j i)=true then (1:F) else 0) at ht
    erw [seedRadial_matrix,if_pos rfl] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact one_ne_zero ht
  · intro z hz
    have ht := hi z
    change _=(if (RawOne S).qz (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩) z=true then (1:F) else 0) at ht
    erw [seedRadial_matrix,if_pos hz] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact one_ne_zero ht.symm

private def seedZEdge (j : Fin 2) : QStarEdge baseTannerSquarePresentation (seedQ j) :=
  ⟨j,by fin_cases j <;> decide⟩

private theorem seedZEdge_unique (j : Fin 2)
    (z : QStarEdge baseTannerSquarePresentation (seedQ j)) : z=seedZEdge j := by
  fin_cases j
  · exact (by decide : ∀ z : QStarEdge baseTannerSquarePresentation (seedQ 0),
      z=seedZEdge 0) z
  · exact (by decide : ∀ z : QStarEdge baseTannerSquarePresentation (seedQ 1),
      z=seedZEdge 1) z

private def seedConeCheck (S : OddScale) (j : Fin 2) : (RawOne S).Z :=
  .inl (.inr ⟨seedQ j,.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))⟩)

private theorem seedCone_matrix (S : OddScale) (j : Fin 2) (z : (RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S
        (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) z=
      if z=seedConeCheck S j then 1 else 0 := by
  have hq : ∀ e, qDoubleCylinderEdgeVertexIncidence baseTannerSquarePresentation
      (seedQ j) S (0,.inl (.inl ())) e=
        if e=(.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))) then 1 else 0 := by
    intro e
    rcases e with ⟨c,z,i⟩ | z
    · have hz := seedZEdge_unique j z
      subst z
      fin_cases c <;> by_cases hi : i.val=0 <;> by_cases hm : i.val+1=S.half <;>
        simp_all [qDoubleCylinderEdgeVertexIncidence,
          qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd,qSubdivisionEdgeStart,
          qSubdivisionEdgeEnd,qStarEdgeStart,qStarEdgeEnd,
          S.half_pos.ne',Ne.symm S.half_pos.ne',hi,hm,Fin.ext_iff]
    · simp [qDoubleCylinderEdgeVertexIncidence,qDoubleCylinderEdgeStart,
        qDoubleCylinderEdgeEnd,qStarEdgeEnd]
  have hz : ∀ z, qDoubleCylinderVertexZIncidence baseTannerSquarePresentation
      (seedQ j) S (0,.inl (.inl ())) z=0 := by
    intro z
    simp [qDoubleCylinderVertexZIncidence]
  have hm := rx_q_column_indicator baseTannerSquarePresentation S (seedQ j)
    (0,.inl (.inl ())) (.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))) hq hz z
  convert hm using 1 <;> congr 1

private theorem seedCone_degree_one (S : OddScale) (j : Fin 2) :
    (RawOne S).qz (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) (seedConeCheck S j)=true ∧
      ∀ z : (RawOne S).Z,
        (RawOne S).qz (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) z=true → z=seedConeCheck S j := by
  have hi (z : (RawOne S).Z) := rxPresentation_boundary2Matrix_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4 S
      (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) z
  constructor
  · have ht := hi (seedConeCheck S j)
    change _=(if (RawOne S).qz (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) (seedConeCheck S j)=true then (1:F) else 0) at ht
    erw [seedCone_matrix,if_pos rfl] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact one_ne_zero ht
  · intro z hz
    have ht := hi z
    change _=(if (RawOne S).qz (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩) z=true then (1:F) else 0) at ht
    erw [seedCone_matrix,if_pos hz] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact one_ne_zero ht.symm

private def radialNode (S : OddScale) (j : Fin 2) (n : Nat) (hn : n≤S.half) :
    SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) S :=
  if h0 : n=0 then .inl (xStarEdgeStart _ _ (seedRadial j))
  else if hm : n=S.half then .inl (xStarEdgeEnd _ _ (seedRadial j))
  else .inr (.inl (seedRadial j,⟨n-1,by omega⟩))

private noncomputable def radialPath (S : OddScale) (j : Fin 2) :
    (n : Nat) → (hn : n≤S.half) →
      UndirectedPath
        (tannerDoubleCylinderEdgeStart baseTannerSquarePresentation (0 : BaseX) S)
        (tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation (0 : BaseX) S)
        (0,.inl (xStarEdgeStart _ _ (seedRadial j))) (0,radialNode S j n hn)
  | 0,_ => .nil
  | n+1,hn => by
    let i : Fin S.half := ⟨n,by omega⟩
    apply UndirectedPath.step (radialPath S j n (by omega))
      (.inl (0,.inl (seedRadial j,i)))
    apply Or.inl
    constructor
    · have hm : n≠S.half := by omega
      simp [tannerDoubleCylinderEdgeStart,subdivisionEdgeStart,
        subdivisionSegmentStart,radialNode,i,hm]
    · simp [tannerDoubleCylinderEdgeEnd,subdivisionEdgeEnd,
        subdivisionSegmentEnd,radialNode,i]

private def radialChain (S : OddScale) (j : Fin 2) :
    Word F (DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S) :=
  pathChain (radialPath S j S.half (Nat.le_refl _))

private theorem radialPath_support (S : OddScale) (j : Fin 2) (n : Nat)
    (hn : n≤S.half) (e : DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S)
    (he : pathChain (radialPath S j n hn) e≠0) :
    ∃ i : Fin S.half, e=.inl (0,.inl (seedRadial j,i)) := by
  revert hn
  induction n with
  | zero =>
    intro hn he
    simp [radialPath,pathChain] at he
  | succ n ih =>
    intro hn he
    let i : Fin S.half := ⟨n,by omega⟩
    have hs : pathChain (radialPath S j (n+1) hn)=
        pathChain (radialPath S j n (by omega))+
          Pi.single (.inl (0,.inl (seedRadial j,i))) (1:F) := rfl
    rw [hs,Pi.add_apply] at he
    by_cases hp : pathChain (radialPath S j n (by omega)) e=0
    · rw [hp,zero_add,Pi.single_apply] at he
      by_cases heq : e=.inl (0,.inl (seedRadial j,i))
      · exact ⟨i,heq⟩
      · exact False.elim (he (if_neg heq))
    · exact ih (by omega) hp

private theorem pairing_graph_gradient_path {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (edgeStart edgeEnd : E → V)
    (root target : V) (path : UndirectedPath edgeStart edgeEnd root target)
    (p : Word F V) :
    wordPairing (pathChain path)
        (wordLinearMapTranspose (graphBoundary edgeStart edgeEnd) p)=p root+p target := by
  calc
    wordPairing (pathChain path)
        (wordLinearMapTranspose (graphBoundary edgeStart edgeEnd) p)=
      wordPairing (wordLinearMapTranspose (graphBoundary edgeStart edgeEnd) p)
        (pathChain path) := dotProduct_comm _ _
    _=wordPairing p (graphBoundary edgeStart edgeEnd (pathChain path)) :=
      wordPairing_wordLinearMapTranspose _ _ _
    _=p root+p target := by
      rw [graphBoundary_pathChain]
      simp only [wordPairing_apply,dotProduct_add,dotProduct_single_one]

private def coordinateMap {I : Type} (i : I) : Word F I →ₗ[F] F where
  toFun w := w i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The explicit copy-zero dual loop: two Q cones and both entire X-Q radial paths. -/
def rawDualReadout (S : OddScale) : Word F (RawOne S).Q →ₗ[F] F :=
  coordinateMap (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)+
    coordinateMap (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)+
    (wordPairing (radialChain S 0+radialChain S 1)).comp
      (wordPullback (fun e => (.inl ⟨(0 : BaseX),e⟩ : (RawOne S).Q)))

private theorem rawDualReadout_zero (S : OddScale) (w : Word F (RawOne S).Q)
    (h0 : w (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)=0)
    (h1 : w (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)=0)
    (hpath : ∀ (j : Fin 2) (i : Fin S.half),
      w (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩)=0) :
    rawDualReadout S w=0 := by
  have hp (j : Fin 2) : wordPairing (radialChain S j)
      (fun e => w (.inl ⟨(0 : BaseX),e⟩))=0 := by
    change (∑ e, radialChain S j e*w (.inl ⟨(0 : BaseX),e⟩))=0
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : radialChain S j e=0
    · rw [he,zero_mul]
    · obtain ⟨i,rfl⟩ := radialPath_support S j S.half (Nat.le_refl _) e he
      exact (congrArg (fun v : F =>
        radialChain S j (.inl (0,.inl (seedRadial j,i)))*v) (hpath j i)).trans
        (mul_zero _)
  change w (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)+
    w (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)+
    wordPairing (radialChain S 0+radialChain S 1)
      (fun e => w (.inl ⟨(0 : BaseX),e⟩))=0
  rw [h0,h1,map_add,LinearMap.add_apply,hp,hp]
  simp

private theorem rx_cone_single_incidence (P : TannerSquarePresentation)
    (S : OddScale) (q : P.Q) (x0 : P.X) (v0 : XStarVertex P x0)
    (hv0 : v0.val=Vertex.q q)
    (hxq : ∀ x, P.xq x q=true ↔ x=x0) (v : RX0 P S) :
    rxBoundary1Matrix P S v (.inr ⟨q,(0,.inl (.inl ()))⟩)=
      if v=⟨x0,(0,.inl v0)⟩ then 1 else 0 := by
  classical
  rcases v with ⟨x,c,v⟩
  by_cases hx : x=x0
  · subst x
    by_cases hc : c=0
    · subst c
      rcases v with v | v | v <;>
        simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
          qSubdivisionVertexXIncidence,(hxq x0).mpr rfl,hv0,
          Subtype.ext_iff,Sigma.mk.injEq]
    · simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,hc,Sigma.mk.injEq]
  · simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence,hxq,hx,Ne.symm hx,Sigma.mk.injEq]

private theorem seedQ_unique_x : ∀ (j : Fin 2) (x : BaseX),
    baseTannerSquarePresentation.xq x (seedQ j)=true ↔ x=0 := by decide

private theorem seed_cone_incidence (S : OddScale) (j : Fin 2)
    (v : RX0 baseTannerSquarePresentation S) :
    rxBoundary1Matrix baseTannerSquarePresentation S v
        (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩)=
      if v=⟨0,(0,.inl (seedQVertex j))⟩ then 1 else 0 := by
  exact rx_cone_single_incidence baseTannerSquarePresentation S (seedQ j)
    (0 : BaseX) (seedQVertex j) rfl (seedQ_unique_x j) v

private theorem seed_cone_gradient (S : OddScale) (j : Fin 2)
    (p : Word F (RX0 baseTannerSquarePresentation S)) :
    BDL26ReplacementCochainMaps.rxCoboundary0 baseTannerSquarePresentation S p
      (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩)=p ⟨0,(0,.inl (seedQVertex j))⟩ := by
  unfold BDL26ReplacementCochainMaps.rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply]
  simp_rw [seed_cone_incidence]
  simp

private theorem radial_gradient (S : OddScale) (j : Fin 2)
    (p : Word F (RX0 baseTannerSquarePresentation S)) :
    wordPairing (radialChain S j)
      (fun e => BDL26ReplacementCochainMaps.rxCoboundary0
        baseTannerSquarePresentation S p (.inl ⟨0,e⟩))=
      p ⟨0,(0,.inl seedCenter)⟩+p ⟨0,(0,.inl (seedQVertex j))⟩ := by
  have hword : (fun e : DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S =>
      BDL26ReplacementCochainMaps.rxCoboundary0 baseTannerSquarePresentation S p
        (.inl ⟨0,e⟩))=
      wordLinearMapTranspose (doubleCylinderBoundary1 baseTannerSquarePresentation 0 S)
        (fun v => p ⟨0,v⟩) := by
    funext e
    exact BDL26RXDecoderAdapter.raw_delta0_x _ _ _ _ _
  rw [hword,← doubleCylinderGraphBoundary_eq_boundary1]
  have hg := pairing_graph_gradient_path
    (tannerDoubleCylinderEdgeStart baseTannerSquarePresentation (0 : BaseX) S)
    (tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation (0 : BaseX) S)
    _ _ (radialPath S j S.half (Nat.le_refl _)) (fun v => p ⟨0,v⟩)
  change wordPairing (pathChain (radialPath S j S.half (Nat.le_refl _)))
    (wordLinearMapTranspose (graphBoundary
      (tannerDoubleCylinderEdgeStart baseTannerSquarePresentation (0 : BaseX) S)
      (tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation (0 : BaseX) S))
      (fun v => p ⟨0,v⟩))=_
  convert hg using 1 <;> simp only [radialNode,dif_pos rfl,dif_neg S.half_pos.ne',
    seedRadial_start,seedRadial_end] <;> rfl

private theorem rawDualReadout_raw_boundary (S : OddScale)
    (p : Word F (RX0 baseTannerSquarePresentation S)) :
    rawDualReadout S (BDL26ReplacementCochainMaps.rxCoboundary0
      baseTannerSquarePresentation S p)=0 := by
  change BDL26ReplacementCochainMaps.rxCoboundary0 baseTannerSquarePresentation S p
      (.inr ⟨seedQ 0,(0,.inl (.inl ()))⟩)+
    BDL26ReplacementCochainMaps.rxCoboundary0 baseTannerSquarePresentation S p
      (.inr ⟨seedQ 1,(0,.inl (.inl ()))⟩)+
    wordPairing (radialChain S 0+radialChain S 1)
      (fun e => BDL26ReplacementCochainMaps.rxCoboundary0
        baseTannerSquarePresentation S p (.inl ⟨0,e⟩))=0
  rw [seed_cone_gradient,seed_cone_gradient]
  rw [map_add,LinearMap.add_apply,radial_gradient,radial_gradient]
  calc
    _=(p ⟨0,(0,.inl seedCenter)⟩+p ⟨0,(0,.inl seedCenter)⟩)+
      (p ⟨0,(0,.inl (seedQVertex 0))⟩+p ⟨0,(0,.inl (seedQVertex 0))⟩)+
      (p ⟨0,(0,.inl (seedQVertex 1))⟩+p ⟨0,(0,.inl (seedQVertex 1))⟩) := by abel
    _=0 := by simp only [ZModModule.add_self,add_zero,zero_add]

/-- The explicit dual loop annihilates every complete actual level-one boundary. -/
theorem rawDualReadout_boundary (S : OddScale) (p : Word F (RawOne S).X) :
    rawDualReadout S (tannerCoboundary0 (RawOne S) p)=0 := by
  have he := congrArg (fun L : Word F (RawOne S).X →ₗ[F] Word F (RawOne S).Q => L p)
    (BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
      baseTannerSquarePresentation baseTannerSquareAdmissibleV4
        baseTannerSquareCellularRegular S)
  exact (congrArg (rawDualReadout S) he).trans (rawDualReadout_raw_boundary S p)

private theorem rawDualReadout_map1 (S : OddScale) (w : Word F BaseQubit) :
    rawDualReadout S (BDL26ReplacementCochainMaps.rxMap1Coord
      baseTannerSquarePresentation S w)=w 0+w 1 := by
  have hz : (fun e : DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S =>
      BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S w
        (.inl ⟨0,e⟩))=0 := by
    funext e
    exact BDL26ReplacementCochainMaps.rxMap1Coord_localEdge _ _ _ _
  change w 0+w 1+wordPairing (radialChain S 0+radialChain S 1)
    (fun e => BDL26ReplacementCochainMaps.rxMap1Coord
      baseTannerSquarePresentation S w (.inl ⟨0,e⟩))=_
  rw [hz,map_zero,add_zero]

/-- The literal C2 dual readout sums all Q-cylinder coordinates over the explicit loop. -/
def dualReadout (S : OddScale) : Word F (RawTwo S).Q →ₗ[F] F :=
  (rawDualReadout S).comp (BDL26LevelTwoDistance.rzQParity (RawOne S) S)

/-- No Z or Q potential summand is omitted from the boundary identity. -/
theorem dualReadout_boundary (S : OddScale) (p : Word F (RawTwo S).X) :
    dualReadout S (tannerCoboundary0 (RawTwo S) p)=0 := by
  change rawDualReadout S (BDL26LevelTwoDistance.rzQParity (RawOne S) S
    (BDL26ReplacementCochainMaps.rzCoboundary0 (RawOne S)
      (rxState S baseState).admissible S p))=0
  exact (congrArg (rawDualReadout S)
    (BDL26LevelTwoDistance.rzQParity_coboundary (RawOne S)
      (rxState S baseState).admissible S p)).trans (rawDualReadout_boundary S _)

/-- The explicit transported nonboundary pairs once with this explicit dual loop. -/
theorem dualReadout_logical (S : OddScale) :
    dualReadout S (BDL26LevelTwoDistance.levelTwoXLogical S)=1 := by
  change rawDualReadout S (BDL26LevelTwoDistance.rzQParity (RawOne S) S
    (map1Coord (RawOne S) (rxState S baseState).admissible S
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        BDL26LevelTwoDistance.seedCocycle)))=1
  exact (congrArg (rawDualReadout S)
    (BDL26LevelTwoDistance.rzQParity_map1Coord (RawOne S)
      (rxState S baseState).admissible S
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        BDL26LevelTwoDistance.seedCocycle))).trans
    ((rawDualReadout_map1 S BDL26LevelTwoDistance.seedCocycle).trans (by decide))

private theorem star_dual_zero_of_no_degree_one (S : OddScale)
    (r : (RawOne S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (RawOne S)) r S)
    (h : BDL26LevelTwoLocalBranchEndpoint.Error S)
    (hh : BDL26LevelTwoLocalBranchEndpoint.supported S (.inl (.inr ⟨r,e⟩)) h)
    (hn : ¬∃ z : (RawOne S).Z, (RawOne S).qz r z=true ∧
      ∀ z', (RawOne S).qz r z'=true → z'=z) : dualReadout S h=0 := by
  have hc (j : Fin 2) : BDL26LevelTwoLocalBranchEndpoint.parity S h
      (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩)=0 := by
    apply BDL26LevelTwoLocalBranchEndpoint.edge_parity_other S r e h hh
    intro he
    apply hn
    rw [← he]
    exact ⟨seedConeCheck S j,seedCone_degree_one S j⟩
  have hp (j : Fin 2) (i : Fin S.half) :
      BDL26LevelTwoLocalBranchEndpoint.parity S h
        (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,i))⟩)=0 := by
    apply BDL26LevelTwoLocalBranchEndpoint.edge_parity_other S r e h hh
    intro he
    apply hn
    rw [← he]
    exact ⟨seedRadialCheck S j i,seedRadial_degree_one S j i⟩
  exact rawDualReadout_zero S _ (hc 0) (hc 1) hp

/-- Failure of the actual local search forces the actual terminal loop readout to zero. -/
theorem failed_search_terminal_dual_zero (S : OddScale) (N : Nat)
    (u : XSyndromeDomain S N) (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (hs : firstReadout S N u=0)
    (hn : BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S N u q)=none) :
    dualReadout S (descent S N u q).word=0 := by
  apply star_dual_zero_of_no_degree_one S a.1 a.2.1 _ (terminal_raw_star S N u q a hp)
  rintro ⟨z,hz,hunique⟩
  obtain ⟨w,hw⟩ := degree_one_original_search S N u q a hp hs z hz hunique
  rw [hn] at hw
  cases hw

private theorem boundary_of_normalized_detector
    (S : OddScale) (phi : Word F (state S 2).presentation.Q →ₗ[F] F)
    (hphi : ∀ p : Word F (state S 2).presentation.X,
      phi (tannerCoboundary0 (state S 2).presentation p)=0)
    (k : FC.Cocycle S 2) (hk : phi k.val=1)
    (w : FC.Cocycle S 2) (hw : phi w.val=0) :
    ∃ p : Word F (state S 2).presentation.X,
      tannerCoboundary0 (state S 2).presentation p=w.val := by
  have hkc : FC.finiteH1Equiv S 2 (FC.classOf S 2 k)=1 := by
    rcases BDL26RXQEdgePairTransport.bit_cases
      (FC.finiteH1Equiv S 2 (FC.classOf S 2 k)) with hz | ho
    · obtain ⟨p,hp⟩ := (coefficient_zero_iff_boundary S 2 k).mp hz
      exact False.elim (one_ne_zero (hk.symm.trans
        ((congrArg phi hp).symm.trans (hphi p))))
    · exact ho
  rcases BDL26RXQEdgePairTransport.bit_cases
    (FC.finiteH1Equiv S 2 (FC.classOf S 2 w)) with hz | ho
  · exact (coefficient_zero_iff_boundary S 2 w).mp hz
  · obtain ⟨p,hp⟩ := (coefficient_eq_iff_boundary S 2 w k).mp (ho.trans hkc.symm)
    have hp' : phi (w.val-k.val)=0 := (congrArg phi hp).symm.trans (hphi p)
    rw [map_sub,hw,hk,zero_sub] at hp'
    exact False.elim (one_ne_zero (neg_eq_zero.mp hp'))

private theorem differential0_heq {U V : TannerSquarePresentation} (h : U=V) :
    HEq (tannerCoboundary0 U) (tannerCoboundary0 V) := by cases h; exact HEq.rfl

/-- For actual closed C2 words, this explicit dual readout detects the full boundary space. -/
theorem dualReadout_zero_boundary (S : OddScale) (w : FC.Cocycle S 2)
    (hw : dualReadout S w.val=0) :
    ∃ p : Word F (state S 2).presentation.X,
      tannerCoboundary0 (state S 2).presentation p=w.val := by
  have hzero : ∀ p : Word F (state S 2).presentation.X,
      dualReadout S (tannerCoboundary0 (state S 2).presentation p)=0 := by
    have h0 : (tannerCoboundary0 (state S 2).presentation :
        Word F (RawTwo S).X →ₗ[F] Word F (RawTwo S).Q)=tannerCoboundary0 (RawTwo S) :=
      eq_of_heq (differential0_heq
        (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))
    intro p
    rw [h0]
    exact dualReadout_boundary S p
  let k : FC.Cocycle S 2 := ⟨BDL26LevelTwoDistance.levelTwoXLogical S,
    (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
      (BDL26LevelTwoDistance.levelTwoXLogical_cocycle S)⟩
  exact boundary_of_normalized_detector S (dualReadout S) hzero k
    (dualReadout_logical S) w hw

private theorem encoded_coordinates_strict {I : Type} [Fintype I] [Encodable I] :
    (BDL26LevelTwoDecoder.coordinates I).Pairwise
      (fun a b => Encodable.encode a<Encodable.encode b) := by
  letI : LinearOrder I := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  have hs : (BDL26LevelTwoDecoder.coordinates I).Pairwise
      (fun a b => Encodable.encode a≤Encodable.encode b) := by
    change (Finset.univ.sort (· ≤ ·) : List I).Pairwise (· ≤ ·)
    exact Finset.pairwise_sort _ _
  have hn : (BDL26LevelTwoDecoder.coordinates I).Nodup := by
    change (Finset.univ.sort (· ≤ ·) : List I).Nodup
    exact Finset.sort_nodup _ _
  have hi (xs : List I) (hs : xs.Pairwise (fun a b => Encodable.encode a≤Encodable.encode b))
      (hn : xs.Nodup) : xs.Pairwise (fun a b => Encodable.encode a<Encodable.encode b) := by
    revert hs hn
    induction xs with
    | nil => intro hs hn; exact List.Pairwise.nil
    | cons a xs ih =>
      intro hs hn
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        have hle := (List.pairwise_cons.mp hs).1 b hb
        have hne : Encodable.encode a≠Encodable.encode b := by
          intro he
          have hab := Encodable.encode_injective he
          exact (List.nodup_cons.mp hn).1 (hab.symm ▸ hb)
        omega
      · exact ih (List.pairwise_cons.mp hs).2 (List.nodup_cons.mp hn).2
  exact hi _ hs hn

private theorem before_add_of_encoded_kernel {I : Type} [Encodable I]
    (xs : List I) (hs : xs.Pairwise (fun a b => Encodable.encode a<Encodable.encode b))
    (q : I) (hm : q∈xs) (r k : Word F I)
    (hp : ∀ i, Encodable.encode i<Encodable.encode q → k i=0)
    (hq : k q=1) (hr : r q=1) : BDL26GlobalLookupLinearity.Before xs (r+k) r := by
  revert hs hm
  induction xs with
  | nil => intro hs hm; cases hm
  | cons a xs ih =>
    intro hs hm
    by_cases ha : a=q
    · subst a
      apply Or.inl
      refine ⟨?_,hr⟩
      change r q+k q=0
      rw [hr,hq]
      exact ZModModule.add_self _
    · have hmem : q∈xs := (List.mem_cons.mp hm).resolve_left (Ne.symm ha)
      have hlt := (List.pairwise_cons.mp hs).1 q hmem
      apply Or.inr
      constructor
      · change r a+k a=r a
        rw [hp a hlt,add_zero]
      · exact ih (List.pairwise_cons.mp hs).2 hmem

private theorem global_zero_of_encoded_kernel {I J : Type} [Fintype I]
    [DecidableEq I] [Encodable I] [Fintype J] [DecidableEq J]
    (L : Word F I →ₗ[F] Word F J) (a : Word F I) (q : I)
    (k : Word F I) (hk : L k=0)
    (hp : ∀ i, Encodable.encode i<Encodable.encode q → k i=0) (hq : k q=1) :
    BDL26GlobalLookupLinearity.G L (L a) q=0 := by
  let r := BDL26GlobalLookupLinearity.G L (L a)
  rcases BDL26RXQEdgePairTransport.bit_cases (r q) with hz | ho
  · exact hz
  · have hpre : L r=L a := BDL26GlobalLookupLinearity.global_preimage L _ ⟨a,rfl⟩
    have hsum : L (r+k)=L a := by rw [map_add,hpre,hk,add_zero]
    have hmin := BDL26GlobalLookupLinearity.global_minimal L (L a) ⟨a,rfl⟩ (r+k) hsum
    exact False.elim (hmin (before_add_of_encoded_kernel _ encoded_coordinates_strict
      q (BDL26LevelTwoDecoder.mem_coordinates I q) r k hp hq ho))

private theorem executableLevelOne_eq_raw (S : OddScale) :
    BDL26LevelTwoDecoder.executableLevelOne S=RawOne S := by
  exact (BDL26LevelTwoDecoder.executableLevelOne_eq S).trans rfl

private def executableCoordinate (S : OddScale) (q : (levelTwoPresentation S).Q) :
    BDL26LevelTwoDecoder.ExecutableQ S :=
  cast (BDL26LevelTwoDecoder.executableQ_eq S).symm q

private theorem cast_rz_cone (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (c : BDL26FiniteTannerSquare.Two) :
    cast (congrArg (fun P => RZQ P S) h).symm
        (.inr ⟨r,(c,.inl (.inl ()))⟩)=
      .inr ⟨cast (congrArg TannerSquarePresentation.Q h).symm r,(c,.inl (.inl ()))⟩ := by
  cases h
  rfl

private theorem executableCoordinate_cone (S : OddScale) (r : (RawOne S).Q)
    (c : BDL26FiniteTannerSquare.Two) :
    executableCoordinate S (.inr ⟨r,(c,.inl (.inl ()))⟩)=
      (.inr ⟨r,(c,.inl (.inl ()))⟩ : BDL26LevelTwoDecoder.ExecutableQ S) := by
  change cast (congrArg (fun P => RZQ P S)
      (executableLevelOne_eq_raw S)).symm
        (.inr ⟨r,(c,.inl (.inl ()))⟩)=_
  exact cast_rz_cone S (executableLevelOne_eq_raw S) r c

private theorem encoded_cone (S : OddScale) (r : (RawOne S).Q)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inl (.inl ()))⟩))=
      2*Nat.pair (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val 0)+1 := by
  rw [executableCoordinate_cone]
  rfl

private theorem cast_xq {P Q : TannerSquarePresentation} (h : P=Q)
    (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true) :
    P.xq (cast (congrArg TannerSquarePresentation.X h).symm x)
      (cast (congrArg TannerSquarePresentation.Q h).symm r)=true := by
  cases h
  exact hx

private theorem cast_qz {P Q : TannerSquarePresentation} (h : P=Q)
    (r : Q.Q) (z : Q.Z) (hz : Q.qz r z=true) :
    P.qz (cast (congrArg TannerSquarePresentation.Q h).symm r)
      (cast (congrArg TannerSquarePresentation.Z h).symm z)=true := by
  cases h
  exact hz

private theorem cast_rz_radial_image (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (A : TannerSquareAdmissible Q) (r : Q.Q) (x : Q.X)
    (hx : Q.xq x r=true) (z : Q.Z) (hz : Q.qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,qToZDoubleCylinderEdge Q A r z hz S (.inl (c,(⟨x,hx⟩,i)))⟩)=
    .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
      qToZDoubleCylinderEdge P (h.symm ▸ A)
        (cast (congrArg TannerSquarePresentation.Q h).symm r)
        (cast (congrArg TannerSquarePresentation.Z h).symm z)
        (cast_qz h r z hz) S
        (.inl (c,(⟨cast (congrArg TannerSquarePresentation.X h).symm x,
          cast_xq h r x hx⟩,i)))⟩ := by
  cases h
  rfl

private theorem encoded_radial_image (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible
        r z hz S (.inl (c,(⟨x,hx⟩,i)))⟩))=
      2*Nat.pair
        (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val
          (2*Nat.pair
            (2*Nat.pair
              (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
              (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X))+1)
            i.val)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
      (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_radial_image S (executableLevelOne_eq_raw S)
    (rxState S baseState).admissible.toTannerSquareAdmissible r x hx z hz c i]
  rfl

private theorem cone_before_radial_code (r x z : Nat)
    (c : BDL26FiniteTannerSquare.Two) :
    2*Nat.pair r (Nat.pair c.val 0)+1 <
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair (2*Nat.pair r x+1) 0)) := by
  have hc : Nat.pair c.val 0≤2 := by
    rcases two_eq_zero_or_one c with hc | hc <;> subst c <;> decide
  have hupper := Nat.pair_lt_max_add_one_sq r (Nat.pair c.val 0)
  have hr := Nat.left_le_pair r x
  have hinner := Nat.left_le_pair (2*Nat.pair r x+1) 0
  have hmiddle := Nat.right_le_pair c.val (2*Nat.pair (2*Nat.pair r x+1) 0)
  have hlarge := Nat.max_sq_add_min_le_pair z
    (2*Nat.pair c.val (2*Nat.pair (2*Nat.pair r x+1) 0))
  have hmax : max r (Nat.pair c.val 0)+1 ≤
      2*Nat.pair c.val (2*Nat.pair (2*Nat.pair r x+1) 0) := by
    have hright := Nat.right_le_pair c.val (2*Nat.pair (2*Nat.pair r x+1) 0)
    omega
  have hsquare : (max r (Nat.pair c.val 0)+1)^2 ≤
      (max z (2*Nat.pair c.val (2*Nat.pair (2*Nat.pair r x+1) 0)))^2 := by
    exact Nat.pow_le_pow_left (hmax.trans (Nat.le_max_right _ _)) 2
  omega

private theorem cast_rz_endpoint (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩)=
    .inr ⟨cast (congrArg TannerSquarePresentation.Q h).symm r,
      (c,.inl (.inr ⟨cast (congrArg TannerSquarePresentation.X h).symm x,
        cast_xq h r x hx⟩))⟩ := by
  cases h
  rfl

private theorem cast_rz_interior (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩)=
    .inr ⟨cast (congrArg TannerSquarePresentation.Q h).symm r,
      (c,.inr (⟨cast (congrArg TannerSquarePresentation.X h).symm x,
        cast_xq h r x hx⟩,i))⟩ := by
  cases h
  rfl

private theorem encoded_endpoint (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩))=
      2*Nat.pair
        (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val
          (2*(2*Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1 := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
      (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_endpoint S (executableLevelOne_eq_raw S) r x hx c]
  rfl

private theorem encoded_interior (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩))=
      2*Nat.pair
        (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val
          (2*Nat.pair
            (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
      (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_interior S (executableLevelOne_eq_raw S) r x hx c i]
  rfl

private theorem cone_before_vertex_code (r : Nat)
    (c : BDL26FiniteTannerSquare.Two) (v : Nat) (hv : 0<v) :
    2*Nat.pair r (Nat.pair c.val 0)+1 <
      2*Nat.pair r (Nat.pair c.val v)+1 := by
  have h := Nat.pair_lt_pair_right r (Nat.pair_lt_pair_right c.val hv)
  omega

private theorem q_before_local_code (r z u v : Nat)
    (c : BDL26FiniteTannerSquare.Two) (huv : u<v)
    (hr : r<2*Nat.pair c.val v) :
    2*Nat.pair r (Nat.pair c.val u)+1 <
      2*Nat.pair z (2*Nat.pair c.val v) := by
  have htail := Nat.pair_lt_pair_right c.val huv
  have hmax : max r (Nat.pair c.val u)+1≤2*Nat.pair c.val v := by omega
  have hup := Nat.pair_lt_max_add_one_sq r (Nat.pair c.val u)
  have hlow := Nat.max_sq_add_min_le_pair z (2*Nat.pair c.val v)
  have hsq := Nat.pow_le_pow_left
    (hmax.trans (Nat.le_max_right z (2*Nat.pair c.val v))) 2
  omega

private theorem interior_before_later_radial_code (r r' x z j k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hrr : r≤r') (hjk : j<k) :
    2*Nat.pair r (Nat.pair c.val (2*Nat.pair x j+1))+1 <
      2*Nat.pair z
        (2*Nat.pair c.val (2*Nat.pair (2*Nat.pair r' x+1) k)) := by
  have hx := Nat.right_le_pair r' x
  have hr := Nat.left_le_pair r' x
  have hfirst : x<2*Nat.pair r' x+1 := by omega
  have hsub := Nat.pair_lt_pair_left j hfirst
  have hsub' := Nat.pair_lt_pair_right (2*Nat.pair r' x+1) hjk
  have huv : 2*Nat.pair x j+1<2*Nat.pair (2*Nat.pair r' x+1) k := by omega
  have htail := Nat.left_le_pair (2*Nat.pair r' x+1) k
  have hout := Nat.right_le_pair c.val (2*Nat.pair (2*Nat.pair r' x+1) k)
  apply q_before_local_code _ _ _ _ c huv
  omega

private theorem interior_before_grid_code (r x z f i a b tag : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hri : r< i) (hxi : x< i)
    (hi : i≤ max a b) (htag : 1≤tag) :
    2*Nat.pair r (Nat.pair c.val (2*Nat.pair x i+1))+1 <
      2*Nat.pair z (2*Nat.pair c.val (4*Nat.pair f (Nat.pair a b)+tag)) := by
  have hp : Nat.pair x i=i*i+x := by simp [Nat.pair,hxi]
  have hsq := Nat.pow_le_pow_left hi 2
  have hlow := Nat.max_sq_add_min_le_pair a b
  have hright := Nat.right_le_pair f (Nat.pair a b)
  have hiP : i^2≤Nat.pair f (Nat.pair a b) :=
    hsq.trans (((Nat.le_add_right ((max a b)^2) (min a b)).trans hlow).trans hright)
  have hiP' : i≤Nat.pair f (Nat.pair a b) :=
    (Nat.le_self_pow (by decide) i).trans hiP
  have huv : 2*Nat.pair x i+1<4*Nat.pair f (Nat.pair a b)+tag := by
    rw [hp]
    have hisq : i*i≤Nat.pair f (Nat.pair a b) := by simpa only [pow_two] using hiP
    have hxP : x+1≤Nat.pair f (Nat.pair a b) := (Nat.succ_le_of_lt hxi).trans hiP'
    omega
  have htail := Nat.right_le_pair c.val (4*Nat.pair f (Nat.pair a b)+tag)
  apply q_before_local_code _ _ _ _ c huv
  omega

private theorem encoded_interior_lt (S : OddScale) (r r' : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (hx' : (RawOne S).xq x r'=true) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1))
    (hlt : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r',(c,.inr (⟨x,hx'⟩,i))⟩)) := by
  have hp := Nat.pair_lt_pair_left
    (Nat.pair c.val (2*Nat.pair
      (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1)) hlt
  have hn : 2*Nat.pair
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
      (Nat.pair c.val (2*Nat.pair
        (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 <
      2*Nat.pair (Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
      (Nat.pair c.val (2*Nat.pair
        (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 := by omega
  exact (encoded_interior S r x hx c i).trans_lt
    (hn.trans_eq (encoded_interior S r' x hx' c i).symm)

private theorem encoded_interior_before_radial (S : OddScale)
    (r r' : (RawOne S).Q) (x : (RawOne S).X)
    (hx : (RawOne S).xq x r=true) (hx' : (RawOne S).xq x r'=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r' z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) (k : Fin S.half)
    (hrr : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hik : i.val<k.val) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz S
        (.inl (c,(⟨x,hx'⟩,k)))⟩)) := by
  have hn := interior_before_later_radial_code
    (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    i.val k.val c hrr hik
  exact (encoded_interior S r x hx c i).trans_lt
    (hn.trans_eq (encoded_radial_image S r' x hx' z hz c k).symm)

private theorem actualGlobal_zero_of_encoded_kernel (S : OddScale)
    (a k : Word F (levelTwoPresentation S).Q) (q : (levelTwoPresentation S).Q)
    (hk : tannerCoboundary1 (levelTwoPresentation S) k=0) (hq : k q=1)
    (hp : ∀ p, Encodable.encode (executableCoordinate S p)<
      Encodable.encode (executableCoordinate S q) → k p=0) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a) q=0 := by
  have hkernel : BDL26GlobalLookupLinearity.executableLinear S
      (BDL26LevelTwoDecoder.toExecutableError S k)=0 := by
    rw [BDL26GlobalLookupLinearity.executableLinear_actual,hk]
    rfl
  have hpoint : BDL26LevelTwoDecoder.toExecutableError S k (executableCoordinate S q)=1 := by
    simpa [BDL26LevelTwoDecoder.toExecutableError,executableCoordinate] using hq
  have hprefix (p : BDL26LevelTwoDecoder.ExecutableQ S)
      (h : Encodable.encode p<Encodable.encode (executableCoordinate S q)) :
      BDL26LevelTwoDecoder.toExecutableError S k p=0 := by
    apply hp (cast (BDL26LevelTwoDecoder.executableQ_eq S) p)
    simpa [executableCoordinate] using h
  have h := global_zero_of_encoded_kernel
    (BDL26GlobalLookupLinearity.executableLinear S)
    (BDL26LevelTwoDecoder.toExecutableError S a) (executableCoordinate S q)
    (BDL26LevelTwoDecoder.toExecutableError S k) hkernel hprefix hpoint
  change BDL26GlobalLookupLinearity.executableGlobal S
    (BDL26LevelTwoDecoder.toExecutableSyndrome S
      (tannerCoboundary1 (levelTwoPresentation S) a)) (executableCoordinate S q)=0
  rw [← BDL26GlobalLookupLinearity.executableLinear_actual S a]
  exact h

private theorem actualGlobal_zero_of_first_actual_star_coordinate (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (x : (levelTwoPresentation S).X)
    (q : (levelTwoPresentation S).Q) (hxq : (levelTwoPresentation S).xq x q=true)
    (hfirst : ∀ p, (levelTwoPresentation S).xq x p=true → p≠q →
      Encodable.encode (executableCoordinate S q)<Encodable.encode (executableCoordinate S p)) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a) q=0 := by
  let k := tannerCoboundary0 (levelTwoPresentation S) (canonicalBasisWord (F:=F) x)
  apply actualGlobal_zero_of_encoded_kernel S a k q
  · have h := LinearMap.congr_fun
      (BDL26LevelTwoDistance.tannerCoboundary_squared (levelTwoPresentation S))
        (canonicalBasisWord (F:=F) x)
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply,k] using h
  · dsimp only [k]
    rw [tannerCoboundary0_canonicalBasis_apply,if_pos hxq]
  · intro p hlt
    dsimp only [k]
    rw [tannerCoboundary0_canonicalBasis_apply]
    apply if_neg
    intro hxp
    by_cases he : p=q
    · subst p
      exact (Nat.lt_irrefl _ hlt)
    · have hgt := hfirst p hxp he
      exact (Nat.lt_asymm hlt hgt)

private theorem xq_heq {U V : TannerSquarePresentation} (h : U=V) :
    HEq U.xq V.xq := by cases h; rfl

private theorem actual_raw_xq (S : OddScale) :
    ((levelTwoPresentation S).xq : (RawTwo S).X → (RawTwo S).Q → Bool)=
      (RawTwo S).xq :=
  eq_of_heq (xq_heq (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))

private theorem actualGlobal_zero_of_first_star_coordinate (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (x : (RawTwo S).X)
    (q : (RawTwo S).Q) (hxq : (RawTwo S).xq x q=true)
    (hfirst : ∀ p, (RawTwo S).xq x p=true → p≠q →
      Encodable.encode (executableCoordinate S q)<Encodable.encode (executableCoordinate S p)) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a) q=0 := by
  apply actualGlobal_zero_of_first_actual_star_coordinate S a x q
  · exact (congrFun (congrFun (actual_raw_xq S) x) q).trans hxq
  · intro p hp hn
    exact hfirst p ((congrFun (congrFun (actual_raw_xq S) x) p).symm.trans hp) hn

private theorem qedge_local_incidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q)
    (e : QDoubleCylinderEdge (transposePresentation P) r S)
    (z : P.Z) (d : ZDoubleCylinderEdge P z S) :
    rzXQIncidence P A S (.inl (.inr ⟨r,e⟩)) (.inl ⟨z,d⟩)=true ↔
      ∃ hz : P.qz r z=true, qToZDoubleCylinderEdge P A r z hz S e=d := by
  classical
  change decide (∃ hz : P.qz r z=true,
    qToZDoubleCylinderEdge P A r z hz S e=d)=true ↔ _
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

private theorem qedge_port_incidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q)
    (e : QDoubleCylinderEdge (transposePresentation P) r S)
    (r' : P.Q) (v : QDoubleCylinderVertex (transposePresentation P) r' S) :
    rzXQIncidence P A S (.inl (.inr ⟨r,e⟩)) (.inr ⟨r',v⟩)=true ↔
      ∃ h : r'=r,
        h ▸ v=qDoubleCylinderEdgeStart (transposePresentation P) r S e ∨
        h ▸ v=qDoubleCylinderEdgeEnd (transposePresentation P) r S e := by
  classical
  change decide (∃ h : r'=r,
    h ▸ v=qDoubleCylinderEdgeStart (transposePresentation P) r S e ∨
    h ▸ v=qDoubleCylinderEdgeEnd (transposePresentation P) r S e)=true ↔ _
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

private theorem qedge_star_cases (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q)
    (e : QDoubleCylinderEdge (transposePresentation P) r S) (p : RZQ P S)
    (hp : rzXQIncidence P A S (.inl (.inr ⟨r,e⟩)) p=true) :
    (∃ (z : P.Z) (hz : P.qz r z=true),
      p=.inl ⟨z,qToZDoubleCylinderEdge P A r z hz S e⟩) ∨
      p=.inr ⟨r,qDoubleCylinderEdgeStart (transposePresentation P) r S e⟩ ∨
      p=.inr ⟨r,qDoubleCylinderEdgeEnd (transposePresentation P) r S e⟩ := by
  rcases p with ⟨z,d⟩ | ⟨r',v⟩
  · obtain ⟨hz,hd⟩ := (qedge_local_incidence P A S r e z d).mp hp
    exact Or.inl ⟨z,hz,congrArg (fun edge => Sum.inl (Sigma.mk z edge)) hd.symm⟩
  · obtain ⟨hr,hv⟩ := (qedge_port_incidence P A S r e r' v).mp hp
    subst r'
    rcases hv with hv | hv
    · exact Or.inr (Or.inl (congrArg (fun vertex => Sum.inr (Sigma.mk r vertex)) hv))
    · exact Or.inr (Or.inr (congrArg (fun vertex => Sum.inr (Sigma.mk r vertex)) hv))

private theorem q_segment_end_last (P : TannerSquarePresentation) (S : OddScale)
    (r : P.Q) (e : QStarEdge P r) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (h : i.val+1=S.half) :
    qDoubleCylinderEdgeEnd P r S (.inl (c,(e,i)))=(c,.inl (qStarEdgeEnd P r e)) := by
  simp only [qDoubleCylinderEdgeEnd,qSubdivisionEdgeEnd,dif_pos h]

private theorem q_segment_end_inner (P : TannerSquarePresentation) (S : OddScale)
    (r : P.Q) (e : QStarEdge P r) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (h : i.val+1≠S.half) :
    qDoubleCylinderEdgeEnd P r S (.inl (c,(e,i)))=
      (c,.inr (e,⟨i.val,by have := i.isLt; omega⟩)) := by
  simp only [qDoubleCylinderEdgeEnd,qSubdivisionEdgeEnd,dif_neg h]

private def firstQEdge (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    QDoubleCylinderEdge (transposePresentation (RawOne S)) r S :=
  .inl (c,(⟨x,hx⟩,⟨0,S.half_pos⟩))

private theorem firstQEdge_start (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    qDoubleCylinderEdgeStart (transposePresentation (RawOne S)) r S
      (firstQEdge S r x hx c)=(c,.inl (.inl ())) := by
  simp [firstQEdge,qDoubleCylinderEdgeStart,qSubdivisionEdgeStart,qStarEdgeStart]

private theorem cone_before_firstQEdge_end (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inl (.inl ()))⟩)) <
      Encodable.encode (executableCoordinate S
        (.inr ⟨r,qDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) r S
          (firstQEdge S r x hx c)⟩)) := by
  by_cases h : S.half=1
  · have he : qDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) r S
        (firstQEdge S r x hx c)=(c,.inl (.inr ⟨x,hx⟩)) :=
      q_segment_end_last (transposePresentation (RawOne S)) S r ⟨x,hx⟩ c
        ⟨0,S.half_pos⟩ (by simpa only [Fin.val_mk,zero_add] using h.symm)
    have hnumber := cone_before_vertex_code
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) c
      (2*(2*Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1))
      (by omega)
    have hbound := (encoded_cone S r c).trans_lt
      (hnumber.trans_eq (encoded_endpoint S r x hx c).symm)
    exact hbound.trans_eq (congrArg (fun v =>
      Encodable.encode (executableCoordinate S (.inr ⟨r,v⟩))) he).symm
  · let i : Fin (S.half-1) := ⟨0,by have := S.half_pos; omega⟩
    have he : qDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) r S
        (firstQEdge S r x hx c)=(c,.inr (⟨x,hx⟩,i)) :=
      q_segment_end_inner (transposePresentation (RawOne S)) S r ⟨x,hx⟩ c
        ⟨0,S.half_pos⟩ (by change 0+1≠S.half; simpa only [zero_add] using Ne.symm h)
    have hnumber := cone_before_vertex_code
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) c
      (2*Nat.pair (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1)
      (by omega)
    have hbound := (encoded_cone S r c).trans_lt
      (hnumber.trans_eq (encoded_interior S r x hx c i).symm)
    exact hbound.trans_eq (congrArg (fun v =>
      Encodable.encode (executableCoordinate S (.inr ⟨r,v⟩))) he).symm

private theorem cone_before_first_image (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inl (.inl ()))⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (firstQEdge S r x hx c)⟩)) := by
  have hn := cone_before_radial_code
    (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z)) c
  exact (encoded_cone S r c).trans_lt
    (hn.trans_eq (encoded_radial_image S r x hx z hz c ⟨0,S.half_pos⟩).symm)

/-- A genuine Q-cone is forced to zero by the original global lookup order.
The lowering kernel is the full actual Q-edge coboundary, including its Z bits. -/
theorem global_cone_zero (S : OddScale) (a : Word F (levelTwoPresentation S).Q)
    (r : (RawOne S).Q) (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨r,(c,.inl (.inl ()))⟩)=0 := by
  let e := firstQEdge S r x hx c
  apply actualGlobal_zero_of_first_star_coordinate S a (.inl (.inr ⟨r,e⟩))
    (.inr ⟨r,(c,.inl (.inl ()))⟩)
  · apply (qedge_port_incidence (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S r e r
      (c,Sum.inl (Sum.inl ()))).mpr
    exact ⟨rfl,Or.inl (firstQEdge_start S r x hx c).symm⟩
  · intro p hi hn
    rcases qedge_star_cases (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible S r e p hi with
      ⟨z,hz,he⟩ | he | he
    · have hcode := congrArg (fun q : (RawTwo S).Q =>
        Encodable.encode (executableCoordinate S q)) he
      exact (cone_before_first_image S r x hx z hz c).trans_eq hcode.symm
    · have hstart := congrArg (fun vertex : QDoubleCylinderVertex
          (transposePresentation (RawOne S)) r S => (Sum.inr ⟨r,vertex⟩ : (RawTwo S).Q))
        (firstQEdge_start S r x hx c)
      exact False.elim (hn (he.trans hstart))
    · have hcode := congrArg (fun q : (RawTwo S).Q =>
        Encodable.encode (executableCoordinate S q)) he
      exact (cone_before_firstQEdge_end S r x hx c).trans_eq hcode.symm

private theorem encoded_endpoint_lt (S : OddScale) (r r' : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (hx' : (RawOne S).xq x r'=true) (c : BDL26FiniteTannerSquare.Two)
    (hlt : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) :
    Encodable.encode (executableCoordinate S (Sum.inr ⟨r,(c,Sum.inl (Sum.inr ⟨x,hx⟩))⟩))<
      Encodable.encode (executableCoordinate S (Sum.inr ⟨r',(c,Sum.inl (Sum.inr ⟨x,hx'⟩))⟩)) := by
  have hpair := Nat.pair_lt_pair_left
    (Nat.pair c.val
      (2*(2*Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1))) hlt
  have hnumber :
      2*Nat.pair (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val (2*(2*Encodable.encode
          (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1 <
      2*Nat.pair (Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val (2*(2*Encodable.encode
          (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1 := by omega
  exact (encoded_endpoint S r x hx c).trans_lt
    (hnumber.trans_eq (encoded_endpoint S r' x hx' c).symm)

private theorem global_endpoint_of_least_old_neighbor (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two)
    (hmin : ∀ r' : (RawOne S).Q, (RawOne S).xq x r'=true → r'≠r →
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
        Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩)=0 := by
  apply actualGlobal_zero_of_first_star_coordinate S a (.inr (x,c))
    (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩)
  · exact (BDL26ReplacementCochainMaps.rzOldX_incidence_iff (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S x c
      (Sum.inr ⟨r,(c,Sum.inl (Sum.inr ⟨x,hx⟩))⟩)).mpr ⟨r,hx,rfl⟩
  · intro p hi hn
    change rzXQIncidence (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S (.inr (x,c)) p=true at hi
    obtain ⟨r',hx',hp⟩ :=
      (BDL26ReplacementCochainMaps.rzOldX_incidence_iff _ _ _ _ _ _).mp hi
    have hne : r'≠r := by
      intro he
      subst r'
      exact hn hp
    have hlt := encoded_endpoint_lt S r r' x hx hx' c (hmin r' hx' hne)
    have hcoordinate := congrArg (fun p : (RawTwo S).Q =>
      Encodable.encode (executableCoordinate S p)) hp
    exact hlt.trans_eq hcoordinate.symm

private def firstRadialQ (S : OddScale) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial 0,⟨0,S.half_pos⟩))⟩

/-- The first literal radial coordinate has derived endpoint normalization in
both copies; no coordinate-minimality certificate is an input. -/
private theorem global_first_radial_endpoint_zero (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (x : (RawOne S).X)
    (hx : (RawOne S).xq x
      (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial 0,⟨0,S.half_pos⟩))⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial 0,⟨0,S.half_pos⟩))⟩,
        (c,.inl (.inr ⟨x,hx⟩))⟩)=0 := by
  apply global_endpoint_of_least_old_neighbor S a (firstRadialQ S) x hx c
  intro r' hx' hn
  have hz : Encodable.encode
      (firstRadialQ S : (BDL26LevelTwoDecoder.executableLevelOne S).Q)=0 := by rfl
  have hne : Encodable.encode
      (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≠0 := by
    intro he
    apply hn
    exact Encodable.encode_injective (he.trans hz.symm)
  omega

private def lastSegment (S : OddScale) : Fin S.half :=
  ⟨S.half-1,by have := S.half_pos; omega⟩

private def lastQEdge (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    QDoubleCylinderEdge (transposePresentation (RawOne S)) r S :=
  .inl (c,(⟨x,hx⟩,⟨S.half-1,by have := S.half_pos; omega⟩))

private def lastInterior (S : OddScale) (h : 2≤S.half) : Fin (S.half-1) :=
  ⟨S.half-2,by omega⟩

private theorem lastQEdge_start (S : OddScale) (h : 2≤S.half)
    (r : (RawOne S).Q) (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    qDoubleCylinderEdgeStart (transposePresentation (RawOne S)) r S
      (lastQEdge S r x hx c)=(c,.inr (⟨x,hx⟩,lastInterior S h)) := by
  change (c,if hn : S.half-1=0 then _ else _)=_
  rw [dif_neg (by omega)]
  congr 2 <;> (apply Fin.ext; dsimp [lastInterior]; omega)

private theorem lastQEdge_end (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) :
    qDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) r S
      (lastQEdge S r x hx c)=(c,.inl (.inr ⟨x,hx⟩)) := by
  have hlast : S.half-1+1=S.half := by have := S.half_pos; omega
  simp [lastQEdge,qDoubleCylinderEdgeEnd,qSubdivisionEdgeEnd,hlast,qStarEdgeEnd]

private def shiftedOldXPotential (S : OddScale) (x : (RawOne S).X)
    (c : BDL26FiniteTannerSquare.Two) : Word F (RawTwo S).X :=
  canonicalBasisWord (.inr (x,c)) +
    ∑ r : (RawOne S).Q, if hx : (RawOne S).xq x r=true then
      canonicalBasisWord (.inl (.inr ⟨r,lastQEdge S r x hx c⟩)) else 0

private theorem shiftedOldXBoundary_eq (S : OddScale) (h : 2≤S.half)
    (x : (RawOne S).X) (c : BDL26FiniteTannerSquare.Two) :
    tannerCoboundary0 (RawTwo S) (shiftedOldXPotential S x c)=
      ∑ r : (RawOne S).Q, if hx : (RawOne S).xq x r=true then
        canonicalBasisWord (F:=F) (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩) +
          ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r z=true then
            canonicalBasisWord (F:=F) (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
              (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
              (lastQEdge S r x hx c)⟩) else 0
      else 0 := by
  apply mapped_shifted_sum_cancel (tannerCoboundary0 (RawTwo S))
    (canonicalBasisWord (F:=F) (.inr (x,c)))
    (fun r : (RawOne S).Q => (RawOne S).xq x r=true)
    (fun r hx => canonicalBasisWord (F:=F) (.inl (.inr ⟨r,lastQEdge S r x hx c⟩)))
    (fun r hx => canonicalBasisWord (F:=F) (.inr ⟨r,(c,.inl (.inr ⟨x,hx⟩))⟩))
    (fun r hx => canonicalBasisWord (F:=F) (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩))
    (fun r hx => ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r z=true then
      canonicalBasisWord (F:=F) (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (lastQEdge S r x hx c)⟩) else 0)
  · exact BDL26ReplacementCochainMaps.rzOldX_delta0 (RawOne S)
      (rxState S baseState).admissible S x c
  · intro r hx
    have hedge := rzMap1QEdge_delta0_canonicalBasis (RawOne S)
      (rxState S baseState).admissible S r (lastQEdge S r x hx c)
    change tannerCoboundary0 (RawTwo S)
      (canonicalBasisWord (F:=F) (.inl (.inr ⟨r,lastQEdge S r x hx c⟩)))=_ at hedge
    apply hedge.trans
    dsimp only [rzMap1QEdgeDelta0BasisImage]
    erw [lastQEdge_start S h r x hx c,lastQEdge_end S r x hx c]
    all_goals rfl

private def interiorQEdge (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    QDoubleCylinderEdge (transposePresentation (RawOne S)) r S :=
  .inl (c,(⟨x,hx⟩,⟨i.val+1,by have := i.isLt; omega⟩))

private theorem interiorQEdge_start (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    qDoubleCylinderEdgeStart (transposePresentation (RawOne S)) r S
      (interiorQEdge S r x hx c i)=(c,.inr (⟨x,hx⟩,i)) := by
  simp [interiorQEdge,qDoubleCylinderEdgeStart,qSubdivisionEdgeStart]

private theorem interiorQEdge_end (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1))
    (hi : i.val+2<S.half) :
    qDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) r S
      (interiorQEdge S r x hx c i)=
        (c,.inr (⟨x,hx⟩,⟨i.val+1,by omega⟩)) := by
  have hnot : i.val+1+1≠S.half := by omega
  simp [interiorQEdge,qDoubleCylinderEdgeEnd,qSubdivisionEdgeEnd,hnot]

private theorem encoded_interior_index_lt (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i j : Fin (S.half-1)) (hij : i.val<j.val) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,(c,.inr (⟨x,hx⟩,j))⟩)) := by
  have hinner := Nat.pair_lt_pair_right
    (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) hij
  have hmiddle := Nat.pair_lt_pair_right c.val
    (show 2*Nat.pair (Encodable.encode (x :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1 <
      2*Nat.pair (Encodable.encode (x :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) j.val+1 by omega)
  have houter := Nat.pair_lt_pair_right
    (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) hmiddle
  have hn : 2*Nat.pair
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
      (Nat.pair c.val (2*Nat.pair
        (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 <
      2*Nat.pair (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
      (Nat.pair c.val (2*Nat.pair
        (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)) j.val+1))+1 := by omega
  exact (encoded_interior S r x hx c i).trans_lt
    (hn.trans_eq (encoded_interior S r x hx c j).symm)

/-- Every nonterminal Q-ray interior has its own actual leading coboundary.
This statement holds for arbitrary scale and interior index, in both copies. -/
theorem global_interior_zero_before_last (S : OddScale)
    (a : Word F (levelTwoPresentation S).Q) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1))
    (hi : i.val+2<S.half) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩)=0 := by
  let e := interiorQEdge S r x hx c i
  apply actualGlobal_zero_of_first_star_coordinate S a (.inl (.inr ⟨r,e⟩))
    (.inr ⟨r,(c,.inr (⟨x,hx⟩,i))⟩)
  · apply (qedge_port_incidence (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S r e r
      (c,Sum.inr (⟨x,hx⟩,i))).mpr
    exact ⟨rfl,Or.inl (interiorQEdge_start S r x hx c i).symm⟩
  · intro p hp hn
    rcases qedge_star_cases (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible S r e p hp with
      ⟨z,hz,he⟩ | he | he
    · have hcode := congrArg (fun q : (RawTwo S).Q =>
        Encodable.encode (executableCoordinate S q)) he
      have hlate := encoded_interior_before_radial S r r x hx hx z hz c i
        ⟨i.val+1,by omega⟩ le_rfl (by change i.val < i.val+1; omega)
      exact hlate.trans_eq hcode.symm
    · have hstart := congrArg (fun vertex : QDoubleCylinderVertex
          (transposePresentation (RawOne S)) r S => (Sum.inr ⟨r,vertex⟩ : (RawTwo S).Q))
        (interiorQEdge_start S r x hx c i)
      exact False.elim (hn (he.trans hstart))
    · have hcode := congrArg (fun q : (RawTwo S).Q =>
        Encodable.encode (executableCoordinate S q)) he
      have hend := congrArg (fun vertex : QDoubleCylinderVertex
          (transposePresentation (RawOne S)) r S =>
        Encodable.encode (executableCoordinate S (.inr ⟨r,vertex⟩)))
        (interiorQEdge_end S r x hx c i hi)
      have hlate := encoded_interior_index_lt S r x hx c i ⟨i.val+1,by omega⟩ (by change i.val < i.val+1; omega)
      exact (hlate.trans_eq hend.symm).trans_eq hcode.symm

private theorem global_last_interior_of_least_old_neighbor (S : OddScale)
    (h : 2≤S.half) (a : Word F (levelTwoPresentation S).Q) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two)
    (hmin : ∀ r' : (RawOne S).Q, (RawOne S).xq x r'=true → r'≠r →
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
        Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a)
      (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)=0 := by
  let k := tannerCoboundary0 (RawTwo S) (shiftedOldXPotential S x c)
  have hrle (r' : (RawOne S).Q) (hx' : (RawOne S).xq x r'=true) :
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
        Encodable.encode (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
    by_cases he : r'=r
    · subst r'; exact le_rfl
    · exact (hmin r' hx' he).le
  apply actualGlobal_zero_of_encoded_kernel S a k
    (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)
  · have hs := LinearMap.congr_fun
      (BDL26LevelTwoDistance.tannerCoboundary_squared (RawTwo S))
        (shiftedOldXPotential S x c)
    change tannerCoboundary1 (RawTwo S) k=0
    change tannerCoboundary1 (RawTwo S)
      (tannerCoboundary0 (RawTwo S) (shiftedOldXPotential S x c))=0 at hs
    exact hs
  · have hvalue := congrFun (shiftedOldXBoundary_eq S h x c)
      (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)
    apply hvalue.trans
    erw [conditional_word_sum_apply,Finset.sum_eq_single r]
    · erw [dif_pos hx]
      have hlocal := disjoint_conditional_basis_apply
        (fun z : (RawOne S).Z => (RawOne S).qz r z=true)
        (fun z hz => (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
          (lastQEdge S r x hx c)⟩ : (RawTwo S).Q))
        (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)
        (by intro z hz he; cases he)
      exact (generic_basis_plus_value _ _ _ hlocal).trans (if_pos rfl)
    · intro r' _ hn
      by_cases hx' : (RawOne S).xq x r'=true
      · erw [dif_pos hx']
        have hlocal := disjoint_conditional_basis_apply
          (fun z : (RawOne S).Z => (RawOne S).qz r' z=true)
          (fun z hz => (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
            (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz S
            (lastQEdge S r' x hx' c)⟩ : (RawTwo S).Q))
          (.inr ⟨r,(c,.inr (⟨x,hx⟩,lastInterior S h))⟩)
          (by intro z hz he; cases he)
        have hne : (Sum.inr ⟨r,(c,Sum.inr (⟨x,hx⟩,lastInterior S h))⟩ : (RawTwo S).Q)≠
            Sum.inr ⟨r',(c,Sum.inr (⟨x,hx'⟩,lastInterior S h))⟩ := by
          intro he
          exact hn (congrArg Sigma.fst (Sum.inr.inj he)).symm
        exact (generic_basis_plus_value _ _ _ hlocal).trans (if_neg hne)
      · simp only [dif_neg hx',word_zero_eval]
    · intro hn
      exact False.elim (hn (Finset.mem_univ r))
  · intro p hprefix
    have hvalue := congrFun (shiftedOldXBoundary_eq S h x c) p
    apply hvalue.trans
    erw [conditional_word_sum_apply]
    apply Finset.sum_eq_zero
    intro r' _
    by_cases hx' : (RawOne S).xq x r'=true
    · erw [dif_pos hx']
      have hQ : p≠(.inr ⟨r',(c,.inr (⟨x,hx'⟩,lastInterior S h))⟩ : (RawTwo S).Q) := by
        intro he
        have hcode := congrArg (fun q : (RawTwo S).Q =>
          Encodable.encode (executableCoordinate S q)) he
        have hbefore := hcode.symm.trans_lt hprefix
        by_cases hrr : r'=r
        · subst r'
          exact Nat.lt_irrefl _ hbefore
        · exact Nat.lt_asymm hbefore
            (encoded_interior_lt S r r' x hx hx' c (lastInterior S h) (hmin r' hx' hrr))
      have hlocal := disjoint_conditional_basis_apply
        (fun z : (RawOne S).Z => (RawOne S).qz r' z=true)
        (fun z hz => (.inl ⟨z,qToZDoubleCylinderEdge (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz S
          (lastQEdge S r' x hx' c)⟩ : (RawTwo S).Q)) p (by
          intro z hz he
          have hcode := congrArg (fun q : (RawTwo S).Q =>
            Encodable.encode (executableCoordinate S q)) he
          have hlate := encoded_interior_before_radial S r r' x hx hx' z hz c
            (lastInterior S h) (lastSegment S) (hrle r' hx') (by
              dsimp [lastInterior,lastSegment]
              omega)
          exact Nat.lt_asymm (hcode.symm.trans_lt hprefix) hlate)
      exact (generic_basis_plus_value _ _ _ hlocal).trans (if_neg hQ)
    · simp only [dif_neg hx',word_zero_eval]

private theorem linear_add_zero {I : Type} (L : Word F I →ₗ[F] F)
    (a b : Word F I) (ha : L a=0) (hb : L b=0) : L (a+b)=0 := by
  rw [map_add,ha,hb,zero_add]

private theorem word_base_pair {I : Type} (a b c d : Word F I)
    (hb : b=0) (hc : c=d) : a+d=a+b+c := by
  rw [hb,hc,add_zero]

private def closed_word_cocycle (P : TannerSquarePresentation) (w : Word F P.Q)
    (hw : tannerCoboundary1 P w=0) : BDL26RZCohomology.Cocycle P :=
  ⟨w,(BDL26RZCohomology.mem_cocycle_iff P w).mpr hw⟩

private theorem fallback_base_boundary_of_global_dual_zero (S : OddScale) (N : Nat)
    (u : XSyndromeDomain S N) (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (hs : firstReadout S N u=0)
    (hn : BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S N u q)=none)
    (hg : dualReadout S (BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) (descent S N u q).word))=0) :
    ∃ p0 : (SuffixData S N).family.Cochain0 0,
      (SuffixData S N).family.coboundary0 0 p0=
        (descent S N u q).word+
          (actualBase S N).decode (actualInputs S N (input S N u) 0)+
          (actualBase S N).decode (actualInputs S N
            (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q)) 0) := by
  let h : Word F (levelTwoPresentation S).Q := (descent S N u q).word
  let w : FC.Cocycle S 2 := closed_word_cocycle (levelTwoPresentation S)
    (h+BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) h))
    (BDL26GlobalLookupLinearity.actualGlobal_residual S h)
  have hw : dualReadout S w.val=0 :=
    linear_add_zero (dualReadout S) h
      (BDL26GlobalLookupLinearity.actualGlobal S
        (tannerCoboundary1 (levelTwoPresentation S) h))
      (failed_search_terminal_dual_zero S N u q a hp hs hn) hg
  obtain ⟨p0,hp0⟩ := dualReadout_zero_boundary S w hw
  have hfirst : (actualBase S N).decode (actualInputs S N (input S N u) 0)=0 :=
    (first_base_original_D S N u).trans
      ((congrArg (BDL26LevelTwoDecoder.decode S) hs).trans
        (BDL26LevelTwoDecoder.decode_zero S))
  have hdecode := BDL26GlobalLookupLinearity.decode_of_local_none S
    (secondReadout S N u q) hn
  have hsecond : (actualBase S N).decode (actualInputs S N
      (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q)) 0)=
      BDL26GlobalLookupLinearity.actualGlobal S
        (tannerCoboundary1 (levelTwoPresentation S) h) := by
    exact (second_base_original_D S N u q).trans
      (hdecode.trans (congrArg (BDL26GlobalLookupLinearity.actualGlobal S)
        (BDL26FirstZeroFaceEndpoint.terminal_syndrome S N u q hs).symm))
  refine ⟨p0,?_⟩
  rw [suffix_delta0]
  exact hp0.trans (word_base_pair h _ _ _ hfirst hsecond)

private theorem full_endpoint_of_base_boundary (S : OddScale) (N : Nat)
    (u : XSyndromeDomain S N) (q : Physical S (N+2))
    (p0 : (SuffixData S N).family.Cochain0 0)
    (hp0 : (SuffixData S N).family.coboundary0 0 p0=
      (descent S N u q).word+
        (actualBase S N).decode (actualInputs S N (input S N u) 0)+
        (actualBase S N).decode (actualInputs S N
          (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q)) 0)) :
    ∃ p : (SuffixData S N).family.Cochain0 (TopIndex N),
      p=intervalMap0 (SuffixData S N) 0 (TopIndex N) (Nat.zero_le _) p0+
        accumulated S N u q ∧
      (SuffixData S N).family.coboundary0 (TopIndex N) p=
        BDL26LogicalDefectProtection.deltaX S N u q ∧
      (SuffixData S N).family.coboundary0 (TopIndex N) p=
        BDL26ActualFailureReadout.flip S N q+xCorrection S N u+
          xCorrection S N (translateX S N u (BDL26ActualFailureReadout.flip S N q)) ∧
      BDL26LogicalDefectProtection.chiX S N u q=0 := by
  let p := intervalMap0 (SuffixData S N) 0 (TopIndex N) (Nat.zero_le _) p0+
    accumulated S N u q
  have htop : (SuffixData S N).family.coboundary0 (TopIndex N) p=
      BDL26LogicalDefectProtection.deltaX S N u q := by
    dsimp only [p]
    have hcomm := intervalMap_commutes0 (SuffixData S N) N (Nat.le_refl _)
      (0 : StepIndex (N+1)) (Nat.zero_le _) p0
    rw [map_add]
    exact (congrArg (fun w => w+
      (SuffixData S N).family.coboundary0 (TopIndex N) (accumulated S N u q))
      (hcomm.trans (congrArg (intervalMap1 (SuffixData S N) 0 (TopIndex N) (Nat.zero_le _)) hp0))).trans
        (full_history S N u q).symm
  refine ⟨p,rfl,htop,?_,?_⟩
  · rw [htop]
    unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
    ac_rfl
  · rw [chiX_top_coefficient]
    apply (top_zero_iff_boundary S N (input S N u) (BDL26ActualFailureReadout.flip S N q)).mpr
    refine ⟨p,?_⟩
    rw [full_residual]
    exact htop

private def gridAt (S : OddScale) (n : Nat) (h : n≤S.half) : Fin (S.half+1) :=
  ⟨n,by omega⟩

private noncomputable def verticalAtColumnPath (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (column : Fin (S.half+1)) :
    (n : Nat) → (hn : n≤S.half) →
      UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S f column 0)
        (subdivisionGridVertex P x S f column (gridAt S n hn))
  | 0,_ => .nil
  | n+1,hn => by
    let k : Fin S.half := ⟨n,by omega⟩
    apply UndirectedPath.step (verticalAtColumnPath P x S f column n (by omega))
      (subdivisionVerticalEdge P x S f column k)
    apply Or.inl
    constructor
    · exact own_vertical_start P x S f column k
    · exact own_vertical_end P x S f column k

private noncomputable def horizontalAtRowPath (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (row : Fin (S.half+1)) :
    (n : Nat) → (hn : n≤S.half) →
      UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S f 0 row)
        (subdivisionGridVertex P x S f (gridAt S n hn) row)
  | 0,_ => .nil
  | n+1,hn => by
    let k : Fin S.half := ⟨n,by omega⟩
    apply UndirectedPath.step (horizontalAtRowPath P x S f row n (by omega))
      (subdivisionHorizontalEdge P x S f k row)
    apply Or.inl
    constructor
    · exact own_horizontal_start P x S f k row
    · exact own_horizontal_end P x S f k row

private theorem verticalAtColumnPath_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (column : Fin (S.half+1))
    (n : Nat) (hn : n≤S.half) (e : SubdivisionEdge P x S)
    (he : pathChain (verticalAtColumnPath P x S f column n hn) e≠0) :
    ∃ k : Fin S.half, k.val<n ∧ e=subdivisionVerticalEdge P x S f column k := by
  revert hn
  induction n with
  | zero => intro hn he; simp [verticalAtColumnPath,pathChain] at he
  | succ n ih =>
    intro hn he
    let k : Fin S.half := ⟨n,by omega⟩
    have hs : pathChain (verticalAtColumnPath P x S f column (n+1) hn)=
        pathChain (verticalAtColumnPath P x S f column n (by omega))+
          Pi.single (subdivisionVerticalEdge P x S f column k) (1:F) := rfl
    rw [hs,Pi.add_apply] at he
    by_cases hp : pathChain (verticalAtColumnPath P x S f column n (by omega)) e=0
    · rw [hp,zero_add,Pi.single_apply] at he
      by_cases hq : e=subdivisionVerticalEdge P x S f column k
      · exact ⟨k,by dsimp [k]; omega,hq⟩
      · exact False.elim (he (if_neg hq))
    · obtain ⟨k,hk,hq⟩ := ih (by omega) hp
      exact ⟨k,by omega,hq⟩

private theorem horizontalAtRowPath_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (row : Fin (S.half+1))
    (n : Nat) (hn : n≤S.half) (e : SubdivisionEdge P x S)
    (he : pathChain (horizontalAtRowPath P x S f row n hn) e≠0) :
    ∃ k : Fin S.half, k.val<n ∧ e=subdivisionHorizontalEdge P x S f k row := by
  revert hn
  induction n with
  | zero => intro hn he; simp [horizontalAtRowPath,pathChain] at he
  | succ n ih =>
    intro hn he
    let k : Fin S.half := ⟨n,by omega⟩
    have hs : pathChain (horizontalAtRowPath P x S f row (n+1) hn)=
        pathChain (horizontalAtRowPath P x S f row n (by omega))+
          Pi.single (subdivisionHorizontalEdge P x S f k row) (1:F) := rfl
    rw [hs,Pi.add_apply] at he
    by_cases hp : pathChain (horizontalAtRowPath P x S f row n (by omega)) e=0
    · rw [hp,zero_add,Pi.single_apply] at he
      by_cases hq : e=subdivisionHorizontalEdge P x S f k row
      · exact ⟨k,by dsimp [k]; omega,hq⟩
      · exact False.elim (he (if_neg hq))
    · obtain ⟨k,hk,hq⟩ := ih (by omega) hp
      exact ⟨k,by omega,hq⟩

private def lastGridInterior (S : OddScale) : Fin (S.half+1) :=
  ⟨S.half-1,by omega⟩

private noncomputable def shiftedFacePath0 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin (S.half-1)) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f (lastGridInterior S) 0)
      (subdivisionGridVertex P x S f (gridAt S S.half le_rfl)
        (gridAt S (i.val+1) (by have := i.isLt; omega))) := by
  let t := gridAt S (i.val+1) (by have := i.isLt; omega)
  apply UndirectedPath.step
    (verticalAtColumnPath P x S f (lastGridInterior S) (i.val+1)
      (by have := i.isLt; omega))
    (subdivisionHorizontalEdge P x S f (lastSegment S) t)
  apply Or.inl
  constructor
  · have hs : subdivisionEdgeStart P x S
        (subdivisionHorizontalEdge P x S f (lastSegment S) t)=
        subdivisionGridVertex P x S f (finCastGrid (lastSegment S)) t :=
      own_horizontal_start P x S f (lastSegment S) t
    exact hs.trans (congrArg (fun v => subdivisionGridVertex P x S f v t)
      (show finCastGrid (lastSegment S)=lastGridInterior S from rfl))
  · have hs : subdivisionEdgeEnd P x S
        (subdivisionHorizontalEdge P x S f (lastSegment S) t)=
        subdivisionGridVertex P x S f (finSuccGrid (lastSegment S)) t :=
      own_horizontal_end P x S f (lastSegment S) t
    exact hs.trans (congrArg (fun v => subdivisionGridVertex P x S f v t)
      (by apply Fin.ext; dsimp [finSuccGrid,lastSegment,gridAt]; have := S.half_pos; omega))

private noncomputable def shiftedFacePath1 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin (S.half-1)) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f 0 (lastGridInterior S))
      (subdivisionGridVertex P x S f
        (gridAt S (i.val+1) (by have := i.isLt; omega)) (gridAt S S.half le_rfl)) := by
  let t := gridAt S (i.val+1) (by have := i.isLt; omega)
  apply UndirectedPath.step
    (horizontalAtRowPath P x S f (lastGridInterior S) (i.val+1)
      (by have := i.isLt; omega))
    (subdivisionVerticalEdge P x S f t (lastSegment S))
  apply Or.inl
  constructor
  · have hs : subdivisionEdgeStart P x S
        (subdivisionVerticalEdge P x S f t (lastSegment S))=
        subdivisionGridVertex P x S f t (finCastGrid (lastSegment S)) :=
      own_vertical_start P x S f t (lastSegment S)
    exact hs.trans (congrArg (fun v => subdivisionGridVertex P x S f t v)
      (show finCastGrid (lastSegment S)=lastGridInterior S from rfl))
  · have hs : subdivisionEdgeEnd P x S
        (subdivisionVerticalEdge P x S f t (lastSegment S))=
        subdivisionGridVertex P x S f t (finSuccGrid (lastSegment S)) :=
      own_vertical_end P x S f t (lastSegment S)
    exact hs.trans (congrArg (fun v => subdivisionGridVertex P x S f t v)
      (by apply Fin.ext; dsimp [finSuccGrid,lastSegment,gridAt]; have := S.half_pos; omega))

private theorem shiftedFacePath0_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin (S.half-1))
    (e : SubdivisionEdge P x S) (he : pathChain (shiftedFacePath0 P x S f i) e≠0) :
    (∃ k : Fin S.half, k.val≤ i.val ∧
      e=.inr (.inr (f,lastInterior S (by have := i.isLt; omega),k))) ∨
      e=.inr (.inl (f,lastSegment S,i)) := by
  have hh : 2≤S.half := by have := i.isLt; omega
  have hc0 : S.half-1≠0 := by omega
  have hch : S.half-1≠S.half := by omega
  have ht0 : i.val+1≠0 := by omega
  have hth : i.val+1≠S.half := by have := i.isLt; omega
  have hs : pathChain (shiftedFacePath0 P x S f i)=
      pathChain (verticalAtColumnPath P x S f (lastGridInterior S) (i.val+1)
        (by have := i.isLt; omega))+
      Pi.single (subdivisionHorizontalEdge P x S f (lastSegment S)
        (gridAt S (i.val+1) (by have := i.isLt; omega))) (1:F) := rfl
  rw [hs,Pi.add_apply] at he
  by_cases hp : pathChain (verticalAtColumnPath P x S f (lastGridInterior S)
      (i.val+1) (by have := i.isLt; omega)) e=0
  · right
    rw [hp,zero_add,Pi.single_apply] at he
    have hneq : ¬ e≠subdivisionHorizontalEdge P x S f (lastSegment S)
        (gridAt S (i.val+1) (by have := i.isLt; omega)) := by
      intro hn
      exact he (if_neg hn)
    have heq := not_not.mp hneq
    rw [heq]
    simp [subdivisionHorizontalEdge,gridAt,ht0,hth,finInteriorIndex] <;> (congr 3 <;> apply Fin.ext <;> dsimp [gridAt] <;> omega)
  · left
    obtain ⟨k,hk,heq⟩ := verticalAtColumnPath_support P x S f
      (lastGridInterior S) (i.val+1) _ e hp
    refine ⟨k,by omega,?_⟩
    rw [heq]
    simp [subdivisionVerticalEdge,lastGridInterior,hc0,hch,finInteriorIndex,lastInterior] <;>
      (congr 3 <;> apply Fin.ext <;> dsimp [lastGridInterior,lastInterior] <;> omega)

private theorem shiftedFacePath1_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (i : Fin (S.half-1))
    (e : SubdivisionEdge P x S) (he : pathChain (shiftedFacePath1 P x S f i) e≠0) :
    (∃ k : Fin S.half, k.val≤ i.val ∧
      e=.inr (.inl (f,k,lastInterior S (by have := i.isLt; omega)))) ∨
      e=.inr (.inr (f,i,lastSegment S)) := by
  have hh : 2≤S.half := by have := i.isLt; omega
  have hc0 : S.half-1≠0 := by omega
  have hch : S.half-1≠S.half := by omega
  have ht0 : i.val+1≠0 := by omega
  have hth : i.val+1≠S.half := by have := i.isLt; omega
  have hs : pathChain (shiftedFacePath1 P x S f i)=
      pathChain (horizontalAtRowPath P x S f (lastGridInterior S) (i.val+1)
        (by have := i.isLt; omega))+
      Pi.single (subdivisionVerticalEdge P x S f
        (gridAt S (i.val+1) (by have := i.isLt; omega)) (lastSegment S)) (1:F) := rfl
  rw [hs,Pi.add_apply] at he
  by_cases hp : pathChain (horizontalAtRowPath P x S f (lastGridInterior S)
      (i.val+1) (by have := i.isLt; omega)) e=0
  · right
    rw [hp,zero_add,Pi.single_apply] at he
    have hneq : ¬ e≠subdivisionVerticalEdge P x S f
        (gridAt S (i.val+1) (by have := i.isLt; omega)) (lastSegment S) := by
      intro hn
      exact he (if_neg hn)
    have heq := not_not.mp hneq
    rw [heq]
    simp [subdivisionVerticalEdge,gridAt,ht0,hth,finInteriorIndex] <;> (congr 3 <;> apply Fin.ext <;> dsimp [gridAt] <;> omega)
  · left
    obtain ⟨k,hk,heq⟩ := horizontalAtRowPath_support P x S f
      (lastGridInterior S) (i.val+1) _ e hp
    refine ⟨k,by omega,?_⟩
    rw [heq]
    simp [subdivisionHorizontalEdge,lastGridInterior,hc0,hch,finInteriorIndex,lastInterior] <;>
      (congr 3 <;> apply Fin.ext <;> dsimp [lastGridInterior,lastInterior] <;> omega)

private theorem qToZ_face_boundary_edge (P : TannerSquarePresentation)
    (z : P.Z) (f : XStarFace (transposePresentation P) z)
    (j : BDL26FiniteTannerSquare.Two)
    (hz : P.qz (P.faceQ f.val j) z=true) :
    xStarBoundaryEdgeToStar (transposePresentation P) z
      ((transposeXStarBoundaryEdgeEquiv P z).symm
        (qToZBoundaryEdge P (P.faceQ f.val j) z hz
          ⟨P.faceX f.val,P.data.faceQ_xq f.val j⟩))=
      xStarFaceQZEdge (transposePresentation P) z f j := by
  apply Subtype.ext
  rfl

private theorem qToZ_face_interior0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z)
    (f : XStarFace (transposePresentation P) z)
    (hz : P.qz (P.faceQ f.val 0) z=true) (S : OddScale) (i : Fin (S.half-1)) :
    qToZSubdivisionVertex P A (P.faceQ f.val 0) z hz S
      (.inr (⟨P.faceX f.val,P.data.faceQ_xq f.val 0⟩,i))=
      subdivisionGridVertex (transposePresentation P) z S f
        (gridAt S S.half le_rfl)
        (gridAt S (i.val+1) (by have := i.isLt; omega)) := by
  rw [show subdivisionGridVertex (transposePresentation P) z S f
      (gridAt S S.half le_rfl)
      (gridAt S (i.val+1) (by have := i.isLt; omega))=
        .inr (.inl (xStarFaceQZEdge (transposePresentation P) z f 0,i)) by
    exact subdivisionGridVertex_edgeInterior_qz0 (transposePresentation P) z S f i]
  change (Sum.inr (Sum.inl (_,i)) :
    SubdivisionVertex (transposePresentation P) z S)=Sum.inr (Sum.inl (_,i))
  rw [qToZ_face_boundary_edge]

private theorem qToZ_face_interior1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z)
    (f : XStarFace (transposePresentation P) z)
    (hz : P.qz (P.faceQ f.val 1) z=true) (S : OddScale) (i : Fin (S.half-1)) :
    qToZSubdivisionVertex P A (P.faceQ f.val 1) z hz S
      (.inr (⟨P.faceX f.val,P.data.faceQ_xq f.val 1⟩,i))=
      subdivisionGridVertex (transposePresentation P) z S f
        (gridAt S (i.val+1) (by have := i.isLt; omega))
        (gridAt S S.half le_rfl) := by
  rw [show subdivisionGridVertex (transposePresentation P) z S f
      (gridAt S (i.val+1) (by have := i.isLt; omega))
      (gridAt S S.half le_rfl)=
        .inr (.inl (xStarFaceQZEdge (transposePresentation P) z f 1,i)) by
    exact subdivisionGridVertex_edgeInterior_qz1 (transposePresentation P) z S f i]
  change (Sum.inr (Sum.inl (_,i)) :
    SubdivisionVertex (transposePresentation P) z S)=Sum.inr (Sum.inl (_,i))
  rw [qToZ_face_boundary_edge]

private theorem rz_q_basis_delta_generic (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q)
    (v : QDoubleCylinderVertex (transposePresentation P) r S) :
    tannerCoboundary1 (rzReplacementPresentation P A S)
      (canonicalBasisWord (F:=F) (.inr ⟨r,v⟩))=
      ∑ z : P.Z, if hz : P.qz r z=true then
        extendZVertexWord P S z (canonicalBasisWord (F:=F)
          (qToZDoubleCylinderVertex P A r z hz S v)) else 0 := by
  ext ⟨z,v'⟩
  erw [tannerCoboundary1_canonicalBasis_apply,Finset.sum_apply]
  change (if rzQZIncidence P A S (.inr ⟨r,v⟩) ⟨z,v'⟩=true then (1:F) else 0)=_
  erw [Finset.sum_eq_single z]
  · by_cases hz : P.qz r z=true
    · erw [dif_pos hz]
      have hinc : rzQZIncidence P A S (.inr ⟨r,v⟩) ⟨z,v'⟩=true ↔
          qToZDoubleCylinderVertex P A r z hz S v=v' := by
        change decide (∃ h : P.qz r z=true,
          qToZDoubleCylinderVertex P A r z h S v=v')=true ↔ _
        simp only [decide_eq_true_eq]
        exact ⟨fun ⟨_,he⟩ => he,fun he => ⟨hz,he⟩⟩
      have hext : extendZVertexWord P S z
          (canonicalBasisWord (F:=F) (qToZDoubleCylinderVertex P A r z hz S v))
          ⟨z,v'⟩=
          (if v'=qToZDoubleCylinderVertex P A r z hz S v then 1 else 0) := by
        simp only [extendZVertexWord,↓reduceDIte,basis_value] <;> split_ifs <;> rfl
      apply (indicator_iff _ _ hinc).trans
      calc
        _ = (if v'=qToZDoubleCylinderVertex P A r z hz S v then 1 else 0) :=
          indicator_iff _ _ ⟨Eq.symm,Eq.symm⟩
        _ = _ := hext.symm
    · erw [dif_neg hz]
      have hn : ¬rzQZIncidence P A S (.inr ⟨r,v⟩) ⟨z,v'⟩=true := by
        change ¬decide (∃ h : P.qz r z=true,
          qToZDoubleCylinderVertex P A r z h S v=v')=true
        simpa only [decide_eq_true_eq] using
          (fun h : ∃ h : P.qz r z=true,
            qToZDoubleCylinderVertex P A r z h S v=v' => hz h.1)
      exact if_neg hn
  · intro z' _ hne
    by_cases hz : P.qz r z'=true <;>
      simp [hz,extendZVertexWord,Ne.symm hne]
  · simp

private theorem unique_z_qBasis_delta1 (S : OddScale) (r : (RawOne S).Q)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S) :
    tannerCoboundary1 (RawTwo S) (canonicalBasisWord (F:=F) (.inr ⟨r,v⟩))=
      extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F)
        (qToZDoubleCylinderVertex (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v)) := by
  calc
    _ = ∑ z' : (RawOne S).Z, if h : (RawOne S).qz r z'=true then
        extendZVertexWord (RawOne S) S z' (canonicalBasisWord (F:=F)
          (qToZDoubleCylinderVertex (RawOne S)
            (rxState S baseState).admissible.toTannerSquareAdmissible r z' h S v)) else 0 :=
      rz_q_basis_delta_generic (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible S r v
    _ = _ := by
      rw [Finset.sum_eq_single z]
      · exact dif_pos hz
      · intro z' _ hn
        have hnot : ¬(RawOne S).qz r z'=true := fun h => hn (hu z' h)
        exact dif_neg hnot
      · intro hn
        exact False.elim (hn (Finset.mem_univ z))

private theorem linear_word_add_zero {I J : Type}
    (D : Word F I →ₗ[F] Word F J) (a b : Word F I)
    (ha : D a=0) (hb : D b=0) : D (a+b)=0 := by
  rw [map_add,ha,hb,zero_add]

private theorem linear_three_cancel {I J : Type}
    (D : Word F I →ₗ[F] Word F J) (a b c : Word F I)
    (u v w : Word F J) (ha : D a=u) (hb : D b=v)
    (hc : D c=(w+u)+(w+v)) : D (a+b+c)=0 := by
  rw [map_add,map_add,ha,hb,hc]
  exact three_words_cancel u v w

private theorem extended_two_paths_boundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (root u v : ZDoubleCylinderVertex P z S)
    (p : UndirectedPath (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) root u)
    (p' : UndirectedPath (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S) root v) :
    tannerCoboundary1 (rzReplacementPresentation P A.toTannerSquareAdmissible S)
      (extendZEdgeWord P S z (pathChain p+pathChain p'))=
        (extendZVertexWord P S z (canonicalBasisWord (F:=F) root)+
          extendZVertexWord P S z (canonicalBasisWord (F:=F) u))+
        (extendZVertexWord P S z (canonicalBasisWord (F:=F) root)+
          extendZVertexWord P S z (canonicalBasisWord (F:=F) v)) := by
  rw [rzCoboundary1_extendZEdgeWord P A S z,map_add]
  have hp : rzCzGraphBoundary P z S (pathChain p)=
      canonicalBasisWord (F:=F) root+canonicalBasisWord (F:=F) u :=
    graphBoundary_pathChain _ _ root p
  have hp' : rzCzGraphBoundary P z S (pathChain p')=
      canonicalBasisWord (F:=F) root+canonicalBasisWord (F:=F) v :=
    graphBoundary_pathChain _ _ root p'
  rw [hp,hp',extendZVertexWord_add,extendZVertexWord_add,extendZVertexWord_add]

private def twoArmKernel (S : OddScale)
    (r r' : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true) (hz' : (RawOne S).qz r' z=true)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S)
    (v' : QDoubleCylinderVertex (transposePresentation (RawOne S)) r' S)
    (root : ZDoubleCylinderVertex (RawOne S) z S)
    (p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      root (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v))
    (p' : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      root (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz' S v')) :
    Word F (RawTwo S).Q :=
  canonicalBasisWord (.inr ⟨r,v⟩)+canonicalBasisWord (.inr ⟨r',v'⟩)+
    extendZEdgeWord (RawOne S) S z (pathChain p+pathChain p')

private theorem twoArmKernel_closed (S : OddScale)
    (r r' : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true) (hz' : (RawOne S).qz r' z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (hu' : ∀ z', (RawOne S).qz r' z'=true → z'=z)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S)
    (v' : QDoubleCylinderVertex (transposePresentation (RawOne S)) r' S)
    (root : ZDoubleCylinderVertex (RawOne S) z S)
    (p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      root (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v))
    (p' : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      root (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz' S v')) :
    tannerCoboundary1 (RawTwo S) (twoArmKernel S r r' z hz hz' v v' root p p')=0 := by
  exact linear_three_cancel (tannerCoboundary1 (RawTwo S))
    (canonicalBasisWord (F:=F) (.inr ⟨r,v⟩))
    (canonicalBasisWord (F:=F) (.inr ⟨r',v'⟩))
    (extendZEdgeWord (RawOne S) S z (pathChain p+pathChain p'))
    (extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v)))
    (extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r' z hz' S v')))
    (extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F) root))
    (unique_z_qBasis_delta1 S r z hz hu v)
    (unique_z_qBasis_delta1 S r' z hz' hu' v')
    (extended_two_paths_boundary (RawOne S) (rxState S baseState).admissible
      S z root _ _ p p')

private def stripQ (j : Fin 2) (x : BaseX) : BaseQubit :=
  ⟨j.val+2*x.val,by have := j.isLt; have := x.isLt; omega⟩

private def stripMember (j : Fin 2) (x : BaseX) (S : OddScale) :
    SubdivisionVertex baseTannerSquarePresentation x S → Bool
  | .inl node => match node.val with
      | .x _ => false
      | .q q => decide (q=stripQ j x)
      | .z z => decide (z=j)
  | .inr (.inl edgeInterior) => match edgeInterior.1.val with
      | .inl _ => false
      | .inr e => decide (e.val.1=stripQ j x ∧ e.val.2=j)
  | .inr (.inr _) => false

private def stripPotential (S : OddScale) (j : Fin 2) : Word F (RawOne S).X :=
  fun ⟨x,(_,v)⟩ => if stripMember j x S v then 1 else 0

private def stripSeedCocycle (j : Fin 2) : Word F BaseQubit :=
  if j=0 then ![1,0,1,0,0] else ![0,1,0,1,0]

private theorem stripSeedCocycle_closed (j : Fin 2) :
    tannerCoboundary1 baseTannerSquarePresentation (stripSeedCocycle j)=0 := by
  fin_cases j <;> decide

private def rawSeedLift (S : OddScale) (j : Fin 2) : Word F (RawOne S).Q := by
  exact BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
    (stripSeedCocycle j)

private def terminalOldKernel (S : OddScale) (j : Fin 2) : Word F (RawOne S).Q :=
  rawSeedLift S j+tannerCoboundary0 (RawOne S) (stripPotential S j)

private theorem terminalOldKernel_closed (S : OddScale) (j : Fin 2) :
    tannerCoboundary1 (RawOne S) (terminalOldKernel S j)=0 := by
  have hrx := LinearMap.congr_fun
    (BDL26ReplacementCochainMaps.rxMap_commutes_coboundary1
      baseTannerSquarePresentation S) (stripSeedCocycle j)
  change BDL26ReplacementCochainMaps.rxCoboundary1 baseTannerSquarePresentation S
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        (stripSeedCocycle j))=
    BDL26ReplacementCochainMaps.rxMap2Coord baseTannerSquarePresentation S
      (tannerCoboundary1 baseTannerSquarePresentation (stripSeedCocycle j)) at hrx
  rw [stripSeedCocycle_closed,map_zero] at hrx
  have hmap : tannerCoboundary1 (RawOne S)
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        (stripSeedCocycle j))=0 := by
    erw [BDL26RXLocalReplacement.rxPresentation_coboundary1_eq
      baseTannerSquarePresentation baseTannerSquareAdmissibleV4
      baseTannerSquareCellularRegular S]
    exact hrx
  have hb := LinearMap.congr_fun
    (BDL26LevelTwoDistance.tannerCoboundary_squared (RawOne S)) (stripPotential S j)
  change tannerCoboundary1 (RawOne S)
    (tannerCoboundary0 (RawOne S) (stripPotential S j))=0 at hb
  have hmap' : tannerCoboundary1 (RawOne S) (rawSeedLift S j)=0 := hmap
  exact linear_word_add_zero (tannerCoboundary1 (RawOne S))
    (rawSeedLift S j) (tannerCoboundary0 (RawOne S) (stripPotential S j)) hmap' hb

private theorem rx_local_gradient (S : OddScale) (p : Word F (RawOne S).X)
    (x : BaseX) (e : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    tannerCoboundary0 (RawOne S) p (.inl ⟨x,e⟩)=
      p ⟨x,tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S e⟩+
        p ⟨x,tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S e⟩ := by
  erw [BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S]
  erw [BDL26RXDecoderAdapter.raw_delta0_x,
    ← doubleCylinderGraphBoundary_eq_boundary1]
  exact wordLinearMapTranspose_graphBoundary_apply _ _ _ _

private theorem old_local_incidence (S : OddScale) (v : (RawOne S).X)
    (x : BaseX) (e : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    (RawOne S).xq v (.inl ⟨x,e⟩)=true ↔
      v=⟨x,tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S e⟩ ∨
        v=⟨x,tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S e⟩ := by
  have h := rx_local_gradient S (canonicalBasisWord (F:=F) v) x e
  erw [tannerCoboundary0_canonicalBasis_apply] at h
  have hn : (⟨x,tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S e⟩ :
      (RawOne S).X)≠⟨x,tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S e⟩ := by
    intro he
    exact tannerDoubleCylinderEdgeStart_ne_end baseTannerSquarePresentation x S e
      (@sigma_same_index_inj baseTannerSquarePresentation.X
        (fun owner => DoubleCylinderVertex baseTannerSquarePresentation owner S) x _ _ he)
  exact scalar_unit_pair v _ _ hn _ h

private def stripFace (j : Fin 2) (x : BaseX) :
    XStarFace baseTannerSquarePresentation x :=
  ⟨⟨j.val+2*x.val,by have := j.isLt; have := x.isLt; omega⟩,
    by fin_cases j <;> fin_cases x <;> decide⟩

private theorem base_star_face_cases (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    ∃ k : Fin 2, f=stripFace k x := by
  fin_cases x
  · exact (by decide : ∀ f : XStarFace baseTannerSquarePresentation (0 : BaseX),
      ∃ k : Fin 2, f=stripFace k 0) f
  · exact (by decide : ∀ f : XStarFace baseTannerSquarePresentation (1 : BaseX),
      ∃ k : Fin 2, f=stripFace k 1) f

private def stripHorizontal (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) : (RawOne S).Q :=
  .inl ⟨x,.inl (c,subdivisionHorizontalEdge baseTannerSquarePresentation x S
    (stripFace j x) (lastSegment S) row)⟩

private theorem grid_vertex_view (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i j : Fin (S.half+1)) :
    subdivisionGridVertex P x S f i j=
      if hi0 : i.val=0 then
        if hj0 : j.val=0 then Sum.inl (xStarFaceXVertex P x f)
        else if hjm : j.val=S.half then Sum.inl (xStarFaceQVertex P x f 1)
        else Sum.inr (Sum.inl (xStarFaceXQEdge P x f 1,finInteriorIndex S j hj0 hjm))
      else if him : i.val=S.half then
        if hj0 : j.val=0 then Sum.inl (xStarFaceQVertex P x f 0)
        else if hjm : j.val=S.half then Sum.inl (xStarFaceZVertex P x f)
        else Sum.inr (Sum.inl (xStarFaceQZEdge P x f 0,finInteriorIndex S j hj0 hjm))
      else if hj0 : j.val=0 then
        Sum.inr (Sum.inl (xStarFaceXQEdge P x f 0,finInteriorIndex S i hi0 him))
      else if hjm : j.val=S.half then
        Sum.inr (Sum.inl (xStarFaceQZEdge P x f 1,finInteriorIndex S i hi0 him))
      else Sum.inr (Sum.inr
        (f,finInteriorIndex S i hi0 him,finInteriorIndex S j hj0 hjm)) := rfl

private theorem segment_end_view (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarEdge P x) (k : Fin S.half) :
    subdivisionSegmentEnd P x S e k=
      if h : k.val+1=S.half then Sum.inl (xStarEdgeEnd P x e)
      else Sum.inr (Sum.inl (e,⟨k.val,by have := k.isLt; omega⟩)) := rfl

private theorem stripMember_face_x (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    stripMember j x S (.inl (xStarFaceXVertex _ _ f))=false := rfl

private theorem stripMember_face_q (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two) :
    stripMember j x S (.inl (xStarFaceQVertex _ _ f c))=
      decide (f=stripFace j x ∧ c=0) := by
  dsimp only [stripMember,xStarFaceQVertex]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega

private theorem stripMember_face_z (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    stripMember j x S (.inl (xStarFaceZVertex _ _ f))=
      decide (f=stripFace j x) := by
  dsimp only [stripMember,xStarFaceZVertex]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases x <;> fin_cases k
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega

private theorem stripMember_face_xq (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    stripMember j x S (.inr (.inl (xStarFaceXQEdge _ _ f c,i)))=false := rfl

private theorem stripMember_face_qz (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    stripMember j x S (.inr (.inl (xStarFaceQZEdge _ _ f c,i)))=
      decide (f=stripFace j x ∧ c=0) := by
  dsimp only [stripMember,xStarFaceQZEdge,faceQZEdge]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega

private theorem stripMember_face_cell (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (i k : Fin (S.half-1)) :
    stripMember j x S (.inr (.inr (f,i,k)))=false := rfl

private theorem stripMember_grid (S : OddScale) (j : Fin 2) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (a b : Fin (S.half+1)) :
    stripMember j x S (subdivisionGridVertex baseTannerSquarePresentation x S f a b)=
      decide (f=stripFace j x ∧ a.val=S.half) := by
  have hm : S.half≠0 := S.half_pos.ne'
  have h01 : (0 : BDL26FiniteTannerSquare.Two)≠1 := by decide
  have h10 : (1 : BDL26FiniteTannerSquare.Two)≠0 := by decide
  by_cases hf : f=stripFace j x
  all_goals erw [grid_vertex_view]
  all_goals split_ifs
  all_goals simp_all only [stripMember_face_x,stripMember_face_q,stripMember_face_z,
    stripMember_face_xq,stripMember_face_qz,stripMember_face_cell,hm,Ne.symm hm,h01,h10,
    true_and,false_and,and_true,and_false,decide_true,decide_false,
    Bool.false_eq_true,Bool.true_eq_false,not_true_eq_false,not_false_eq_true]

private theorem terminalOldKernel_horizontal (S : OddScale) (j : Fin 2)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (f : XStarFace baseTannerSquarePresentation x) (i : Fin S.half)
    (row : Fin (S.half+1)) :
    terminalOldKernel S j (.inl ⟨x,.inl (c,
      subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)⟩)=
      if f=stripFace j x ∧ i.val+1=S.half then 1 else 0 := by
  erw [terminalOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,rx_local_gradient]
  change (if stripMember j x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)) then
      (1:F) else 0)+
    (if stripMember j x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)) then
      (1:F) else 0)=_
  erw [own_horizontal_start,own_horizontal_end,
    stripMember_grid,stripMember_grid]
  have hi : i.val≠S.half := Nat.ne_of_lt i.isLt
  simp only [finCastGrid,finSuccGrid,Fin.val_mk,hi,false_and,and_false,decide_false,
    Bool.false_eq_true,if_false,zero_add,decide_eq_true_eq]
  by_cases hp : f=stripFace j x ∧ i.val+1=S.half
  · simp [hp]
  · simp [hp]

private theorem terminalOldKernel_vertical (S : OddScale) (j : Fin 2)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (f : XStarFace baseTannerSquarePresentation x) (column : Fin (S.half+1))
    (i : Fin S.half) :
    terminalOldKernel S j (.inl ⟨x,.inl (c,
      subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)⟩)=0 := by
  erw [terminalOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,rx_local_gradient]
  change (if stripMember j x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)) then
      (1:F) else 0)+
    (if stripMember j x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)) then
      (1:F) else 0)=0
  erw [own_vertical_start,own_vertical_end,
    stripMember_grid,stripMember_grid]
  exact ZModModule.add_self _

private theorem subdivision_edge_grid_cover (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (x : P.X) (S : OddScale)
    (e : SubdivisionEdge P x S) :
    (∃ (f : XStarFace P x) (i : Fin S.half) (row : Fin (S.half+1)),
      e=subdivisionHorizontalEdge P x S f i row) ∨
    (∃ (f : XStarFace P x) (column : Fin (S.half+1)) (i : Fin S.half),
      e=subdivisionVerticalEdge P x S f column i) := by
  rcases e with ⟨⟨edge,hm⟩,k⟩ | h | v
  · rcases edge with edge | edge
    · obtain ⟨⟨f,c⟩,hf⟩ := A.xRadialFaceOwner x edge hm
      fin_cases c
      · left
        refine ⟨f,k,0,?_⟩
        simpa [subdivisionHorizontalEdge] using
          congrArg (fun e : XStarEdge P x => (Sum.inl (e,k) : SubdivisionEdge P x S)) hf.symm
      · right
        refine ⟨f,0,k,?_⟩
        simpa [subdivisionVerticalEdge] using
          congrArg (fun e : XStarEdge P x => (Sum.inl (e,k) : SubdivisionEdge P x S)) hf.symm
    · obtain ⟨⟨f,c⟩,hf⟩ := A.xBoundaryFaceOwner x edge hm
      fin_cases c
      · right
        refine ⟨f,gridAt S S.half le_rfl,k,?_⟩
        simpa [subdivisionVerticalEdge,gridAt,S.half_pos.ne'] using
          congrArg (fun e : XStarEdge P x => (Sum.inl (e,k) : SubdivisionEdge P x S)) hf.symm
      · left
        refine ⟨f,k,gridAt S S.half le_rfl,?_⟩
        simpa [subdivisionHorizontalEdge,gridAt,S.half_pos.ne'] using
          congrArg (fun e : XStarEdge P x => (Sum.inl (e,k) : SubdivisionEdge P x S)) hf.symm
  · rcases h with ⟨f,i,k⟩
    left
    refine ⟨f,i,finInteriorGrid S k,?_⟩
    have hk0 : (finInteriorGrid S k).val≠0 := by simp [finInteriorGrid]
    have hkh : (finInteriorGrid S k).val≠S.half := by
      have := k.isLt
      dsimp [finInteriorGrid]
      omega
    unfold subdivisionHorizontalEdge
    rw [dif_neg hk0,dif_neg hkh]
    apply congrArg (fun k' : Fin (S.half-1) =>
      (Sum.inr (Sum.inl (f,i,k')) : SubdivisionEdge P x S))
    apply Fin.ext
    change k.val=(k.val+1)-1
    omega
  · rcases v with ⟨f,k,i⟩
    right
    refine ⟨f,finInteriorGrid S k,i,?_⟩
    have hk0 : (finInteriorGrid S k).val≠0 := by simp [finInteriorGrid]
    have hkh : (finInteriorGrid S k).val≠S.half := by
      have := k.isLt
      dsimp [finInteriorGrid]
      omega
    unfold subdivisionVerticalEdge
    rw [dif_neg hk0,dif_neg hkh]
    apply congrArg (fun k' : Fin (S.half-1) =>
      (Sum.inr (Sum.inr (f,k',i)) : SubdivisionEdge P x S))
    apply Fin.ext
    change k.val=(k.val+1)-1
    omega

private theorem terminalOldKernel_target (S : OddScale) (j : Fin 2)
    (c : BDL26FiniteTannerSquare.Two) :
    terminalOldKernel S j (.inl ⟨(0 : BaseX),
      .inl (c,.inl (seedRadial j,lastSegment S))⟩)=1 := by
  have h := terminalOldKernel_horizontal S j (0 : BaseX) c (seedFace j) (lastSegment S) 0
  have hedge : subdivisionHorizontalEdge baseTannerSquarePresentation (0 : BaseX) S
      (seedFace j) (lastSegment S) 0=(.inl (seedRadial j,lastSegment S) :
        SubdivisionEdge baseTannerSquarePresentation 0 S) := by
    simp only [subdivisionHorizontalEdge,Fin.val_zero,↓reduceDIte]
    exact congrArg (fun e : XStarEdge baseTannerSquarePresentation (0 : BaseX) =>
      (Sum.inl (e,lastSegment S) : SubdivisionEdge baseTannerSquarePresentation 0 S))
        ((seedRadial_face_zero j (seedFace j)).mpr rfl).symm
  erw [hedge] at h
  apply h.trans
  apply if_pos
  constructor
  · fin_cases j <;> rfl
  · dsimp only [lastSegment]; have := S.half_pos; omega

private theorem qVertexX_coordinate (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X) (q : P.Q)
    (hx : P.xq x q=true) (v : QDoubleCylinderVertex P q S)
    (u : DoubleCylinderVertex P x S) :
    qDoubleCylinderVertexXIncidence P q x S u v=
      vertexIndicator u (qToXDoubleCylinderVertexAtRoot P q x hx S (A.qzRoot q) v) := by
  rcases u with ⟨uc,u⟩
  rcases v with ⟨vc,v⟩
  fin_cases uc <;> fin_cases vc
  all_goals rcases u with u | edgeInterior | faceInterior
  all_goals rcases v with v | edgeInterior'
  all_goals
    first
    | (rcases v with cone | endpoint <;>
        simp [qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
          qToXDoubleCylinderVertexAtRoot,qToXSubdivisionVertexAtRoot,
          qToXBoundaryVertexAtRoot,xStarBoundaryVertexToStar,xBoundaryEdgeStart,
          xBoundaryEdgeEnd,qToXBoundaryEdge,vertexIndicator,Subtype.ext_iff,
          Prod.ext_iff,hx])
    | simp [qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
        qToXDoubleCylinderVertexAtRoot,qToXSubdivisionVertexAtRoot,
        qToXBoundaryVertexAtRoot,xStarBoundaryVertexToStar,xBoundaryEdgeStart,
        xBoundaryEdgeEnd,qToXBoundaryEdge,vertexIndicator,Subtype.ext_iff,Prod.ext_iff,hx]
  all_goals
    rcases edgeInterior with ⟨⟨edge,hm⟩,i⟩
    rcases edge with xq | qz
    · simp [xStarBoundaryEdgeToStar,vertexIndicator,Subtype.ext_iff] at hm ⊢
    · simp [xStarBoundaryEdgeToStar,qToXBoundaryEdge,vertexIndicator,
        Subtype.ext_iff,Prod.ext_iff,and_assoc]

private theorem rx_q_gradient (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (p : Word F (RX0 P S))
    (q : P.Q) (v : QDoubleCylinderVertex P q S) :
    BDL26ReplacementCochainMaps.rxCoboundary0 P S p (.inr ⟨q,v⟩)=
      ∑ x : P.X, if hx : P.xq x q=true then
        p ⟨x,qToXDoubleCylinderVertexAtRoot P q x hx S (A.qzRoot q) v⟩ else 0 := by
  unfold BDL26ReplacementCochainMaps.rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P.xq x q=true
  · rw [dif_pos hx]
    change (∑ u : DoubleCylinderVertex P x S,
      p ⟨x,u⟩*qDoubleCylinderVertexXIncidence P q x S u v)=_
    simp_rw [qVertexX_coordinate P A S x q hx v]
    let target := qToXDoubleCylinderVertexAtRoot P q x hx S (A.qzRoot q) v
    rw [Finset.sum_eq_single target]
    · simp [vertexIndicator,target]
    · intro u _ hu
      change u≠qToXDoubleCylinderVertexAtRoot P q x hx S (A.qzRoot q) v at hu
      simp only [vertexIndicator,if_neg hu,mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_univ target))
  · simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
      qSubdivisionVertexXIncidence,hx]

private theorem stripPotential_port_cone (S : OddScale) (j : Fin 2)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two) :
    stripPotential S j ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inl (.inl ()))⟩=
        if decide (q=stripQ j x) then 1 else 0 := by
  dsimp only [stripPotential,stripMember,qToXDoubleCylinderVertexAtRoot,
    qToXSubdivisionVertexAtRoot,qToXBoundaryVertexAtRoot,qToXBoundaryEdge,
    xBoundaryEdgeStart,xBoundaryEdgeEnd,xStarBoundaryVertexToStar,xStarBoundaryEdgeToStar]
  apply indicator_iff
  simp only [decide_eq_true_eq]
  all_goals rfl


private theorem stripPotential_port_endpoint (S : OddScale) (j : Fin 2)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root edge : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two) :
    stripPotential S j ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inl (.inr edge))⟩=
        if decide (edge.val=j) then 1 else 0 := rfl

private theorem stripPotential_port_interior (S : OddScale) (j : Fin 2)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root edge : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    stripPotential S j ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inr (edge,i))⟩=
        if decide (q=stripQ j x ∧ edge.val=j) then 1 else 0 := by
  dsimp only [stripPotential,stripMember,qToXDoubleCylinderVertexAtRoot,
    qToXSubdivisionVertexAtRoot,qToXBoundaryVertexAtRoot,qToXBoundaryEdge,
    xBoundaryEdgeStart,xBoundaryEdgeEnd,xStarBoundaryVertexToStar,xStarBoundaryEdgeToStar]
  apply indicator_iff
  simp only [decide_eq_true_eq]
  all_goals rfl


private theorem strip_sum_cone (j : Fin 2) (q : BaseQubit) :
    (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
      (if decide (q=stripQ j x) then (1:F) else 0) else 0)=stripSeedCocycle j q := by
  have h10 : (1:F)≠0 := one_ne_zero
  have h01 : (0:F)≠1 := zero_ne_one
  rw [Fin.sum_univ_two]
  simp only [base_xq_matrix_value]
  fin_cases j <;> fin_cases q
  all_goals
    norm_num [baseBoundary1Matrix,stripQ,stripSeedCocycle,
      base_X_eq_value,base_Q_eq_value,base_Z_eq_value,Fin.ext_iff,
      Fin.val_mk,Fin.val_zero,Fin.val_one,ZModModule.add_self,h10,h01]

private theorem strip_sum_endpoint (j : Fin 2) (q : BaseQubit) (z : baseTannerSquarePresentation.Z)
    (hz : baseTannerSquarePresentation.qz q z=true) :
    (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
      (if decide (z=j) then (1:F) else 0) else 0)=stripSeedCocycle j q := by
  have h10 : (1:F)≠0 := one_ne_zero
  have h01 : (0:F)≠1 := zero_ne_one
  rw [Fin.sum_univ_two]
  simp only [base_xq_matrix_value]
  have hz' := (base_qz_matrix_value q z).symm.trans hz
  have hqz : baseBoundary2Matrix q z≠0 := of_decide_eq_true hz'
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases q <;> fin_cases z
  all_goals norm_num [baseBoundary2Matrix] at hqz
  all_goals
    norm_num [baseBoundary1Matrix,stripSeedCocycle,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one,ZModModule.add_self,h10,h01]
  all_goals first | rfl | omega

private theorem strip_sum_interior (j : Fin 2) (q : BaseQubit) (z : baseTannerSquarePresentation.Z)
    (hz : baseTannerSquarePresentation.qz q z=true) :
    (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
      (if decide (q=stripQ j x ∧ z=j) then (1:F) else 0) else 0)=stripSeedCocycle j q := by
  have h10 : (1:F)≠0 := one_ne_zero
  have h01 : (0:F)≠1 := zero_ne_one
  rw [Fin.sum_univ_two]
  simp only [base_xq_matrix_value]
  have hz' := (base_qz_matrix_value q z).symm.trans hz
  have hqz : baseBoundary2Matrix q z≠0 := of_decide_eq_true hz'
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases j <;> fin_cases q <;> fin_cases z
  all_goals norm_num [baseBoundary2Matrix] at hqz
  all_goals
    norm_num [baseBoundary1Matrix,stripSeedCocycle,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one,ZModModule.add_self,h10,h01]
  all_goals first | rfl | omega

private theorem stripPotential_q_gradient (S : OddScale) (j : Fin 2) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    tannerCoboundary0 (RawOne S) (stripPotential S j) (.inr ⟨q,v⟩)=
      stripSeedCocycle j q := by
  erw [BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S]
  erw [rx_q_gradient baseTannerSquarePresentation baseTannerSquareAdmissible S]
  change (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
    stripPotential S j ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S (baseTannerSquareAdmissible.qzRoot q) v⟩ else 0)=stripSeedCocycle j q
  rcases v with ⟨c,(cone | endpoint) | ⟨edge,i⟩⟩
  · cases cone
    simp_rw [stripPotential_port_cone]
    exact strip_sum_cone j q
  · rcases endpoint with ⟨z,hz⟩
    change BaseZ at z
    simp_rw [stripPotential_port_endpoint]
    exact strip_sum_endpoint j q z hz
  · rcases edge with ⟨z,hz⟩
    change BaseZ at z
    simp_rw [stripPotential_port_interior]
    exact strip_sum_interior j q z hz

private theorem terminalOldKernel_q_zero (S : OddScale) (j : Fin 2) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    terminalOldKernel S j (.inr ⟨q,v⟩)=0 := by
  erw [terminalOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_qVertex,stripPotential_q_gradient]
  exact ZModModule.add_self _

private theorem terminalOldKernel_support (S : OddScale) (j : Fin 2)
    (r : (RawOne S).Q) (hr : terminalOldKernel S j r≠0) :
    ∃ (x : BaseX) (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)),
      r=stripHorizontal S j x c row := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · rcases e with ⟨c,e⟩ | v
    · rcases subdivision_edge_grid_cover baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 x S e with hh | hv
      · obtain ⟨f,i,row,he⟩ := hh
        subst e
        erw [terminalOldKernel_horizontal] at hr
        have h : f=stripFace j x ∧ i.val+1=S.half := by
          by_contra hn
          erw [if_neg hn] at hr
          exact hr rfl
        rcases h with ⟨hf,hi⟩
        subst f
        have hilast : i=lastSegment S := by
          apply Fin.ext
          have := i.isLt
          dsimp [lastSegment]
          omega
        subst i
        exact ⟨x,c,row,rfl⟩
      · obtain ⟨f,column,i,he⟩ := hv
        subst e
        erw [terminalOldKernel_vertical] at hr
        exact False.elim (hr rfl)
    · erw [terminalOldKernel,Pi.add_apply,rawSeedLift,
        BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,
        rx_local_gradient] at hr
      change ((if stripMember j x S v.val then (1:F) else 0)+
        (if stripMember j x S v.val then (1:F) else 0))≠0 at hr
      exact False.elim (hr (ZModModule.add_self _))
  · exact False.elim (hr (terminalOldKernel_q_zero S j q v))

private theorem qBasis_delta1 (S : OddScale) (r : (RawOne S).Q)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S) :
    tannerCoboundary1 (RawTwo S) (canonicalBasisWord (F:=F) (.inr ⟨r,v⟩))=
      ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r z=true then
        extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F)
          (qToZDoubleCylinderVertex (RawOne S)
            (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v))
      else 0 := by
  exact rz_q_basis_delta_generic (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S r v

private abbrev PortVertices (S : OddScale) :=
  (r : (RawOne S).Q) → QDoubleCylinderVertex (transposePresentation (RawOne S)) r S

private abbrev PortRoots (S : OddScale) :=
  (z : (RawOne S).Z) → ZDoubleCylinderVertex (RawOne S) z S

private abbrev PortPaths (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) :=
  (r : (RawOne S).Q) → (z : (RawOne S).Z) →
    (hz : (RawOne S).qz r z=true) →
      UndirectedPath
        (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
        (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
        (roots z) (qToZDoubleCylinderVertex (RawOne S)
          (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S (vertices r))

private def portBasis (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots) (r : (RawOne S).Q) :
    Word F (RawTwo S).Q :=
  canonicalBasisWord (.inr ⟨r,vertices r⟩)+
    ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r z=true then
      extendZEdgeWord (RawOne S) S z (pathChain (paths r z hz)) else 0

private theorem portBasis_delta1 (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots) (r : (RawOne S).Q) :
    tannerCoboundary1 (RawTwo S) (portBasis S vertices roots paths r)=
      ∑ z : (RawOne S).Z, if (RawOne S).qz r z=true then
        extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F) (roots z)) else 0 := by
  erw [portBasis,map_add,qBasis_delta1,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (RawOne S).qz r z=true
  · erw [dif_pos hz,dif_pos hz,if_pos hz,
      rzCoboundary1_extendZEdgeWord (RawOne S)
        (rxState S baseState).admissible S z]
    have hp : rzCzGraphBoundary (RawOne S) z S (pathChain (paths r z hz))=
        canonicalBasisWord (F:=F) (roots z)+canonicalBasisWord (F:=F)
          (qToZDoubleCylinderVertex (RawOne S)
            (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
            (vertices r)) := graphBoundary_pathChain _ _ _ _
    erw [hp,extendZVertexWord_add]
    exact words_cancel_middle _ _
  · erw [dif_neg hz,dif_neg hz,if_neg hz]
    exact (zero_add ((tannerCoboundary1 (RawTwo S))
      (0 : Word F (RawTwo S).Q))).trans (map_zero _)

private def portKernel (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots)
    (w : Word F (RawOne S).Q) : Word F (RawTwo S).Q :=
  ∑ r : (RawOne S).Q, w r • portBasis S vertices roots paths r

private theorem portKernel_closed (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots)
    (w : Word F (RawOne S).Q) (hw : tannerCoboundary1 (RawOne S) w=0) :
    tannerCoboundary1 (RawTwo S) (portKernel S vertices roots paths w)=0 := by
  have hmap : tannerCoboundary1 (RawTwo S) (portKernel S vertices roots paths w)=
      ∑ r : (RawOne S).Q, w r •
        (∑ z : (RawOne S).Z, if (RawOne S).qz r z=true then
          extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F) (roots z)) else 0) := by
    erw [portKernel,map_sum]
    apply Finset.sum_congr rfl
    intro r _
    exact (map_smul (tannerCoboundary1 (RawTwo S)) (w r)
      (portBasis S vertices roots paths r)).trans
        (congrArg (fun out : Word F (RawTwo S).Z => w r • out)
          (portBasis_delta1 S vertices roots paths r))
  refine hmap.trans ?_
  refine (collect_indicator_sums w (RawOne S).qz
    (fun z => (extendZVertexWord (RawOne S) S z
      (canonicalBasisWord (F:=F) (roots z)) : Word F (RawTwo S).Z))).trans ?_
  apply Finset.sum_eq_zero
  intro z _
  have hz := congrFun hw z
  change (∑ r : (RawOne S).Q,
    w r*(if (RawOne S).qz r z=true then 1 else 0))=0 at hz
  exact (congrArg (fun c : F => c •
    extendZVertexWord (RawOne S) S z (canonicalBasisWord (F:=F) (roots z))) hz).trans
      (zero_smul _ _)

private theorem portKernel_q (S : OddScale) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots)
    (w : Word F (RawOne S).Q) (r : (RawOne S).Q)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S) :
    portKernel S vertices roots paths w (.inr ⟨r,v⟩)=
      w r*(if v=vertices r then 1 else 0) := by
  have hport (r' : (RawOne S).Q) :
      portBasis S vertices roots paths r' (.inr ⟨r,v⟩)=
        if (.inr ⟨r,v⟩ : (RawTwo S).Q)=.inr ⟨r',vertices r'⟩ then 1 else 0 := by
    change (canonicalBasisWord (F:=F) (Sum.inr ⟨r',vertices r'⟩ : (RawTwo S).Q)+
      ∑ z : (RawOne S).Z, if hz : (RawOne S).qz r' z=true then
        extendZEdgeWord (RawOne S) S z (pathChain (paths r' z hz)) else 0)
        (.inr ⟨r,v⟩)=_
    apply generic_basis_plus_value
    have hs := word_sum_eval (fun z : (RawOne S).Z =>
      if hz : (RawOne S).qz r' z=true then
        extendZEdgeWord (RawOne S) S z (pathChain (paths r' z hz)) else 0)
      (.inr ⟨r,v⟩ : (RawTwo S).Q)
    refine hs.trans (Finset.sum_eq_zero ?_)
    intro z _
    by_cases hz : (RawOne S).qz r' z=true
    · simpa only [dif_pos hz] using
        extend_edge_at_port (RawOne S) S z (pathChain (paths r' z hz)) r v
    · simp only [dif_neg hz,word_zero_eval]
  calc
    _ = ∑ r' : (RawOne S).Q, w r'*portBasis S vertices roots paths r' (.inr ⟨r,v⟩) :=
      sum_scaled_words_apply w (portBasis S vertices roots paths) _
    _ = _ := by
      erw [Finset.sum_eq_single r]
      · rw [hport]
        by_cases he : v=vertices r
        · subst v
          simp
        · simp [he,Sigma.mk.injEq]
      · intro r' _ hn
        rw [hport]
        have hne : (.inr ⟨r,v⟩ : (RawTwo S).Q)≠.inr ⟨r',vertices r'⟩ := by
          intro he
          exact hn (congrArg Sigma.fst (Sum.inr.inj he)).symm
        rw [if_neg hne,mul_zero]
      · simp

private theorem global_zero_of_port_kernel (S : OddScale)
    (a : Word F (RawTwo S).Q) (vertices : PortVertices S)
    (roots : PortRoots S) (paths : PortPaths S vertices roots)
    (w : Word F (RawOne S).Q) (hw : tannerCoboundary1 (RawOne S) w=0)
    (r : (RawOne S).Q) (hr : w r=1)
    (hq : ∀ r', w r'≠0 → r'≠r →
      Encodable.encode (executableCoordinate S (.inr ⟨r,vertices r⟩))<
        Encodable.encode (executableCoordinate S (.inr ⟨r',vertices r'⟩)))
    (hz : ∀ r', w r'≠0 → ∀ z (h : (RawOne S).qz r' z=true) e,
      pathChain (paths r' z h) e≠0 →
        Encodable.encode (executableCoordinate S (.inr ⟨r,vertices r⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩))) :
    BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (RawTwo S) a) (.inr ⟨r,vertices r⟩)=0 := by
  apply actualGlobal_zero_of_encoded_kernel S a
    (portKernel S vertices roots paths w) (.inr ⟨r,vertices r⟩)
  · exact portKernel_closed S vertices roots paths w hw
  · erw [portKernel_q,hr,if_pos rfl,mul_one]
  · intro p hp
    cases p with
    | inr q =>
      rcases q with ⟨r',v⟩
      erw [portKernel_q]
      by_cases hr' : w r'=0
      · erw [hr',zero_mul]
      · by_cases hv : v=vertices r'
        · subst v
          by_cases he : r'=r
          · subst r'
            exact False.elim (Nat.lt_irrefl _ hp)
          · exact False.elim (Nat.lt_asymm hp (hq r' hr' he))
        · erw [if_neg hv,mul_zero]
    | inl edge =>
      rcases edge with ⟨z,e⟩
      erw [portKernel,Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro r' _
      by_cases hr' : w r'=0
      · change w r'*portBasis S vertices roots paths r' (.inl ⟨z,e⟩)=0
        rw [hr',zero_mul]
      · have he : portBasis S vertices roots paths r' (.inl ⟨z,e⟩)=0 := by
          erw [portBasis,Pi.add_apply]
          have hbase : canonicalBasisWord (F:=F)
              (Sum.inr ⟨r',vertices r'⟩ : (RawTwo S).Q) (.inl ⟨z,e⟩)=0 := by
            simp [canonicalBasisWord]
          erw [hbase,zero_add,Finset.sum_apply]
          apply Finset.sum_eq_zero
          intro z' _
          by_cases h : (RawOne S).qz r' z'=true
          · erw [dif_pos h]
            by_cases hzz : z=z'
            · subst z'
              have hpath : pathChain (paths r' z h) e=0 := by
                by_contra hn
                exact Nat.lt_asymm hp (hz r' hr' z h e hn)
              simp [extendZEdgeWord,hpath]
            · exact dif_neg hzz
          · simp only [dif_neg h,word_zero_eval]
        change w r'*portBasis S vertices roots paths r' (.inl ⟨z,e⟩)=0
        rw [he,mul_zero]

private theorem q_before_larger_port_code (r r' u v : Nat)
    (c : BDL26FiniteTannerSquare.Two) (huv : u<v)
    (hr : r<Nat.pair c.val v) :
    2*Nat.pair r (Nat.pair c.val u)+1<
      2*Nat.pair r' (Nat.pair c.val v)+1 := by
  have ht := Nat.pair_lt_pair_right c.val huv
  have hb : max r (Nat.pair c.val u)+1≤Nat.pair c.val v := by omega
  have hu := Nat.pair_lt_max_add_one_sq r (Nat.pair c.val u)
  have hl := Nat.max_sq_add_min_le_pair r' (Nat.pair c.val v)
  have hsq := Nat.pow_le_pow_left
    (hb.trans (Nat.le_max_right r' (Nat.pair c.val v))) 2
  omega

private theorem interior_before_any_root_code (r x z A i k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hr : r<A) (hx : x<A) (hi : i<A) :
    2*Nat.pair r (Nat.pair c.val (2*Nat.pair x i+1))+1<
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair A k)) := by
  have hmax : max x i+1≤A := by omega
  have hu := Nat.pair_lt_max_add_one_sq x i
  have hs := Nat.pow_le_pow_left hmax 2
  have hl := Nat.max_sq_add_min_le_pair A k
  have hA := Nat.le_max_left A k
  have hs' := Nat.pow_le_pow_left hA 2
  have huv : 2*Nat.pair x i+1<2*Nat.pair A k := by omega
  apply q_before_local_code _ _ _ _ c huv
  have ha := Nat.left_le_pair A k
  have hc := Nat.right_le_pair c.val (2*Nat.pair A k)
  omega

private theorem endpoint_before_any_root_code (r x z A k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hr : r<A) (hx : x<A) (hA : 1<A) :
    2*Nat.pair r (Nat.pair c.val (2*(2*x+1)))+1<
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair A k)) := by
  have hl : A^2+A≤Nat.pair A k := by
    rw [Nat.pair]
    split_ifs with h
    · have hs := Nat.pow_le_pow_left h.le 2
      nlinarith
    · nlinarith
  have huv : 2*(2*x+1)<2*Nat.pair A k := by nlinarith
  apply q_before_local_code _ _ _ _ c huv
  have ha := Nat.left_le_pair A k
  have hc := Nat.right_le_pair c.val (2*Nat.pair A k)
  omega

private theorem pathChain_append_eq {V E : Type} [Fintype E] [DecidableEq E]
    {start finish : E → V} {u v w : V}
    (p : UndirectedPath start finish u v) (q : UndirectedPath start finish v w) :
    pathChain (p.append q)=pathChain p+pathChain q := by
  induction q with
  | nil => simp [UndirectedPath.append,pathChain]
  | @step a b q edge connects ih =>
    change pathChain (p.append q)+Pi.single edge (1:F)=
      pathChain p+(pathChain q+Pi.single edge (1:F))
    rw [ih]
    exact add_assoc _ _ _

private theorem pathChain_reverse_eq {V E : Type} [Fintype E] [DecidableEq E]
    {start finish : E → V} {u v : V} (p : UndirectedPath start finish u v) :
    pathChain p.reverse=pathChain p := by
  induction p with
  | nil => rfl
  | @step a b p edge connects ih =>
    let reversedEdge : UndirectedPath start finish b a :=
      .step .nil edge (by
        rcases connects with h | h
        · exact Or.inr h
        · exact Or.inl h)
    change pathChain (reversedEdge.append p.reverse)=pathChain p+Pi.single edge (1:F)
    rw [pathChain_append_eq,ih]
    change (0+Pi.single edge (1:F))+pathChain p=pathChain p+Pi.single edge (1:F)
    simpa only [zero_add] using add_comm (Pi.single edge (1:F)) (pathChain p)

private theorem path_append_support {V E : Type} [Fintype E] [DecidableEq E]
    {start finish : E → V} {u v w : V} (P : E → Prop)
    (p : UndirectedPath start finish u v) (q : UndirectedPath start finish v w)
    (hp : ∀ e, pathChain p e≠0 → P e)
    (hq : ∀ e, pathChain q e≠0 → P e) :
    ∀ e, pathChain (p.append q) e≠0 → P e := by
  intro e he
  rw [pathChain_append_eq,Pi.add_apply] at he
  by_cases h : pathChain p e=0
  · rw [h,zero_add] at he
    exact hq e he
  · exact hp e h

private theorem exists_path_substitution {V E V' E' : Type}
    [Fintype E'] [DecidableEq E']
    {start finish : E → V} {start' finish' : E' → V'}
    (f : V → V') (P : E' → Prop)
    (segments : ∀ e, ∃ p : UndirectedPath start' finish'
      (f (start e)) (f (finish e)), ∀ e', pathChain p e'≠0 → P e')
    {u v : V} (p : UndirectedPath start finish u v) :
    ∃ p' : UndirectedPath start' finish' (f u) (f v),
      ∀ e', pathChain p' e'≠0 → P e' := by
  induction p with
  | nil =>
    refine ⟨.nil,?_⟩
    intro e he
    exact False.elim (he (by simp [pathChain]))
  | @step a b p edge connects ih =>
    obtain ⟨initialPath,hprefix⟩ := ih
    obtain ⟨segment,hsegment⟩ := segments edge
    rcases connects with h | h
    · rcases h with ⟨hstart,hend⟩
      cases hstart
      cases hend
      exact ⟨initialPath.append segment,
        path_append_support P initialPath segment hprefix hsegment⟩
    · rcases h with ⟨hstart,hend⟩
      cases hstart
      cases hend
      refine ⟨initialPath.append segment.reverse,
        path_append_support P initialPath segment.reverse hprefix ?_⟩
      intro e he
      apply hsegment e
      simpa only [pathChain_reverse_eq] using he

private noncomputable def directFacePath0 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (n : Nat) (hn : n≤S.half) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f 0 0)
      (subdivisionGridVertex P x S f (gridAt S S.half le_rfl) (gridAt S n hn)) :=
  (horizontalAtRowPath P x S f 0 S.half le_rfl).append
    (verticalAtColumnPath P x S f (gridAt S S.half le_rfl) n hn)

private noncomputable def directFacePath1 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (n : Nat) (hn : n≤S.half) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f 0 0)
      (subdivisionGridVertex P x S f (gridAt S n hn) (gridAt S S.half le_rfl)) :=
  (verticalAtColumnPath P x S f 0 S.half le_rfl).append
    (horizontalAtRowPath P x S f (gridAt S S.half le_rfl) n hn)

private theorem directFacePath0_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (n : Nat) (hn : n≤S.half) :
    ∀ e, pathChain (directFacePath0 P x S f n hn) e≠0 →
      (∃ k : Fin S.half, e=.inl (xStarFaceXQEdge P x f 0,k)) ∨
      (∃ k : Fin S.half, e=.inl (xStarFaceQZEdge P x f 0,k)) := by
  apply path_append_support
  · intro e he
    obtain ⟨k,_,hk⟩ := horizontalAtRowPath_support P x S f 0 S.half le_rfl e he
    left
    refine ⟨k,?_⟩
    simpa [subdivisionHorizontalEdge] using hk
  · intro e he
    obtain ⟨k,_,hk⟩ := verticalAtColumnPath_support P x S f
      (gridAt S S.half le_rfl) n hn e he
    right
    refine ⟨k,?_⟩
    simpa [subdivisionVerticalEdge,gridAt,S.half_pos.ne'] using hk

private theorem directFacePath1_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (n : Nat) (hn : n≤S.half) :
    ∀ e, pathChain (directFacePath1 P x S f n hn) e≠0 →
      (∃ k : Fin S.half, e=.inl (xStarFaceXQEdge P x f 1,k)) ∨
      (∃ k : Fin S.half, e=.inl (xStarFaceQZEdge P x f 1,k)) := by
  apply path_append_support
  · intro e he
    obtain ⟨k,_,hk⟩ := verticalAtColumnPath_support P x S f 0 S.half le_rfl e he
    left
    refine ⟨k,?_⟩
    simpa [subdivisionVerticalEdge] using hk
  · intro e he
    obtain ⟨k,_,hk⟩ := horizontalAtRowPath_support P x S f
      (gridAt S S.half le_rfl) n hn e he
    right
    refine ⟨k,?_⟩
    simpa [subdivisionHorizontalEdge,gridAt,S.half_pos.ne'] using hk

private def baseEdgeCode : Edge baseTannerSquarePresentation → Nat
  | .inl e => 2*Nat.pair e.val.1.val e.val.2.val
  | .inr e => 2*Nat.pair e.val.1.val e.val.2.val+1

private def baseVertexCode : Vertex baseTannerSquarePresentation → Nat
  | .x x => 2*x.val
  | .q q => 4*q.val+1
  | .z z => 4*z.val+3

private theorem seedRadial_start_code (j : Fin 2) :
    baseVertexCode (xStarEdgeStart baseTannerSquarePresentation 0 (seedRadial j)).val=0 := by
  fin_cases j <;> decide

private theorem seedRadial_end_code (j : Fin 2) :
    baseVertexCode (xStarEdgeEnd baseTannerSquarePresentation 0 (seedRadial j)).val=
      4*j.val+1 := by
  fin_cases j <;> decide

private theorem stripFace_qz1_start_code (j : Fin 2) (x : BaseX) :
    baseVertexCode (xStarEdgeStart baseTannerSquarePresentation x
      (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1)).val=17 := by
  fin_cases j <;> fin_cases x <;> decide

private def subVertexCode (x : BaseX) (S : OddScale) :
    SubdivisionVertex baseTannerSquarePresentation x S → Nat
  | .inl v => 2*baseVertexCode v.val
  | .inr (.inl ⟨e,i⟩) => 4*Nat.pair (baseEdgeCode e.val) i.val+1
  | .inr (.inr ⟨f,i,j⟩) => 4*Nat.pair f.val.val (Nat.pair i.val j.val)+3

private def subEdgeCode (x : BaseX) (S : OddScale) :
    SubdivisionEdge baseTannerSquarePresentation x S → Nat
  | .inl ⟨e,i⟩ => 2*Nat.pair (baseEdgeCode e.val) i.val
  | .inr (.inl ⟨f,i,j⟩) => 4*Nat.pair f.val.val (Nat.pair i.val j.val)+1
  | .inr (.inr ⟨f,i,j⟩) => 4*Nat.pair f.val.val (Nat.pair i.val j.val)+3

private theorem encoded_old_X (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two)
    (v : SubdivisionVertex baseTannerSquarePresentation x S) :
    Encodable.encode (⟨x,(c,v)⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)=
      Nat.pair x.val (Nat.pair c.val (subVertexCode x S v)) := by
  rcases v with ⟨v,hv⟩ | ⟨⟨e,he⟩,i⟩ | ⟨f,i,j⟩
  · cases v with
    | x a => rfl
    | q a =>
      change Nat.pair x.val (Nat.pair c.val (2*(2*(2*a.val)+1)))=
        Nat.pair x.val (Nat.pair c.val (2*(4*a.val+1)))
      apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
      omega
    | z a =>
      change Nat.pair x.val (Nat.pair c.val (2*(2*(2*a.val+1)+1)))=
        Nat.pair x.val (Nat.pair c.val (2*(4*a.val+3)))
      apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
      omega
  · cases e with
    | inl a =>
      change Nat.pair x.val (Nat.pair c.val
        (2*(2*Nat.pair (2*Nat.pair a.val.1.val a.val.2.val) i.val)+1))=
        Nat.pair x.val (Nat.pair c.val
          (4*Nat.pair (2*Nat.pair a.val.1.val a.val.2.val) i.val+1))
      apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
      omega
    | inr a =>
      change Nat.pair x.val (Nat.pair c.val
        (2*(2*Nat.pair (2*Nat.pair a.val.1.val a.val.2.val+1) i.val)+1))=
        Nat.pair x.val (Nat.pair c.val
          (4*Nat.pair (2*Nat.pair a.val.1.val a.val.2.val+1) i.val+1))
      apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
      omega
  · change Nat.pair x.val (Nat.pair c.val
      (2*(2*Nat.pair f.val.val (Nat.pair i.val j.val)+1)+1))=
        Nat.pair x.val (Nat.pair c.val
          (4*Nat.pair f.val.val (Nat.pair i.val j.val)+3))
    apply congrArg (fun n => Nat.pair x.val (Nat.pair c.val n))
    omega

private theorem encoded_old_local_Q (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two)
    (e : SubdivisionEdge baseTannerSquarePresentation x S) :
    Encodable.encode (.inl ⟨x,.inl (c,e)⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)=
      2*Nat.pair x.val (2*Nat.pair c.val (subEdgeCode x S e)) := by
  rcases e with ⟨⟨e,he⟩,i⟩ | ⟨f,i,j⟩ | ⟨f,i,j⟩
  · cases e <;> rfl
  · change 2*Nat.pair x.val (2*Nat.pair c.val
      (2*(2*Nat.pair f.val.val (Nat.pair i.val j.val))+1))=
        2*Nat.pair x.val (2*Nat.pair c.val
          (4*Nat.pair f.val.val (Nat.pair i.val j.val)+1))
    apply congrArg (fun n => 2*Nat.pair x.val (2*Nat.pair c.val n))
    omega
  · change 2*Nat.pair x.val (2*Nat.pair c.val
      (2*(2*Nat.pair f.val.val (Nat.pair i.val j.val)+1)+1))=
        2*Nat.pair x.val (2*Nat.pair c.val
          (4*Nat.pair f.val.val (Nat.pair i.val j.val)+3))
    apply congrArg (fun n => 2*Nat.pair x.val (2*Nat.pair c.val n))
    omega

private def oldLocalStart (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) : (RawOne S).X :=
  ⟨x,tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S e⟩

private def oldLocalEnd (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) : (RawOne S).X :=
  ⟨x,tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S e⟩

private def oldLargestX (S : OddScale) : (r : (RawOne S).Q) → (RawOne S).X
  | .inl ⟨x,e⟩ =>
      if Encodable.encode (oldLocalStart S x e :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
        Encodable.encode (oldLocalEnd S x e :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) then oldLocalEnd S x e
      else oldLocalStart S x e
  | .inr q => ((rxState S baseState).admissible.toTannerSquareAdmissible.xqRoot (.inr q)).val

private theorem oldLargestX_incident (S : OddScale) (r : (RawOne S).Q) :
    (RawOne S).xq (oldLargestX S r) r=true := by
  rcases r with ⟨x,e⟩ | q
  · change (RawOne S).xq
      (if Encodable.encode (oldLocalStart S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
        Encodable.encode (oldLocalEnd S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)
       then oldLocalEnd S x e else oldLocalStart S x e) (.inl ⟨x,e⟩)=true
    split_ifs
    · exact (old_local_incidence S _ x e).2 (Or.inr rfl)
    · exact (old_local_incidence S _ x e).2 (Or.inl rfl)
  · exact ((rxState S baseState).admissible.toTannerSquareAdmissible.xqRoot (.inr q)).property

private theorem oldLargestX_start_le (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    Encodable.encode (oldLocalStart S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  exact code_larger_left
    (oldLocalStart S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    (oldLocalEnd S x e)

private theorem oldLargestX_end_le (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) :
    Encodable.encode (oldLocalEnd S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  exact code_larger_right
    (oldLocalStart S x e : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    (oldLocalEnd S x e)

private def largePorts (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) : PortVertices S := fun r =>
  match depth with
  | none => (c,.inl (.inr ⟨oldLargestX S r,oldLargestX_incident S r⟩))
  | some i => (c,.inr (⟨oldLargestX S r,oldLargestX_incident S r⟩,i))

private theorem encoded_largePorts (S : OddScale)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (r : (RawOne S).Q) :
    Encodable.encode (executableCoordinate S (.inr ⟨r,largePorts S c depth r⟩))=
      match depth with
      | none => 2*Nat.pair
          (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
          (Nat.pair c.val (2*(2*Encodable.encode (oldLargestX S r :
            (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1
      | some i => 2*Nat.pair
          (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
          (Nat.pair c.val (2*Nat.pair (Encodable.encode (oldLargestX S r :
            (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 := by
  cases depth with
  | none => exact encoded_endpoint S r (oldLargestX S r) (oldLargestX_incident S r) c
  | some i => exact encoded_interior S r (oldLargestX S r) (oldLargestX_incident S r) c i

private def gammaRadial (S : OddScale) (j : Fin 2) (n : Fin S.half) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial j,n))⟩

private theorem terminalOldKernel_gamma (S : OddScale) (j : Fin 2) :
    terminalOldKernel S j (gammaRadial S j (lastSegment S))=1 :=
  terminalOldKernel_target S j 0

private theorem pathChain_map_eq {V E V' E' : Type}
    [Fintype E] [Fintype E'] [DecidableEq E] [DecidableEq E']
    {start finish : E → V} {start' finish' : E' → V'}
    (f : V → V') (g : E → E')
    (hs : ∀ e, start' (g e)=f (start e)) (ht : ∀ e, finish' (g e)=f (finish e))
    {u v : V} (p : UndirectedPath start finish u v) :
    pathChain (p.map f g hs ht)=wordPushforward g (pathChain p) := by
  induction p with
  | nil => simp [UndirectedPath.map,pathChain]
  | @step a b p edge connects ih =>
    change pathChain (p.map f g hs ht)+Pi.single (g edge) (1:F)=
      wordPushforward g (pathChain p+Pi.single edge (1:F))
    rw [map_add,ih]
    apply congrArg (fun w : Word F E' => wordPushforward g (pathChain p)+w)
    simpa only [basis_eq_single] using (wordPushforward_canonicalBasis g edge).symm

private theorem pushforward_support {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (f : I → J) (w : Word F I) (j : J)
    (hj : wordPushforward f w j≠0) :
    ∃ i, w i≠0 ∧ j=f i := by
  rw [wordPushforward_apply] at hj
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  by_cases he : j=f i
  · rw [if_pos he] at hi
    exact ⟨i,hi,he⟩
  · rw [if_neg he] at hi
    exact False.elim (hi rfl)

private theorem face_of_qxz (P : TannerSquarePresentation) (x : P.X)
    (q : P.Q) (z : P.Z) (hx : P.xq x q=true) (hz : P.qz q z=true) :
    ∃ (f : XStarFace (transposePresentation P) z)
      (j : BDL26FiniteTannerSquare.Two), P.faceQ f.val j=q ∧ P.faceX f.val=x := by
  let shared : SharedQ P.data x z := ⟨q,by simp [hx,hz]⟩
  obtain ⟨⟨f,j⟩,hf⟩ := (P.perfectPairing x z).2 shared
  refine ⟨⟨f.val,(transposed_face_member P z f.val).mpr f.property.2⟩,j,?_,f.property.1⟩
  exact congrArg Subtype.val hf

private theorem qToZ_face_endpoint (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z)
    (f : XStarFace (transposePresentation P) z) (j : BDL26FiniteTannerSquare.Two)
    (hz : P.qz (P.faceQ f.val j) z=true) (S : OddScale) :
    qToZSubdivisionVertex P A (P.faceQ f.val j) z hz S
      (.inl (.inr ⟨P.faceX f.val,P.data.faceQ_xq f.val j⟩))=
      subdivisionGridVertex (transposePresentation P) z S f
        (gridAt S S.half le_rfl) (gridAt S S.half le_rfl) := by
  simp only [qToZSubdivisionVertex,subdivisionGridVertex,gridAt,S.half_pos.ne',
    ↓reduceDIte] <;> congr 1

private noncomputable def atCopyPath (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    {u v : SubdivisionVertex P x S}
    (p : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S) u v) :
    UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S) (c,u) (c,v) :=
  UndirectedPath.map
    (edgeStart':=tannerDoubleCylinderEdgeStart P x S)
    (edgeEnd':=tannerDoubleCylinderEdgeEnd P x S)
    (fun v : SubdivisionVertex P x S => (c,v))
    (fun e : SubdivisionEdge P x S => (Sum.inl (c,e) : DoubleCylinderEdge P x S))
    (fun _ => rfl) (fun _ => rfl) p

private theorem atCopyPath_support (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    {u v : SubdivisionVertex P x S}
    (p : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S) u v)
    (e : DoubleCylinderEdge P x S) (he : pathChain (atCopyPath P x S c p) e≠0) :
    ∃ e', pathChain p e'≠0 ∧ e=.inl (c,e') := by
  erw [atCopyPath,pathChain_map_eq] at he
  exact pushforward_support _ _ _ he

private theorem exists_directFaceAtCopy0 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (c : BDL26FiniteTannerSquare.Two)
    (n : Nat) (hn : n≤S.half) :
    ∃ p : UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (c,subdivisionGridVertex P x S f 0 0)
      (c,subdivisionGridVertex P x S f (gridAt S S.half le_rfl) (gridAt S n hn)),
      ∀ e, pathChain p e≠0 → ∃ (a : XStarEdge P x) (k : Fin S.half),
        e=.inl (c,.inl (a,k)) ∧
          (a=xStarFaceXQEdge P x f 0 ∨ a=xStarFaceQZEdge P x f 0) := by
  refine ⟨atCopyPath P x S c (directFacePath0 P x S f n hn),?_⟩
  intro e he
  obtain ⟨e',he',rfl⟩ := atCopyPath_support P x S c _ e he
  rcases directFacePath0_support P x S f n hn e' he' with h | h
  · obtain ⟨k,rfl⟩ := h
    exact ⟨_,k,rfl,Or.inl rfl⟩
  · obtain ⟨k,rfl⟩ := h
    exact ⟨_,k,rfl,Or.inr rfl⟩

private theorem exists_directFaceAtCopy1 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (c : BDL26FiniteTannerSquare.Two)
    (n : Nat) (hn : n≤S.half) :
    ∃ p : UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (c,subdivisionGridVertex P x S f 0 0)
      (c,subdivisionGridVertex P x S f (gridAt S n hn) (gridAt S S.half le_rfl)),
      ∀ e, pathChain p e≠0 → ∃ (a : XStarEdge P x) (k : Fin S.half),
        e=.inl (c,.inl (a,k)) ∧
          (a=xStarFaceXQEdge P x f 1 ∨ a=xStarFaceQZEdge P x f 1) := by
  refine ⟨atCopyPath P x S c (directFacePath1 P x S f n hn),?_⟩
  intro e he
  obtain ⟨e',he',rfl⟩ := atCopyPath_support P x S c _ e he
  rcases directFacePath1_support P x S f n hn e' he' with h | h
  · obtain ⟨k,rfl⟩ := h
    exact ⟨_,k,rfl,Or.inl rfl⟩
  · obtain ⟨k,rfl⟩ := h
    exact ⟨_,k,rfl,Or.inr rfl⟩

private def chosenPort (P : TannerSquarePresentation) (S : OddScale)
    (r : P.Q) (x : P.X) (hx : P.xq x r=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) : QDoubleCylinderVertex (transposePresentation P) r S :=
  match depth with
  | none => (c,.inl (.inr ⟨x,hx⟩))
  | some i => (c,.inr (⟨x,hx⟩,i))

private theorem encoded_chosenPort (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1))) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c depth⟩))=
      match depth with
      | none => 2*Nat.pair
          (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
          (Nat.pair c.val (2*(2*Encodable.encode (x :
            (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1
      | some i => 2*Nat.pair
          (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
          (Nat.pair c.val (2*Nat.pair (Encodable.encode (x :
            (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1))+1 := by
  cases depth with
  | none => exact encoded_endpoint S r x hx c
  | some i => exact encoded_interior S r x hx c i

private def zCenter (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (c : BDL26FiniteTannerSquare.Two) : ZDoubleCylinderVertex P z S :=
  (c,.inl ⟨.x z,by change decide (z=z)=true; exact decide_eq_true rfl⟩)

private theorem exists_supported_path_congr {V E : Type} [DecidableEq E]
    {start finish : E → V} {u u' v v' : V}
    (hu : u=u') (hv : v=v') (property : E → Prop) :
    (∃ p : UndirectedPath start finish u v, ∀ e, pathChain p e≠0 → property e) ↔
      (∃ p : UndirectedPath start finish u' v', ∀ e, pathChain p e≠0 → property e) := by
  cases hu
  cases hv
  rfl

private theorem exists_direct_face_port_path (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (z : P.Z)
    (f : XStarFace (transposePresentation P) z) (j : BDL26FiniteTannerSquare.Two)
    (hz : P.qz (P.faceQ f.val j) z=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (zCenter P S z c)
      (qToZDoubleCylinderVertex P A (P.faceQ f.val j) z hz S
        (chosenPort P S (P.faceQ f.val j) (P.faceX f.val)
          (P.data.faceQ_xq f.val j) c depth)),
      ∀ e, pathChain p e≠0 →
        ∃ (a : XStarEdge (transposePresentation P) z) (k : Fin S.half),
          e=.inl (c,.inl (a,k)) ∧
            (a=xStarFaceXQEdge (transposePresentation P) z f j ∨
              a=xStarFaceQZEdge (transposePresentation P) z f j) := by
  have hf : P.faceZ f.val=z := (transposed_face_member P z f.val).mp f.property
  have hcenter : (c,subdivisionGridVertex (transposePresentation P) z S f 0 0)=
      zCenter P S z c := by
    simp [subdivisionGridVertex,xStarFaceXVertex,zCenter,hf,Subtype.ext_iff,
      transposePresentation,transposeTannerSquareData,TannerSquarePresentation.faceX]
  fin_cases j
  · cases depth with
    | none =>
      have hend := congrArg (fun v => (c,v)) (qToZ_face_endpoint P A z f 0 hz S)
      apply (exists_supported_path_congr hcenter hend.symm _).mp
      exact exists_directFaceAtCopy0 (transposePresentation P) z S f c S.half le_rfl
    | some i =>
      have hend := congrArg (fun v => (c,v)) (qToZ_face_interior0 P A z f hz S i)
      apply (exists_supported_path_congr hcenter hend.symm _).mp
      exact exists_directFaceAtCopy0 (transposePresentation P) z S f c (i.val+1)
        (by have := i.isLt; omega)
  · cases depth with
    | none =>
      have hend := congrArg (fun v => (c,v)) (qToZ_face_endpoint P A z f 1 hz S)
      apply (exists_supported_path_congr hcenter hend.symm _).mp
      exact exists_directFaceAtCopy1 (transposePresentation P) z S f c S.half le_rfl
    | some i =>
      have hend := congrArg (fun v => (c,v)) (qToZ_face_interior1 P A z f hz S i)
      apply (exists_supported_path_congr hcenter hend.symm _).mp
      exact exists_directFaceAtCopy1 (transposePresentation P) z S f c (i.val+1)
        (by have := i.isLt; omega)

private theorem exists_direct_port_path (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q) (x : P.X) (z : P.Z)
    (hx : P.xq x r=true) (hz : P.qz r z=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (zCenter P S z c)
      (qToZDoubleCylinderVertex P A r z hz S (chosenPort P S r x hx c depth)),
      ∀ e, pathChain p e≠0 →
        ∃ (a : XStarEdge (transposePresentation P) z) (k : Fin S.half),
          e=.inl (c,.inl (a,k)) ∧
            (a.val=Sum.inl ⟨(z,r),hz⟩ ∨ a.val=Sum.inr ⟨(r,x),hx⟩) := by
  obtain ⟨f,j,hq,hx'⟩ := face_of_qxz P x r z hx hz
  cases hq
  cases hx'
  obtain ⟨p,hp⟩ := exists_direct_face_port_path P A S z f j hz c depth
  refine ⟨p,?_⟩
  intro e he
  obtain ⟨a,k,rfl,ha⟩ := hp e he
  refine ⟨a,k,rfl,?_⟩
  rcases ha with rfl | rfl
  · left
    have hf : P.faceZ f.val=z := (transposed_face_member P z f.val).mp f.property
    apply congrArg Sum.inl
    apply Subtype.ext
    exact Prod.ext hf rfl
  · right
    rfl

private theorem direct_port_path_property (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r : P.Q) (x : P.X) (z : P.Z)
    (hx : P.xq x r=true) (hz : P.qz r z=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1)))
    (property : ZDoubleCylinderEdge P z S → Prop)
    (hproperty : ∀ (a : XStarEdge (transposePresentation P) z) (k : Fin S.half),
      (a.val=Sum.inl ⟨(z,r),hz⟩ ∨ a.val=Sum.inr ⟨(r,x),hx⟩) →
        property (.inl (c,.inl (a,k)))) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (zCenter P S z c)
      (qToZDoubleCylinderVertex P A r z hz S (chosenPort P S r x hx c depth)),
      ∀ e, pathChain p e≠0 → property e := by
  obtain ⟨p,hp⟩ := exists_direct_port_path P A S r x z hx hz c depth
  refine ⟨p,?_⟩
  intro e he
  obtain ⟨a,k,rfl,ha⟩ := hp e he
  exact hproperty a k ha

private theorem between_direct_ports (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r0 r : P.Q) (x0 x : P.X)
    (z : P.Z) (hx0 : P.xq x0 r0=true) (hx : P.xq x r=true)
    (hz0 : P.qz r0 z=true) (hz : P.qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1))) :
    Nonempty (UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (qToZDoubleCylinderVertex P A r0 z hz0 S (chosenPort P S r0 x0 hx0 c depth))
      (qToZDoubleCylinderVertex P A r z hz S (chosenPort P S r x hx c depth))) := by
  obtain ⟨p0,_⟩ := exists_direct_port_path P A S r0 x0 z hx0 hz0 c depth
  obtain ⟨p,_⟩ := exists_direct_port_path P A S r x z hx hz c depth
  exact ⟨p0.reverse.append p⟩

private def directRoots (S : OddScale) (c : BDL26FiniteTannerSquare.Two) : PortRoots S :=
  fun z => zCenter (RawOne S) S z c

private def directPaths (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    PortPaths S (largePorts S c depth) (directRoots S c) := fun r z hz =>
  Classical.choose (exists_direct_port_path (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S r (oldLargestX S r) z
    (oldLargestX_incident S r) hz c depth)

private theorem directPaths_support (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (r : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true) (e : ZDoubleCylinderEdge (RawOne S) z S)
    (he : pathChain (directPaths S c depth r z hz) e≠0) :
    ∃ (a : XStarEdge (transposePresentation (RawOne S)) z) (k : Fin S.half),
      e=.inl (c,.inl (a,k)) ∧
        (a.val=Sum.inl ⟨(z,r),hz⟩ ∨
          a.val=Sum.inr ⟨(r,oldLargestX S r),oldLargestX_incident S r⟩) :=
  Classical.choose_spec (exists_direct_port_path (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S r (oldLargestX S r) z
    (oldLargestX_incident S r) hz c depth) e he

private theorem cast_root_star_member {P Q : TannerSquarePresentation} (h : P=Q)
    (r : Q.Q) (z : Q.Z) (hz : Q.qz r z=true)
    (hm : xStarEdgeMember (transposePresentation Q) z (Sum.inl ⟨(z,r),hz⟩)=true) :
    xStarEdgeMember (transposePresentation P)
      (cast (congrArg TannerSquarePresentation.Z h).symm z)
      (Sum.inl ⟨(cast (congrArg TannerSquarePresentation.Z h).symm z,
        cast (congrArg TannerSquarePresentation.Q h).symm r),cast_qz h r z hz⟩)=true := by
  cases h
  exact hm

private theorem cast_rz_root_segment (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (z : Q.Z) (hz : Q.qz r z=true)
    (hm : xStarEdgeMember (transposePresentation Q) z (Sum.inl ⟨(z,r),hz⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inl ⟨(z,r),hz⟩,hm⟩,k))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inl (⟨Sum.inl
          ⟨(cast (congrArg TannerSquarePresentation.Z h).symm z,
            cast (congrArg TannerSquarePresentation.Q h).symm r),cast_qz h r z hz⟩,
          cast_root_star_member h r z hz hm⟩,k))⟩ := by
  cases h
  rfl

private theorem encoded_root_segment (S : OddScale) (r : (RawOne S).Q)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hm : xStarEdgeMember (transposePresentation (RawOne S)) z
      (Sum.inl ⟨(z,r),hz⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inl ⟨(z,r),hz⟩,hm⟩,k))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*Nat.pair
          (2*Nat.pair
            (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
            (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))) k.val)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_root_segment S (executableLevelOne_eq_raw S) r z hz hm c k]
  rfl

private theorem cast_x_star_member {P Q : TannerSquarePresentation} (h : P=Q)
    (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true) (z : Q.Z)
    (hm : xStarEdgeMember (transposePresentation Q) z (Sum.inr ⟨(r,x),hx⟩)=true) :
    xStarEdgeMember (transposePresentation P)
      (cast (congrArg TannerSquarePresentation.Z h).symm z)
      (Sum.inr ⟨(cast (congrArg TannerSquarePresentation.Q h).symm r,
        cast (congrArg TannerSquarePresentation.X h).symm x),cast_xq h r x hx⟩)=true := by
  cases h
  exact hm

private theorem cast_rz_x_segment (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (r : Q.Q) (x : Q.X) (hx : Q.xq x r=true) (z : Q.Z)
    (hm : xStarEdgeMember (transposePresentation Q) z (Sum.inr ⟨(r,x),hx⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inr ⟨(r,x),hx⟩,hm⟩,k))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inl (⟨Sum.inr
          ⟨(cast (congrArg TannerSquarePresentation.Q h).symm r,
            cast (congrArg TannerSquarePresentation.X h).symm x),cast_xq h r x hx⟩,
          cast_x_star_member h r x hx z hm⟩,k))⟩ := by
  cases h
  rfl

private theorem encoded_x_segment (S : OddScale) (r : (RawOne S).Q)
    (x : (RawOne S).X) (hx : (RawOne S).xq x r=true) (z : (RawOne S).Z)
    (hm : xStarEdgeMember (transposePresentation (RawOne S)) z
      (Sum.inr ⟨(r,x),hx⟩)=true)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inr ⟨(r,x),hx⟩,hm⟩,k))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*Nat.pair
          (2*Nat.pair
            (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
            (Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X))+1) k.val)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_x_segment S (executableLevelOne_eq_raw S) r x hx z hm c k]
  rfl

private theorem chosen_code_before_root {m : Nat} (r x z A k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin m))
    (hr : r<A) (hx : x<A) (hA : 1<A)
    (hi : ∀ i, depth=some i → i.val<A) :
    (match depth with
      | none => 2*Nat.pair r (Nat.pair c.val (2*(2*x+1)))+1
      | some i => 2*Nat.pair r (Nat.pair c.val (2*Nat.pair x i.val+1))+1)<
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair A k)) := by
  cases depth with
  | none => exact endpoint_before_any_root_code r x z A k c hr hx hA
  | some i => exact interior_before_any_root_code r x z A i.val k c hr hx (hi i rfl)

private theorem pair_parameter_bounds (r a b : Nat) (hr : 0<r) (h : r≤ max a b) :
    r<2*Nat.pair a b ∧ r^2<2*Nat.pair a b ∧ 1<2*Nat.pair a b := by
  have hsq := Nat.pow_le_pow_left h 2
  have hl := Nat.max_sq_add_min_le_pair a b
  have hself : r≤r^2 := Nat.le_self_pow (by decide) r
  have hpos : 0<r^2 := by positivity
  omega

private theorem direct_root_segment_later (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hr0 : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX0 : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2)
    (hm : xStarEdgeMember (transposePresentation (RawOne S)) z
      (Sum.inl ⟨(z,r),hz⟩)=true) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
      Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inl ⟨(z,r),hz⟩,hm⟩,k))⟩)) := by
  have hroot := pair_parameter_bounds K
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) hK
    (hr.trans (Nat.le_max_right _ _))
  have hnum := chosen_code_before_root
    (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (2*Nat.pair
      (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)))
    k.val c depth (hr0.trans_lt hroot.2.1) (hX0.trans_lt hroot.2.1)
    hroot.2.2 (fun i he => (hi i he).trans hroot.2.1)
  cases depth with
  | none =>
      exact (encoded_chosenPort S r0 x0 hx0 c none).trans_lt
        (hnum.trans_eq (encoded_root_segment S r z hz hm c k).symm)
  | some i =>
      exact (encoded_chosenPort S r0 x0 hx0 c (some i)).trans_lt
        (hnum.trans_eq (encoded_root_segment S r z hz hm c k).symm)

private theorem direct_x_segment_later (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hr0 : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX0 : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2)
    (hm : xStarEdgeMember (transposePresentation (RawOne S)) z
      (Sum.inr ⟨(r,x),hx⟩)=true) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
      Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inl (⟨Sum.inr ⟨(r,x),hx⟩,hm⟩,k))⟩)) := by
  let R := Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  let X := Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)
  have harm := pair_parameter_bounds K R X hK (hr.trans (Nat.le_max_left R X))
  have hR : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      2*Nat.pair R X+1 := hr0.trans_lt (harm.2.1.trans_le (Nat.le_succ _))
  have hX : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      2*Nat.pair R X+1 := hX0.trans_lt (harm.2.1.trans_le (Nat.le_succ _))
  have hnum := chosen_code_before_root
    (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (2*Nat.pair R X+1) k.val c depth hR hX (by omega)
    (fun i he => (hi i he).trans (harm.2.1.trans_le (Nat.le_succ _)))
  cases depth with
  | none =>
      exact (encoded_chosenPort S r0 x0 hx0 c none).trans_lt
        (hnum.trans_eq (encoded_x_segment S r x hx z hm c k).symm)
  | some i =>
      exact (encoded_chosenPort S r0 x0 hx0 c (some i)).trans_lt
        (hnum.trans_eq (encoded_x_segment S r x hx z hm c k).symm)

private theorem direct_segment_later (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hr0 : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX0 : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2)
    (a : XStarEdge (transposePresentation (RawOne S)) z) (k : Fin S.half)
    (ha : a.val=Sum.inl ⟨(z,r),hz⟩ ∨ a.val=Sum.inr ⟨(r,x),hx⟩) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,.inl (c,.inl (a,k))⟩)) := by
  rcases a with ⟨a,hm⟩
  rcases ha with ha | ha
  · change a=_ at ha
    subst a
    exact direct_root_segment_later S r0 r x0 x hx0 hx z hz c depth
      K hK hr hr0 hX0 hi hm k
  · change a=_ at ha
    subst a
    exact direct_x_segment_later S r0 r x0 x hx0 hx z hz c depth
      K hK hr hr0 hX0 hi hm k

private theorem largePorts_eq_chosen (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (r : (RawOne S).Q) :
    largePorts S c depth r=chosenPort (RawOne S) S r (oldLargestX S r)
      (oldLargestX_incident S r) c depth := by
  cases depth <;> rfl

private theorem directPaths_later (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (r0 r : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true)
    (hr0 : 0<Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hrr : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hx0 : Encodable.encode (oldLargestX S r0 :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))^2)
    (hi : ∀ i, depth=some i → i.val<
      (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))^2)
    (e : ZDoubleCylinderEdge (RawOne S) z S)
    (he : pathChain (directPaths S c depth r z hz) e≠0) :
    Encodable.encode (executableCoordinate S (.inr ⟨r0,largePorts S c depth r0⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)) := by
  obtain ⟨a,k,heq,ha⟩ := directPaths_support S c depth r z hz e he
  rw [heq,largePorts_eq_chosen]
  exact direct_segment_later S r0 r (oldLargestX S r0) (oldLargestX S r)
    (oldLargestX_incident S r0) (oldLargestX_incident S r) z hz c depth
    (Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    hr0 hrr (Nat.le_self_pow (by decide) _) hx0 hi a k ha

private theorem pair_zero_left_sq (n : Nat) : Nat.pair 0 n=n^2 := by
  rw [Nat.pair]
  split_ifs with h
  · ring
  · have hn : n=0 := by omega
    subst n
    rfl

private theorem encoded_gammaRadial (S : OddScale) (j : Fin 2) (n : Fin S.half) :
    Encodable.encode (gammaRadial S j n :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)=
      128*(Nat.pair (2*j.val) n.val)^4 := by
  erw [gammaRadial,encoded_old_local_Q]
  change 2*Nat.pair 0 (2*Nat.pair 0
    (2*Nat.pair (2*Nat.pair 0 j.val) n.val))=128*(Nat.pair (2*j.val) n.val)^4
  simp only [pair_zero_left_sq]
  fin_cases j <;> norm_num <;> ring

private theorem pair_mono_right (a b d : Nat) (h : b≤d) :
    Nat.pair a b≤Nat.pair a d := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (Nat.pair_lt_pair_right a h).le
  · exact le_rfl

private theorem seedRadial_code (j : Fin 2) :
    baseEdgeCode (seedRadial j).val=2*j.val := by
  fin_cases j <;> decide

private theorem encoded_old_X_copy0 (S : OddScale)
    (v : SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) S) :
    Encodable.encode (⟨(0 : BaseX),(0,v)⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)=(subVertexCode 0 S v)^4 := by
  calc
    _ = Nat.pair 0 (Nat.pair 0 (subVertexCode 0 S v)) := encoded_old_X S 0 0 v
    _ = (subVertexCode 0 S v)^4 := by
      simp only [pair_zero_left_sq]
      ring

private theorem radial_tag_fourth_bound (p v : Nat) (hp : 0<p)
    (hv : v≤4*p+1 ∨ v≤10) : v^4≤(128*p^4)^2 := by
  have hp4 : 1≤p^4 := Nat.succ_le_of_lt (pow_pos hp 4)
  have hself : p^4≤(p^4)^2 := Nat.le_self_pow (by decide) (p^4)
  rcases hv with hv | hv
  · have hv' : v≤5*p := by omega
    have hpow := Nat.pow_le_pow_left hv' 4
    have hscaled : (5*p)^4=625*p^4 := by ring
    rw [hscaled] at hpow
    have hbig : 625*p^4≤(128*p^4)^2 := by nlinarith
    exact hpow.trans hbig
  · have hpow := Nat.pow_le_pow_left hv 4
    have hbig : 10^4≤(128*p^4)^2 := by nlinarith
    exact hpow.trans hbig

private theorem gammaLargestX_le_square (S : OddScale) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) :
    Encodable.encode (oldLargestX S (gammaRadial S j n) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      (Encodable.encode (gammaRadial S j n :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q))^2 := by
  let p := Nat.pair (2*j.val) n.val
  have hp : 0<p := by
    have hleft := Nat.left_le_pair (2*j.val) n.val
    have hright := Nat.right_le_pair (2*j.val) n.val
    dsimp [p]
    omega
  have hstart : Encodable.encode (oldLocalStart S 0
      (.inl (0,.inl (seedRadial j,n))) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(128*p^4)^2 := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial j) n)⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0]
    unfold subdivisionSegmentStart
    split_ifs with hzero
    · erw [seedRadial_start]
      change (0 : Nat)≤_
      exact Nat.zero_le _
    · apply radial_tag_fourth_bound p _ hp
      left
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) (n.val-1)+1≤4*p+1
      rw [seedRadial_code]
      have hm := pair_mono_right (2*j.val) (n.val-1) n.val (Nat.sub_le _ _)
      dsimp [p]
      omega
  have hend : Encodable.encode (oldLocalEnd S 0
      (.inl (0,.inl (seedRadial j,n))) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(128*p^4)^2 := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial j) n)⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0]
    unfold subdivisionSegmentEnd
    split_ifs with hlast
    · apply radial_tag_fourth_bound p _ hp
      right
      change 2*(4*j.val+1)≤10
      have := j.isLt
      omega
    · apply radial_tag_fourth_bound p _ hp
      left
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) n.val+1≤4*p+1
      rw [seedRadial_code]
  erw [encoded_gammaRadial]
  change Encodable.encode (oldLargestX S (.inl ⟨(0 : BaseX),
    .inl (0,.inl (seedRadial j,n))⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(128*p^4)^2
  exact code_larger_upper _ _ _ hstart hend

private theorem gamma_index_le_code (S : OddScale) (j : Fin 2) (n : Fin S.half) :
    n.val≤Encodable.encode (gammaRadial S j n :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [encoded_gammaRadial]
  have hright := Nat.right_le_pair (2*j.val) n.val
  have hself : Nat.pair (2*j.val) n.val≤(Nat.pair (2*j.val) n.val)^4 :=
    Nat.le_self_pow (by decide) _
  omega

private theorem gamma_code_pos (S : OddScale) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) :
    0<Encodable.encode (gammaRadial S j n :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [encoded_gammaRadial]
  have hleft := Nat.left_le_pair (2*j.val) n.val
  have hright := Nat.right_le_pair (2*j.val) n.val
  have hp : 0<Nat.pair (2*j.val) n.val := by omega
  positivity

private theorem pair_mono_left (a b d : Nat) (h : a≤b) :
    Nat.pair a d≤Nat.pair b d := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (Nat.pair_lt_pair_left d h).le
  · exact le_rfl

private theorem largePorts_later (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (r0 r : (RawOne S).Q) (hne : r≠r0)
    (hr : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hx : Encodable.encode (oldLargestX S r0 :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) :
    Encodable.encode (executableCoordinate S (.inr ⟨r0,largePorts S c depth r0⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,largePorts S c depth r⟩)) := by
  have hR : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
    have hne' : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≠
        Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) :=
      fun he => hne (Encodable.encode_injective he).symm
    omega
  cases depth with
  | none =>
    rw [encoded_largePorts,encoded_largePorts]
    dsimp only
    have ht := pair_mono_right c.val
      (2*(2*Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)+1))
      (2*(2*Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)) (by omega)
    have hfirst := Nat.pair_lt_pair_left
      (Nat.pair c.val (2*(2*Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)+1))) hR
    have hsecond := pair_mono_right
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) _ _ ht
    omega
  | some i =>
    rw [encoded_largePorts,encoded_largePorts]
    dsimp only
    have ht0 := pair_mono_left
      (Encodable.encode (oldLargestX S r0 : (BDL26LevelTwoDecoder.executableLevelOne S).X))
      (Encodable.encode (oldLargestX S r : (BDL26LevelTwoDecoder.executableLevelOne S).X))
      i.val hx
    have ht := pair_mono_right c.val
      (2*Nat.pair (Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1)
      (2*Nat.pair (Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1) (by omega)
    have hfirst := Nat.pair_lt_pair_left
      (Nat.pair c.val (2*Nat.pair (Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1)) hR
    have hsecond := pair_mono_right
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) _ _ ht
    omega

/- Source-only insertion snippets for the existing RXPrimitiveC2QEndpoint namespace.
   Not compiled. The owner remains the only editor of the production module. -/

private theorem interior_before_far_last_radial_code (r x z A i k : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hri : r< i) (hxi : x< i) (hik : i<k) :
    2*Nat.pair r (Nat.pair c.val (2*Nat.pair x i+1))+1 <
      2*Nat.pair z (2*Nat.pair c.val (2*Nat.pair A k)) := by
  have hp : Nat.pair x i=i*i+x := by simp [Nat.pair,hxi]
  have hik' : i+1≤k := by omega
  have hs := Nat.pow_le_pow_left hik' 2
  have hm := Nat.pow_le_pow_left (Nat.le_max_right A k) 2
  have hl := Nat.max_sq_add_min_le_pair A k
  have hsquare : (i+1)^2≤Nat.pair A k :=
    hs.trans (hm.trans ((Nat.le_add_right _ _).trans hl))
  have huv : 2*Nat.pair x i+1<2*Nat.pair A k := by
    rw [hp]
    nlinarith [hsquare]
  apply q_before_local_code _ _ _ _ c huv
  have hk := Nat.right_le_pair A k
  have hc := Nat.right_le_pair c.val (2*Nat.pair A k)
  omega

private def halfOneTinyPotential (S : OddScale) : Word F (RawOne S).X :=
  canonicalBasisWord ⟨(0 : BaseX),(0,.inl seedCenter)⟩+
    canonicalBasisWord ⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩

private def halfOneTinyKernel (S : OddScale) : Word F (RawOne S).Q :=
  tannerCoboundary0 (RawOne S) (halfOneTinyPotential S)

private theorem old_X_coordinate_eq (S : OddScale) (x y : BaseX)
    (c d : BDL26FiniteTannerSquare.Two)
    (u : SubdivisionVertex baseTannerSquarePresentation x S)
    (v : SubdivisionVertex baseTannerSquarePresentation y S) :
    ((⟨x,(c,u)⟩ : RX0 baseTannerSquarePresentation S)=⟨y,(d,v)⟩) ↔
      x=y ∧ c=d ∧ HEq u v := by
  constructor
  · intro h
    rcases Sigma.mk.inj_iff.mp h with ⟨rfl,hpair⟩
    have hp := eq_of_heq hpair
    exact ⟨rfl,congrArg Prod.fst hp,heq_of_eq (congrArg Prod.snd hp)⟩
  · rintro ⟨rfl,rfl,h⟩
    have hv := eq_of_heq h
    cases hv
    rfl

private theorem two_basis_value_with_decisions {I : Type} (u v x : I)
    (du : Decidable (x=u)) (dv : Decidable (x=v)) :
    ((canonicalBasisWord (F:=F) u+canonicalBasisWord v : Word F I)) x=
      @ite F (x=u) du 1 0+@ite F (x=v) dv 1 0 := by
  have h := two_basis_value u v x
  exact h.trans (congrArg₂ (fun a b : F => a+b)
    (@indicator_iff (x=u) (x=u) (Classical.propDecidable _) du Iff.rfl)
    (@indicator_iff (x=v) (x=v) (Classical.propDecidable _) dv Iff.rfl))

private theorem halfOneTinyPotential_value (S : OddScale)
    (x : RX0 baseTannerSquarePresentation S) :
    halfOneTinyPotential S x=
      (if x=⟨(0 : BaseX),(0,.inl seedCenter)⟩ then (1:F) else 0)+
      (if x=⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩ then 1 else 0) := by
  change ((canonicalBasisWord (F:=F)
      (⟨(0 : BaseX),(0,.inl seedCenter)⟩ : RX0 baseTannerSquarePresentation S)+
    canonicalBasisWord (F:=F)
      (⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩ : RX0 baseTannerSquarePresentation S) :
        Word F (RX0 baseTannerSquarePresentation S)) x)=_
  exact two_basis_value_with_decisions _ _ x _ _

private theorem halfOneTinyPotential_local_value (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two)
    (v : SubdivisionVertex baseTannerSquarePresentation x S) :
    halfOneTinyPotential S ⟨x,(c,v)⟩=
      if x.val=0 ∧ c.val=0 then
        match v with
        | .inl node => match node.val with
            | .x y => if y.val=0 then (1:F) else 0
            | .q q => if q.val=0 then 1 else 0
            | .z _ => 0
        | .inr _ => 0
      else 0 := by
  have hvalue := halfOneTinyPotential_value S
    (⟨x,(c,v)⟩ : RX0 baseTannerSquarePresentation S)
  have h0 := old_X_coordinate_eq S x (0 : BaseX) c 0 v (.inl seedCenter)
  have h1 := old_X_coordinate_eq S x (0 : BaseX) c 0 v (.inl (seedQVertex 0))
  have hn : halfOneTinyPotential S ⟨x,(c,v)⟩=
      (if x=(0 : BaseX) ∧ c=0 ∧ HEq v (.inl seedCenter : SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) S) then (1:F) else 0)+
      (if x=(0 : BaseX) ∧ c=0 ∧ HEq v (.inl (seedQVertex 0) : SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) S) then 1 else 0) := by
    exact hvalue.trans (congrArg₂ (fun a b : F => a+b)
      (indicator_iff _ _ h0) (indicator_iff _ _ h1))
  rw [hn]
  by_cases hx : x=(0 : BaseX)
  · subst x
    by_cases hc : c=0
    · subst c
      rcases v with ⟨v,hv⟩ | ⟨⟨edge,he⟩,i⟩ | ⟨f,i,k⟩
      · cases v with
        | x y =>
            simp [seedCenter,seedQVertex,seedQ,heq_eq_eq,Subtype.ext_iff,
              base_X_eq_value,Fin.ext_iff]
            have hz : ((0 : baseTannerSquarePresentation.X) : BaseX).val=0 := rfl
            simpa only [hz]
        | q q =>
            simp [seedCenter,seedQVertex,seedQ,heq_eq_eq,Subtype.ext_iff,
              base_Q_eq_value,Fin.ext_iff]
            apply indicator_iff
            constructor
            · intro h
              have hq : q=(0 : BaseQubit) := Vertex.q.inj h
              exact congrArg (fun r : BaseQubit => r.val) hq
            · intro h
              have hq : q=(0 : BaseQubit) := Fin.ext h
              exact congrArg (fun r : baseTannerSquarePresentation.Q =>
                (Vertex.q r : Vertex baseTannerSquarePresentation)) hq
        | z z =>
            simp [seedCenter,seedQVertex,seedQ,heq_eq_eq,Subtype.ext_iff]
      · simp [heq_eq_eq]
      · simp [heq_eq_eq]
    · have hcv : c.val≠0 := by
        intro h
        exact hc (Fin.ext h)
      simp only [hc,false_and,and_false,if_false,zero_add,Fin.val_zero,hcv]
  · have hxv : x.val≠0 := by
      intro h
      exact hx (Fin.ext h)
    simp only [hx,false_and,if_false,zero_add,hxv]

private theorem halfOneTinyKernel_closed (S : OddScale) :
    tannerCoboundary1 (RawOne S) (halfOneTinyKernel S)=0 := by
  have h := LinearMap.congr_fun
    (BDL26LevelTwoDistance.tannerCoboundary_squared (RawOne S))
    (halfOneTinyPotential S)
  exact h

private theorem halfOneTinyKernel_target (S : OddScale) :
    halfOneTinyKernel S (.inr ⟨seedQ 0,(0,.inl (.inl ()))⟩)=1 := by
  erw [halfOneTinyKernel,
    BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
      baseTannerSquarePresentation baseTannerSquareAdmissibleV4
      baseTannerSquareCellularRegular S,
    seed_cone_gradient]
  change ((canonicalBasisWord (F:=F)
    (⟨(0 : BaseX),(0,.inl seedCenter)⟩ : (RawOne S).X)+
    canonicalBasisWord (F:=F)
    (⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩ : (RawOne S).X)) :
    Word F (RawOne S).X) ⟨(0 : BaseX),(0,.inl (seedQVertex 0))⟩=1
  rw [word_add_eval,basis_value,basis_value]
  have hne : (⟨(0 : BaseX),(0,Sum.inl (seedQVertex 0))⟩ : (RawOne S).X)≠
      ⟨(0 : BaseX),(0,Sum.inl seedCenter)⟩ := by
    intro h
    have hv := congrArg Prod.snd (sigma_same_index_inj _ _ h)
    have hvertex := congrArg Subtype.val (Sum.inl.inj hv)
    cases hvertex
  simp only [if_neg hne,if_pos rfl,if_true,zero_add]

private def firstCutMember (x : BaseX) (S : OddScale) :
    SubdivisionVertex baseTannerSquarePresentation x S → Bool
  | .inl node => match node.val with
      | .x _ => false
      | .q q => decide (q=stripQ 1 x)
      | .z z => decide (z=(1 : BaseZ))
  | .inr (.inl edgeInterior) => match edgeInterior.1.val with
      | .inl e => decide (e.val.2=stripQ 1 x)
      | .inr e => decide (e.val.2=(1 : BaseZ))
  | .inr (.inr faceInterior) => decide (faceInterior.1=stripFace 1 x)

private def firstCutPotential (S : OddScale) : Word F (RawOne S).X :=
  fun ⟨x,(_,v)⟩ => if firstCutMember x S v then 1 else 0

private def firstCutOldKernel (S : OddScale) : Word F (RawOne S).Q :=
  rawSeedLift S 1+tannerCoboundary0 (RawOne S) (firstCutPotential S)

private theorem firstCutOldKernel_closed (S : OddScale) :
    tannerCoboundary1 (RawOne S) (firstCutOldKernel S)=0 := by
  have hrx := LinearMap.congr_fun
    (BDL26ReplacementCochainMaps.rxMap_commutes_coboundary1
      baseTannerSquarePresentation S) (stripSeedCocycle 1)
  change BDL26ReplacementCochainMaps.rxCoboundary1 baseTannerSquarePresentation S
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        (stripSeedCocycle 1))=
    BDL26ReplacementCochainMaps.rxMap2Coord baseTannerSquarePresentation S
      (tannerCoboundary1 baseTannerSquarePresentation (stripSeedCocycle 1)) at hrx
  rw [stripSeedCocycle_closed,map_zero] at hrx
  have hmap : tannerCoboundary1 (RawOne S)
      (BDL26ReplacementCochainMaps.rxMap1Coord baseTannerSquarePresentation S
        (stripSeedCocycle 1))=0 := by
    erw [BDL26RXLocalReplacement.rxPresentation_coboundary1_eq
      baseTannerSquarePresentation baseTannerSquareAdmissibleV4
      baseTannerSquareCellularRegular S]
    exact hrx
  have hb := LinearMap.congr_fun
    (BDL26LevelTwoDistance.tannerCoboundary_squared (RawOne S)) (firstCutPotential S)
  change tannerCoboundary1 (RawOne S)
    (tannerCoboundary0 (RawOne S) (firstCutPotential S))=0 at hb
  have hmap' : tannerCoboundary1 (RawOne S) (rawSeedLift S 1)=0 := hmap
  exact linear_word_add_zero (tannerCoboundary1 (RawOne S))
    (rawSeedLift S 1) (tannerCoboundary0 (RawOne S) (firstCutPotential S)) hmap' hb

/- Source-only, not compiled; insert after concrete-snippets definitions. -/
private theorem firstCutMember_face_x (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    firstCutMember x S (.inl (xStarFaceXVertex _ _ f))=false := rfl

private theorem firstCutMember_face_q (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two) :
    firstCutMember x S (.inl (xStarFaceQVertex _ _ f c))=
      decide (f=stripFace 1 x ∧ c=0) := by
  dsimp only [firstCutMember,xStarFaceQVertex]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega

private theorem firstCutMember_face_z (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) :
    firstCutMember x S (.inl (xStarFaceZVertex _ _ f))=
      decide (f=stripFace 1 x) := by
  dsimp only [firstCutMember,xStarFaceZVertex]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases x <;> fin_cases k
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega

private theorem firstCutMember_face_xq (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    firstCutMember x S (.inr (.inl (xStarFaceXQEdge _ _ f c,i)))=
      decide (f=stripFace 1 x ∧ c=0) := by
  dsimp only [firstCutMember,xStarFaceXQEdge,faceXQEdge]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega

private theorem firstCutMember_face_qz (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    firstCutMember x S (.inr (.inl (xStarFaceQZEdge _ _ f c,i)))=
      decide (f=stripFace 1 x) := by
  dsimp only [firstCutMember,xStarFaceQZEdge,faceQZEdge]
  apply Bool.decide_congr
  obtain ⟨k,rfl⟩ := base_star_face_cases x f
  dsimp only [stripFace,stripQ,XStarFace,TannerSquarePresentation.X,
    TannerSquarePresentation.Q,TannerSquarePresentation.Z,TannerSquarePresentation.Face,
    TannerSquarePresentation.faceX,TannerSquarePresentation.faceQ,TannerSquarePresentation.faceZ,
    TannerSquarePresentation.xq,TannerSquarePresentation.qz,
    baseTannerSquarePresentation,baseTannerSquareData,baseZeroX,
    BaseX,BaseQubit,BaseZ,BaseFace,BDL26FiniteTannerSquare.Two] at *
  fin_cases x <;> fin_cases k <;> fin_cases c
  all_goals
    norm_num [baseFaceQ,baseFaceZ,Subtype.ext_iff,
      raw_two_eq_value,raw_four_eq_value,raw_five_eq_value,
      Fin.val_mk,Fin.val_zero,Fin.val_one]
  all_goals first | rfl | omega

private theorem firstCutMember_face_cell (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (i k : Fin (S.half-1)) :
    firstCutMember x S (.inr (.inr (f,i,k)))=decide (f=stripFace 1 x) := rfl

private theorem firstCutMember_grid (S : OddScale) (x : BaseX)
    (f : XStarFace baseTannerSquarePresentation x) (a b : Fin (S.half+1)) :
    firstCutMember x S (subdivisionGridVertex baseTannerSquarePresentation x S f a b)=
      decide (f=stripFace 1 x ∧ a.val≠0) := by
  have hm : S.half≠0 := S.half_pos.ne'
  have h01 : (0 : BDL26FiniteTannerSquare.Two)≠1 := by decide
  have h10 : (1 : BDL26FiniteTannerSquare.Two)≠0 := by decide
  by_cases hf : f=stripFace 1 x
  all_goals erw [grid_vertex_view]
  all_goals split_ifs
  all_goals simp_all only [firstCutMember_face_x,firstCutMember_face_q,firstCutMember_face_z,
    firstCutMember_face_xq,firstCutMember_face_qz,firstCutMember_face_cell,hm,Ne.symm hm,h01,h10,
    true_and,false_and,and_true,and_false,decide_true,decide_false,
    Bool.false_eq_true,Bool.true_eq_false,not_true_eq_false,not_false_eq_true]
  all_goals simp_all

private theorem firstCutOldKernel_horizontal (S : OddScale)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (f : XStarFace baseTannerSquarePresentation x) (i : Fin S.half)
    (row : Fin (S.half+1)) :
    firstCutOldKernel S (.inl ⟨x,.inl (c,
      subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)⟩)=
      if f=stripFace 1 x ∧ i.val=0 then 1 else 0 := by
  erw [firstCutOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,rx_local_gradient]
  change (if firstCutMember x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)) then
      (1:F) else 0)+
    (if firstCutMember x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S f i row)) then
      (1:F) else 0)=_
  erw [own_horizontal_start,own_horizontal_end,
    firstCutMember_grid,firstCutMember_grid]
  by_cases hf : f=stripFace 1 x <;> by_cases hi : i.val=0
  all_goals simp [finCastGrid,finSuccGrid,hf,hi,ZModModule.add_self]

private theorem firstCutOldKernel_vertical (S : OddScale)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (f : XStarFace baseTannerSquarePresentation x) (column : Fin (S.half+1))
    (i : Fin S.half) :
    firstCutOldKernel S (.inl ⟨x,.inl (c,
      subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)⟩)=0 := by
  erw [firstCutOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,rx_local_gradient]
  change (if firstCutMember x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)) then
      (1:F) else 0)+
    (if firstCutMember x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (subdivisionVerticalEdge baseTannerSquarePresentation x S f column i)) then
      (1:F) else 0)=0
  erw [own_vertical_start,own_vertical_end,
    firstCutMember_grid,firstCutMember_grid]
  exact ZModModule.add_self _

private theorem stripFace_xq_code (j : Fin 2) (x : BaseX) :
    baseEdgeCode (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0).val=
      2*Nat.pair x.val (j.val+2*x.val) := by
  fin_cases j <;> fin_cases x <;> decide

private theorem stripFace_qz_code (j : Fin 2) (x : BaseX) :
    baseEdgeCode (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1).val=
      41+2*j.val := by
  fin_cases j <;> fin_cases x <;> decide

private theorem strip_inner_edge_code (j : Fin 2) (x : BaseX) (n k : Nat)
    (hn : 1≤n) (hk : k<n) :
    2*Nat.pair (2*j.val) n<4*Nat.pair (j.val+2*x.val) (Nat.pair n k)+1 := by
  have hf := pair_mono_left j.val (j.val+2*x.val) (Nat.pair n k) (by omega)
  suffices h : 2*Nat.pair (2*j.val) n<4*Nat.pair j.val (Nat.pair n k)+1 by omega
  fin_cases j
  · change 2*Nat.pair 0 n<4*Nat.pair 0 (Nat.pair n k)+1
    rw [pair_zero_left_sq,pair_zero_left_sq]
    have hs := Nat.pow_le_pow_left (Nat.left_le_pair n k) 2
    omega
  · change 2*Nat.pair 2 n<4*Nat.pair 1 (Nat.pair n k)+1
    by_cases h1 : n=1
    · subst n
      have hk0 : k=0 := by omega
      subst k
      decide
    · have hn2 : 2≤n := by omega
      have hu := Nat.pair_lt_max_add_one_sq 2 n
      rw [max_eq_right hn2] at hu
      have hna : n^2≤Nat.pair n k := by
        have hl := Nat.max_sq_add_min_le_pair n k
        have hs := Nat.pow_le_pow_left (Nat.le_max_left n k) 2
        omega
      have ha : n+1≤Nat.pair n k := by nlinarith
      have hs := Nat.pow_le_pow_left ha 2
      have hl := Nat.max_sq_add_min_le_pair 1 (Nat.pair n k)
      have hs' := Nat.pow_le_pow_left (Nat.le_max_right 1 (Nat.pair n k)) 2
      omega

private theorem strip_subEdge_code_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (row : Fin (S.half+1)) :
    2*Nat.pair (2*j.val) (S.half-1)≤
      subEdgeCode x S (subdivisionHorizontalEdge baseTannerSquarePresentation x S
        (stripFace j x) (lastSegment S) row) := by
  unfold subdivisionHorizontalEdge
  split_ifs with hzero hlast
  · change 2*Nat.pair (2*j.val) (S.half-1)≤
      2*Nat.pair (baseEdgeCode
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0).val) (S.half-1)
    rw [stripFace_xq_code]
    have hright := Nat.right_le_pair x.val (j.val+2*x.val)
    have hm := pair_mono_left (2*j.val)
      (2*Nat.pair x.val (j.val+2*x.val)) (S.half-1) (by omega)
    omega
  · change 2*Nat.pair (2*j.val) (S.half-1)≤
      2*Nat.pair (baseEdgeCode
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1).val) (S.half-1)
    rw [stripFace_qz_code]
    have hm := pair_mono_left (2*j.val) (41+2*j.val) (S.half-1) (by omega)
    omega
  · change 2*Nat.pair (2*j.val) (S.half-1)≤
      4*Nat.pair (j.val+2*x.val) (Nat.pair (S.half-1) (row.val-1))+1
    have hh : 2≤S.half := by have := row.isLt; have := S.half_pos; omega
    have hk : row.val-1<S.half-1 := by have := row.isLt; omega
    exact (strip_inner_edge_code j x (S.half-1) (row.val-1) (by omega) hk).le

private theorem strip_oldQ_code_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) :
    Encodable.encode (gammaRadial S j (lastSegment S) :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (stripHorizontal S j x c row :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [gammaRadial,stripHorizontal,encoded_old_local_Q,encoded_old_local_Q]
  have hE := strip_subEdge_code_lower S j x row
  have hEt : subEdgeCode 0 S (.inl (seedRadial j,lastSegment S))=
      2*Nat.pair (2*j.val) (S.half-1) := by
    simp only [subEdgeCode,seedRadial_code,lastSegment]
  erw [hEt]
  have h0 := pair_mono_right 0 _ _ hE
  have h1 := pair_mono_left 0 c.val
    (subEdgeCode x S (subdivisionHorizontalEdge baseTannerSquarePresentation x S
      (stripFace j x) (lastSegment S) row)) (Nat.zero_le _)
  have hinner : 2*Nat.pair 0 (2*Nat.pair (2*j.val) (S.half-1))≤
      2*Nat.pair c.val (subEdgeCode x S
        (subdivisionHorizontalEdge baseTannerSquarePresentation x S
          (stripFace j x) (lastSegment S) row)) := by omega
  have hout := pair_mono_right 0 _ _ hinner
  have howner := pair_mono_left 0 x.val
    (2*Nat.pair c.val (subEdgeCode x S
      (subdivisionHorizontalEdge baseTannerSquarePresentation x S
        (stripFace j x) (lastSegment S) row))) (Nat.zero_le _)
  simp only [Fin.val_zero,Fin.val_one,Fin.val_mk] at *
  omega

private theorem oldX_tag_lower (u v x c : Nat) (h : u≤v) :
    u^4≤Nat.pair x (Nat.pair c v) := by
  have hi := pair_mono_right 0 u v h
  have hc := pair_mono_left 0 c v (Nat.zero_le _)
  have hinner : Nat.pair 0 u≤Nat.pair c v := hi.trans hc
  calc
    u^4=Nat.pair 0 (Nat.pair 0 u) := by rw [pair_zero_left_sq,pair_zero_left_sq]; ring
    _≤Nat.pair 0 (Nat.pair c v) := pair_mono_right 0 _ _ hinner
    _≤Nat.pair x (Nat.pair c v) := pair_mono_left 0 x _ (Nat.zero_le _)

private def terminalTag (S : OddScale) (j : Fin 2) : Nat :=
  max (2*(4*j.val+1)) (4*Nat.pair (2*j.val) (S.half-2)+1)

private theorem terminalX_le_tag (S : OddScale) (j : Fin 2) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(terminalTag S j)^4 := by
  have hstart : Encodable.encode (oldLocalStart S 0
      (.inl (0,.inl (seedRadial j,lastSegment S))) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(terminalTag S j)^4 := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial j)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0]
    unfold subdivisionSegmentStart
    split_ifs with hzero
    · erw [seedRadial_start]
      change (0 : Nat)≤_
      exact Nat.zero_le _
    · apply Nat.pow_le_pow_left _ 4
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) ((S.half-1)-1)+1≤terminalTag S j
      rw [seedRadial_code]
      have hs : (S.half-1)-1=S.half-2 := by omega
      rw [hs]
      exact Nat.le_max_right _ _
  have hend : Encodable.encode (oldLocalEnd S 0
      (.inl (0,.inl (seedRadial j,lastSegment S))) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤(terminalTag S j)^4 := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial j)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0]
    have hlast : (lastSegment S).val+1=S.half := by have := S.half_pos; dsimp [lastSegment]; omega
    unfold subdivisionSegmentEnd
    simp only [dif_pos hlast]
    change (2*(4*j.val+1))^4≤(terminalTag S j)^4
    exact Nat.pow_le_pow_left (Nat.le_max_left _ _) 4
  change Encodable.encode (oldLargestX S (.inl ⟨(0 : BaseX),
    .inl (0,.inl (seedRadial j,lastSegment S))⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
  exact code_larger_upper _ _ _ hstart hend

private theorem oldLargestX_le_of_ends (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) (B : Nat)
    (hs : Encodable.encode (oldLocalStart S x e :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤B)
    (ht : Encodable.encode (oldLocalEnd S x e :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤B) :
    Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤B := by
  exact code_larger_upper _ _ _ hs ht

private theorem stripFace_q0_vertex_code (j : Fin 2) (x : BaseX) :
    baseVertexCode (xStarFaceQVertex baseTannerSquarePresentation x (stripFace j x) 0).val=
      4*(j.val+2*x.val)+1 := by
  fin_cases j <;> fin_cases x <;> decide

private theorem strip_row0_X_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (stripHorizontal S j x c 0) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  let e0 : DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S :=
    .inl (0,.inl (seedRadial j,lastSegment S))
  let e : DoubleCylinderEdge baseTannerSquarePresentation x S :=
    .inl (c,.inl (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0,
      lastSegment S))
  have hbase : 2*j.val≤baseEdgeCode
      (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0).val := by
    rw [stripFace_xq_code]
    have := Nat.right_le_pair x.val (j.val+2*x.val)
    omega
  have hs : Encodable.encode (oldLocalStart S 0 e0 :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLocalStart S x e :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial j)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (⟨x,(c,subdivisionSegmentStart baseTannerSquarePresentation x S
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_copy0,encoded_old_X]
    unfold subdivisionSegmentStart
    split_ifs with hzero
    · erw [seedRadial_start]
      change (0 : Nat)≤_
      exact Nat.zero_le _
    · apply oldX_tag_lower
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) ((S.half-1)-1)+1≤
        4*Nat.pair (baseEdgeCode
          (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0).val)
          ((S.half-1)-1)+1
      rw [seedRadial_code]
      have hm := pair_mono_left _ _ ((S.half-1)-1) hbase
      omega
  have ht : Encodable.encode (oldLocalEnd S 0 e0 :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLocalEnd S x e :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial j)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (⟨x,(c,subdivisionSegmentEnd baseTannerSquarePresentation x S
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace j x) 0)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_copy0,encoded_old_X]
    have hlast : (lastSegment S).val+1=S.half := by have := S.half_pos; dsimp [lastSegment]; omega
    unfold subdivisionSegmentEnd
    simp only [dif_pos hlast]
    apply oldX_tag_lower
    change 2*(4*j.val+1)≤2*baseVertexCode
      (xStarFaceQVertex baseTannerSquarePresentation x (stripFace j x) 0).val
    rw [stripFace_q0_vertex_code]
    omega
  change Encodable.encode (oldLargestX S (.inl ⟨(0 : BaseX),e0⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
    Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)
  apply oldLargestX_le_of_ends
  · exact hs.trans (oldLargestX_start_le S x e)
  · exact ht.trans (oldLargestX_end_le S x e)

private theorem stripFace_q1_vertex_code (j : Fin 2) (x : BaseX) :
    baseVertexCode (xStarFaceQVertex baseTannerSquarePresentation x (stripFace j x) 1).val=17 := by
  fin_cases j <;> fin_cases x <;> decide

private theorem terminalTag_le_qz_start (S : OddScale) (j : Fin 2) (x : BaseX) :
    terminalTag S j ≤ subVertexCode x S
      (subdivisionSegmentStart baseTannerSquarePresentation x S
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1)
        (lastSegment S)) := by
  unfold subdivisionSegmentStart
  split_ifs with hzero
  · have hh : S.half=1 := by have := S.half_pos; dsimp [lastSegment] at hzero; omega
    change terminalTag S j≤2*baseVertexCode
      (xStarEdgeStart baseTannerSquarePresentation x
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1)).val
    erw [xStarEdgeStart_faceQZEdge,stripFace_q1_vertex_code]
    fin_cases j <;> norm_num [terminalTag,hh,Nat.pair]
  · change terminalTag S j≤4*Nat.pair (baseEdgeCode
      (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1).val)
      ((S.half-1)-1)+1
    rw [stripFace_qz_code]
    have hs : (S.half-1)-1=S.half-2 := by omega
    rw [hs]
    apply max_le
    · have hj := j.isLt
      have hl := Nat.left_le_pair (41+2*j.val) (S.half-2)
      omega
    · have hm := pair_mono_left (2*j.val) (41+2*j.val) (S.half-2) (by omega)
      omega

private theorem strip_rowh_X_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S
        (stripHorizontal S j x c (gridAt S S.half le_rfl)) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  let e : DoubleCylinderEdge baseTannerSquarePresentation x S :=
    .inl (c,.inl (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1,
      lastSegment S))
  have hs : (terminalTag S j)^4≤Encodable.encode (oldLocalStart S x e :
      (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    change (terminalTag S j)^4≤Encodable.encode (⟨x,(c,
      subdivisionSegmentStart baseTannerSquarePresentation x S
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 1)
        (lastSegment S))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X]
    exact oldX_tag_lower _ _ _ _ (terminalTag_le_qz_start S j x)
  have h := (terminalX_le_tag S j).trans (hs.trans (oldLargestX_start_le S x e))
  have hedge := horizontal_last_eq baseTannerSquarePresentation x S (stripFace j x)
    (lastSegment S) (gridAt S S.half le_rfl) rfl
  have he := congrArg (fun edge : SubdivisionEdge baseTannerSquarePresentation x S =>
    Encodable.encode (oldLargestX S (.inl ⟨x,.inl (c,edge)⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)) hedge
  exact h.trans_eq he.symm

private theorem terminalTag_inner_bound (j : Fin 2) (x : BaseX) (m k : Nat) :
    max (2*(4*j.val+1)) (4*Nat.pair (2*j.val) m+1)≤
      max (4*Nat.pair (j.val+2*x.val) (Nat.pair m k)+3)
        (4*Nat.pair (2*Nat.pair (j.val+2*x.val) j.val+1) k+1) := by
  fin_cases j
  · simp only [Fin.val_mk,Nat.zero_add,Nat.mul_zero,Nat.add_zero]
    change max 2 (4*Nat.pair 0 m+1)≤
      max (4*Nat.pair (2*x.val) (Nat.pair m k)+3)
        (4*Nat.pair (2*Nat.pair (2*x.val) 0+1) k+1)
    apply le_trans _ (Nat.le_max_left _ _)
    have hm := Nat.pow_le_pow_left (Nat.left_le_pair m k) 2
    have hf := pair_mono_left 0 (2*x.val) (Nat.pair m k) (Nat.zero_le _)
    rw [pair_zero_left_sq] at hf
    rw [pair_zero_left_sq]
    apply max_le <;> omega
  · simp only [Fin.val_mk]
    norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceMod]
    change max 10 (4*Nat.pair 2 m+1)≤
      max (4*Nat.pair (1+2*x.val) (Nat.pair m k)+3)
        (4*Nat.pair (2*Nat.pair (1+2*x.val) 1+1) k+1)
    by_cases hm : m≤1
    · apply le_trans _ (Nat.le_max_right _ _)
      have hsmall : Nat.pair 2 m≤7 := by interval_cases m <;> decide
      have hpair := pair_mono_left 1 (1+2*x.val) 1 (by omega)
      have h11 : Nat.pair 1 1=3 := rfl
      rw [h11] at hpair
      have he : 7≤2*Nat.pair (1+2*x.val) 1+1 := by omega
      have hs := Nat.pow_le_pow_left he 2
      have hl := Nat.max_sq_add_min_le_pair (2*Nat.pair (1+2*x.val) 1+1) k
      have hs' := Nat.pow_le_pow_left
        (Nat.le_max_left (2*Nat.pair (1+2*x.val) 1+1) k) 2
      apply max_le <;> omega
    · apply le_trans _ (Nat.le_max_left _ _)
      have hm2 : 2 ≤ m := by omega
      have hu := Nat.pair_lt_max_add_one_sq 2 m
      rw [max_eq_right hm2] at hu
      have hma : m^2≤Nat.pair m k := by
        have hl := Nat.max_sq_add_min_le_pair m k
        have hs := Nat.pow_le_pow_left (Nat.le_max_left m k) 2
        omega
      have ha : m+1≤Nat.pair m k := by nlinarith
      have hs := Nat.pow_le_pow_left ha 2
      have hl := Nat.max_sq_add_min_le_pair (1+2*x.val) (Nat.pair m k)
      have hs' := Nat.pow_le_pow_left
        (Nat.le_max_right (1+2*x.val) (Nat.pair m k)) 2
      apply max_le <;> omega

private theorem stripFace_qz0_code (j : Fin 2) (x : BaseX) :
    baseEdgeCode (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 0).val=
      2*Nat.pair (j.val+2*x.val) j.val+1 := by
  fin_cases j <;> fin_cases x <;> decide

private theorem strip_inner_start_code (S : OddScale) (j : Fin 2) (x : BaseX)
    (k : Fin (S.half-1)) :
    subVertexCode x S (subdivisionEdgeStart baseTannerSquarePresentation x S
      (.inr (.inl (stripFace j x,lastSegment S,k))))=
      4*Nat.pair (j.val+2*x.val) (Nat.pair (S.half-2) k.val)+3 := by
  have hh : 2≤S.half := by have := k.isLt; omega
  have hc0 : S.half-1≠0 := by omega
  have hch : S.half-1≠S.half := by omega
  have hk0 : k.val+1≠0 := by omega
  have hkh : k.val+1≠S.half := by have := k.isLt; omega
  have hs : (S.half-1)-1=S.half-2 := by omega
  erw [horizontal_inner_start_grid,grid_vertex_view]
  simp only [finCastGrid,finInteriorGrid,lastSegment,Fin.val_mk]
  simp only [hc0,hch,hk0,hkh,↓reduceDIte]
  change 4*Nat.pair (j.val+2*x.val)
    (Nat.pair ((S.half-1)-1) ((k.val+1)-1))+3=_
  rw [hs,Nat.add_sub_cancel]

private theorem strip_inner_end_code (S : OddScale) (j : Fin 2) (x : BaseX)
    (k : Fin (S.half-1)) :
    subVertexCode x S (subdivisionEdgeEnd baseTannerSquarePresentation x S
      (.inr (.inl (stripFace j x,lastSegment S,k))))=
      4*Nat.pair (2*Nat.pair (j.val+2*x.val) j.val+1) k.val+1 := by
  have hh : 2≤S.half := by have := k.isLt; omega
  have hl : S.half-1+1=S.half := by omega
  have hk0 : k.val+1≠0 := by omega
  have hkh : k.val+1≠S.half := by have := k.isLt; omega
  erw [horizontal_inner_end_grid,grid_vertex_view]
  simp only [finSuccGrid,finInteriorGrid,lastSegment,Fin.val_mk]
  simp only [hl,S.half_pos.ne',hk0,hkh,↓reduceDIte]
  change 4*Nat.pair (baseEdgeCode
    (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace j x) 0).val)
      ((k.val+1)-1)+1=_
  erw [stripFace_qz0_code,Nat.add_sub_cancel]

private theorem localLargestX_ge_tag (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (e : SubdivisionEdge baseTannerSquarePresentation x S)
    (T : Nat) (hT : T≤ max
      (subVertexCode x S (subdivisionEdgeStart baseTannerSquarePresentation x S e))
      (subVertexCode x S (subdivisionEdgeEnd baseTannerSquarePresentation x S e))) :
    T^4≤Encodable.encode (oldLargestX S (.inl ⟨x,.inl (c,e)⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  rcases le_max_iff.mp hT with hs | ht
  · have h : T^4≤Encodable.encode (oldLocalStart S x (.inl (c,e)) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
      change T^4≤Encodable.encode (⟨x,(c,
        subdivisionEdgeStart baseTannerSquarePresentation x S e)⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)
      erw [encoded_old_X]
      exact oldX_tag_lower _ _ _ _ hs
    exact h.trans (oldLargestX_start_le S x (.inl (c,e)))
  · have h : T^4≤Encodable.encode (oldLocalEnd S x (.inl (c,e)) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
      change T^4≤Encodable.encode (⟨x,(c,
        subdivisionEdgeEnd baseTannerSquarePresentation x S e)⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)
      erw [encoded_old_X]
      exact oldX_tag_lower _ _ _ _ ht
    exact h.trans (oldLargestX_end_le S x (.inl (c,e)))

private theorem strip_inner_X_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin (S.half-1)) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (.inl ⟨x,
        .inl (c,.inr (.inl (stripFace j x,lastSegment S,k)))⟩) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  apply (terminalX_le_tag S j).trans
  apply localLargestX_ge_tag
  erw [strip_inner_start_code,strip_inner_end_code]
  exact terminalTag_inner_bound j x (S.half-2) k.val

private theorem strip_oldX_code_lower (S : OddScale) (j : Fin 2) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) :
    Encodable.encode (oldLargestX S (gammaRadial S j (lastSegment S)) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (stripHorizontal S j x c row) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  by_cases h0 : row.val=0
  · have he : row=0 := Fin.ext h0
    subst row
    exact strip_row0_X_lower S j x c
  · by_cases hh : row.val=S.half
    · have he : row=gridAt S S.half le_rfl := Fin.ext hh
      subst row
      exact strip_rowh_X_lower S j x c
    · have h := strip_inner_X_lower S j x c (finInteriorIndex S row h0 hh)
      have hedge := horizontal_inner_eq baseTannerSquarePresentation x S
        (stripFace j x) (lastSegment S) row h0 hh
      have he := congrArg (fun edge : SubdivisionEdge baseTannerSquarePresentation x S =>
        Encodable.encode (oldLargestX S (.inl ⟨x,.inl (c,edge)⟩) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)) hedge
      exact h.trans_eq he.symm

private theorem global_terminal_large_port_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1)))
    (hn : 0<j.val+(lastSegment S).val) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j (lastSegment S),
        largePorts S c depth (gammaRadial S j (lastSegment S))⟩)=0 := by
  apply global_zero_of_port_kernel S a (largePorts S c depth) (directRoots S c)
    (directPaths S c depth) (terminalOldKernel S j) (terminalOldKernel_closed S j)
    (gammaRadial S j (lastSegment S)) (terminalOldKernel_gamma S j)
  · intro r hr hne
    obtain ⟨x,c',row,rfl⟩ := terminalOldKernel_support S j r hr
    exact largePorts_later S c depth _ _ hne
      (strip_oldQ_code_lower S j x c' row) (strip_oldX_code_lower S j x c' row)
  · intro r hr z hz e he
    obtain ⟨x,c',row,rfl⟩ := terminalOldKernel_support S j r hr
    apply directPaths_later S c depth (gammaRadial S j (lastSegment S))
      (stripHorizontal S j x c' row) z hz (gamma_code_pos S j (lastSegment S) hn)
      (strip_oldQ_code_lower S j x c' row)
      (gammaLargestX_le_square S j (lastSegment S) hn) _ e he
    intro i _
    have hi : i.val<(lastSegment S).val := by have := i.isLt; dsimp [lastSegment]; omega
    have hindex := gamma_index_le_code S j (lastSegment S)
    have hself : Encodable.encode (gammaRadial S j (lastSegment S) :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      (Encodable.encode (gammaRadial S j (lastSegment S) :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q))^2 := Nat.le_self_pow (by decide) _
    exact hi.trans_le (hindex.trans hself)

private theorem exists_direct_path_later (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hr0 : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX0 : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (zCenter (RawOne S) S z c)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (chosenPort (RawOne S) S r x hx c depth)),
      ∀ e, pathChain p e≠0 →
        Encodable.encode (executableCoordinate S
          (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)) := by
  apply direct_port_path_property (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S r x z hx hz c depth
    (fun edge => Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c depth⟩))<
        Encodable.encode (executableCoordinate S (.inl ⟨z,edge⟩)))
  intro a k ha
  exact direct_segment_later S r0 r x0 x hx0 hx z hz c depth
    K hK hr hr0 hX0 hi a k ha

/- Source-only, uncompiled. Insert q lemmas before first-cut support; gamma lemma after gammaRadial. -/
private theorem firstCutPotential_port_cone (S : OddScale)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two) :
    firstCutPotential S ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inl (.inl ()))⟩=
        if decide (q=stripQ 1 x) then 1 else 0 := by
  dsimp only [firstCutPotential,firstCutMember,qToXDoubleCylinderVertexAtRoot,
    qToXSubdivisionVertexAtRoot,qToXBoundaryVertexAtRoot,qToXBoundaryEdge,
    xBoundaryEdgeStart,xBoundaryEdgeEnd,xStarBoundaryVertexToStar,xStarBoundaryEdgeToStar]
  apply indicator_iff
  simp only [decide_eq_true_eq]
  all_goals rfl


private theorem firstCutPotential_port_endpoint (S : OddScale)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root edge : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two) :
    firstCutPotential S ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inl (.inr edge))⟩=
        if decide (edge.val=(1 : BaseZ)) then 1 else 0 := rfl

private theorem firstCutPotential_port_interior (S : OddScale)
    (x : BaseX) (q : BaseQubit) (hx : baseTannerSquarePresentation.xq x q=true)
    (root edge : QStarEdge baseTannerSquarePresentation q) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1)) :
    firstCutPotential S ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S root (c,.inr (edge,i))⟩=
        if decide (edge.val=(1 : BaseZ)) then 1 else 0 := rfl

private theorem firstCutPotential_q_gradient (S : OddScale) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    tannerCoboundary0 (RawOne S) (firstCutPotential S) (.inr ⟨q,v⟩)=
      stripSeedCocycle 1 q := by
  erw [BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
    baseTannerSquarePresentation baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S]
  erw [rx_q_gradient baseTannerSquarePresentation baseTannerSquareAdmissible S]
  change (∑ x : BaseX, if hx : baseTannerSquarePresentation.xq x q=true then
    firstCutPotential S ⟨x,qToXDoubleCylinderVertexAtRoot baseTannerSquarePresentation
      q x hx S (baseTannerSquareAdmissible.qzRoot q) v⟩ else 0)=stripSeedCocycle 1 q
  rcases v with ⟨c,(cone | endpoint) | ⟨edge,i⟩⟩
  · cases cone
    simp_rw [firstCutPotential_port_cone]
    exact strip_sum_cone 1 q
  · rcases endpoint with ⟨z,hz⟩
    change BaseZ at z
    simp_rw [firstCutPotential_port_endpoint]
    exact strip_sum_endpoint 1 q z hz
  · rcases edge with ⟨z,hz⟩
    change BaseZ at z
    simp_rw [firstCutPotential_port_interior]
    exact strip_sum_endpoint 1 q z hz

private theorem firstCutOldKernel_q_zero (S : OddScale) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    firstCutOldKernel S (.inr ⟨q,v⟩)=0 := by
  erw [firstCutOldKernel,Pi.add_apply,rawSeedLift,
    BDL26ReplacementCochainMaps.rxMap1Coord_qVertex,firstCutPotential_q_gradient]
  exact ZModModule.add_self _

private theorem firstCutOldKernel_gamma (S : OddScale) :
    firstCutOldKernel S (gammaRadial S 1 ⟨0,S.half_pos⟩)=1 := by
  have h := firstCutOldKernel_horizontal S (0 : BaseX) 0 (seedFace 1) (⟨0,S.half_pos⟩) 0
  have hedge : subdivisionHorizontalEdge baseTannerSquarePresentation (0 : BaseX) S
      (seedFace 1) (⟨0,S.half_pos⟩) 0=(.inl (seedRadial 1,⟨0,S.half_pos⟩) :
        SubdivisionEdge baseTannerSquarePresentation 0 S) := by
    simp only [subdivisionHorizontalEdge,Fin.val_zero,↓reduceDIte]
    exact congrArg (fun e : XStarEdge baseTannerSquarePresentation (0 : BaseX) =>
      (Sum.inl (e,⟨0,S.half_pos⟩) : SubdivisionEdge baseTannerSquarePresentation 0 S))
        ((seedRadial_face_zero 1 (seedFace 1)).mpr rfl).symm
  erw [hedge] at h
  apply h.trans
  apply if_pos
  constructor
  · rfl
  · rfl

private theorem oldLargestX_upper (S : OddScale) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S) (v : (RawOne S).X)
    (hv : (RawOne S).xq v (.inl ⟨x,e⟩)=true) :
    Encodable.encode (v : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (.inl ⟨x,e⟩) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  rcases (old_local_incidence S v x e).mp hv with rfl | rfl
  · exact oldLargestX_start_le S x e
  · exact oldLargestX_end_le S x e

private theorem chosenPort_order_same_owner (S : OddScale) (r : (RawOne S).Q)
    (x y : (RawOne S).X) (hx : (RawOne S).xq x r=true) (hy : (RawOne S).xq y r=true)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (hxy : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      Encodable.encode (y : (BDL26LevelTwoDecoder.executableLevelOne S).X)) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c depth⟩))<
      Encodable.encode (executableCoordinate S
        (.inr ⟨r,chosenPort (RawOne S) S r y hy c depth⟩)) := by
  cases depth with
  | none =>
    rw [encoded_chosenPort,encoded_chosenPort]
    dsimp only
    have ht : 2*(2*Encodable.encode (x :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)<
      2*(2*Encodable.encode (y : (BDL26LevelTwoDecoder.executableLevelOne S).X)+1) := by omega
    have hc := Nat.pair_lt_pair_right c.val ht
    have hr := Nat.pair_lt_pair_right
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) hc
    omega
  | some i =>
    rw [encoded_chosenPort,encoded_chosenPort]
    dsimp only
    have hi := Nat.pair_lt_pair_left i.val hxy
    have ht : 2*Nat.pair (Encodable.encode (x :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1<
      2*Nat.pair (Encodable.encode (y :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)) i.val+1 := by omega
    have hc := Nat.pair_lt_pair_right c.val ht
    have hr := Nat.pair_lt_pair_right
      (Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) hc
    omega

private theorem global_zero_of_same_owner_pair (S : OddScale) (a : Word F (RawTwo S).Q)
    (r : (RawOne S).Q) (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (v v' : QDoubleCylinderVertex (transposePresentation (RawOne S)) r S)
    (root : ZDoubleCylinderVertex (RawOne S) z S)
    (p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      root (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v))
    (p' : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      root (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S v'))
    (horder : Encodable.encode (executableCoordinate S (.inr ⟨r,v⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,v'⟩)))
    (hp : ∀ e, pathChain p e≠0 →
      Encodable.encode (executableCoordinate S (.inr ⟨r,v⟩))<
        Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)))
    (hp' : ∀ e, pathChain p' e≠0 →
      Encodable.encode (executableCoordinate S (.inr ⟨r,v⟩))<
        Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨r,v⟩)=0 := by
  have hne : (Sum.inr ⟨r,v⟩ : (RawTwo S).Q)≠Sum.inr ⟨r,v'⟩ := by
    intro he
    have hcode := congrArg (fun q : (RawTwo S).Q =>
      Encodable.encode (executableCoordinate S q)) he
    exact Nat.lt_irrefl _ (horder.trans_eq hcode.symm)
  have eval (q : (RawTwo S).Q) :
      twoArmKernel S r r z hz hz v v' root p p' q=
        ((if q=.inr ⟨r,v⟩ then 1 else 0)+(if q=.inr ⟨r,v'⟩ then 1 else 0))+
          extendZEdgeWord (RawOne S) S z (pathChain p+pathChain p') q :=
    two_units_apply _ _ _ _
  apply actualGlobal_zero_of_encoded_kernel S a
    (twoArmKernel S r r z hz hz v v' root p p') (.inr ⟨r,v⟩)
  · exact twoArmKernel_closed S r r z hz hz hu hu v v' root p p'
  · have hlocal := extend_edge_at_port (RawOne S) S z (pathChain p+pathChain p') r v
    exact (eval _).trans (by erw [if_pos rfl,if_neg hne,hlocal,add_zero,add_zero])
  · intro q hq
    change (RawTwo S).Q at q
    have hq0 : q≠Sum.inr ⟨r,v⟩ := by
      intro he
      have hcode := congrArg (fun out : (RawTwo S).Q =>
        Encodable.encode (executableCoordinate S out)) he
      exact Nat.lt_irrefl _ (hq.trans_eq hcode.symm)
    have hq1 : q≠Sum.inr ⟨r,v'⟩ := by
      intro he
      have hcode := congrArg (fun out : (RawTwo S).Q =>
        Encodable.encode (executableCoordinate S out)) he
      exact Nat.lt_asymm (hcode.symm.trans_lt hq) horder
    have hbase : twoArmKernel S r r z hz hz v v' root p p' q=
        extendZEdgeWord (RawOne S) S z (pathChain p+pathChain p') q :=
      (eval q).trans (two_indicators_zero q (.inr ⟨r,v⟩) (.inr ⟨r,v'⟩) _ hq0 hq1)
    apply hbase.trans
    change RZQ (RawOne S) S at q
    rcases q with ⟨z',e⟩ | ⟨q,vq⟩
    · by_cases he : z'=z
      · subst z'
        have h0 : pathChain p e=0 := by
          by_contra hn
          exact Nat.lt_asymm hq (hp e hn)
        have h1 : pathChain p' e=0 := by
          by_contra hn
          exact Nat.lt_asymm hq (hp' e hn)
        exact (extend_edge_at_same (RawOne S) S z (pathChain p+pathChain p') e).trans
          ((word_add_eval (pathChain p) (pathChain p') e).trans
            (by rw [h0,h1,zero_add]))
      · exact extend_edge_at_other (RawOne S) S z z' (pathChain p+pathChain p') e he
    · exact extend_edge_at_port (RawOne S) S z (pathChain p+pathChain p') q vq

private theorem global_same_owner_direct_zero (S : OddScale) (a : Word F (RawTwo S).Q)
    (r : (RawOne S).Q) (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (x x' : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (hx' : (RawOne S).xq x' r=true) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) (K : Nat) (hK : 0<K)
    (hr : K≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q))
    (hR : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤K^2)
    (hX : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2)
    (hi : ∀ i, depth=some i → i.val<K^2)
    (horder : Encodable.encode (executableCoordinate S
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c depth⟩))<
        Encodable.encode (executableCoordinate S
          (.inr ⟨r,chosenPort (RawOne S) S r x' hx' c depth⟩))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c depth⟩)=0 := by
  obtain ⟨p,hp⟩ := exists_direct_path_later S r r x x hx hx z hz c depth
    K hK hr hR hX hi
  obtain ⟨p',hp'⟩ := exists_direct_path_later S r r x x' hx hx' z hz c depth
    K hK hr hR hX hi
  exact global_zero_of_same_owner_pair S a r z hz hu _ _
    (zCenter (RawOne S) S z c) p p' horder hp hp'

private theorem global_radial_minor_endpoint_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) (x : (RawOne S).X)
    (hx : (RawOne S).xq x (gammaRadial S j n)=true)
    (hne : x≠oldLargestX S (gammaRadial S j n))
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j n,(c,.inl (.inr ⟨x,hx⟩))⟩)=0 := by
  let r := gammaRadial S j n
  let K := Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  have hK : 0<K := gamma_code_pos S j n hn
  have hxle : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) :=
    oldLargestX_upper S 0 (.inl (0,.inl (seedRadial j,n))) x hx
  have hstrict : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    have hncode : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≠
        Encodable.encode (oldLargestX S r :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) :=
      fun he => hne (Encodable.encode_injective he)
    omega
  have hX : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤K^2 :=
    hxle.trans (gammaLargestX_le_square S j n hn)
  have hR : K≤K^2 := Nat.le_self_pow (by decide) K
  have hi : ∀ i : Fin (S.half-1), (none : Option (Fin (S.half-1)))=some i → i.val<K^2 := by
    intro i he
    cases he
  have hz : (RawOne S).qz r (seedRadialCheck S j n)=true :=
    (seedRadial_degree_one S j n).1
  exact global_same_owner_direct_zero S a r (seedRadialCheck S j n) hz
    (seedRadial_degree_one S j n).2 x (oldLargestX S r) hx
    (oldLargestX_incident S r) c none K hK le_rfl hR hX hi
    (chosenPort_order_same_owner S r x (oldLargestX S r) hx
      (oldLargestX_incident S r) c none hstrict)

private theorem global_first_radial_last_interior_zero (S : OddScale) (hh : 2≤S.half)
    (a : Word F (RawTwo S).Q) (x : (RawOne S).X)
    (hx : (RawOne S).xq x (firstRadialQ S)=true)
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨firstRadialQ S,(c,.inr (⟨x,hx⟩,lastInterior S hh))⟩)=0 := by
  apply global_last_interior_of_least_old_neighbor S hh a (firstRadialQ S) x hx c
  intro r' _ hn
  have hz : Encodable.encode
      (firstRadialQ S : (BDL26LevelTwoDecoder.executableLevelOne S).Q)=0 := by rfl
  have hne : Encodable.encode
      (r' : (BDL26LevelTwoDecoder.executableLevelOne S).Q)≠0 := by
    intro he
    exact hn (Encodable.encode_injective (he.trans hz.symm))
  omega

private def radialPrevious (S : OddScale) (i : Fin (S.half-1)) : Fin S.half :=
  ⟨i.val,by have := i.isLt; omega⟩

private def radialFollowing (S : OddScale) (i : Fin (S.half-1)) : Fin S.half :=
  ⟨i.val+1,by have := i.isLt; omega⟩

private def radialInteriorX (S : OddScale) (j : Fin 2) (i : Fin (S.half-1)) : (RawOne S).X :=
  ⟨(0 : BaseX),(0,.inr (.inl (seedRadial j,i)))⟩

private def radialPerp (S : OddScale) (j : Fin 2) (i : Fin (S.half-1)) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inr (.inr (seedFace j,i,⟨0,S.half_pos⟩)))⟩

private theorem radialInterior_grid_eq (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (f : XStarFace baseTannerSquarePresentation (0 : BaseX))
    (a b : Fin (S.half+1))
    (h : subdivisionGridVertex baseTannerSquarePresentation 0 S f a b=
      .inr (.inl (seedRadial j,i))) :
    f=seedFace j ∧ a.val=i.val+1 ∧ b.val=0 := by
  rcases subdivisionGridVertex_eq_edgeInterior_coordinates
    baseTannerSquarePresentation 0 S f a b (seedRadial j) i h with h | h | h | h
  · exact False.elim (seedRadial_face_one j f h.1)
  · exact False.elim (seedRadial_ne_qz j f 0 h.1)
  · exact ⟨(seedRadial_face_zero j f).mp h.1,h.2.1,h.2.2⟩
  · exact False.elim (seedRadial_ne_qz j f 1 h.1)

private theorem radialInterior_subdivision_edges (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (e : SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)
    (h : subdivisionEdgeStart baseTannerSquarePresentation 0 S e=.inr (.inl (seedRadial j,i)) ∨
      subdivisionEdgeEnd baseTannerSquarePresentation 0 S e=.inr (.inl (seedRadial j,i))) :
    e=.inl (seedRadial j,radialPrevious S i) ∨
      e=.inl (seedRadial j,radialFollowing S i) ∨
      e=.inr (.inr (seedFace j,i,⟨0,S.half_pos⟩)) := by
  rcases subdivision_edge_grid_cover baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4 0 S e with hh | hv
  · obtain ⟨f,k,row,rfl⟩ := hh
    rcases h with hs | ht
    · erw [own_horizontal_start] at hs
      obtain ⟨hf,hk,hr⟩ := radialInterior_grid_eq S j i f _ _ hs
      subst f
      have hrow : row=0 := Fin.ext hr
      have hseg : k=radialFollowing S i := Fin.ext hk
      subst row
      subst k
      right
      left
      simp only [subdivisionHorizontalEdge,dif_pos (by rfl :
        (0 : Fin (S.half+1)).val=0)]
      exact congrArg (fun a : XStarEdge baseTannerSquarePresentation (0 : BaseX) =>
        (Sum.inl (a,radialFollowing S i) : SubdivisionEdge baseTannerSquarePresentation 0 S))
        ((seedRadial_face_zero j (seedFace j)).mpr rfl).symm
    · erw [own_horizontal_end] at ht
      obtain ⟨hf,hk,hr⟩ := radialInterior_grid_eq S j i f _ _ ht
      subst f
      have hrow : row=0 := Fin.ext hr
      have hseg : k=radialPrevious S i := by
        apply Fin.ext
        change k.val=i.val
        change k.val+1=i.val+1 at hk
        omega
      subst row
      subst k
      left
      simp only [subdivisionHorizontalEdge,dif_pos (by rfl :
        (0 : Fin (S.half+1)).val=0)]
      exact congrArg (fun a : XStarEdge baseTannerSquarePresentation (0 : BaseX) =>
        (Sum.inl (a,radialPrevious S i) : SubdivisionEdge baseTannerSquarePresentation 0 S))
        ((seedRadial_face_zero j (seedFace j)).mpr rfl).symm
  · obtain ⟨f,column,k,rfl⟩ := hv
    rcases h with hs | ht
    · erw [own_vertical_start] at hs
      obtain ⟨hf,hc,hk⟩ := radialInterior_grid_eq S j i f _ _ hs
      subst f
      have hcolumn : column=finInteriorGrid S i := Fin.ext hc
      have hseg : k=⟨0,S.half_pos⟩ := Fin.ext hk
      subst column
      subst k
      right
      right
      have hi0 : (finInteriorGrid S i).val≠0 := by simp [finInteriorGrid]
      have hih : (finInteriorGrid S i).val≠S.half := by have := i.isLt; dsimp [finInteriorGrid]; omega
      have hn : i.val+1≠S.half := by have := i.isLt; omega
      erw [vertical_inner_eq baseTannerSquarePresentation (0 : BaseX) S
        (seedFace j) (finInteriorGrid S i) ⟨0,S.half_pos⟩ hi0 hih]
      apply congrArg (fun k : Fin (S.half-1) =>
        (Sum.inr (Sum.inr (seedFace j,k,⟨0,S.half_pos⟩)) :
          SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S))
      apply Fin.ext
      change (i.val+1)-1=i.val
      omega
    · erw [own_vertical_end] at ht
      obtain ⟨_,_,hk⟩ := radialInterior_grid_eq S j i f _ _ ht
      change k.val+1=0 at hk
      omega

/- Source-only insertions in the existing endpoint namespace. Not compiled.
   These use the actual admissibility boundary path, never a caller path witness. -/

private noncomputable def boundarySpokeEdge (P : TannerSquarePresentation)
    (x : P.X) (q : P.Q) (hm : xStarBoundaryVertexMember P x (.q q)=true) :
    XStarEdge P x := by
  have hinc : P.xq x q=true := by
    obtain ⟨f,hf,hq⟩ := of_decide_eq_true hm
    have hfx : P.faceX f=x := by simpa [xStarFaceMember] using hf
    rcases hq with hq | hq
    · simpa only [hfx,← hq] using P.data.faceQ_xq f 0
    · simpa only [hfx,← hq] using P.data.faceQ_xq f 1
  refine ⟨.inl ⟨(x,q),hinc⟩,?_⟩
  change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧
    decide (⟨(x,q),hinc⟩=faceXQEdge P f 0 ∨
      ⟨(x,q),hinc⟩=faceXQEdge P f 1)=true)=true
  rw [decide_eq_true_eq]
  obtain ⟨f,hf,hq⟩ := of_decide_eq_true hm
  refine ⟨f,hf,?_⟩
  have hfx : P.faceX f=x := by simpa [xStarFaceMember] using hf
  change decide (⟨(x,q),hinc⟩=faceXQEdge P f 0 ∨
    ⟨(x,q),hinc⟩=faceXQEdge P f 1)=true
  rw [decide_eq_true_eq]
  rcases hq with hq | hq
  · left
    apply Subtype.ext
    exact Prod.ext hfx.symm hq
  · right
    apply Subtype.ext
    exact Prod.ext hfx.symm hq

private noncomputable def raisedBoundaryVertex (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) :
    XStarBoundaryVertex P x → SubdivisionVertex P x S
  | ⟨.x _,hm⟩ => False.elim (by simpa [xStarBoundaryVertexMember] using hm)
  | ⟨.q q,hm⟩ => .inr (.inl (boundarySpokeEdge P x q hm,lastInterior S hh))
  | ⟨.z z,hm⟩ => .inl (xStarBoundaryVertexToStar P x ⟨.z z,hm⟩)

private def raisedBoundarySupport (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (hh : 2≤S.half) (e : SubdivisionEdge P x S) : Prop :=
  (∃ (f : XStarFace P x) (k : Fin S.half),
    e=.inr (.inr (f,lastInterior S hh,k))) ∨
  (∃ (f : XStarFace P x) (k : Fin S.half),
    e=.inr (.inl (f,k,lastInterior S hh))) ∨
  (∃ a : XStarEdge P x, e=.inl (a,lastSegment S))

private noncomputable def raisedBoundaryL0 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f (lastGridInterior S) 0)
      (subdivisionGridVertex P x S f (gridAt S S.half le_rfl)
        (gridAt S S.half le_rfl)) := by
  apply UndirectedPath.step
    (verticalAtColumnPath P x S f (lastGridInterior S) S.half le_rfl)
    (subdivisionHorizontalEdge P x S f (lastSegment S) (gridAt S S.half le_rfl))
  apply Or.inl
  constructor
  · simpa [lastSegment,lastGridInterior,finCastGrid] using
      own_horizontal_start P x S f (lastSegment S)
        (gridAt S S.half le_rfl)
  · simpa [lastSegment,finSuccGrid,gridAt,
      show S.half-1+1=S.half by have := S.half_pos; omega] using
      own_horizontal_end P x S f (lastSegment S)
        (gridAt S S.half le_rfl)

private noncomputable def raisedBoundaryL1 (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) :
    UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S f 0 (lastGridInterior S))
      (subdivisionGridVertex P x S f (gridAt S S.half le_rfl)
        (gridAt S S.half le_rfl)) := by
  apply UndirectedPath.step
    (horizontalAtRowPath P x S f (lastGridInterior S) S.half le_rfl)
    (subdivisionVerticalEdge P x S f (gridAt S S.half le_rfl) (lastSegment S))
  apply Or.inl
  constructor
  · simpa [lastSegment,lastGridInterior,finCastGrid] using
      own_vertical_start P x S f (gridAt S S.half le_rfl)
        (lastSegment S)
  · simpa [lastSegment,finSuccGrid,gridAt,
      show S.half-1+1=S.half by have := S.half_pos; omega] using
      own_vertical_end P x S f (gridAt S S.half le_rfl)
        (lastSegment S)

private theorem raisedBoundaryL0_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) (f : XStarFace P x)
    (e : SubdivisionEdge P x S) (he : pathChain (raisedBoundaryL0 P x S f) e≠0) :
    raisedBoundarySupport P x S hh e := by
  change (pathChain
    (verticalAtColumnPath P x S f (lastGridInterior S) S.half le_rfl) e+
      (Pi.single (subdivisionHorizontalEdge P x S f (lastSegment S)
        (gridAt S S.half le_rfl)) (1:F) : Word F (SubdivisionEdge P x S)) e)≠0 at he
  by_cases hp : pathChain
      (verticalAtColumnPath P x S f (lastGridInterior S) S.half le_rfl) e=0
  · rw [hp,zero_add] at he
    have heq : e=subdivisionHorizontalEdge P x S f (lastSegment S)
        (gridAt S S.half le_rfl) := by
      by_contra hn
      exact he (by simp [hn,Ne.symm hn])
    right; right
    refine ⟨xStarFaceQZEdge P x f 1,?_⟩
    simpa [subdivisionHorizontalEdge,gridAt,S.half_pos.ne'] using heq
  · obtain ⟨k,_,hk⟩ := verticalAtColumnPath_support P x S f
      (lastGridInterior S) S.half le_rfl e hp
    left
    refine ⟨f,k,?_⟩
    have hc0 : (lastGridInterior S).val≠0 := by dsimp [lastGridInterior]; omega
    have hch : (lastGridInterior S).val≠S.half := by dsimp [lastGridInterior]; omega
    have hedge : subdivisionVerticalEdge P x S f (lastGridInterior S) k=
        (Sum.inr (Sum.inr (f,lastInterior S hh,k)) :
          SubdivisionEdge P x S) := by
      simp only [subdivisionVerticalEdge,dif_neg hc0,dif_neg hch]
      apply congrArg (fun index : Fin (S.half-1) =>
        (Sum.inr (Sum.inr (f,index,k)) : SubdivisionEdge P x S))
      apply Fin.ext
      change (S.half-1)-1=S.half-2
      omega
    exact hk.trans hedge

private theorem raisedBoundaryL1_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) (f : XStarFace P x)
    (e : SubdivisionEdge P x S) (he : pathChain (raisedBoundaryL1 P x S f) e≠0) :
    raisedBoundarySupport P x S hh e := by
  change (pathChain
    (horizontalAtRowPath P x S f (lastGridInterior S) S.half le_rfl) e+
      (Pi.single (subdivisionVerticalEdge P x S f (gridAt S S.half le_rfl)
        (lastSegment S)) (1:F) : Word F (SubdivisionEdge P x S)) e)≠0 at he
  by_cases hp : pathChain
      (horizontalAtRowPath P x S f (lastGridInterior S) S.half le_rfl) e=0
  · rw [hp,zero_add] at he
    have heq : e=subdivisionVerticalEdge P x S f (gridAt S S.half le_rfl)
        (lastSegment S) := by
      by_contra hn
      exact he (by simp [hn,Ne.symm hn])
    right; right
    refine ⟨xStarFaceQZEdge P x f 0,?_⟩
    simpa [subdivisionVerticalEdge,gridAt,S.half_pos.ne'] using heq
  · obtain ⟨k,_,hk⟩ := horizontalAtRowPath_support P x S f
      (lastGridInterior S) S.half le_rfl e hp
    right; left
    refine ⟨f,k,?_⟩
    have hc0 : (lastGridInterior S).val≠0 := by dsimp [lastGridInterior]; omega
    have hch : (lastGridInterior S).val≠S.half := by dsimp [lastGridInterior]; omega
    have hedge : subdivisionHorizontalEdge P x S f k (lastGridInterior S)=
        (Sum.inr (Sum.inl (f,k,lastInterior S hh)) :
          SubdivisionEdge P x S) := by
      simp only [subdivisionHorizontalEdge,dif_neg hc0,dif_neg hch]
      apply congrArg (fun index : Fin (S.half-1) =>
        (Sum.inr (Sum.inl (f,k,index)) : SubdivisionEdge P x S))
      apply Fin.ext
      change (S.half-1)-1=S.half-2
      omega
    exact hk.trans hedge

private def faceBoundaryEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (j : BDL26FiniteTannerSquare.Two) :
    XStarBoundaryEdge P x :=
  ⟨.inr (faceQZEdge P f.val j),by
    rw [boundary_edge_qz_view,decide_eq_true_eq]
    refine ⟨f.val,f.property,?_⟩
    fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl⟩

private theorem boundarySpokeEdge_face (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (j : BDL26FiniteTannerSquare.Two)
    (hm : xStarBoundaryVertexMember P x (.q (P.faceQ f.val j))=true) :
    boundarySpokeEdge P x (P.faceQ f.val j) hm=xStarFaceXQEdge P x f j := by
  apply Subtype.ext
  unfold boundarySpokeEdge xStarFaceXQEdge
  change (.inl ⟨(x,P.faceQ f.val j),_⟩ : Edge P)=.inl (faceXQEdge P f.val j)
  apply congrArg Sum.inl
  apply Subtype.ext
  have hfx : P.faceX f.val=x := by simpa [xStarFaceMember] using f.property
  exact Prod.ext hfx.symm rfl

private theorem raisedBoundary_face_start (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half)
    (f : XStarFace P x) (j : BDL26FiniteTannerSquare.Two) :
    raisedBoundaryVertex P x S hh (xBoundaryEdgeStart P x (faceBoundaryEdge P x f j))=
      if j=0 then subdivisionGridVertex P x S f (lastGridInterior S) 0
      else subdivisionGridVertex P x S f 0 (lastGridInterior S) := by
  change (Sum.inr (Sum.inl
    (boundarySpokeEdge P x (P.faceQ f.val j) _,lastInterior S hh)) : SubdivisionVertex P x S)=_
  erw [boundarySpokeEdge_face]
  have hi : (⟨(lastInterior S hh).val+1,by have := (lastInterior S hh).isLt; omega⟩ :
      Fin (S.half+1))=lastGridInterior S := by
    apply Fin.ext
    dsimp [lastInterior,lastGridInterior]
    omega
  fin_cases j
  · change (Sum.inr (Sum.inl (xStarFaceXQEdge P x f 0,lastInterior S hh)) :
      SubdivisionVertex P x S)=
      subdivisionGridVertex P x S f (lastGridInterior S) 0
    simpa only [hi] using
      (subdivisionGridVertex_edgeInterior_xq0 P x S f (lastInterior S hh)).symm
  · change (Sum.inr (Sum.inl (xStarFaceXQEdge P x f 1,lastInterior S hh)) :
      SubdivisionVertex P x S)=
      subdivisionGridVertex P x S f 0 (lastGridInterior S)
    simpa only [hi] using
      (subdivisionGridVertex_edgeInterior_xq1 P x S f (lastInterior S hh)).symm

private theorem raisedBoundary_face_end (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half)
    (f : XStarFace P x) (j : BDL26FiniteTannerSquare.Two) :
    raisedBoundaryVertex P x S hh (xBoundaryEdgeEnd P x (faceBoundaryEdge P x f j))=
      subdivisionGridVertex P x S f (gridAt S S.half le_rfl)
        (gridAt S S.half le_rfl) := by
  change (.inl ⟨.z (P.faceZ f.val),_⟩ : SubdivisionVertex P x S)=_
  simp only [subdivisionGridVertex,gridAt,S.half_pos.ne',↓reduceDIte]
  rfl

private theorem exists_raised_boundary_segment (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (x : P.X) (S : OddScale) (hh : 2≤S.half)
    (e : XStarBoundaryEdge P x) :
    ∃ p : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (raisedBoundaryVertex P x S hh (xBoundaryEdgeStart P x e))
      (raisedBoundaryVertex P x S hh (xBoundaryEdgeEnd P x e)),
      ∀ e', pathChain p e'≠0 → raisedBoundarySupport P x S hh e' := by
  rcases e with ⟨e,hm⟩
  rcases e with e | e
  · simp [xStarBoundaryEdgeMember] at hm
  · have hs : xStarEdgeMember P x (.inr e)=true :=
      xStarBoundaryEdgeMember_to_star P x (.inr e) hm
    obtain ⟨⟨f,j⟩,he⟩ := A.xBoundaryFaceOwner x e hs
    have hfull : (⟨.inr e,hm⟩ : XStarBoundaryEdge P x)=faceBoundaryEdge P x f j := by
      apply Subtype.ext
      exact (congrArg Subtype.val he).symm
    rw [hfull,raisedBoundary_face_start,raisedBoundary_face_end]
    fin_cases j
    · refine ⟨raisedBoundaryL0 P x S f,?_⟩
      exact raisedBoundaryL0_support P x S hh f
    · refine ⟨raisedBoundaryL1 P x S f,?_⟩
      exact raisedBoundaryL1_support P x S hh f

private theorem exists_raised_boundary_path (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (x : P.X) (S : OddScale) (hh : 2≤S.half)
    (v : XStarBoundaryVertex P x) :
    ∃ p : UndirectedPath (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
      (raisedBoundaryVertex P x S hh (A.xBoundaryRoot x))
      (raisedBoundaryVertex P x S hh v),
      ∀ e, pathChain p e≠0 → raisedBoundarySupport P x S hh e := by
  exact exists_path_substitution (raisedBoundaryVertex P x S hh)
    (raisedBoundarySupport P x S hh)
    (exists_raised_boundary_segment P A x S hh)
    (A.xBoundaryPath x v)

private noncomputable def actualRaisedRoots (S : OddScale) (hh : 2≤S.half)
    (c : BDL26FiniteTannerSquare.Two) : PortRoots S := fun z =>
  let A := transposeTannerSquareAdmissibleV4 (RawOne S) (rxState S baseState).admissible
  (c,raisedBoundaryVertex (transposePresentation (RawOne S)) z S hh
    (A.xBoundaryRoot z))

private theorem exists_actual_raised_boundary_path (S : OddScale) (hh : 2≤S.half)
    (c : BDL26FiniteTannerSquare.Two) (z : (RawOne S).Z)
    (v : XStarBoundaryVertex (transposePresentation (RawOne S)) z) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (actualRaisedRoots S hh c z)
      (c,raisedBoundaryVertex (transposePresentation (RawOne S)) z S hh v),
      ∀ e, pathChain p e≠0 → ∃ e',
        e=.inl (c,e') ∧ raisedBoundarySupport (transposePresentation (RawOne S)) z S hh e' := by
  let A := transposeTannerSquareAdmissibleV4 (RawOne S) (rxState S baseState).admissible
  obtain ⟨p,hp⟩ := exists_raised_boundary_path
    (transposePresentation (RawOne S)) A z S hh v
  refine ⟨atCopyPath (transposePresentation (RawOne S)) z S c p,?_⟩
  intro e he
  obtain ⟨e',he',heq⟩ := atCopyPath_support (transposePresentation (RawOne S)) z S c p e he
  exact ⟨e',heq,hp e' he'⟩

private theorem radialInterior_endpoint_neighbours (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S)
    (b : BDL26FiniteTannerSquare.Two)
    (h : radialInteriorX S j i=⟨x,BDL26TannerLocalRegularity.edgeEndpoint
      (tannerDoubleCylinderEdgeStart baseTannerSquarePresentation x S)
      (tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation x S) e b⟩) :
    (Sum.inl ⟨x,e⟩ : (RawOne S).Q)=gammaRadial S j (radialPrevious S i) ∨
      (Sum.inl ⟨x,e⟩ : (RawOne S).Q)=gammaRadial S j (radialFollowing S i) ∨
      (Sum.inl ⟨x,e⟩ : (RawOne S).Q)=radialPerp S j i := by
  have howner : (0 : BaseX)=x := congrArg Sigma.fst h
  cases howner
  have hv := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  change (0,.inr (.inl (seedRadial j,i)))=
    BDL26TannerLocalRegularity.edgeEndpoint
      (tannerDoubleCylinderEdgeStart baseTannerSquarePresentation 0 S)
      (tannerDoubleCylinderEdgeEnd baseTannerSquarePresentation 0 S) e b at hv
  rcases e with ⟨c,e⟩ | v
  · have hc : (0 : BDL26FiniteTannerSquare.Two)=c := by
      fin_cases b <;> exact congrArg Prod.fst hv
    cases hc
    have hs : subdivisionEdgeStart baseTannerSquarePresentation 0 S e=
        .inr (.inl (seedRadial j,i)) ∨
      subdivisionEdgeEnd baseTannerSquarePresentation 0 S e=
        .inr (.inl (seedRadial j,i)) := by
      fin_cases b
      · left
        exact (congrArg Prod.snd hv).symm
      · right
        exact (congrArg Prod.snd hv).symm
    rcases radialInterior_subdivision_edges S j i e hs with he | he | he
    · left
      exact congrArg (fun a : SubdivisionEdge baseTannerSquarePresentation 0 S =>
        (Sum.inl ⟨(0 : BaseX),.inl (0,a)⟩ : (RawOne S).Q)) he
    · right
      left
      exact congrArg (fun a : SubdivisionEdge baseTannerSquarePresentation 0 S =>
        (Sum.inl ⟨(0 : BaseX),.inl (0,a)⟩ : (RawOne S).Q)) he
    · right
      right
      exact congrArg (fun a : SubdivisionEdge baseTannerSquarePresentation 0 S =>
        (Sum.inl ⟨(0 : BaseX),.inl (0,a)⟩ : (RawOne S).Q)) he
  · fin_cases b
    · have hvertex : (Sum.inr (.inl (seedRadial j,i)) :
          SubdivisionVertex baseTannerSquarePresentation 0 S)=v.val := congrArg Prod.snd hv
      have hm := v.property
      rw [← hvertex] at hm
      simp [subdivisionBoundaryVertexMember,seedRadial,xStarBoundaryEdgeMember] at hm
    · change (0,Sum.inr (Sum.inl (seedRadial j,i)))=(1,v.val) at hv
      have hc := congrArg Prod.fst hv
      have : (0 : BDL26FiniteTannerSquare.Two)≠1 := by decide
      exact False.elim (this hc)

private theorem radialInterior_shifted_false (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    ¬(RawOne S).xq (radialInteriorX S j i) (.inr ⟨q,v⟩)=true := by
  have hm := raw_boundary1_view S (radialInteriorX S j i) (.inr ⟨q,v⟩)
  have hz : rxBoundary1Matrix baseTannerSquarePresentation S
      (radialInteriorX S j i) (.inr ⟨q,v⟩)=0 := by
    rcases v with ⟨c,(cone | endpoint) | ⟨edge,k⟩⟩
    all_goals
      fin_cases c <;>
        simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
          qSubdivisionVertexXIncidence,radialInteriorX,seedRadial,
          xStarBoundaryEdgeToStar,qToXBoundaryEdge,Subtype.ext_iff,dite_eq_ite,ite_self]
    all_goals split_ifs <;> simp_all only [dite_eq_ite,ite_self]
    all_goals
      change (if _hxq : baseTannerSquarePresentation.xq (0 : BaseX) q=true then
        (0:F) else 0)=0
      split_ifs <;> rfl
  change rxBoundary1Matrix baseTannerSquarePresentation S
    (radialInteriorX S j i) (.inr ⟨q,v⟩)=
    (if (RawOne S).xq (radialInteriorX S j i) (.inr ⟨q,v⟩)=true then (1:F) else 0) at hm
  intro hi
  erw [hz,if_pos hi] at hm
  exact zero_ne_one hm

private theorem radialInterior_neighbours (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (r : (RawOne S).Q)
    (hr : (RawOne S).xq (radialInteriorX S j i) r=true) :
    r=gammaRadial S j (radialPrevious S i) ∨
      r=gammaRadial S j (radialFollowing S i) ∨ r=radialPerp S j i := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · rcases (old_local_incidence S _ x e).mp hr with hs | ht
    · exact radialInterior_endpoint_neighbours S j i x e 0
        (by change radialInteriorX S j i=⟨x,tannerDoubleCylinderEdgeStart
          baseTannerSquarePresentation x S e⟩; exact hs)
    · exact radialInterior_endpoint_neighbours S j i x e 1
        (by change radialInteriorX S j i=⟨x,tannerDoubleCylinderEdgeEnd
          baseTannerSquarePresentation x S e⟩; exact ht)
  · exact False.elim (radialInterior_shifted_false S j i q v hr)

/- Source-only continuation after raised-boundary-snippets.lean; uncompiled. -/

private def raisedPortSupport (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (hh : 2≤S.half) (i : Fin (S.half-1))
    (e : SubdivisionEdge P x S) : Prop :=
  raisedBoundarySupport P x S hh e ∨
    ∃ f : XStarFace P x,
      e=.inr (.inl (f,lastSegment S,i)) ∨ e=.inr (.inr (f,i,lastSegment S))

private theorem shiftedFacePath0_raised_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) (f : XStarFace P x)
    (i : Fin (S.half-1)) (e : SubdivisionEdge P x S)
    (he : pathChain (shiftedFacePath0 P x S f i) e≠0) :
    raisedPortSupport P x S hh i e := by
  rcases shiftedFacePath0_support P x S f i e he with h | h
  · obtain ⟨k,_,rfl⟩ := h
    left; left
    exact ⟨f,k,rfl⟩
  · right
    exact ⟨f,Or.inl h⟩

private theorem shiftedFacePath1_raised_support (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (hh : 2≤S.half) (f : XStarFace P x)
    (i : Fin (S.half-1)) (e : SubdivisionEdge P x S)
    (he : pathChain (shiftedFacePath1 P x S f i) e≠0) :
    raisedPortSupport P x S hh i e := by
  rcases shiftedFacePath1_support P x S f i e he with h | h
  · obtain ⟨k,_,rfl⟩ := h
    left; right; left
    exact ⟨f,k,rfl⟩
  · right
    exact ⟨f,Or.inr h⟩

private theorem exists_actual_raised_face_port_path (S : OddScale) (hh : 2≤S.half)
    (z : (RawOne S).Z) (f : XStarFace (transposePresentation (RawOne S)) z)
    (j : BDL26FiniteTannerSquare.Two)
    (hz : (RawOne S).qz ((RawOne S).faceQ f.val j) z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (actualRaisedRoots S hh c z)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible
        ((RawOne S).faceQ f.val j) z hz S
        (chosenPort (RawOne S) S ((RawOne S).faceQ f.val j)
          ((RawOne S).faceX f.val) ((RawOne S).data.faceQ_xq f.val j) c (some i))),
      ∀ e, pathChain p e≠0 → ∃ e',
        e=.inl (c,e') ∧ raisedPortSupport (transposePresentation (RawOne S)) z S hh i e' := by
  have oldBoundary := exists_actual_raised_boundary_path S hh c z
    (xBoundaryEdgeStart (transposePresentation (RawOne S)) z
      (faceBoundaryEdge (transposePresentation (RawOne S)) z f j))
  have hboundary := congrArg (fun v => (c,v))
    (raisedBoundary_face_start (transposePresentation (RawOne S)) z S hh f j)
  have boundary := (exists_supported_path_congr rfl hboundary _).mp oldBoundary
  fin_cases j
  · have hend := congrArg (fun v => (c,v))
      (qToZ_face_interior0 (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible z f hz S i)
    apply (exists_supported_path_congr rfl hend.symm _).mp
    simp only [ite_true] at boundary
    obtain ⟨initialPath,hprefix⟩ := boundary
    let suffix := atCopyPath (transposePresentation (RawOne S)) z S c
      (shiftedFacePath0 (transposePresentation (RawOne S)) z S f i)
    refine ⟨initialPath.append suffix,?_⟩
    apply path_append_support
    · intro e he
      obtain ⟨e',heq,hs⟩ := hprefix e he
      exact ⟨e',heq,Or.inl hs⟩
    · intro e he
      obtain ⟨e',he',heq⟩ := atCopyPath_support
        (transposePresentation (RawOne S)) z S c _ e he
      exact ⟨e',heq,shiftedFacePath0_raised_support
        (transposePresentation (RawOne S)) z S hh f i e' he'⟩
  · have hend := congrArg (fun v => (c,v))
      (qToZ_face_interior1 (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible z f hz S i)
    apply (exists_supported_path_congr rfl hend.symm _).mp
    simp only [show (1 : BDL26FiniteTannerSquare.Two)≠0 by decide,ite_false] at boundary
    obtain ⟨initialPath,hprefix⟩ := boundary
    let suffix := atCopyPath (transposePresentation (RawOne S)) z S c
      (shiftedFacePath1 (transposePresentation (RawOne S)) z S f i)
    refine ⟨initialPath.append suffix,?_⟩
    apply path_append_support
    · intro e he
      obtain ⟨e',heq,hs⟩ := hprefix e he
      exact ⟨e',heq,Or.inl hs⟩
    · intro e he
      obtain ⟨e',he',heq⟩ := atCopyPath_support
        (transposePresentation (RawOne S)) z S c _ e he
      exact ⟨e',heq,shiftedFacePath1_raised_support
        (transposePresentation (RawOne S)) z S hh f i e' he'⟩

private theorem exists_actual_raised_port_path (S : OddScale) (hh : 2≤S.half)
    (r : (RawOne S).Q) (x : (RawOne S).X) (z : (RawOne S).Z)
    (hx : (RawOne S).xq x r=true) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (actualRaisedRoots S hh c z)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (chosenPort (RawOne S) S r x hx c (some i))),
      ∀ e, pathChain p e≠0 → ∃ e',
        e=.inl (c,e') ∧ raisedPortSupport (transposePresentation (RawOne S)) z S hh i e' := by
  obtain ⟨f,j,hq,hx'⟩ := face_of_qxz (RawOne S) x r z hx hz
  cases hq
  cases hx'
  exact exists_actual_raised_face_port_path S hh z f j hz c i

private def castZStarEdge {P Q : TannerSquarePresentation} (h : P=Q)
    (z : Q.Z) (a : XStarEdge (transposePresentation Q) z) :
    XStarEdge (transposePresentation P)
      (cast (congrArg TannerSquarePresentation.Z h).symm z) := by
  cases h
  exact a

private def castZStarFace {P Q : TannerSquarePresentation} (h : P=Q)
    (z : Q.Z) (f : XStarFace (transposePresentation Q) z) :
    XStarFace (transposePresentation P)
      (cast (congrArg TannerSquarePresentation.Z h).symm z) := by
  cases h
  exact f

private theorem cast_rz_any_segment (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (z : Q.Z) (a : XStarEdge (transposePresentation Q) z)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inl (a,k))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inl (castZStarEdge h z a,k))⟩ := by
  cases h
  rfl

private theorem cast_rz_horizontal (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (z : Q.Z) (f : XStarFace (transposePresentation Q) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin S.half) (b : Fin (S.half-1)) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inr (.inl (f,a,b)))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inr (.inl (castZStarFace h z f,a,b)))⟩ := by
  cases h
  rfl

private theorem cast_rz_vertical (S : OddScale) {P Q : TannerSquarePresentation}
    (h : P=Q) (z : Q.Z) (f : XStarFace (transposePresentation Q) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin (S.half-1)) (b : Fin S.half) :
    cast (congrArg (fun P => RZQ P S) h).symm
      (.inl ⟨z,.inl (c,.inr (.inr (f,a,b)))⟩)=
      .inl ⟨cast (congrArg TannerSquarePresentation.Z h).symm z,
        .inl (c,.inr (.inr (castZStarFace h z f,a,b)))⟩ := by
  cases h
  rfl

private theorem encoded_any_segment (S : OddScale) (z : (RawOne S).Z)
    (a : XStarEdge (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    Encodable.encode (executableCoordinate S (.inl ⟨z,.inl (c,.inl (a,k))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*Nat.pair
          (Encodable.encode (castZStarEdge
            (executableLevelOne_eq_raw S) z a).val) k.val)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_any_segment S (executableLevelOne_eq_raw S) z a c k]
  rfl

private theorem structural_horizontal_encoding (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] [Encodable P.Face]
    (S : OddScale) (z : P.Z) (f : XStarFace (transposePresentation P) z)
    (c : BDL26FiniteTannerSquare.Two)
    (a : Fin S.half) (b : Fin (S.half-1)) :
  letI : Encodable (transposePresentation P).Face :=
    inferInstanceAs (Encodable P.Face)
  letI : ∀ z : P.Z, Encodable (SubdivisionVertex (transposePresentation P) z S) :=
    fun z => by
      dsimp [SubdivisionVertex,XStarVertex,XStarEdge,XStarFace,
        BDL26FiniteTannerSquare.Edge,XQEdge,QZEdge,
        transposePresentation,transposeTannerSquareData]
      infer_instance
  letI : ∀ z : P.Z, Encodable (SubdivisionEdge (transposePresentation P) z S) :=
    fun z => by
      dsimp [SubdivisionEdge,XStarEdge,XStarFace,BDL26FiniteTannerSquare.Edge,
        XQEdge,QZEdge,transposePresentation,transposeTannerSquareData]
      infer_instance
  letI : Encodable (RZQ P S) := by
    dsimp [RZQ,ZDoubleCylinderEdge,DoubleCylinderEdge,QDoubleCylinderVertex,
      transposePresentation,transposeTannerSquareData]
    infer_instance
  Encodable.encode (Sum.inl ⟨z,Sum.inl (c,Sum.inr (Sum.inl (f,a,b)))⟩ : RZQ P S)=
    2*Nat.pair (Encodable.encode z) (2*Nat.pair c.val (2*(2*Nat.pair (Encodable.encode f.val) (Nat.pair a.val b.val))+1)) := by
  rfl

private theorem structural_vertical_encoding (P : TannerSquarePresentation)
    [Encodable P.X] [Encodable P.Q] [Encodable P.Z] [Encodable P.Face]
    (S : OddScale) (z : P.Z) (f : XStarFace (transposePresentation P) z)
    (c : BDL26FiniteTannerSquare.Two)
    (a : Fin (S.half-1)) (b : Fin S.half) :
  letI : Encodable (transposePresentation P).Face :=
    inferInstanceAs (Encodable P.Face)
  letI : ∀ z : P.Z, Encodable (SubdivisionVertex (transposePresentation P) z S) :=
    fun z => by
      dsimp [SubdivisionVertex,XStarVertex,XStarEdge,XStarFace,
        BDL26FiniteTannerSquare.Edge,XQEdge,QZEdge,
        transposePresentation,transposeTannerSquareData]
      infer_instance
  letI : ∀ z : P.Z, Encodable (SubdivisionEdge (transposePresentation P) z S) :=
    fun z => by
      dsimp [SubdivisionEdge,XStarEdge,XStarFace,BDL26FiniteTannerSquare.Edge,
        XQEdge,QZEdge,transposePresentation,transposeTannerSquareData]
      infer_instance
  letI : Encodable (RZQ P S) := by
    dsimp [RZQ,ZDoubleCylinderEdge,DoubleCylinderEdge,QDoubleCylinderVertex,
      transposePresentation,transposeTannerSquareData]
    infer_instance
  Encodable.encode (Sum.inl ⟨z,Sum.inl (c,Sum.inr (Sum.inr (f,a,b)))⟩ : RZQ P S)=
    2*Nat.pair (Encodable.encode z) (2*Nat.pair c.val (2*(2*Nat.pair (Encodable.encode f.val) (Nat.pair a.val b.val)+1)+1)) := by
  rfl

private theorem encoded_horizontal_raw (S : OddScale) (z : (RawOne S).Z)
    (f : XStarFace (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin S.half) (b : Fin (S.half-1)) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inr (.inl (f,a,b)))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*(2*Nat.pair
          (Encodable.encode (castZStarFace
            (executableLevelOne_eq_raw S) z f).val)
          (Nat.pair a.val b.val))+1)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_horizontal S (executableLevelOne_eq_raw S) z f c a b]
  exact structural_horizontal_encoding (BDL26LevelTwoDecoder.executableLevelOne S) S
    (cast (congrArg TannerSquarePresentation.Z (executableLevelOne_eq_raw S)).symm z)
    (castZStarFace (executableLevelOne_eq_raw S) z f) c a b

private theorem encoded_horizontal (S : OddScale) (z : (RawOne S).Z)
    (f : XStarFace (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin S.half) (b : Fin (S.half-1)) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inr (.inl (f,a,b)))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (4*Nat.pair
          (Encodable.encode (castZStarFace
            (executableLevelOne_eq_raw S) z f).val)
          (Nat.pair a.val b.val)+1)) := by
  rw [encoded_horizontal_raw]
  apply congrArg (fun n => 2*Nat.pair
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (2*Nat.pair c.val n))
  omega

private theorem encoded_vertical_raw (S : OddScale) (z : (RawOne S).Z)
    (f : XStarFace (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin (S.half-1)) (b : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inr (.inr (f,a,b)))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (2*(2*Nat.pair
          (Encodable.encode (castZStarFace
            (executableLevelOne_eq_raw S) z f).val)
          (Nat.pair a.val b.val)+1)+1)) := by
  change Encodable.encode (cast (congrArg (fun P => RZQ P S)
    (executableLevelOne_eq_raw S)).symm _) = _
  erw [cast_rz_vertical S (executableLevelOne_eq_raw S) z f c a b]
  exact structural_vertical_encoding (BDL26LevelTwoDecoder.executableLevelOne S) S
    (cast (congrArg TannerSquarePresentation.Z (executableLevelOne_eq_raw S)).symm z)
    (castZStarFace (executableLevelOne_eq_raw S) z f) c a b

private theorem encoded_vertical (S : OddScale) (z : (RawOne S).Z)
    (f : XStarFace (transposePresentation (RawOne S)) z)
    (c : BDL26FiniteTannerSquare.Two) (a : Fin (S.half-1)) (b : Fin S.half) :
    Encodable.encode (executableCoordinate S
      (.inl ⟨z,.inl (c,.inr (.inr (f,a,b)))⟩))=
      2*Nat.pair (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
        (2*Nat.pair c.val (4*Nat.pair
          (Encodable.encode (castZStarFace
            (executableLevelOne_eq_raw S) z f).val)
          (Nat.pair a.val b.val)+3)) := by
  rw [encoded_vertical_raw]
  apply congrArg (fun n => 2*Nat.pair
    (Encodable.encode (z : (BDL26LevelTwoDecoder.executableLevelOne S).Z))
    (2*Nat.pair c.val n))
  omega

private theorem raisedPortSupport_later (S : OddScale) (hh : 2≤S.half)
    (r0 : (RawOne S).Q) (x0 : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (z : (RawOne S).Z)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1))
    (hr : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)< i.val)
    (hx : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)< i.val)
    (e : SubdivisionEdge (transposePresentation (RawOne S)) z S)
    (he : raisedPortSupport (transposePresentation (RawOne S)) z S hh i e) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c (some i)⟩))<
      Encodable.encode (executableCoordinate S (.inl ⟨z,.inl (c,e)⟩)) := by
  rw [encoded_chosenPort]
  rcases he with (⟨f,k,rfl⟩ | ⟨f,k,rfl⟩ | ⟨a,rfl⟩) | ⟨f,h | h⟩
  · erw [encoded_vertical]
    apply interior_before_grid_code _ _ _ _ _ _ _ _ c hr hx _ (by decide)
    have := i.isLt
    dsimp [lastInterior]
    omega
  · erw [encoded_horizontal]
    apply interior_before_grid_code _ _ _ _ _ _ _ _ c hr hx _ (by decide)
    have := i.isLt
    dsimp [lastInterior]
    omega
  · erw [encoded_any_segment]
    exact interior_before_far_last_radial_code _ _ _ _ _ _ c hr hx
      (by have := i.isLt; dsimp [lastSegment]; omega)
  · subst e
    erw [encoded_horizontal]
    exact interior_before_grid_code _ _ _ _ _ _ _ _ c hr hx
      (by have := i.isLt; dsimp [lastSegment]; omega) (by decide)
  · subst e
    erw [encoded_vertical]
    exact interior_before_grid_code _ _ _ _ _ _ _ _ c hr hx
      (by have := i.isLt; dsimp [lastSegment]; omega) (by decide)

private theorem exists_raised_path_later (S : OddScale)
    (r0 r : (RawOne S).Q) (x0 x : (RawOne S).X)
    (hx0 : (RawOne S).xq x0 r0=true) (hx : (RawOne S).xq x r=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1))
    (hr : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)< i.val)
    (hX : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)< i.val) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (actualRaisedRoots S (by have := i.isLt; omega) c z)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (chosenPort (RawOne S) S r x hx c (some i))),
      ∀ e, pathChain p e≠0 →
        Encodable.encode (executableCoordinate S
          (.inr ⟨r0,chosenPort (RawOne S) S r0 x0 hx0 c (some i)⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)) := by
  have hh : 2≤S.half := by have := i.isLt; omega
  obtain ⟨p,hp⟩ := exists_actual_raised_port_path S hh r x z hx hz c i
  refine ⟨p,?_⟩
  intro e he
  obtain ⟨e',rfl,hs⟩ := hp e he
  exact raisedPortSupport_later S hh r0 x0 hx0 z c i hr hX e' hs

private theorem global_same_owner_raised_zero (S : OddScale) (a : Word F (RawTwo S).Q)
    (r : (RawOne S).Q) (z : (RawOne S).Z) (hz : (RawOne S).qz r z=true)
    (hu : ∀ z', (RawOne S).qz r z'=true → z'=z)
    (x x' : (RawOne S).X) (hx : (RawOne S).xq x r=true)
    (hx' : (RawOne S).xq x' r=true) (c : BDL26FiniteTannerSquare.Two)
    (i : Fin (S.half-1))
    (hr : Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)< i.val)
    (hX : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)< i.val)
    (horder : Encodable.encode (executableCoordinate S
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c (some i)⟩))<
        Encodable.encode (executableCoordinate S
          (.inr ⟨r,chosenPort (RawOne S) S r x' hx' c (some i)⟩))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨r,chosenPort (RawOne S) S r x hx c (some i)⟩)=0 := by
  obtain ⟨p,hp⟩ := exists_raised_path_later S r r x x hx hx z hz c i hr hX
  obtain ⟨p',hp'⟩ := exists_raised_path_later S r r x x' hx hx' z hz c i hr hX
  exact global_zero_of_same_owner_pair S a r z hz hu _ _
    (actualRaisedRoots S (by have := i.isLt; omega) c z) p p' horder hp hp'

private theorem gamma_code_gt_one (S : OddScale) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) :
    1<Encodable.encode (gammaRadial S j n :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [encoded_gammaRadial]
  have hl := Nat.left_le_pair (2*j.val) n.val
  have hr := Nat.right_le_pair (2*j.val) n.val
  have hp : 0<Nat.pair (2*j.val) n.val := by omega
  have hp4 : 0<(Nat.pair (2*j.val) n.val)^4 := pow_pos hp _
  omega

private theorem global_radial_minor_interior_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (n : Fin S.half)
    (hn : 0<j.val+n.val) (x : (RawOne S).X)
    (hx : (RawOne S).xq x (gammaRadial S j n)=true)
    (hne : x≠oldLargestX S (gammaRadial S j n))
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j n,(c,.inr (⟨x,hx⟩,i))⟩)=0 := by
  let r := gammaRadial S j n
  let K := Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  have hK : 0<K := gamma_code_pos S j n hn
  have hK1 : 1<K := gamma_code_gt_one S j n hn
  have hxle := oldLargestX_upper S 0 (.inl (0,.inl (seedRadial j,n))) x hx
  change Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
    Encodable.encode (oldLargestX S r :
      (BDL26LevelTwoDecoder.executableLevelOne S).X) at hxle
  have hstrict : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    have hnc : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)≠
        Encodable.encode (oldLargestX S r :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) :=
      fun he => hne (Encodable.encode_injective he)
    omega
  have hX : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<K^2 :=
    hstrict.trans_le (gammaLargestX_le_square S j n hn)
  have hR : K<K^2 := by nlinarith
  have hz : (RawOne S).qz r (seedRadialCheck S j n)=true :=
    (seedRadial_degree_one S j n).1
  have horder := chosenPort_order_same_owner S r x (oldLargestX S r) hx
    (oldLargestX_incident S r) c (some i) hstrict
  by_cases hi : i.val<K^2
  · have hidepth : ∀ k, some i=some k → k.val<K^2 := by
      intro k he
      cases he
      exact hi
    exact global_same_owner_direct_zero S a r (seedRadialCheck S j n) hz
      (seedRadial_degree_one S j n).2 x (oldLargestX S r) hx
      (oldLargestX_incident S r) c (some i) K hK le_rfl hR.le hX.le hidepth horder
  · have hr : K< i.val := by omega
    have hx' : Encodable.encode (x : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
        i.val := by omega
    exact global_same_owner_raised_zero S a r (seedRadialCheck S j n) hz
      (seedRadial_degree_one S j n).2 x (oldLargestX S r) hx
      (oldLargestX_incident S r) c i hr hx' horder

private theorem radial_perp_tag_gt (j : Fin 2) (i : Nat)
    (hex : j.val≠1 ∨ i≠0) :
    2*Nat.pair (2*j.val) i<4*Nat.pair j.val (Nat.pair i 0)+3 := by
  fin_cases j
  · change 2*Nat.pair 0 i<4*Nat.pair 0 (Nat.pair i 0)+3
    rw [pair_zero_left_sq]
    have hsq : i^2≤Nat.pair i 0 := by
      simpa only [max_eq_left (Nat.zero_le i),min_eq_right (Nat.zero_le i),add_zero] using
        Nat.max_sq_add_min_le_pair i 0
    have hl := Nat.right_le_pair 0 (Nat.pair i 0)
    omega
  · change 1≠1 ∨ i≠0 at hex
    change 2*Nat.pair 2 i<4*Nat.pair 1 (Nat.pair i 0)+3
    have hi : 0 < i := by omega
    by_cases hone : i=1
    · subst i
      decide
    · have hi2 : 2 ≤ i := by omega
      have hp : Nat.pair 2 i<(i+1)^2 := by
        simpa only [max_eq_right hi2] using Nat.pair_lt_max_add_one_sq 2 i
      have hl : i^2≤Nat.pair i 0 := by
        simpa only [max_eq_left (Nat.zero_le i),min_eq_right (Nat.zero_le i),add_zero] using
          Nat.max_sq_add_min_le_pair i 0
      have hli : i+1≤Nat.pair i 0 := by nlinarith
      have hs := Nat.pow_le_pow_left hli 2
      have hlow := Nat.max_sq_add_min_le_pair 1 (Nat.pair i 0)
      have hs' := Nat.pow_le_pow_left (Nat.le_max_right 1 (Nat.pair i 0)) 2
      have hlow' : max 1 (Nat.pair i 0)^2≤Nat.pair 1 (Nat.pair i 0) := by omega
      have hpair := hp.trans_le (hs.trans (hs'.trans hlow'))
      omega

private theorem old_local_subedge_order (S : OddScale)
    (e e' : SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) S)
    (h : subEdgeCode 0 S e<subEdgeCode 0 S e') :
    Encodable.encode (.inl ⟨(0 : BaseX),.inl (0,e)⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (.inl ⟨(0 : BaseX),.inl (0,e')⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [encoded_old_local_Q,encoded_old_local_Q]
  have hi := Nat.pair_lt_pair_right 0 h
  have ho := Nat.pair_lt_pair_right 0 (show 2*Nat.pair 0 (subEdgeCode 0 S e)<
      2*Nat.pair 0 (subEdgeCode 0 S e') by omega)
  simp only [Fin.val_zero,Fin.val_one,Fin.val_mk] at *
  omega

private theorem radialInterior_minimum (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) (hex : j.val≠1 ∨ i.val≠0)
    (r : (RawOne S).Q) (hr : (RawOne S).xq (radialInteriorX S j i) r=true)
    (hne : r≠gammaRadial S j (radialPrevious S i)) :
    Encodable.encode (gammaRadial S j (radialPrevious S i) :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  rcases radialInterior_neighbours S j i r hr with h | h | h
  · exact False.elim (hne h)
  · subst r
    apply old_local_subedge_order S
    change 2*Nat.pair (baseEdgeCode (seedRadial j).val) i.val<
      2*Nat.pair (baseEdgeCode (seedRadial j).val) (i.val+1)
    have := Nat.pair_lt_pair_right (baseEdgeCode (seedRadial j).val)
      (Nat.lt_succ_self i.val)
    simp only [Nat.succ_eq_add_one,Fin.val_mk] at *
    omega
  · subst r
    apply old_local_subedge_order S
    change 2*Nat.pair (baseEdgeCode (seedRadial j).val) i.val<
      4*Nat.pair j.val (Nat.pair i.val 0)+3
    rw [seedRadial_code]
    exact radial_perp_tag_gt j i.val hex

private theorem radialInterior_is_end (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) :
    oldLocalEnd S 0 (.inl (0,.inl (seedRadial j,radialPrevious S i)))=
      radialInteriorX S j i := by
  have hn : (radialPrevious S i).val+1≠S.half := by
    have := i.isLt
    dsimp [radialPrevious]
    omega
  simp only [oldLocalEnd,tannerDoubleCylinderEdgeEnd,subdivisionEdgeEnd,
    subdivisionSegmentEnd,dif_neg hn]
  apply congrArg (fun v => (⟨(0 : BaseX),(0,v)⟩ : (RawOne S).X))
  apply congrArg Sum.inr
  apply congrArg Sum.inl
  apply Prod.ext rfl
  apply Fin.ext
  rfl

private theorem radialInterior_incident (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) :
    (RawOne S).xq (radialInteriorX S j i)
      (gammaRadial S j (radialPrevious S i))=true := by
  apply (old_local_incidence S _ 0
    (.inl (0,.inl (seedRadial j,radialPrevious S i)))).2
  right
  exact (radialInterior_is_end S j i).symm

private theorem radialInterior_largest (S : OddScale) (j : Fin 2)
    (i : Fin (S.half-1)) :
    oldLargestX S (gammaRadial S j (radialPrevious S i))=radialInteriorX S j i := by
  have horder : Encodable.encode (oldLocalStart S 0
      (.inl (0,.inl (seedRadial j,radialPrevious S i))) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLocalEnd S 0
        (.inl (0,.inl (seedRadial j,radialPrevious S i))) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
    rw [radialInterior_is_end]
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial j)
        (radialPrevious S i))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (⟨(0 : BaseX),(0,.inr (.inl (seedRadial j,i)))⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_copy0,encoded_old_X_copy0]
    unfold subdivisionSegmentStart
    split_ifs with hz
    · simp only [subVertexCode,seedRadial_start_code,mul_zero,zero_pow (by decide : (4:Nat)≠0)]
      exact Nat.zero_le _
    · apply Nat.pow_le_pow_left _ 4
      change 4*Nat.pair (baseEdgeCode (seedRadial j).val) (i.val-1)+1≤
        4*Nat.pair (baseEdgeCode (seedRadial j).val) i.val+1
      have := pair_mono_right (baseEdgeCode (seedRadial j).val) (i.val-1) i.val
        (Nat.sub_le _ _)
      omega
  change (if _ then _ else _)=_
  erw [if_pos horder]
  exact radialInterior_is_end S j i

private theorem global_nonterminal_large_port_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (i : Fin (S.half-1))
    (hex : j.val≠1 ∨ i.val≠0) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j (radialPrevious S i),
        largePorts S c depth (gammaRadial S j (radialPrevious S i))⟩)=0 := by
  have hx := radialInterior_incident S j i
  have hl := radialInterior_largest S j i
  cases depth with
  | none =>
    change BDL26GlobalLookupLinearity.actualGlobal S _
      (.inr ⟨_,(c,.inl (.inr ⟨_,_⟩))⟩)=0
    simp only [hl]
    exact global_endpoint_of_least_old_neighbor S a _ _ hx c
      (radialInterior_minimum S j i hex)
  | some k =>
    by_cases hk : k.val+2<S.half
    · exact global_interior_zero_before_last S a _ _ _ c k hk
    · have hh : 2≤S.half := by have := k.isLt; omega
      have hlast : k=lastInterior S hh := by
        apply Fin.ext
        have := k.isLt
        dsimp [lastInterior]
        omega
      subst k
      change BDL26GlobalLookupLinearity.actualGlobal S _
        (.inr ⟨_,(c,.inr (⟨_,_⟩,lastInterior S hh))⟩)=0
      simp only [hl]
      exact global_last_interior_of_least_old_neighbor S hh a _ _ hx c
        (radialInterior_minimum S j i hex)

private def firstCutHorizontal (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) : (RawOne S).Q :=
  .inl ⟨x,.inl (c,subdivisionHorizontalEdge baseTannerSquarePresentation x S
    (stripFace 1 x) ⟨0,S.half_pos⟩ row)⟩

private theorem firstCutOldKernel_support (S : OddScale)
    (r : (RawOne S).Q) (hr : firstCutOldKernel S r≠0) :
    ∃ (x : BaseX) (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)),
      r=firstCutHorizontal S x c row := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · rcases e with ⟨c,e⟩ | v
    · rcases subdivision_edge_grid_cover baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 x S e with hh | hv
      · obtain ⟨f,i,row,he⟩ := hh
        subst e
        erw [firstCutOldKernel_horizontal] at hr
        have h : f=stripFace 1 x ∧ i.val=0 := by
          by_contra hn
          rw [if_neg hn] at hr
          exact hr rfl
        rcases h with ⟨hf,hi⟩
        subst f
        have hi0 : i=⟨0,S.half_pos⟩ := Fin.ext hi
        subst i
        exact ⟨x,c,row,rfl⟩
      · obtain ⟨f,column,i,he⟩ := hv
        subst e
        erw [firstCutOldKernel_vertical] at hr
        exact False.elim (hr rfl)
    · erw [firstCutOldKernel,Pi.add_apply,rawSeedLift,
        BDL26ReplacementCochainMaps.rxMap1Coord_localEdge,zero_add,
        rx_local_gradient] at hr
      change ((if firstCutMember x S v.val then (1:F) else 0)+
        (if firstCutMember x S v.val then (1:F) else 0))≠0 at hr
      exact False.elim (hr (ZModModule.add_self _))
  · exact False.elim (hr (firstCutOldKernel_q_zero S q v))

private theorem firstCut_subedge_lower (S : OddScale) (x : BaseX)
    (row : Fin (S.half+1)) :
    9≤ subEdgeCode x S (subdivisionHorizontalEdge baseTannerSquarePresentation x S
      (stripFace 1 x) ⟨0,S.half_pos⟩ row) := by
  unfold subdivisionHorizontalEdge
  split_ifs with hzero hlast
  · change 9≤2*Nat.pair (baseEdgeCode
      (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0).val) 0
    rw [stripFace_xq_code]
    fin_cases x <;> decide
  · change 9≤2*Nat.pair (baseEdgeCode
      (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace 1 x) 1).val) 0
    rw [stripFace_qz_code]
    decide
  · change 9≤4*Nat.pair (1+2*x.val) (Nat.pair 0 (row.val-1))+1
    have hl := Nat.max_sq_add_min_le_pair (1+2*x.val) (Nat.pair 0 (row.val-1))
    have hs := Nat.pow_le_pow_left (Nat.le_max_left (1+2*x.val)
      (Nat.pair 0 (row.val-1))) 2
    have hx : 1≤1+2*x.val := by omega
    have hp : 2≤Nat.pair (1+2*x.val) (Nat.pair 0 (row.val-1)) := by
      rw [Nat.pair]
      split_ifs with h
      · have := Nat.pow_le_pow_left h.le 2
        nlinarith
      · nlinarith
    omega

private theorem firstCut_oldQ_lower (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) :
    52488≤Encodable.encode (firstCutHorizontal S x c row :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  erw [firstCutHorizontal,encoded_old_local_Q]
  have hE := firstCut_subedge_lower S x row
  let E := subEdgeCode x S (subdivisionHorizontalEdge baseTannerSquarePresentation x S
    (stripFace 1 x) ⟨0,S.half_pos⟩ row)
  have hi := pair_mono_right 0 9 E hE
  have hc := pair_mono_left 0 c.val E (Nat.zero_le _)
  have hm : 2*Nat.pair 0 9≤2*Nat.pair c.val E := by omega
  have ho := pair_mono_right 0 _ _ hm
  have hx := pair_mono_left 0 x.val (2*Nat.pair c.val E) (Nat.zero_le _)
  have hconstant : 2*Nat.pair 0 (2*Nat.pair 0 9)=52488 := by decide
  have ho' : 2*Nat.pair 0 (2*Nat.pair 0 9)≤
      2*Nat.pair 0 (2*Nat.pair c.val E) := Nat.mul_le_mul_left 2 ho
  rw [hconstant] at ho'
  exact ho'.trans (Nat.mul_le_mul_left 2 hx)

private theorem largePorts_later_of_X (S : OddScale)
    (r0 r : (RawOne S).Q) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1)))
    (hX : Encodable.encode (oldLargestX S r0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      Encodable.encode (oldLargestX S r : (BDL26LevelTwoDecoder.executableLevelOne S).X))
    (hR : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      (Encodable.encode (oldLargestX S r :
        (BDL26LevelTwoDecoder.executableLevelOne S).X))^2) :
    Encodable.encode (executableCoordinate S (.inr ⟨r0,largePorts S c depth r0⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,largePorts S c depth r⟩)) := by
  let X0 := Encodable.encode (oldLargestX S r0 :
    (BDL26LevelTwoDecoder.executableLevelOne S).X)
  let X := Encodable.encode (oldLargestX S r :
    (BDL26LevelTwoDecoder.executableLevelOne S).X)
  have htail : ∀ V : Nat, X≤V →
      Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
        Nat.pair c.val V := by
    intro V hV
    have hs := Nat.pow_le_pow_left hV 2
    have hl := Nat.max_sq_add_min_le_pair c.val V
    have hm := Nat.pow_le_pow_left (Nat.le_max_right c.val V) 2
    dsimp only [X,X0] at *
    omega
  cases depth with
  | none =>
    rw [encoded_largePorts,encoded_largePorts]
    dsimp only
    apply q_before_larger_port_code _ _ _ _ c (by omega)
    exact htail _ (by omega)
  | some i =>
    rw [encoded_largePorts,encoded_largePorts]
    dsimp only
    have hp := Nat.pair_lt_pair_left i.val hX
    apply q_before_larger_port_code _ _ _ _ c (by omega)
    apply htail
    have hl := Nat.left_le_pair X i.val
    dsimp only [X,X0] at *
    omega

private theorem firstCut_target_X_bound (S : OddScale) :
    Encodable.encode (oldLargestX S (gammaRadial S 1 ⟨0,S.half_pos⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤390625 := by
  apply oldLargestX_le_of_ends
  · change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial 1)
        ⟨0,S.half_pos⟩)⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0]
    simp only [subdivisionSegmentStart,Fin.val_mk,↓reduceDIte,subVertexCode,
      seedRadial_start_code,mul_zero,zero_pow (by decide : (4:Nat)≠0)]
    decide
  · change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial 1)
        ⟨0,S.half_pos⟩)⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0]
    unfold subdivisionSegmentEnd
    split_ifs
    · norm_num [subVertexCode,seedRadial_end_code]
    · norm_num [subVertexCode,seedRadial_code,Nat.pair]

private theorem firstCut_nonbottom_X_lower (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) (row : Fin (S.half+1)) (hrow : row.val≠0) :
    1336336≤Encodable.encode (oldLargestX S (firstCutHorizontal S x c row) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  apply localLargestX_ge_tag S x c _ 34
  apply le_trans _ (Nat.le_max_left _ _)
  unfold subdivisionHorizontalEdge
  simp only [dif_neg hrow]
  split_ifs with hlast
  · change 34≤ subVertexCode x S
      (subdivisionSegmentStart baseTannerSquarePresentation x S
        (xStarFaceQZEdge baseTannerSquarePresentation x (stripFace 1 x) 1)
        ⟨0,S.half_pos⟩)
    simp only [subdivisionSegmentStart,Fin.val_mk,↓reduceDIte,subVertexCode,
      stripFace_qz1_start_code]
    decide
  · have hrh : row.val≠S.half := hlast
    have hcode : 32≤baseEdgeCode
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 1).val := by
      fin_cases x <;> decide
    change 34≤ subVertexCode x S (subdivisionGridVertex baseTannerSquarePresentation x S
      (stripFace 1 x) (finCastGrid ⟨0,S.half_pos⟩)
      (finInteriorGrid S (finInteriorIndex S row hrow hrh)))
    have hk0 : (finInteriorGrid S (finInteriorIndex S row hrow hrh)).val≠0 := by
      simp [finInteriorGrid]
    have hkh : (finInteriorGrid S (finInteriorIndex S row hrow hrh)).val≠S.half := by
      have := row.isLt
      dsimp [finInteriorGrid,finInteriorIndex]
      omega
    simp only [subdivisionGridVertex,finCastGrid,↓reduceDIte,hk0,hkh]
    change 34≤4*Nat.pair
      (baseEdgeCode (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 1).val)
      (finInteriorIndex S row hrow hrh).val+1
    have hl := Nat.left_le_pair
      (baseEdgeCode (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 1).val)
      (finInteriorIndex S row hrow hrh).val
    omega

private theorem firstCut_row0_Q_lower (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (gammaRadial S 1 ⟨0,S.half_pos⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
      Encodable.encode (firstCutHorizontal S x c 0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  change Encodable.encode (.inl ⟨(0 : BaseX),.inl (0,.inl (seedRadial 1,⟨0,S.half_pos⟩))⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤
    Encodable.encode (.inl ⟨x,.inl (c,.inl
      (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0,
        ⟨0,S.half_pos⟩))⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).Q)
  erw [encoded_old_local_Q,encoded_old_local_Q]
  have hb : baseEdgeCode (seedRadial 1).val≤baseEdgeCode
      (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0).val := by
    fin_cases x <;> decide
  have he := pair_mono_left _ _ 0 hb
  have hi := pair_mono_right 0 _ _ (show
      subEdgeCode 0 S (.inl (seedRadial 1,⟨0,S.half_pos⟩))≤
      subEdgeCode x S (.inl
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0,
          ⟨0,S.half_pos⟩)) by change 2*Nat.pair _ 0≤2*Nat.pair _ 0; omega)
  have hc := pair_mono_left 0 c.val (subEdgeCode x S (.inl
    (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0,
      ⟨0,S.half_pos⟩))) (Nat.zero_le _)
  have hm := pair_mono_right 0 _ _ (show
      2*Nat.pair 0 (subEdgeCode 0 S (.inl (seedRadial 1,⟨0,S.half_pos⟩)))≤
      2*Nat.pair c.val (subEdgeCode x S (.inl
        (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0,
          ⟨0,S.half_pos⟩))) by omega)
  have ho := pair_mono_left 0 x.val (2*Nat.pair c.val (subEdgeCode x S (.inl
    (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0,
      ⟨0,S.half_pos⟩)))) (Nat.zero_le _)
  simp only [Fin.val_zero,Fin.val_one,Fin.val_mk] at *
  omega

private theorem firstCut_row0_X_lower (S : OddScale) (x : BaseX)
    (c : BDL26FiniteTannerSquare.Two) :
    Encodable.encode (oldLargestX S (gammaRadial S 1 ⟨0,S.half_pos⟩) :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (oldLargestX S (firstCutHorizontal S x c 0) :
        (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  let e : DoubleCylinderEdge baseTannerSquarePresentation x S :=
    .inl (c,.inl (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0,
      ⟨0,S.half_pos⟩))
  have hb : 2≤baseEdgeCode
      (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0).val := by
    fin_cases x <;> decide
  apply oldLargestX_le_of_ends
  · change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentStart baseTannerSquarePresentation 0 S (seedRadial 1)
        ⟨0,S.half_pos⟩)⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤_
    erw [encoded_old_X_copy0]
    simp only [subdivisionSegmentStart,Fin.val_mk,↓reduceDIte,subVertexCode,
      seedRadial_start_code,mul_zero,zero_pow (by decide : (4:Nat)≠0)]
    exact Nat.zero_le _
  · apply le_trans _ (oldLargestX_end_le S x e)
    change Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial 1)
        ⟨0,S.half_pos⟩)⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)≤
      Encodable.encode (⟨x,(c,
        subdivisionSegmentEnd baseTannerSquarePresentation x S
          (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0)
          ⟨0,S.half_pos⟩)⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_copy0,encoded_old_X]
    unfold subdivisionSegmentEnd
    split_ifs
    · apply oldX_tag_lower
      change 2*(4*(1 : Nat)+1)≤2*baseVertexCode
        (xStarFaceQVertex baseTannerSquarePresentation x (stripFace 1 x) 0).val
      rw [stripFace_q0_vertex_code]
      omega
    · apply oldX_tag_lower
      change 4*Nat.pair (baseEdgeCode (seedRadial 1).val) 0+1≤
        4*Nat.pair (baseEdgeCode
          (xStarFaceXQEdge baseTannerSquarePresentation x (stripFace 1 x) 0).val) 0+1
      rw [seedRadial_code]
      change 4*Nat.pair 2 0+1≤_
      have hp := pair_mono_left 2 _ 0 hb
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 hp) 1

private theorem firstCut_ports_later (S : OddScale)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1)))
    (r : (RawOne S).Q) (hr : firstCutOldKernel S r≠0)
    (hne : r≠gammaRadial S 1 ⟨0,S.half_pos⟩) :
    Encodable.encode (executableCoordinate S
      (.inr ⟨gammaRadial S 1 ⟨0,S.half_pos⟩,
        largePorts S c depth (gammaRadial S 1 ⟨0,S.half_pos⟩)⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,largePorts S c depth r⟩)) := by
  obtain ⟨x,c',row,rfl⟩ := firstCutOldKernel_support S r hr
  by_cases hrow : row.val=0
  · have hz : row=0 := Fin.ext hrow
    subst row
    exact largePorts_later S c depth _ _ hne
      (firstCut_row0_Q_lower S x c') (firstCut_row0_X_lower S x c')
  · apply largePorts_later_of_X
    · have h0 := firstCut_target_X_bound S
      have h1 := firstCut_nonbottom_X_lower S x c' row hrow
      omega
    · have ht : Encodable.encode (gammaRadial S 1 ⟨0,S.half_pos⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).Q)=165888 := by
        erw [encoded_gammaRadial]
        norm_num [Fin.val_mk] <;> decide
      rw [ht]
      have h1 := firstCut_nonbottom_X_lower S x c' row hrow
      nlinarith

private theorem global_firstCut_large_port_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (c : BDL26FiniteTannerSquare.Two)
    (depth : Option (Fin (S.half-1))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S 1 ⟨0,S.half_pos⟩,
        largePorts S c depth (gammaRadial S 1 ⟨0,S.half_pos⟩)⟩)=0 := by
  let r0 := gammaRadial S 1 ⟨0,S.half_pos⟩
  let x0 := oldLargestX S r0
  have hR : Encodable.encode (r0 : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      52488^2 := by
    change Encodable.encode (gammaRadial S 1 ⟨0,S.half_pos⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)<_
    erw [encoded_gammaRadial]
    norm_num [Fin.val_mk] <;> decide
  have hX : Encodable.encode (x0 : (BDL26LevelTwoDecoder.executableLevelOne S).X)<
      52488^2 := by
    have := firstCut_target_X_bound S
    dsimp [x0,r0]
    omega
  have hmin (r : (RawOne S).Q) (hr : firstCutOldKernel S r≠0) :
      52488≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
    obtain ⟨x,c',row,rfl⟩ := firstCutOldKernel_support S r hr
    exact firstCut_oldQ_lower S x c' row
  have direct (d : Option (Fin (S.half-1)))
      (hi : ∀ i, d=some i → i.val<52488^2) :
      BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
        (.inr ⟨r0,largePorts S c d r0⟩)=0 := by
    let paths : PortPaths S (largePorts S c d) (directRoots S c) := fun r z hz =>
      if hr : firstCutOldKernel S r≠0 then
        Classical.choose (exists_direct_path_later S r0 r x0 (oldLargestX S r)
          (oldLargestX_incident S r0) (oldLargestX_incident S r) z hz c d
          52488 (by decide) (hmin r hr) hR.le hX.le hi)
      else directPaths S c d r z hz
    apply global_zero_of_port_kernel S a (largePorts S c d) (directRoots S c) paths
      (firstCutOldKernel S) (firstCutOldKernel_closed S) r0 (firstCutOldKernel_gamma S)
    · exact firstCut_ports_later S c d
    · intro r hr z hz e he
      have hp := Classical.choose_spec (exists_direct_path_later S r0 r x0
        (oldLargestX S r) (oldLargestX_incident S r0) (oldLargestX_incident S r)
        z hz c d 52488 (by decide) (hmin r hr) hR.le hX.le hi)
      have he' : pathChain (Classical.choose (exists_direct_path_later S r0 r x0
          (oldLargestX S r) (oldLargestX_incident S r0) (oldLargestX_incident S r)
          z hz c d 52488 (by decide) (hmin r hr) hR.le hX.le hi)) e≠0 := by
        have hpath : paths r z hz=Classical.choose (exists_direct_path_later S r0 r x0
            (oldLargestX S r) (oldLargestX_incident S r0) (oldLargestX_incident S r)
            z hz c d 52488 (by decide) (hmin r hr) hR.le hX.le hi) := by
          exact dif_pos hr
        exact Eq.mp (congrArg (fun p => pathChain p e≠0) hpath) he
      exact hp e he'
  cases depth with
  | none =>
    exact direct none (by intro i hi; cases hi)
  | some i =>
    by_cases hi : i.val<52488^2
    · exact direct (some i) (by intro k hk; cases hk; exact hi)
    · have hr : Encodable.encode (r0 :
          (BDL26LevelTwoDecoder.executableLevelOne S).Q)< i.val := by omega
      have hx : Encodable.encode (x0 :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)< i.val := by omega
      have hh : 2≤S.half := by have := i.isLt; omega
      let paths : PortPaths S (largePorts S c (some i)) (actualRaisedRoots S hh c) :=
        fun r z hz => Classical.choose (exists_raised_path_later S r0 r x0
          (oldLargestX S r) (oldLargestX_incident S r0) (oldLargestX_incident S r)
          z hz c i hr hx)
      apply global_zero_of_port_kernel S a (largePorts S c (some i))
        (actualRaisedRoots S hh c) paths (firstCutOldKernel S)
        (firstCutOldKernel_closed S) r0 (firstCutOldKernel_gamma S)
      · exact firstCut_ports_later S c (some i)
      · intro r _ z hz e he
        exact Classical.choose_spec (exists_raised_path_later S r0 r x0
          (oldLargestX S r) (oldLargestX_incident S r0) (oldLargestX_incident S r)
          z hz c i hr hx) e he

private def gammaCone (S : OddScale) (j : Fin 2) : (RawOne S).Q :=
  .inr ⟨seedQ j,(0,.inl (.inl ()))⟩

private def seedQNode (S : OddScale) (j : Fin 2) : (RawOne S).X :=
  ⟨(0 : BaseX),(0,.inl (seedQVertex j))⟩

private theorem encoded_gammaCone (S : OddScale) (j : Fin 2) :
    Encodable.encode (gammaCone S j :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)=2*Nat.pair j.val 0+1 := by
  rfl

private theorem encoded_seedQNode (S : OddScale) (j : Fin 2) :
    Encodable.encode (seedQNode S j :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)=(2*(4*j.val+1))^4 := by
  change Encodable.encode (⟨(0 : BaseX),(0,Sum.inl (seedQVertex j))⟩ :
    (BDL26LevelTwoDecoder.executableLevelOne S).X)=_
  erw [encoded_old_X_copy0]
  rfl

private theorem encoded_seed_boundary_Q (S : OddScale) (j : Fin 2)
    (hm : subdivisionBoundaryVertexMember baseTannerSquarePresentation 0 S
      (Sum.inl (seedQVertex j))=true) :
    Encodable.encode (Sum.inl ⟨(0 : BaseX),Sum.inr
      ⟨Sum.inl (seedQVertex j),hm⟩⟩ :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q)=
      2*Nat.pair 0 (4*(4*j.val+1)+1) := by
  change 2*Nat.pair 0 (2*(2*(2*(2*j.val)+1))+1)=_
  apply congrArg (fun n => 2*Nat.pair 0 n)
  omega

private theorem seedQNode_incident (S : OddScale) (j : Fin 2) :
    (RawOne S).xq (seedQNode S j) (gammaCone S j)=true := by
  have h := raw_boundary1_view S (seedQNode S j) (gammaCone S j)
  change rxBoundary1Matrix baseTannerSquarePresentation S (seedQNode S j)
      (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩)=
    (if (RawOne S).xq (seedQNode S j) (gammaCone S j)=true then (1:F) else 0) at h
  erw [seed_cone_incidence,if_pos rfl] at h
  by_contra hn
  simp [hn] at h

private theorem seedQNode_first_radial_false (S : OddScale) (j : Fin 2)
    (hex : j.val≠0 ∨ 2≤S.half) :
    ¬(RawOne S).xq (seedQNode S j) (firstRadialQ S)=true := by
  intro hr
  rcases (old_local_incidence S _ 0
    (.inl (0,.inl (seedRadial 0,⟨0,S.half_pos⟩)))).mp hr with hs | ht
  · have hv := eq_of_heq (Sigma.mk.inj hs).2
    have hb := congrArg (fun v : DoubleCylinderVertex baseTannerSquarePresentation 0 S =>
      match v.2 with
      | .inl w => match w.val with | .q _ => true | _ => false
      | _ => false) hv
    change true=false at hb
    cases hb
  · have hv := eq_of_heq (Sigma.mk.inj ht).2
    change (0,.inl (seedQVertex j))=(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial 0)
        ⟨0,S.half_pos⟩) at hv
    by_cases hh : 1=S.half
    · have hj : j.val≠0 := by
        rcases hex with h | h
        · exact h
        · omega
      have he : seedQVertex j=seedQVertex 0 := by
        apply Sum.inl.inj
        have hv' := congrArg Prod.snd hv
        have hv'' : (Sum.inl (seedQVertex j) : SubdivisionVertex
            baseTannerSquarePresentation 0 S)=Sum.inl (seedQVertex 0) := by
          calc
            _ = _ := hv'
            _ = _ := by
              erw [segment_end_view]
              simp only [Fin.val_mk,dif_pos hh]
              exact congrArg Sum.inl (seedRadial_end 0)
        exact hv''
      have hval := congrArg (fun v : XStarVertex baseTannerSquarePresentation 0 =>
        match v.val with | .q q => q.val | _ => 0) he
      change j.val=0 at hval
      exact hj hval
    · have hv' := congrArg Prod.snd hv
      simp only [subdivisionSegmentEnd,Fin.val_mk,dif_neg hh] at hv'
      cases hv'

private theorem seedQNode_shifted_neighbour (S : OddScale) (j : Fin 2)
    (q : BaseQubit) (v : QDoubleCylinderVertex baseTannerSquarePresentation q S)
    (hr : (RawOne S).xq (seedQNode S j) (.inr ⟨q,v⟩)=true) :
    (Sum.inr ⟨q,v⟩ : (RawOne S).Q)=gammaCone S j := by
  have h := raw_boundary1_view S (seedQNode S j) (.inr ⟨q,v⟩)
  change rxBoundary1Matrix baseTannerSquarePresentation S (seedQNode S j)
      (.inr ⟨q,v⟩)=
    (if (RawOne S).xq (seedQNode S j) (.inr ⟨q,v⟩)=true then (1:F) else 0) at h
  rw [if_pos hr] at h
  rcases v with ⟨c,(cone | endpoint) | ⟨edge,i⟩⟩
  · cases cone
    fin_cases j <;> fin_cases q <;> fin_cases c
    all_goals
      simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
        seedQNode,seedQVertex,seedQ,gammaCone,xStarBoundaryEdgeToStar,
        qToXBoundaryEdge,TannerSquarePresentation.xq,baseTannerSquarePresentation,
        baseTannerSquareData,baseBoundary1Matrix,Fin.ext_iff] at h ⊢
    all_goals first | rfl | contradiction
  · rcases endpoint with ⟨z,hz⟩
    fin_cases j <;> fin_cases q <;> fin_cases z <;> fin_cases c
    all_goals
      simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
        seedQNode,seedQVertex,seedQ,gammaCone,xStarBoundaryEdgeToStar,
        qToXBoundaryEdge,TannerSquarePresentation.xq,baseTannerSquarePresentation,
        baseTannerSquareData,baseBoundary1Matrix,Fin.ext_iff] at h
    all_goals simp_all only [ite_self,dite_eq_ite,zero_ne_one]
  · rcases edge with ⟨z,hz⟩
    fin_cases j <;> fin_cases q <;> fin_cases z <;> fin_cases c
    all_goals
      simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
        seedQNode,seedQVertex,seedQ,gammaCone,xStarBoundaryEdgeToStar,
        qToXBoundaryEdge,TannerSquarePresentation.xq,baseTannerSquarePresentation,
        baseTannerSquareData,baseBoundary1Matrix,Fin.ext_iff] at h
    all_goals simp_all only [ite_self,dite_eq_ite,zero_ne_one]

private theorem seedQNode_local_code_large (S : OddScale) (j : Fin 2)
    (hex : j.val≠0 ∨ 2≤S.half) (x : BaseX)
    (e : DoubleCylinderEdge baseTannerSquarePresentation x S)
    (hr : (RawOne S).xq (seedQNode S j) (.inl ⟨x,e⟩)=true) :
    5<Encodable.encode (.inl ⟨x,e⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  rcases (old_local_incidence S _ x e).mp hr with hs | ht
  all_goals
    have hx : (0 : BaseX)=x := congrArg Sigma.fst (by first | exact hs | exact ht)
    cases hx
  all_goals
    rcases e with ⟨c,e⟩ | v
  · have hc : (0 : BDL26FiniteTannerSquare.Two)=c :=
      congrArg Prod.fst (eq_of_heq (Sigma.mk.inj hs).2)
    cases hc
    erw [encoded_old_local_Q]
    have hcode : subEdgeCode 0 S e≠0 := by
      intro hz
      have hz' : Encodable.encode (.inl ⟨(0 : BaseX),.inl (0,e)⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).Q)=0 := by
        erw [encoded_old_local_Q,hz]
        rfl
      have he0 : (Sum.inl ⟨(0 : BaseX),.inl (0,e)⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).Q)=firstRadialQ S :=
        Encodable.encode_injective hz'
      have he : (Sum.inl ⟨(0 : BaseX),.inl (0,e)⟩ : (RawOne S).Q)=firstRadialQ S := he0
      exact seedQNode_first_radial_false S j hex (he ▸ hr)
    simp only [Fin.val_zero]
    rw [pair_zero_left_sq,pair_zero_left_sq]
    have hp : 0<(subEdgeCode 0 S e)^2 := pow_pos (by omega) _
    nlinarith
  · have hv : (Sum.inl (seedQVertex j) : SubdivisionVertex baseTannerSquarePresentation 0 S)=
        v.val := congrArg Prod.snd (eq_of_heq (Sigma.mk.inj hs).2)
    have he : v=⟨.inl (seedQVertex j),hv.symm ▸ v.property⟩ := Subtype.ext hv.symm
    rw [he]
    erw [encoded_seed_boundary_Q]
    fin_cases j <;> decide
  · have hc : (0 : BDL26FiniteTannerSquare.Two)=c :=
      congrArg Prod.fst (eq_of_heq (Sigma.mk.inj ht).2)
    cases hc
    erw [encoded_old_local_Q]
    have hcode : subEdgeCode 0 S e≠0 := by
      intro hz
      have hz' : Encodable.encode (.inl ⟨(0 : BaseX),.inl (0,e)⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).Q)=0 := by
        erw [encoded_old_local_Q,hz]
        rfl
      have he0 : (Sum.inl ⟨(0 : BaseX),.inl (0,e)⟩ :
          (BDL26LevelTwoDecoder.executableLevelOne S).Q)=firstRadialQ S :=
        Encodable.encode_injective hz'
      have he : (Sum.inl ⟨(0 : BaseX),.inl (0,e)⟩ : (RawOne S).Q)=firstRadialQ S := he0
      exact seedQNode_first_radial_false S j hex (he ▸ hr)
    simp only [Fin.val_zero]
    rw [pair_zero_left_sq,pair_zero_left_sq]
    have hp : 0<(subEdgeCode 0 S e)^2 := pow_pos (by omega) _
    nlinarith
  · have hc := congrArg Prod.fst (eq_of_heq (Sigma.mk.inj ht).2)
    change (0 : BDL26FiniteTannerSquare.Two)=1 at hc
    norm_num at hc

private theorem seedQNode_minimum (S : OddScale) (j : Fin 2)
    (hex : j.val≠0 ∨ 2≤S.half) (r : (RawOne S).Q)
    (hr : (RawOne S).xq (seedQNode S j) r=true) (hne : r≠gammaCone S j) :
    Encodable.encode (gammaCone S j : (BDL26LevelTwoDecoder.executableLevelOne S).Q)<
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  have hc : Encodable.encode (gammaCone S j :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)≤5 := by
    erw [encoded_gammaCone]
    fin_cases j <;> decide
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · exact hc.trans_lt (seedQNode_local_code_large S j hex x e hr)
  · exact False.elim (hne (seedQNode_shifted_neighbour S j q v hr))

private theorem global_radial_large_port_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (n : Fin S.half)
    (c : BDL26FiniteTannerSquare.Two) (depth : Option (Fin (S.half-1))) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j n,largePorts S c depth (gammaRadial S j n)⟩)=0 := by
  by_cases hn : j.val+n.val=0
  · have hj : j=0 := Fin.ext (by omega)
    have hz : n=⟨0,S.half_pos⟩ := Fin.ext (by change n.val=0; omega)
    subst j
    subst n
    cases depth with
    | none =>
      exact global_first_radial_endpoint_zero S a _ (oldLargestX_incident S _) c
    | some i =>
      by_cases hi : i.val+2<S.half
      · exact global_interior_zero_before_last S a _ _ (oldLargestX_incident S _) c i hi
      · have hh : 2≤S.half := by have := i.isLt; omega
        have hl : i=lastInterior S hh := by
          apply Fin.ext
          have := i.isLt
          dsimp [lastInterior]
          omega
        subst i
        exact global_first_radial_last_interior_zero S hh a _
          (oldLargestX_incident S _) c
  · have hnpos : 0<j.val+n.val := by omega
    by_cases hlast : n.val+1=S.half
    · have he : n=lastSegment S := by apply Fin.ext; dsimp [lastSegment]; omega
      subst n
      exact global_terminal_large_port_zero S a j c depth hnpos
    · let i : Fin (S.half-1) := ⟨n.val,by have := n.isLt; omega⟩
      have he : n=radialPrevious S i := Fin.ext rfl
      by_cases hex : j.val=1 ∧ n.val=0
      · have hj : j=1 := Fin.ext hex.1
        have hz : n=⟨0,S.half_pos⟩ := Fin.ext hex.2
        subst j
        subst n
        exact global_firstCut_large_port_zero S a c depth
      · rw [he]
        exact global_nonterminal_large_port_zero S a j i (by
          dsimp [i]
          omega) c depth

private theorem global_radial_endpoint_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (n : Fin S.half)
    (x : (RawOne S).X) (hx : (RawOne S).xq x (gammaRadial S j n)=true)
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j n,(c,.inl (.inr ⟨x,hx⟩))⟩)=0 := by
  by_cases hz : j.val+n.val=0
  · have hj : j=0 := Fin.ext (by omega)
    have hn : n=⟨0,S.half_pos⟩ := Fin.ext (by change n.val=0; omega)
    subst j
    subst n
    exact global_first_radial_endpoint_zero S a x hx c
  · by_cases he : x=oldLargestX S (gammaRadial S j n)
    · subst x
      exact global_radial_large_port_zero S a j n c none
    · exact global_radial_minor_endpoint_zero S a j n (by omega) x hx he c

private theorem global_radial_interior_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (n : Fin S.half)
    (x : (RawOne S).X) (hx : (RawOne S).xq x (gammaRadial S j n)=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j n,(c,.inr (⟨x,hx⟩,i))⟩)=0 := by
  by_cases hz : j.val+n.val=0
  · have hj : j=0 := Fin.ext (by omega)
    have hn : n=⟨0,S.half_pos⟩ := Fin.ext (by change n.val=0; omega)
    subst j
    subst n
    by_cases hi : i.val+2<S.half
    · exact global_interior_zero_before_last S a _ x hx c i hi
    · have hh : 2≤S.half := by have := i.isLt; omega
      have hl : i=lastInterior S hh := by
        apply Fin.ext
        have := i.isLt
        dsimp [lastInterior]
        omega
      subst i
      exact global_first_radial_last_interior_zero S hh a x hx c
  · by_cases he : x=oldLargestX S (gammaRadial S j n)
    · subst x
      exact global_radial_large_port_zero S a j n c (some i)
    · exact global_radial_minor_interior_zero S a j n (by omega) x hx he c i

private theorem global_radial_vertex_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (n : Fin S.half)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) (gammaRadial S j n) S) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaRadial S j n,v⟩)=0 := by
  rcases v with ⟨c,(cone | ⟨x,hx⟩) | ⟨⟨x,hx⟩,i⟩⟩
  · cases cone
    exact global_cone_zero S a _ _ (oldLargestX_incident S _) c
  · exact global_radial_endpoint_zero S a j n x hx c
  · exact global_radial_interior_zero S a j n x hx c i

private theorem seedQNode_only (S : OddScale) (j : Fin 2) (x : (RawOne S).X)
    (hx : (RawOne S).xq x (gammaCone S j)=true) : x=seedQNode S j := by
  have h := raw_boundary1_view S x (gammaCone S j)
  change rxBoundary1Matrix baseTannerSquarePresentation S x
      (.inr ⟨seedQ j,(0,.inl (.inl ()))⟩)=
    (if (RawOne S).xq x (gammaCone S j)=true then (1:F) else 0) at h
  erw [if_pos hx,seed_cone_incidence] at h
  by_contra hn
  have he : x≠⟨(0 : BaseX),(0,Sum.inl (seedQVertex j))⟩ := hn
  erw [if_neg he] at h
  exact zero_ne_one h

private theorem global_old_cone_endpoint_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2) (hex : j.val≠0 ∨ 2≤S.half)
    (x : (RawOne S).X) (hx : (RawOne S).xq x (gammaCone S j)=true)
    (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaCone S j,(c,.inl (.inr ⟨x,hx⟩))⟩)=0 := by
  have he := seedQNode_only S j x hx
  subst x
  exact global_endpoint_of_least_old_neighbor S a _ _ (seedQNode_incident S j) c
    (seedQNode_minimum S j hex)

private theorem global_old_cone_interior_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2)
    (x : (RawOne S).X) (hx : (RawOne S).xq x (gammaCone S j)=true)
    (c : BDL26FiniteTannerSquare.Two) (i : Fin (S.half-1)) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaCone S j,(c,.inr (⟨x,hx⟩,i))⟩)=0 := by
  have he := seedQNode_only S j x hx
  subst x
  by_cases hi : i.val+2<S.half
  · exact global_interior_zero_before_last S a _ _ (seedQNode_incident S j) c i hi
  · have hh : 2≤S.half := by have := i.isLt; omega
    have hl : i=lastInterior S hh := by
      apply Fin.ext
      have := i.isLt
      dsimp [lastInterior]
      omega
    subst i
    exact global_last_interior_of_least_old_neighbor S hh a _ _ (seedQNode_incident S j) c
      (seedQNode_minimum S j (Or.inr hh))

private def tinyQZ (S : OddScale) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inl
    (xStarFaceQZEdge baseTannerSquarePresentation 0 (seedFace 0) 0,⟨0,S.half_pos⟩))⟩

private def tinyRadial4 (S : OddScale) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inl (0,.inl
    (xStarFaceXQEdge baseTannerSquarePresentation 0 (seedFace 0) 1,⟨0,S.half_pos⟩))⟩

private def tinyBoundaryNode (S : OddScale) :
    SubdivisionBoundaryVertex baseTannerSquarePresentation (0 : BaseX) S :=
  ⟨.inl (seedQVertex 0),by
    change xStarBoundaryVertexMember baseTannerSquarePresentation 0
      (seedQVertex 0).val=true
    decide⟩

private def tinyVertical (S : OddScale) : (RawOne S).Q :=
  .inl ⟨(0 : BaseX),.inr (tinyBoundaryNode S)⟩

private theorem encoded_tinyQZ (S : OddScale) :
    Encodable.encode (tinyQZ S :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)=2048 := by
  erw [tinyQZ,encoded_old_local_Q]
  change 2*Nat.pair 0 (2*Nat.pair 0 (2*Nat.pair 1 0))=2048
  decide

private theorem encoded_tinyRadial4 (S : OddScale) :
    Encodable.encode (tinyRadial4 S :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)=159171622207488 := by
  erw [tinyRadial4,encoded_old_local_Q]
  change 2*Nat.pair 0 (2*Nat.pair 0 (2*Nat.pair 32 0))=159171622207488
  decide

private theorem encoded_tinyVertical (S : OddScale) :
    Encodable.encode (tinyVertical S :
      (BDL26LevelTwoDecoder.executableLevelOne S).Q)=50 := by
  erw [encoded_seed_boundary_Q S 0]
  decide

private theorem tiny_other_ne_QZ (S : OddScale) :
    gammaRadial S 1 ⟨0,S.half_pos⟩≠tinyQZ S ∧
      tinyRadial4 S≠tinyQZ S ∧ tinyVertical S≠tinyQZ S := by
  have hz := encoded_tinyQZ S
  have hr := encoded_tinyRadial4 S
  have hv := encoded_tinyVertical S
  have hg := encoded_gammaRadial S 1 ⟨0,S.half_pos⟩
  norm_num [Fin.val_mk,Nat.pair] at hg
  refine ⟨?_,?_,?_⟩
  all_goals
    intro he
    have hc := congrArg (fun r : (RawOne S).Q =>
      Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q)) he
    omega

private theorem tinyRadial4_end_vertex (S : OddScale) (hh : S.half=1) :
    oldLocalEnd S 0 (.inl (0,.inl
      (xStarFaceXQEdge baseTannerSquarePresentation 0 (seedFace 0) 1,
        ⟨0,S.half_pos⟩)))=⟨(0 : BaseX),(0,Sum.inl
          (xStarFaceQVertex baseTannerSquarePresentation 0 (seedFace 0) 1))⟩ := by
  have he : (0 : Nat)+1=S.half := by omega
  simp only [oldLocalEnd,tannerDoubleCylinderEdgeEnd,subdivisionEdgeEnd,
    subdivisionSegmentEnd,Fin.val_mk,dif_pos he]
  exact congrArg (fun v : XStarVertex baseTannerSquarePresentation (0 : BaseX) =>
    (⟨(0 : BaseX),(0,Sum.inl v)⟩ : (RawOne S).X))
    (xStarEdgeEnd_faceXQEdge baseTannerSquarePresentation (0 : BaseX) (seedFace 0) 1)

private theorem tiny_center_shifted_zero (S : OddScale) (q : BaseQubit)
    (v : QDoubleCylinderVertex baseTannerSquarePresentation q S) :
    ¬(RawOne S).xq ⟨(0 : BaseX),(0,.inl seedCenter)⟩ (.inr ⟨q,v⟩)=true := by
  have h := raw_boundary1_view S ⟨(0 : BaseX),(0,.inl seedCenter)⟩ (.inr ⟨q,v⟩)
  have hz : rxBoundary1Matrix baseTannerSquarePresentation S
      ⟨(0 : BaseX),(0,.inl seedCenter)⟩ (.inr ⟨q,v⟩)=0 := by
    rcases v with ⟨c,(cone | endpoint) | ⟨edge,i⟩⟩
    all_goals
      fin_cases c <;>
        simp [rxBoundary1Matrix,qDoubleCylinderVertexXIncidence,
          qSubdivisionVertexXIncidence,seedCenter,xStarBoundaryEdgeToStar,
          qToXBoundaryEdge]
  intro hi
  erw [hz,if_pos hi] at h
  exact zero_ne_one h

private theorem halfOneTinyKernel_shifted_support (S : OddScale)
    (q : BaseQubit) (v : QDoubleCylinderVertex baseTannerSquarePresentation q S)
    (hr : halfOneTinyKernel S (.inr ⟨q,v⟩)≠0) :
    (Sum.inr ⟨q,v⟩ : (RawOne S).Q)=gammaCone S 0 := by
  have hx := gradient_two_basis_second (RawOne S)
    (⟨(0 : BaseX),(0,.inl seedCenter)⟩ : (RawOne S).X)
    (seedQNode S 0) (.inr ⟨q,v⟩) (tiny_center_shifted_zero S q v) hr
  exact seedQNode_shifted_neighbour S 0 q v hx

private theorem base_xq_view (x : BaseX) (q : BaseQubit) :
    baseTannerSquarePresentation.xq x q=
      decide (if x=0 then q=0 ∨ q=1 ∨ q=4 else q=2 ∨ q=3 ∨ q=4) := by
  fin_cases x <;> fin_cases q <;> decide

private theorem base_qz_view (q : BaseQubit) (z : BaseZ) :
    baseTannerSquarePresentation.qz q z=
      decide (if z=0 then q=0 ∨ q=2 ∨ q=4 else q=1 ∨ q=3 ∨ q=4) := by
  fin_cases q <;> fin_cases z <;> decide

private theorem star_xq_owner (P : TannerSquarePresentation) (x : P.X)
    (e : XQEdge P) (he : xStarEdgeMember P x (.inl e)=true) : e.val.1=x := by
  rw [star_edge_xq_view] at he
  obtain ⟨f,hf,huse⟩ := of_decide_eq_true he
  have hx : P.faceX f=x := of_decide_eq_true hf
  rcases huse with huse | huse
  · exact (congrArg (fun a : XQEdge P => a.val.1) huse).trans hx
  · exact (congrArg (fun a : XQEdge P => a.val.1) huse).trans hx

private theorem halfOneTinyKernel_segment_value (S : OddScale) (hh : S.half=1)
    (x : BaseX) (c : BDL26FiniteTannerSquare.Two)
    (a : XStarEdge baseTannerSquarePresentation x) (k : Fin S.half) :
    halfOneTinyKernel S (.inl ⟨x,.inl (c,.inl (a,k))⟩)=
      if x.val=0 ∧ c.val=0 then
        match a.val with
        | .inl e => (if e.val.1.val=0 then (1:F) else 0)+
            (if e.val.2.val=0 then 1 else 0)
        | .inr e => if e.val.1.val=0 then 1 else 0
      else 0 := by
  have hk : k.val=0 := by have := k.isLt; omega
  have hlast : k.val+1=S.half := by omega
  erw [halfOneTinyKernel,rx_local_gradient]
  simp only [tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd,
    subdivisionEdgeStart,subdivisionEdgeEnd,subdivisionSegmentStart,
    subdivisionSegmentEnd,dif_pos hk,dif_pos hlast]
  erw [halfOneTinyPotential_local_value,halfOneTinyPotential_local_value]
  rcases a with ⟨a,ha⟩
  rcases a with ⟨⟨x',q⟩,hxq⟩ | ⟨⟨q,z⟩,hqz⟩
  · dsimp only [xStarEdgeStart,xStarEdgeEnd]
    split_ifs <;> simp only [zero_add,add_zero]
  · dsimp only [xStarEdgeStart,xStarEdgeEnd]
    split_ifs <;> simp only [zero_add,add_zero]

private theorem halfOneTinyKernel_support (S : OddScale) (hh : S.half=1)
    (r : (RawOne S).Q) (hr : halfOneTinyKernel S r≠0) :
    r=gammaCone S 0 ∨ r=gammaRadial S 1 ⟨0,S.half_pos⟩ ∨
      r=tinyRadial4 S ∨ r=tinyQZ S ∨ r=tinyVertical S := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · change BaseX at x
    rcases e with ⟨c,e⟩ | ⟨v,hv⟩
    · rcases e with ⟨a,k⟩ | ⟨f,i,k⟩ | ⟨f,k,i⟩
      · have hk : k=⟨0,S.half_pos⟩ := Fin.ext (by have := k.isLt; omega)
        subst k
        erw [halfOneTinyKernel_segment_value S hh] at hr
        have hxc : x.val=0 ∧ c.val=0 := by
          by_contra hn
          exact hr (by simp only [if_neg hn])
        have hx : x=(0 : BaseX) := Fin.ext hxc.1
        have hc : c=(0 : BDL26FiniteTannerSquare.Two) := Fin.ext hxc.2
        subst x
        subst c
        rcases a with ⟨a,ha⟩
        rcases a with ⟨⟨x',q⟩,hxq⟩ | ⟨⟨q,z⟩,hqz⟩
        · change BaseX at x'
          change BaseQubit at q
          have howner : x'=(0 : BaseX) := star_xq_owner _ _ _ ha
          subst x'
          have hq0 : q≠(0 : BaseQubit) := by
            intro he
            subst q
            exact hr (by simp [ZModModule.add_self])
          have hq := of_decide_eq_true ((base_xq_view (0 : BaseX) q).symm.trans hxq)
          simp only [if_pos rfl] at hq
          rcases hq with he | he | he
          · exact False.elim (hq0 he)
          · subst q
            exact Or.inr (Or.inl rfl)
          · subst q
            exact Or.inr (Or.inr (Or.inl rfl))
        · change BaseQubit at q
          change BaseZ at z
          change (if q.val=0 then (1:F) else 0)≠0 at hr
          have hqval : q.val=0 := by
            by_contra hn
            exact hr (if_neg hn)
          have hq : q=(0 : BaseQubit) := Fin.ext hqval
          subst q
          have hz := of_decide_eq_true ((base_qz_view (0 : BaseQubit) z).symm.trans hqz)
          have hz0 : z=(0 : BaseZ) := by
            by_contra hn
            simp [hn,Fin.ext_iff] at hz
          subst z
          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · have := k.isLt
        omega
      · have := k.isLt
        omega
    · erw [halfOneTinyKernel,rx_local_gradient] at hr
      simp only [tannerDoubleCylinderEdgeStart,tannerDoubleCylinderEdgeEnd] at hr
      erw [halfOneTinyPotential_local_value,halfOneTinyPotential_local_value] at hr
      rcases v with ⟨v,hv'⟩ | ⟨a,i⟩ | ⟨f,i,k⟩
      · rcases v with x' | q | z
        · change false=true at hv
          cases hv
        · change BaseQubit at q
          have hxval : x.val=0 := by
            by_contra hn
            have h0 : ¬(x.val=0 ∧ (0 : BDL26FiniteTannerSquare.Two).val=0) :=
              fun h => hn h.1
            have h1 : ¬(x.val=0 ∧ (1 : BDL26FiniteTannerSquare.Two).val=0) :=
              fun h => hn h.1
            exact hr (by simp only [if_neg h0,if_neg h1,zero_add])
          have hqval : q.val=0 := by
            by_contra hn
            exact hr (by simp only [if_neg hn,ite_self,zero_add])
          have hx : x=(0 : BaseX) := Fin.ext hxval
          have hq : q=(0 : BaseQubit) := Fin.ext hqval
          subst x
          subst q
          exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        · simp at hr
      · have := i.isLt
        omega
      · have := i.isLt
        omega
  · exact Or.inl (halfOneTinyKernel_shifted_support S q v hr)

private theorem tinyQZ_node_incident (S : OddScale) :
    (RawOne S).xq (seedQNode S 0) (tinyQZ S)=true := by
  apply (old_local_incidence S _ 0 _).2
  left
  rfl

private def tinyPortX (S : OddScale) (r : (RawOne S).Q) : (RawOne S).X :=
  if r=tinyQZ S then seedQNode S 0 else oldLargestX S r

private theorem tinyPortX_incident (S : OddScale) (r : (RawOne S).Q) :
    (RawOne S).xq (tinyPortX S r) r=true := by
  unfold tinyPortX
  split_ifs with h
  · subst r
    exact tinyQZ_node_incident S
  · exact oldLargestX_incident S r

private theorem tinyPortX_target (S : OddScale) :
    tinyPortX S (gammaCone S 0)=seedQNode S 0 := by
  rw [tinyPortX,if_neg (by intro h; cases h)]
  exact seedQNode_only S 0 _ (oldLargestX_incident S _)

private def tinyPorts (S : OddScale) (c : BDL26FiniteTannerSquare.Two) : PortVertices S :=
  fun r => chosenPort (RawOne S) S r (tinyPortX S r) (tinyPortX_incident S r) c none

private theorem tinyPorts_target (S : OddScale) (c : BDL26FiniteTannerSquare.Two) :
    tinyPorts S c (gammaCone S 0)=
      (c,Sum.inl (Sum.inr ⟨seedQNode S 0,seedQNode_incident S 0⟩)) := by
  unfold tinyPorts chosenPort
  simp only [tinyPortX_target]

private theorem tiny_special_support (S : OddScale) (r : (RawOne S).Q)
    (hr : halfOneTinyKernel S r≠0) (hz : (RawOne S).qz r (seedConeCheck S 0)=true) :
    r=gammaCone S 0 ∨ r=tinyQZ S := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · right
    have h : rxBoundary2Matrix baseTannerSquarePresentation S
        (.inl ⟨x,e⟩) (seedConeCheck S 0)=1 :=
      (raw_boundary2_view S (.inl ⟨x,e⟩) (seedConeCheck S 0)).trans (if_pos hz)
    fin_cases x
    · have he : e=qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation (seedQ 0) 0
          (by decide) S (.inl (0,(seedZEdge 0,⟨0,S.half_pos⟩))) := by
        by_contra hn
        simp [rxBoundary2Matrix,seedConeCheck,qDoubleCylinderEdgeXIncidence,hn] at h
        split_ifs at h <;> simp_all
        all_goals exact hn (by congr)
      rw [he]
      rfl
    · simp [rxBoundary2Matrix,seedConeCheck,qDoubleCylinderEdgeXIncidence,
        base_faceX_value,base_faceZ_value,base_faceQ_value,
        base_xq_matrix_value,base_qz_matrix_value,baseBoundary1Matrix,seedQ] at h
  · exact Or.inl (halfOneTinyKernel_shifted_support S q v hr)

private theorem qToZ_endpoint_independent (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (r r' : P.Q) (x : P.X) (z : P.Z)
    (hx : P.xq x r=true) (hx' : P.xq x r'=true)
    (hz : P.qz r z=true) (hz' : P.qz r' z=true)
    (c : BDL26FiniteTannerSquare.Two) :
    qToZDoubleCylinderVertex P A r z hz S (c,.inl (.inr ⟨x,hx⟩))=
      qToZDoubleCylinderVertex P A r' z hz' S (c,.inl (.inr ⟨x,hx'⟩)) := by
  apply Prod.ext rfl
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl

private def tinyRoot (S : OddScale) (c : BDL26FiniteTannerSquare.Two) :
    ZDoubleCylinderVertex (RawOne S) (seedConeCheck S 0) S :=
  qToZDoubleCylinderVertex (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible
    (gammaCone S 0) (seedConeCheck S 0) (seedCone_degree_one S 0).1 S
    (c,.inl (.inr ⟨seedQNode S 0,seedQNode_incident S 0⟩))

private def tinyRoots (S : OddScale) (c : BDL26FiniteTannerSquare.Two) : PortRoots S :=
  fun z => if h : z=seedConeCheck S 0 then h.symm ▸ tinyRoot S c
    else zCenter (RawOne S) S z c

private theorem tinyRoots_at_seed (S : OddScale) (c : BDL26FiniteTannerSquare.Two) :
    tinyRoots S c (seedConeCheck S 0)=tinyRoot S c := by
  unfold tinyRoots
  split_ifs with h
  · rfl
  · exact False.elim (h rfl)

private theorem tinyRoots_at_other (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (z : (RawOne S).Z) (h : z≠seedConeCheck S 0) :
    tinyRoots S c z=zCenter (RawOne S) S z c := by
  unfold tinyRoots
  exact dif_neg h

private theorem tiny_special_endpoint (S : OddScale) (c : BDL26FiniteTannerSquare.Two)
    (r : (RawOne S).Q) (hr : halfOneTinyKernel S r≠0)
    (hz : (RawOne S).qz r (seedConeCheck S 0)=true) :
    qToZDoubleCylinderVertex (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible r (seedConeCheck S 0)
      hz S (tinyPorts S c r)=tinyRoot S c := by
  have hx : tinyPortX S r=seedQNode S 0 := by
    rcases tiny_special_support S r hr hz with h | h
    · subst r
      exact tinyPortX_target S
    · subst r
      simp [tinyPortX]
  change qToZDoubleCylinderVertex (RawOne S) _ r _ hz S
    (c,.inl (.inr ⟨tinyPortX S r,_⟩))=_
  simp only [hx]
  exact qToZ_endpoint_independent (RawOne S) _ S r (gammaCone S 0)
    (seedQNode S 0) (seedConeCheck S 0) _ _ hz (seedCone_degree_one S 0).1 c

private theorem tiny_other_code_lower (S : OddScale) (hh : S.half=1)
    (r : (RawOne S).Q) (hr : halfOneTinyKernel S r≠0) (hne : r≠gammaCone S 0) :
    50≤Encodable.encode (r : (BDL26LevelTwoDecoder.executableLevelOne S).Q) := by
  rcases halfOneTinyKernel_support S hh r hr with h | h | h | h | h
  · exact False.elim (hne h)
  · subst r
    erw [encoded_gammaRadial]
    norm_num [Fin.val_mk,Nat.pair]
  · subst r
    rw [encoded_tinyRadial4]
    decide
  · subst r
    rw [encoded_tinyQZ]
    decide
  · subst r
    rw [encoded_tinyVertical]

private theorem tiny_other_X_lower (S : OddScale) (hh : S.half=1)
    (r : (RawOne S).Q) (hr : halfOneTinyKernel S r≠0) (hne : r≠gammaCone S 0) :
    16≤Encodable.encode (tinyPortX S r :
      (BDL26LevelTwoDecoder.executableLevelOne S).X) := by
  rcases halfOneTinyKernel_support S hh r hr with h | h | h | h | h
  · exact False.elim (hne h)
  · subst r
    rw [tinyPortX,if_neg (tiny_other_ne_QZ S).1]
    apply le_trans _ (oldLargestX_end_le S 0 _)
    change 16≤Encodable.encode (⟨(0 : BaseX),(0,
      subdivisionSegmentEnd baseTannerSquarePresentation 0 S (seedRadial 1)
        ⟨0,S.half_pos⟩)⟩ : (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X_copy0]
    have he : (0 : Nat)+1=S.half := by omega
    simp only [subdivisionSegmentEnd,Fin.val_mk,dif_pos he,subVertexCode,
      seedRadial_end_code,Fin.val_one]
    decide
  · subst r
    rw [tinyPortX,if_neg (tiny_other_ne_QZ S).2.1]
    apply le_trans _ (oldLargestX_end_le S 0 _)
    erw [tinyRadial4_end_vertex S hh,encoded_old_X_copy0]
    change 16≤(2*17)^4
    decide
  · subst r
    rw [tinyPortX,if_pos rfl]
    rw [encoded_seedQNode]
    decide
  · subst r
    rw [tinyPortX,if_neg (tiny_other_ne_QZ S).2.2]
    apply le_trans _ (oldLargestX_end_le S 0 _)
    change 16≤Encodable.encode (⟨(0 : BaseX),(1,Sum.inl (seedQVertex 0))⟩ :
      (BDL26LevelTwoDecoder.executableLevelOne S).X)
    erw [encoded_old_X]
    change 16≤Nat.pair 0 (Nat.pair 1 2)
    decide

private theorem tiny_endpoint_code_order (R X : Nat)
    (c : BDL26FiniteTannerSquare.Two) (hR : 50≤R) (hX : 16≤X) :
    2*Nat.pair 1 (Nat.pair c.val (2*(2*16+1)))+1<
      2*Nat.pair R (Nat.pair c.val (2*(2*X+1)))+1 := by
  have htail : 2*(2*(16 : Nat)+1)≤2*(2*X+1) := by omega
  have hp := pair_mono_right c.val _ _ htail
  have hleft := Nat.pair_lt_pair_left (Nat.pair c.val (2*(2*(16 : Nat)+1)))
    (show 1<R by omega)
  have hright := pair_mono_right R _ _ hp
  omega

private theorem tiny_ports_later (S : OddScale) (hh : S.half=1)
    (c : BDL26FiniteTannerSquare.Two) (r : (RawOne S).Q)
    (hr : halfOneTinyKernel S r≠0) (hne : r≠gammaCone S 0) :
    Encodable.encode (executableCoordinate S (.inr ⟨gammaCone S 0,tinyPorts S c (gammaCone S 0)⟩))<
      Encodable.encode (executableCoordinate S (.inr ⟨r,tinyPorts S c r⟩)) := by
  change Encodable.encode (executableCoordinate S
    (.inr ⟨gammaCone S 0,(c,.inl (.inr ⟨tinyPortX S (gammaCone S 0),_⟩))⟩))<_
  have hleft := encoded_endpoint S (gammaCone S 0)
    (tinyPortX S (gammaCone S 0)) (tinyPortX_incident S (gammaCone S 0)) c
  have hright := encoded_endpoint S r (tinyPortX S r) (tinyPortX_incident S r) c
  have hn :
      2*Nat.pair (Encodable.encode (gammaCone S 0 :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val (2*(2*Encodable.encode (tinyPortX S (gammaCone S 0) :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1 <
      2*Nat.pair (Encodable.encode (r :
        (BDL26LevelTwoDecoder.executableLevelOne S).Q))
        (Nat.pair c.val (2*(2*Encodable.encode (tinyPortX S r :
          (BDL26LevelTwoDecoder.executableLevelOne S).X)+1)))+1 := by
    rw [tinyPortX_target,encoded_gammaCone,encoded_seedQNode]
    exact tiny_endpoint_code_order _ _ c
      (tiny_other_code_lower S hh r hr hne) (tiny_other_X_lower S hh r hr hne)
  exact hleft.trans_lt (hn.trans_eq hright.symm)

private theorem exists_tiny_seed_port_path (S : OddScale) (hh : S.half=1)
    (c : BDL26FiniteTannerSquare.Two) (r : (RawOne S).Q) (hz : (RawOne S).qz r (seedConeCheck S 0)=true) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) (seedConeCheck S 0) S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) (seedConeCheck S 0) S)
      (tinyRoot S c)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r (seedConeCheck S 0) hz S
        (tinyPorts S c r)),
      halfOneTinyKernel S r≠0 → ∀ e, pathChain p e≠0 →
        Encodable.encode (executableCoordinate S
          (.inr ⟨gammaCone S 0,tinyPorts S c (gammaCone S 0)⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨seedConeCheck S 0,e⟩)) := by
  by_cases hr : halfOneTinyKernel S r≠0
  · rw [tiny_special_endpoint S c r hr hz]
    refine ⟨.nil,?_⟩
    intro _ e he
    exact False.elim (he (by simp [pathChain]))
  · obtain ⟨p⟩ := between_direct_ports (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S (gammaCone S 0) r
      (seedQNode S 0) (tinyPortX S r) (seedConeCheck S 0)
      (seedQNode_incident S 0) (tinyPortX_incident S r)
      (seedCone_degree_one S 0).1 hz c none
    exact ⟨p,fun h => False.elim (hr h)⟩

private theorem exists_tiny_other_port_path (S : OddScale) (hh : S.half=1)
    (c : BDL26FiniteTannerSquare.Two) (r : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true) :
    z≠seedConeCheck S 0 →
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (zCenter (RawOne S) S z c)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (tinyPorts S c r)),
      halfOneTinyKernel S r≠0 → ∀ e, pathChain p e≠0 →
        Encodable.encode (executableCoordinate S
          (.inr ⟨gammaCone S 0,tinyPorts S c (gammaCone S 0)⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)) := by
  intro hzz
  by_cases hr : halfOneTinyKernel S r≠0
  · have hne : r≠gammaCone S 0 := by
      intro he
      subst r
      exact hzz ((seedCone_degree_one S 0).2 z hz)
    obtain ⟨p,hp⟩ := exists_direct_path_later S (gammaCone S 0) r
      (seedQNode S 0) (tinyPortX S r) (seedQNode_incident S 0)
      (tinyPortX_incident S r) z hz c none 50 (by decide)
      (tiny_other_code_lower S hh r hr hne)
      (by erw [encoded_gammaCone]; decide)
      (by erw [encoded_seedQNode]; decide)
      (by intro i hi; cases hi)
    refine ⟨p,?_⟩
    intro _ e he
    have hport : (Sum.inr ⟨gammaCone S 0,chosenPort (RawOne S) S
        (gammaCone S 0) (seedQNode S 0) (seedQNode_incident S 0) c none⟩ :
          (RawTwo S).Q)=Sum.inr ⟨gammaCone S 0,tinyPorts S c (gammaCone S 0)⟩ := by
      exact congrArg (fun v => (Sum.inr ⟨gammaCone S 0,v⟩ : (RawTwo S).Q))
        (tinyPorts_target S c).symm
    have hcode := congrArg (fun q : (RawTwo S).Q =>
      Encodable.encode (executableCoordinate S q)) hport
    exact hcode.symm.trans_lt (hp e he)
  · obtain ⟨p,_⟩ := exists_direct_port_path (RawOne S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S r
      (tinyPortX S r) z (tinyPortX_incident S r) hz c none
    exact ⟨p,fun h => False.elim (hr h)⟩


private theorem exists_tiny_port_path (S : OddScale) (hh : S.half=1)
    (c : BDL26FiniteTannerSquare.Two) (r : (RawOne S).Q) (z : (RawOne S).Z)
    (hz : (RawOne S).qz r z=true) :
    ∃ p : UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation (RawOne S)) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation (RawOne S)) z S)
      (tinyRoots S c z)
      (qToZDoubleCylinderVertex (RawOne S)
        (rxState S baseState).admissible.toTannerSquareAdmissible r z hz S
        (tinyPorts S c r)),
      halfOneTinyKernel S r≠0 → ∀ e, pathChain p e≠0 →
        Encodable.encode (executableCoordinate S
          (.inr ⟨gammaCone S 0,tinyPorts S c (gammaCone S 0)⟩))<
          Encodable.encode (executableCoordinate S (.inl ⟨z,e⟩)) := by
  by_cases hz0 : z=seedConeCheck S 0
  · subst z
    rw [tinyRoots_at_seed]
    exact exists_tiny_seed_port_path S hh c r hz
  · rw [tinyRoots_at_other S c z hz0]
    exact exists_tiny_other_port_path S hh c r z hz hz0

private theorem global_halfOne_q0_endpoint_zero (S : OddScale) (hh : S.half=1)
    (a : Word F (RawTwo S).Q) (c : BDL26FiniteTannerSquare.Two) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaCone S 0,(c,.inl (.inr ⟨seedQNode S 0,seedQNode_incident S 0⟩))⟩)=0 := by
  let paths : PortPaths S (tinyPorts S c) (tinyRoots S c) := fun r z hz =>
    Classical.choose (exists_tiny_port_path S hh c r z hz)
  have h := global_zero_of_port_kernel S a (tinyPorts S c) (tinyRoots S c) paths
    (halfOneTinyKernel S) (halfOneTinyKernel_closed S) (gammaCone S 0)
    (halfOneTinyKernel_target S) (tiny_ports_later S hh c) (by
      intro r hr z hz e he
      exact Classical.choose_spec (exists_tiny_port_path S hh c r z hz) hr e he)
  have hend : (Sum.inr ⟨gammaCone S 0,tinyPorts S c (gammaCone S 0)⟩ :
      (RawTwo S).Q)=Sum.inr ⟨gammaCone S 0,
        (c,Sum.inl (Sum.inr ⟨seedQNode S 0,seedQNode_incident S 0⟩))⟩ := by
    exact congrArg (fun v => (Sum.inr ⟨gammaCone S 0,v⟩ : (RawTwo S).Q))
      (tinyPorts_target S c)
  exact Eq.mp (congrArg (fun q : (RawTwo S).Q =>
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a) q=0) hend) h

private theorem global_old_cone_vertex_zero (S : OddScale)
    (a : Word F (RawTwo S).Q) (j : Fin 2)
    (v : QDoubleCylinderVertex (transposePresentation (RawOne S)) (gammaCone S j) S) :
    BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)
      (.inr ⟨gammaCone S j,v⟩)=0 := by
  rcases v with ⟨c,(cone | ⟨x,hx⟩) | ⟨⟨x,hx⟩,i⟩⟩
  · cases cone
    exact global_cone_zero S a _ _ (seedQNode_incident S j) c
  · by_cases hex : j.val≠0 ∨ 2≤S.half
    · exact global_old_cone_endpoint_zero S a j hex x hx c
    · have hj : j=0 := Fin.ext (by omega)
      have hh : S.half=1 := by have := S.half_pos; omega
      subst j
      have he := seedQNode_only S 0 x hx
      subst x
      exact global_halfOne_q0_endpoint_zero S hh a c
  · exact global_old_cone_interior_zero S a j x hx c i

private theorem dualReadout_global_zero (S : OddScale) (a : Word F (RawTwo S).Q) :
    dualReadout S (BDL26GlobalLookupLinearity.actualGlobal S
      (tannerCoboundary1 (RawTwo S) a))=0 := by
  change rawDualReadout S (BDL26LevelTwoDistance.rzQParity (RawOne S) S
    (BDL26GlobalLookupLinearity.actualGlobal S (tannerCoboundary1 (RawTwo S) a)))=0
  apply rawDualReadout_zero S _
  · change (∑ v : QDoubleCylinderVertex (transposePresentation (RawOne S))
      (gammaCone S 0) S, BDL26GlobalLookupLinearity.actualGlobal S
        (tannerCoboundary1 (RawTwo S) a) (.inr ⟨gammaCone S 0,v⟩))=0
    exact Finset.sum_eq_zero (fun v _ => global_old_cone_vertex_zero S a 0 v)
  · change (∑ v : QDoubleCylinderVertex (transposePresentation (RawOne S))
      (gammaCone S 1) S, BDL26GlobalLookupLinearity.actualGlobal S
        (tannerCoboundary1 (RawTwo S) a) (.inr ⟨gammaCone S 1,v⟩))=0
    exact Finset.sum_eq_zero (fun v _ => global_old_cone_vertex_zero S a 1 v)
  · intro j n
    change (∑ v : QDoubleCylinderVertex (transposePresentation (RawOne S))
      (gammaRadial S j n) S, BDL26GlobalLookupLinearity.actualGlobal S
        (tannerCoboundary1 (RawTwo S) a) (.inr ⟨gammaRadial S j n,v⟩))=0
    exact Finset.sum_eq_zero (fun v _ => global_radial_vertex_zero S a j n v)

private theorem primitive_base_boundary (S : OddScale) (N : Nat)
    (u : XSyndromeDomain S N) (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (hs : firstReadout S N u=0) :
    ∃ p0 : (SuffixData S N).family.Cochain0 0,
      (SuffixData S N).family.coboundary0 0 p0=
        (descent S N u q).word+
          (actualBase S N).decode (actualInputs S N (input S N u) 0)+
          (actualBase S N).decode (actualInputs S N
            (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q)) 0) := by
  cases hsearch : BDL26LevelTwoLocalBranchEndpoint.localSearch S
      (secondReadout S N u q) with
  | none =>
    exact fallback_base_boundary_of_global_dual_zero S N u q a hp hs hsearch
      (dualReadout_global_zero S (descent S N u q).word)
  | some w =>
    have hb : BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S N u q) :=
      ⟨w,hsearch⟩
    exact ⟨BDL26LocalSearchFailureReduction.basePotential S N u q hs hb,
      BDL26LocalSearchFailureReduction.basePotential_spec S N u q hs hb⟩

/-- Every actual primitive C2 Q-edge with original FIRST zero has a complete
original base and top potential, with both original base calls retained. -/
theorem primitive_full_endpoint (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (hs : firstReadout S N u=0) :
    ∃ (p0 : (SuffixData S N).family.Cochain0 0)
      (p : (SuffixData S N).family.Cochain0 (TopIndex N)),
      (SuffixData S N).family.coboundary0 0 p0=
        (descent S N u q).word+
          (actualBase S N).decode (actualInputs S N (input S N u) 0)+
          (actualBase S N).decode (actualInputs S N
            (perturbTop S N (input S N u) (BDL26ActualFailureReadout.flip S N q)) 0) ∧
      p=intervalMap0 (SuffixData S N) 0 (TopIndex N) (Nat.zero_le _) p0+
        accumulated S N u q ∧
      (SuffixData S N).family.coboundary0 (TopIndex N) p=
        BDL26LogicalDefectProtection.deltaX S N u q ∧
      (SuffixData S N).family.coboundary0 (TopIndex N) p=
        BDL26ActualFailureReadout.flip S N q+xCorrection S N u+
          xCorrection S N (translateX S N u (BDL26ActualFailureReadout.flip S N q)) ∧
      BDL26LogicalDefectProtection.chiX S N u q=0 := by
  obtain ⟨p0,hp0⟩ := primitive_base_boundary S N u q a hp hs
  obtain ⟨p,hformula,htop,hcorrection,hchi⟩ := full_endpoint_of_base_boundary S N u q p0 hp0
  exact ⟨p0,p,hp0,hformula,htop,hcorrection,hchi⟩

/-- The original fixed-depth primitive C2 Q-edge class has zero actual X defect
whenever the original FIRST readout is zero. -/
theorem primitive_chiX_zero (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : Seed S)
    (hp : parse S N q=.primitive (Primitive.c2QEdge a.1 a.2.1 a.2.2))
    (hs : firstReadout S N u=0) : BDL26LogicalDefectProtection.chiX S N u q=0 := by
  obtain ⟨_,_,_,_,_,_,hchi⟩ := primitive_full_endpoint S N u q a hp hs
  exact hchi

end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Private transparent coordinate type views of the original providers. Their constructors retain the original finite data, regions, choices, flows and budgets. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26LevelTwoCode BDL26IndexedDecoder
open MultiscaleDecoder.RXCoarseGraining

private instance (priority := high) repair3WordHAdd {I : Type*} :
    HAdd (Word BDL26Field I) (Word BDL26Field I) (Word BDL26Field I) :=
  ⟨fun a b i => a i+b i⟩

/- The subtype head is explicit here. Its dictionary is the same pointwise
addition; it does not inspect or choose a decoder output. -/
private instance (priority := high) repair6RegionWordHAdd {I : Type*} (Y : Finset I) :
    HAdd (Word BDL26Field (LocalRegionIndex Y))
      (Word BDL26Field (LocalRegionIndex Y))
      (Word BDL26Field (LocalRegionIndex Y)) :=
  ⟨@Add.add (LocalRegionIndex Y → BDL26Field) inferInstance⟩

private theorem repair3_scalar_add_self (a : BDL26Field) : a+a=0 :=
  CharTwo.add_self_eq_zero a

private theorem repair3_word_add_self {I : Type*} (w : Word BDL26Field I) : w+w=0 := by
  funext i
  exact repair3_scalar_add_self (w i)

/- These two congruence laws are abstracted over the ACTUAL decoder depth and
step. They compare only the original local input predicates and original
Classical.choose. The caller supplies no selector law or desired conclusion. -/
universe u4 v4
section Repair4OriginalTotalCongruence
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
variable {depth4 : Nat} {C04 C14 C24 : LevelIndex depth4 → Type u4}
variable [∀ i,Fintype (C04 i)] [∀ i,Fintype (C14 i)] [∀ i,Fintype (C24 i)]
variable [∀ i,DecidableEq (C14 i)] [∀ i,DecidableEq (C24 i)]
variable {D4 : BDL26DecoderData depth4 C04 C14 C24} {i4 : StepIndex depth4}
variable {X4 Q4 Z4 : Type v4} [Fintype X4] [DecidableEq X4]
  [Fintype Q4] [DecidableEq Q4] [Fintype Z4] [DecidableEq Z4]
variable {LX4 : LocalComplexData X4 (C24 i4.succ) (C14 i4.succ)}
  {LQ4 : LocalComplexData Q4 (C24 i4.succ) (C14 i4.succ)}
  {LZ4 : LocalComplexData Z4 (C24 i4.succ) (C14 i4.succ)}
variable {X04 : X4 → Type u4} {Q04 : Q4 → Type u4}
  {Z04 Z14 Z24 : Z4 → Type u4}
variable [∀ x,Fintype (X04 x)] [∀ q,Fintype (Q04 q)]
  [∀ z,Fintype (Z04 z)] [∀ z,Fintype (Z14 z)] [∀ z,Fintype (Z24 z)]
variable (G4 : RXCoarseGrainingData (X0 := X04) (Q0 := Q04)
  (Z0 := Z04) (Z1 := Z14) (Z2 := Z24) D4 i4 LX4 LQ4 LZ4)

end Repair4OriginalTotalCongruence

private theorem repair4_basis_weight_one {I : Type} [Fintype I] (p : I) :
    HammingWeight (canonicalBasisWord p : Word BDL26Field I)=1 := by
  classical
  have h : hammingSupport (canonicalBasisWord p : Word BDL26Field I)={p} := by
    ext i
    by_cases hi : i=p <;> simp [hammingSupport,basis_value,hi]
  rw [HammingWeight_eq_card_hammingSupport,h,Finset.card_singleton]

private instance repair4BaseStateZeroX : OfNat BDL26DecodingGraph.baseState.presentation.X 0 :=
  inferInstanceAs (OfNat BDL26FiniteAlternatingCore.BaseX 0)

private instance repair2BaseZeroX : OfNat baseTannerSquarePresentation.X 0 :=
  inferInstanceAs (OfNat BDL26FiniteAlternatingCore.BaseX 0)

private abbrev literalAt (P : TannerSquarePresentation) (S : OddScale) :
    LevelIndex 1 → TannerSquarePresentation :=
  Fin.cases P (fun _ => rxReplacementPresentation P S)
private abbrev literalX (P : TannerSquarePresentation) (S : OddScale)
    (i : LevelIndex 1) := (literalAt P S i).X
private abbrev literalQ (P : TannerSquarePresentation) (S : OddScale)
    (i : LevelIndex 1) := (literalAt P S i).Q
private abbrev literalZ (P : TannerSquarePresentation) (S : OddScale)
    (i : LevelIndex 1) := (literalAt P S i).Z
private abbrev literalFamily (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    BDL26CochainFamily 1 (literalX P S) (literalQ P S) (literalZ P S) :=
  presentationFamily P A R S
/- Both families use exactly the same physical coordinates. These typed
pointwise dictionaries cross only that definitional presentation boundary. -/
private instance (priority := high) repair6C3TopHAdd (S : OddScale) :
    HAdd ((indexedFamily S 3).Cochain2 (3 : LevelIndex 3))
      ((literalFamily (BDL26DecodingGraph.state S 2).presentation
        (BDL26DecodingGraph.state S 2).admissible
        (BDL26DecodingGraph.state S 2).regular S).Cochain2
          (Fin.succ (0 : StepIndex 1)))
      ((indexedFamily S 3).Cochain2 (3 : LevelIndex 3)) :=
  ⟨fun a b => @Add.add (FamilyZ S 3 (3 : LevelIndex 3) → BDL26Field)
    inferInstance a b⟩

private instance (priority := high) repair6C3UpperHAdd (S : OddScale) :
    HAdd (BDL26RXErrorPullback.Upper S 3
        (BDL26LocalizedHistoryErrorDescent.Edge 1 (0 : StepIndex 1)))
      (Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
        (Fin.succ (0 : StepIndex 1))))
      (BDL26RXErrorPullback.Upper S 3
        (BDL26LocalizedHistoryErrorDescent.Edge 1 (0 : StepIndex 1))) :=
  ⟨fun a b => @Add.add
    ((BDL26DecodingGraph.state S 3).presentation.Q → BDL26Field) inferInstance a b⟩

private abbrev literalMap (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    BDL26CochainMap (literalFamily P A R S) (0 : StepIndex 1) :=
  presentationMap P A R S
private abbrev literalDecoderData (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    BDL26DecoderData 1 (literalX P S) (literalQ P S) (literalZ P S) :=
  presentationDecoderData P A R S
private instance (priority := high) repair6LiteralSyndromeHAdd
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    HAdd (Word BDL26Field (literalZ P S 1))
      ((literalDecoderData P A R S).family.Cochain2 (Fin.succ (0 : StepIndex 1)))
      (Word BDL26Field (literalZ P S 1)) :=
  ⟨fun a b => @Add.add (literalZ P S 1 → BDL26Field) inferInstance a b⟩

/- Canonical pointwise Pi addition, with the ACTUAL history's TopIndex head.
The result carrier and every coordinate remain the original indexed family. -/
private instance (priority := high) repair7TopLiteralCochainHAdd (S : OddScale) :
    HAdd ((indexedFamily S (1+2)).Cochain2 (TopIndex (1+2)))
      ((literalFamily (BDL26DecodingGraph.state S 2).presentation
        (BDL26DecodingGraph.state S 2).admissible
        (BDL26DecodingGraph.state S 2).regular S).Cochain2
          (Fin.succ (0 : StepIndex 1)))
      ((indexedFamily S (1+2)).Cochain2 (TopIndex (1+2))) :=
  ⟨fun a b => @Add.add (FamilyZ S 3 (TopIndex 3) → BDL26Field)
    inferInstance a b⟩

private instance (priority := high) repair7TopLiteralWordHAdd (S : OddScale) :
    HAdd ((indexedFamily S (1+2)).Cochain2 (TopIndex (1+2)))
      (Word BDL26Field (literalZ (BDL26DecodingGraph.state S 2).presentation S
        (Fin.succ (0 : StepIndex 1))))
      ((indexedFamily S (1+2)).Cochain2 (TopIndex (1+2))) :=
  ⟨fun a b => @Add.add (FamilyZ S 3 (TopIndex 3) → BDL26Field)
    inferInstance a b⟩

private abbrev literalLx (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :=
  presentationLx P A R S
private abbrev literalLq (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :=
  presentationLq P A R S
private abbrev literalLz (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :=
  presentationLz P A R S
private abbrev literalContract (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXConstructionContractSlice
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (literalDecoderData P A R S) (0 : StepIndex 1)
      (literalLx P A R S) (literalLq P A R S) (literalLz P A R S) :=
  presentationContract P A R S
private abbrev literalData (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    RXCoarseGrainingData
      (X0 := fun x => DoubleCylinderVertex P x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (literalDecoderData P A R S) (0 : StepIndex 1)
      (literalLx P A R S) (literalLq P A R S) (literalLz P A R S) :=
  presentationData P A R S


private theorem repair5_C3_upper_coboundary1 (S : OddScale) :
    (BDL26IndexedDecoder.indexedFamily S 3).coboundary1 (3 : LevelIndex 3)=
      (literalFamily (BDL26DecodingGraph.state S 2).presentation
        (BDL26DecodingGraph.state S 2).admissible
        (BDL26DecodingGraph.state S 2).regular S).coboundary1
          (Fin.succ (0 : StepIndex 1)) := by
  exact (BDL26IndexedDecoder.indexedFamily_coboundary1 S 3 (3 : LevelIndex 3)).trans
    (presentationFamily_coboundary1 (BDL26DecodingGraph.state S 2).presentation
      (BDL26DecodingGraph.state S 2).admissible
      (BDL26DecodingGraph.state S 2).regular S
      (Fin.succ (0 : StepIndex 1))).symm

private abbrev repair2C3Input (S : OddScale) :=
  BDL26HistorySyndromeSensitivity.TopInput S 1

/- The same valid upper word, with its image witness translated by the actual
   two coboundary identities. This avoids asking unification to expand the
   recursive Tanner presentation while elaborating a history argument. -/
private abbrev repair5_literal_to_actual (S : OddScale)
    (sigma : (literalFamily (BDL26DecodingGraph.state S 2).presentation
      (BDL26DecodingGraph.state S 2).admissible
      (BDL26DecodingGraph.state S 2).regular S).Syndrome
        (Fin.succ (0 : StepIndex 1))) : repair2C3Input S := by
  refine ⟨sigma.val,?_⟩
  obtain ⟨w,hw⟩ := sigma.property
  refine ⟨w,?_⟩
  exact (LinearMap.congr_fun (repair5_C3_upper_coboundary1 S) w).trans hw
private abbrev repair5_actual_to_literal (S : OddScale) (sigma : repair2C3Input S) :
    (literalFamily (BDL26DecodingGraph.state S 2).presentation
      (BDL26DecodingGraph.state S 2).admissible
      (BDL26DecodingGraph.state S 2).regular S).Syndrome
        (Fin.succ (0 : StepIndex 1)) := by
  refine ⟨sigma.val,?_⟩
  obtain ⟨w,hw⟩ := sigma.property
  refine ⟨w,?_⟩
  exact (LinearMap.congr_fun (repair5_C3_upper_coboundary1 S) w).symm.trans hw

private abbrev repair2C3InputOfSyndrome (S : OddScale)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1) : repair2C3Input S :=
  BDL26ActualFailureReadout.input S 1 u
private abbrev repair2C3PerturbTop (S : OddScale) (sigma : repair2C3Input S)
    (e : Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
      (Fin.succ (0 : StepIndex 1)))) : repair2C3Input S :=
  BDL26HistorySyndromeSensitivity.perturbTop S 1 sigma e
private theorem repair5_C3_perturb_val (S : OddScale) (sigma : repair2C3Input S)
    (e : Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
      (Fin.succ (0 : StepIndex 1)))) :
    (repair2C3PerturbTop S sigma e).val=
      sigma.val+(literalFamily (BDL26DecodingGraph.state S 2).presentation
        (BDL26DecodingGraph.state S 2).admissible
        (BDL26DecodingGraph.state S 2).regular S).coboundary1
          (Fin.succ (0 : StepIndex 1)) e := by
  funext z
  change sigma.val z+(BDL26IndexedDecoder.indexedFamily S 3).coboundary1
    (TopIndex 3) e z=sigma.val z+_
  exact congrArg (fun a : BDL26Field => sigma.val z+a)
    (congrFun (LinearMap.congr_fun (repair5_C3_upper_coboundary1 S) e) z)

private abbrev repair2C3Flip (S : OddScale) (p : BDL26CSSHamiltonian.Physical S 3) :
    Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
      (Fin.succ (0 : StepIndex 1))) :=
  BDL26ActualFailureReadout.flip S 1 p
private abbrev repair2C3Correction (S : OddScale) (sigma : repair2C3Input S) :
    Word BDL26Field (literalQ (BDL26DecodingGraph.state S 2).presentation S
      (Fin.succ (0 : StepIndex 1))) :=
  (BDL26HistoryErrorTelescoping.actualOutput S 1 sigma
    (0 : StepIndex 1)).correction
private abbrev repair2C3Map2 (S : OddScale) :
    Word BDL26Field (BDL26DecodingGraph.state S 2).presentation.Z →ₗ[BDL26Field]
      Word BDL26Field (literalZ (BDL26DecodingGraph.state S 2).presentation S
        (Fin.succ (0 : StepIndex 1))) :=
  ((indexedDecoderData S 3).selectedMap (2 : StepIndex 3)).map2


private theorem repair2C3Flip_basis (S : OddScale) (p : BDL26CSSHamiltonian.Physical S 3) :
    repair2C3Flip S p = canonicalBasisWord (F := BDL26Field) p := by
  exact BDL26ActualFailureReadout.flip_eq_basis S 1 p

private theorem repair2_interior_succ_lt (S : OddScale) (i : Fin (S.half-1)) :
    i.val+1<S.half := by
  have hi := i.isLt
  have hm : S.half-1+1=S.half := Nat.sub_add_cancel S.half_pos
  omega
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Actual coupled Cx/Cq response families on the original coordinate types. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26ActualFailureReadout
open scoped Classical BigOperators

section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private abbrev LocalQWord (q : P.Q) :=
  Word BDL26Field (LocalRegionIndex ((LQ).correctionRegion q))

private def assemble (W : ∀ q, LocalQWord P A R S q) : (CF).Cochain1 U :=
  ∑ q, extendWordLinear ((LQ).correctionRegion q) (W q)

private theorem cqTotal_at_q (sigma : (CF).Cochain2 U) (q : P.Q) :
    restrictWordLinear ((LQ).correctionRegion q) (cqCorrectionTotal G sigma)=
      restrictWordLinear ((LQ).correctionRegion q) (cqComponentTotal G sigma q) := by
  change restrictWordLinear ((LQ).correctionRegion q)
    (∑ r, cqComponentTotal G sigma r)=_
  erw [map_sum]
  apply Finset.sum_eq_single q
  · intro r _ hr
    funext p
    apply cqComponentTotal_supported G sigma r p.val
    intro hp
    exact Finset.disjoint_left.mp
      ((G).cq_correction_regions_pairwise_disjoint r q hr) hp p.property
  · simp

private theorem original_cq_ranges (sigma : (CF).Syndrome U) :
    CqLocalRange G sigma.val := by
  have hCx := (G).contract.cx_local_ranges_of_syndrome sigma
  have hX : ∀ p∈(G).xSector,rxSigmaAfterCx G sigma.val p=0 := by
    have hc := cx_cleaning_explicit G sigma
    have he := cxCorrectionTotal_eq_explicit G sigma.val hCx
    simpa only [rxSigmaAfterCx,he] using hc.2
  have hsyndrome : ∃ error : (CF).Cochain1 U,
      (CF).coboundary1 U error=sigma.val := sigma.property
  obtain ⟨error,herror⟩ := hsyndrome
  let error1 := error+cxCorrectionTotal G sigma.val
  have he1 : (CF).coboundary1 U error1=rxSigmaAfterCx G sigma.val := by
    dsimp [error1,rxSigmaAfterCx]
    erw [map_add,herror]
    all_goals rfl
  have hk : ∀ x,(G).contract.rx_local_complexes.cxDelta1 x
      (restrictWordLinear ((LX).correctionRegion x) error1)=0 := by
    intro x
    erw [← (G).contract.support_decomposition.cxDelta1_restriction_global x error1,he1]
    funext p
    apply hX p.val
    erw [(G).xSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,p.property⟩
  obtain ⟨stabilizers,hs⟩ := (G).contract.cx_error_cleaning_all error1 hk
  let correction := (CF).coboundary0 U
    (∑ x,(G).contract.support_decomposition.cxLift0 x (stabilizers x))
  have hz : (CF).coboundary1 U correction=0 := by
    have hc := LinearMap.congr_fun
      (BDL26CochainFamily.coboundary1_comp_coboundary0 CF U)
      (∑ x,(G).contract.support_decomposition.cxLift0 x (stabilizers x))
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply] using hc
  let error2 := error1+correction
  have he2 : (CF).coboundary1 U error2=rxSigmaAfterCx G sigma.val := by
    dsimp only [error2]
    erw [map_add,hz,add_zero,he1]
  have hx2 : ∀ x,restrictWordLinear ((LX).correctionRegion x) error2=0 := by
    intro x
    exact hs x
  have hq := (G).contract.cq_local_ranges_of_error error2 hx2
  intro q
  change restrictWordLinear ((LQ).syndromeRegion q) (rxSigmaAfterCx G sigma.val)∈_
  erw [← he2]
  exact hq q

private def addError (sigma : (CF).Syndrome U) (e : (CF).Cochain1 U) : (CF).Syndrome U := by
  refine ⟨sigma.val+(CF).coboundary1 U e,?_⟩
  obtain ⟨a,ha⟩ := sigma.property
  exact ⟨a+e,by erw [map_add,ha]⟩

/-- The shift removes the baseline ACTUAL Cq query and inserts the complete
family W. It preserves the baseline Cx read, rather than setting Cx to zero. -/
private def queryShift (sigma : (CF).Syndrome U)
    (W : ∀ q,LocalQWord P A R S q) : (CF).Cochain1 U :=
  assemble P A R S W+cqCorrectionTotal G sigma.val

private def actualTranslation (sigma : (CF).Syndrome U) (e : (CF).Cochain1 U) (q : P.Q) :
    LocalQWord P A R S q :=
  restrictWordLinear ((LQ).correctionRegion q) (cqCorrectionTotal G sigma.val)+
    restrictWordLinear ((LQ).correctionRegion q)
      (cqCorrectionTotal G (addError P A R S sigma e).val)

private theorem actual_cq_choice (sigma : (CF).Syndrome U) (q : P.Q)
    (w : LocalQWord P A R S q)
    (hq : restrictWordLinear ((LQ).syndromeRegion q) (rxSigmaAfterCx G sigma.val)=
      (G).contract.rx_local_complexes.cqDelta1 q w) :
    restrictWordLinear ((LQ).correctionRegion q) (cqComponentTotal G sigma.val q)=
      Classical.choose ((G).contract.local_boundary_weight_budgets.cq q
        ((G).contract.rx_local_complexes.cqDelta1 q w) ⟨w,rfl⟩) := by
  have hr : CqLocalRangeAt G sigma.val q := by
    change restrictWordLinear ((LQ).syndromeRegion q) (rxSigmaAfterCx G sigma.val)∈_
    erw [hq]
    exact ⟨w,rfl⟩
  erw [cqComponentTotal_eq_explicit G sigma.val q hr,region_restrict_extend]
  change Classical.choose ((G).contract.local_boundary_weight_budgets.cq q
    (restrictWordLinear ((LQ).syndromeRegion q) (rxSigmaAfterCx G sigma.val)) hr)=_
  have hchoice : ∀ (h : restrictWordLinear ((LQ).syndromeRegion q)
      (rxSigmaAfterCx G sigma.val)∈LinearMap.range ((G).contract.rx_local_complexes.cqDelta1 q)),
      Classical.choose ((G).contract.local_boundary_weight_budgets.cq q
        (restrictWordLinear ((LQ).syndromeRegion q) (rxSigmaAfterCx G sigma.val)) h)=
      Classical.choose ((G).contract.local_boundary_weight_budgets.cq q
        ((G).contract.rx_local_complexes.cqDelta1 q w) ⟨w,rfl⟩) := by
    erw [hq]
    intro h
    rfl
  exact hchoice hr

/- Whole typed simultaneous consumer. BOTH actual Cx calls are preserved.
Every Cq component is the original Classical.choose, on w or w+κ. This says
nothing about which resulting terminal response bits are attainable. -/
private theorem rxTotal_at_q (sigma : (CF).Cochain2 U) (q : P.Q) :
    restrictWordLinear ((LQ).correctionRegion q) (rxCorrectionTotal G sigma)=
      restrictWordLinear ((LQ).correctionRegion q) (cqComponentTotal G sigma q) := by
  funext p
  have h := congrFun (rx_mask_total_at_q G sigma q) p.val
  change (if p.val ∈ (LQ).correctionRegion q then
    rxCorrectionTotal G sigma p.val else 0)=cqComponentTotal G sigma q p.val at h
  exact (if_pos p.property).symm.trans h

end
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. The original full Phi is fixed by all original
updated X-block restrictions. No linearity or alternate choice is assumed. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26IndexedDecoder BDL26DecodingGraph BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private theorem actualC3_updated (S : OddScale) (sigma tau : repair2C3Input S)
    (w : LocalizedWord S 1 sigma tau (Fin.succ (0 : StepIndex 1))) :
    BDL26RXErrorPullback.updated S 3 (Edge 1 (0 : StepIndex 1)) (by decide)
      (first S 1 sigma 0) (second S 1 sigma tau 0 w)=
      (fun z => w.word z+repair2C3Correction S sigma z+repair2C3Correction S tau z) := by
  let he : (Edge 1 (0 : StepIndex 1)).val%2=0 := by decide
  have hfirst : BDL26RXErrorPullback.errorSyndrome S 3 (Edge 1 (0 : StepIndex 1))
      (first S 1 sigma (0 : StepIndex 1))=actualInputs S 1 sigma (0 : StepIndex 1).succ :=
    Subtype.ext (first_spec S 1 sigma (0 : StepIndex 1))
  have hsecond : BDL26RXErrorPullback.errorSyndrome S 3 (Edge 1 (0 : StepIndex 1))
      (second S 1 sigma tau (0 : StepIndex 1) w)=actualInputs S 1 tau (0 : StepIndex 1).succ :=
    Subtype.ext (second_spec S 1 sigma tau (0 : StepIndex 1) w)
  have hf : (BDL26RXErrorPullback.run S 3 (Edge 1 (0 : StepIndex 1)) he
      (first S 1 sigma (0 : StepIndex 1))).correction=(actualOutput S 1 sigma (0 : StepIndex 1)).correction := by
    change (rxStepOutput S 3 (Edge 1 (0 : StepIndex 1)) he
      (BDL26RXErrorPullback.errorSyndrome S 3 (Edge 1 (0 : StepIndex 1)) (first S 1 sigma (0 : StepIndex 1)))).correction=_
    erw [hfirst,actualOutput_correction,
      BDL26OwnerIncidenceMasks.actualStep_rx S 3 (Edge 1 (0 : StepIndex 1)) he]
  have ht : (BDL26RXErrorPullback.run S 3 (Edge 1 (0 : StepIndex 1)) he
      (second S 1 sigma tau (0 : StepIndex 1) w)).correction=(actualOutput S 1 tau (0 : StepIndex 1)).correction := by
    change (rxStepOutput S 3 (Edge 1 (0 : StepIndex 1)) he
      (BDL26RXErrorPullback.errorSyndrome S 3 (Edge 1 (0 : StepIndex 1)) (second S 1 sigma tau (0 : StepIndex 1) w))).correction=_
    erw [hsecond,actualOutput_correction,
      BDL26OwnerIncidenceMasks.actualStep_rx S 3 (Edge 1 (0 : StepIndex 1)) he]
  funext z
  change (first S 1 sigma (0 : StepIndex 1) z+second S 1 sigma tau (0 : StepIndex 1) w z)+
    (BDL26RXErrorPullback.run S 3 (Edge 1 (0 : StepIndex 1)) he (first S 1 sigma (0 : StepIndex 1))).correction z+
    (BDL26RXErrorPullback.run S 3 (Edge 1 (0 : StepIndex 1)) he (second S 1 sigma tau (0 : StepIndex 1) w)).correction z=_
  have hd := congrFun (representatives_difference S 1 sigma tau (0 : StepIndex 1) w) z
  exact congrArg₂ (fun a b : BDL26Field => a+b)
    (congrArg₂ (fun a b : BDL26Field => a+b) hd (congrFun hf z)) (congrFun ht z)

/- The entire original accumulated potential, rather than one root or a
truncated boundary, agrees when the actual two-run X restrictions agree. -/
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. Actual original-C3 normalization of the constructed
single-error query families. The FIRST-zero assertion is constructed here;
it is not assumed. No logical conclusion is inferred from a response bit. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26IndexedDecoder BDL26DecodingGraph BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private theorem repair4_C3_total_to_literal (S : OddScale) (sigma : repair2C3Input S) :
    (rxCorrectionTotal (D := indexedDecoderData S 3) (i := (2 : StepIndex 3))
      (X0 := fun x => DoubleCylinderVertex (BDL26DecodingGraph.state S ((2 : StepIndex 3)).val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (Lx := rxLx S 3 (2 : StepIndex 3) (by decide))
      (Lq := rxLq S 3 (2 : StepIndex 3) (by decide))
      (Lz := rxLz S 3 (2 : StepIndex 3) (by decide))
        (rxData S 3 (2 : StepIndex 3) (by decide)) sigma.val :
      Word BDL26Field (RX1 (BDL26DecodingGraph.state S 2).presentation S))=
    rxCorrectionTotal (literalData (BDL26DecodingGraph.state S 2).presentation
      (BDL26DecodingGraph.state S 2).admissible (BDL26DecodingGraph.state S 2).regular S)
      sigma.val := by
  let G3 := rxData S 3 (2 : StepIndex 3) (by decide)
  let G0 := literalData (BDL26DecodingGraph.state S 2).presentation
    (BDL26DecodingGraph.state S 2).admissible (BDL26DecodingGraph.state S 2).regular S
  have hcx : (cxCorrectionTotal (D := indexedDecoderData S 3) (i := (2 : StepIndex 3))
      (X0 := fun x => DoubleCylinderVertex (BDL26DecodingGraph.state S ((2 : StepIndex 3)).val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (Lx := rxLx S 3 (2 : StepIndex 3) (by decide))
      (Lq := rxLq S 3 (2 : StepIndex 3) (by decide))
      (Lz := rxLz S 3 (2 : StepIndex 3) (by decide))
      G3 sigma.val : Word BDL26Field (RX1 (BDL26DecodingGraph.state S 2).presentation S))=cxCorrectionTotal G0 sigma.val := by
    unfold cxCorrectionTotal
    apply Finset.sum_congr rfl
    intro x _
    rfl
  have hcq : (cqCorrectionTotal (D := indexedDecoderData S 3) (i := (2 : StepIndex 3))
      (X0 := fun x => DoubleCylinderVertex (BDL26DecodingGraph.state S ((2 : StepIndex 3)).val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
      (Lx := rxLx S 3 (2 : StepIndex 3) (by decide))
      (Lq := rxLq S 3 (2 : StepIndex 3) (by decide))
      (Lz := rxLz S 3 (2 : StepIndex 3) (by decide))
      G3 sigma.val : Word BDL26Field (RX1 (BDL26DecodingGraph.state S 2).presentation S))=cqCorrectionTotal G0 sigma.val := by
    let chooseQ (q : (BDL26DecodingGraph.state S 2).presentation.Q)
        (a : Word BDL26Field (LocalRegionIndex
          ((literalLq (BDL26DecodingGraph.state S 2).presentation
            (BDL26DecodingGraph.state S 2).admissible
            (BDL26DecodingGraph.state S 2).regular S).syndromeRegion q))) :
        Word BDL26Field (RX1 (BDL26DecodingGraph.state S 2).presentation S) :=
      if ha : a∈LinearMap.range (G0.contract.rx_local_complexes.cqDelta1 q) then
        extendWordLinear ((literalLq (BDL26DecodingGraph.state S 2).presentation
          (BDL26DecodingGraph.state S 2).admissible
          (BDL26DecodingGraph.state S 2).regular S).correctionRegion q)
          (Classical.choose (G0.contract.local_boundary_weight_budgets.cq q a ha)) else 0
    let cleaned3 : Word BDL26Field (RX2 (BDL26DecodingGraph.state S 2).presentation S) :=
      rxSigmaAfterCx (D := indexedDecoderData S 3) (i := (2 : StepIndex 3))
      (X0 := fun x => DoubleCylinderVertex (BDL26DecodingGraph.state S ((2 : StepIndex 3)).val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
        (Lx := rxLx S 3 (2 : StepIndex 3) (by decide))
        (Lq := rxLq S 3 (2 : StepIndex 3) (by decide))
        (Lz := rxLz S 3 (2 : StepIndex 3) (by decide)) G3 sigma.val
    let cleaned0 : Word BDL26Field (RX2 (BDL26DecodingGraph.state S 2).presentation S) :=
      rxSigmaAfterCx G0 sigma.val
    have hcleaned : cleaned3=cleaned0 := by
      funext z
      change sigma.val z+((indexedFamily S 3).coboundary1 (3 : LevelIndex 3)
          (cxCorrectionTotal (D := indexedDecoderData S 3) (i := (2 : StepIndex 3))
      (X0 := fun x => DoubleCylinderVertex (BDL26DecodingGraph.state S ((2 : StepIndex 3)).val).presentation x S)
      (Q0 := fun _ => Fin 0) (Z0 := fun _ => Fin 0)
      (Z1 := fun _ => Fin 0) (Z2 := fun _ => Fin 2)
            (Lx := rxLx S 3 (2 : StepIndex 3) (by decide))
            (Lq := rxLq S 3 (2 : StepIndex 3) (by decide))
            (Lz := rxLz S 3 (2 : StepIndex 3) (by decide)) G3 sigma.val)) z=
        sigma.val z+((literalFamily (BDL26DecodingGraph.state S 2).presentation
          (BDL26DecodingGraph.state S 2).admissible
          (BDL26DecodingGraph.state S 2).regular S).coboundary1
            (Fin.succ (0 : StepIndex 1)) (cxCorrectionTotal G0 sigma.val)) z
      exact congrArg (fun a : BDL26Field => sigma.val z+a)
        ((congrFun (LinearMap.congr_fun (repair5_C3_upper_coboundary1 S) _ ) z).trans
          (congrArg (fun w => ((literalFamily (BDL26DecodingGraph.state S 2).presentation
            (BDL26DecodingGraph.state S 2).admissible
            (BDL26DecodingGraph.state S 2).regular S).coboundary1
              (Fin.succ (0 : StepIndex 1)) w) z) hcx))
    unfold cqCorrectionTotal
    apply Finset.sum_congr rfl
    intro q _
    have harg : restrictWordLinear
        ((literalLq (BDL26DecodingGraph.state S 2).presentation
          (BDL26DecodingGraph.state S 2).admissible
          (BDL26DecodingGraph.state S 2).regular S).syndromeRegion q) cleaned3 =
        restrictWordLinear
        ((literalLq (BDL26DecodingGraph.state S 2).presentation
          (BDL26DecodingGraph.state S 2).admissible
          (BDL26DecodingGraph.state S 2).regular S).syndromeRegion q) cleaned0 :=
      congrArg _ hcleaned
    change chooseQ q (restrictWordLinear
        ((literalLq (BDL26DecodingGraph.state S 2).presentation
          (BDL26DecodingGraph.state S 2).admissible
          (BDL26DecodingGraph.state S 2).regular S).syndromeRegion q) cleaned3) =
      chooseQ q (restrictWordLinear
        ((literalLq (BDL26DecodingGraph.state S 2).presentation
          (BDL26DecodingGraph.state S 2).admissible
          (BDL26DecodingGraph.state S 2).regular S).syndromeRegion q) cleaned0)
    exact congrArg (chooseQ q) harg
  exact congrArg₂ (fun a b : Word BDL26Field
    (RX1 (BDL26DecodingGraph.state S 2).presentation S) => a+b) hcx hcq

private theorem actualC3_correction (S : OddScale) (sigma : repair2C3Input S) :
    (repair2C3Correction S sigma)=
      rxCorrectionTotal (D := indexedDecoderData S 3) (i := (⟨2,by decide⟩ : StepIndex 3)) (rxData S 3 (⟨2,by decide⟩ : StepIndex 3) (by decide)) sigma.val := by
  change (actualOutput S 1 sigma (0 : StepIndex 1)).correction=_
  erw [actualOutput_correction]
  change (BDL26OwnerIncidenceMasks.actualStep S 3 (2 : StepIndex 3)
    (actualInputs S 1 sigma (1 : LevelIndex 1))).correction=_
  erw [actualInputs_top,BDL26OwnerIncidenceMasks.actualStep_rx S 3
    (2 : StepIndex 3) (by decide),rxStepOutput_correction]
  all_goals rfl

/- FIRST is made zero while preserving every original translated total RX
correction. In particular this applies to an actual SINGLE physical basis
error; no gradient-to-single converse is being used. -/
section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

/- Actual original FIRST-zero realization for simultaneous coupled Cq
response families and one unchanged physical basis perturbation. Both calls
of the ORIGINAL full RX correction appear explicitly. The response constants
are constructed from actual selectors, not prescribed terminal bits.

This is a necessary reachability theorem, not a chiX or full endpoint theorem.
It does not claim arbitrary response constants or arbitrary pairs reachable. -/
end
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. This fragment requires the complete immutable M2 C2
module prefix. No imported private lemma from RXLocalReplacement is used. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26LevelTwoCode BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators

private def criticalQZ (j : Fin 2) : XStarEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) :=
  xStarFaceQZEdge baseTannerSquarePresentation 0 (seedFace j) 0

private def criticalRadial (S : OddScale) (j : Fin 2) : (BDL26ActualFailureReadout.RawOne S).Q :=
  gammaRadial S j ⟨S.half-1,by have := S.half_pos;omega⟩

private def criticalBoundary (S : OddScale) (j : Fin 2) : (BDL26ActualFailureReadout.RawOne S).Q :=
  .inl ⟨(0 : BDL26FiniteAlternatingCore.BaseX),.inl (0,.inl (criticalQZ j,⟨0,S.half_pos⟩))⟩

private def criticalVertical (S : OddScale) (j : Fin 2) : (BDL26ActualFailureReadout.RawOne S).Q :=
  .inl ⟨(0 : BDL26FiniteAlternatingCore.BaseX),
    .inr ⟨.inl (seedQVertex j),by change xStarBoundaryVertexMember baseTannerSquarePresentation 0 (seedQVertex j).val=true; fin_cases j <;> decide⟩⟩

/-- A strict interior grid coordinate cannot be an original Q corner. -/
private theorem critical_grid_not_Q_of_interior (S : OddScale) (j : Fin 2)
    (f : XStarFace baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX))
    (a b : Fin (S.half+1))
    (hi : (0<a.val ∧ a.val<S.half) ∨ (0<b.val ∧ b.val<S.half)) :
    subdivisionGridVertex baseTannerSquarePresentation 0 S f a b≠.inl (seedQVertex j) := by
  intro h
  rcases hi with ⟨ha0,ham⟩ | ⟨hb0,hbm⟩
  · have ha0' : a.val≠0 := by omega
    have ham' : a.val≠S.half := by omega
    simp only [subdivisionGridVertex,dif_neg ha0',dif_neg ham'] at h
    split_ifs at h <;> cases h
  · have hb0' : b.val≠0 := by omega
    have hbm' : b.val≠S.half := by omega
    simp only [subdivisionGridVertex] at h
    split_ifs at h <;> first | omega | cases h

private theorem critical_subdivision_incident (S : OddScale) (j : Fin 2)
    (e : SubdivisionEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S)
    (h : subdivisionEdgeStart baseTannerSquarePresentation 0 S e=.inl (seedQVertex j) ∨
      subdivisionEdgeEnd baseTannerSquarePresentation 0 S e=.inl (seedQVertex j)) :
    e=.inl (seedRadial j,⟨S.half-1,by have := S.half_pos;omega⟩) ∨
      e=.inl (criticalQZ j,⟨0,S.half_pos⟩) := by
  rcases e with ⟨edge,k⟩ | (⟨f,k,i⟩ | ⟨f,i,k⟩)
  · rcases h with hs | ht
    · change subdivisionSegmentStart _ _ S edge k=.inl (seedQVertex j) at hs
      by_cases hk : k.val=0
      · simp only [subdivisionSegmentStart,dif_pos hk] at hs
        have he : edge=criticalQZ j := by
          rcases edge with ⟨edge,member⟩
          rcases edge with ⟨⟨x,q⟩,hxq⟩ | ⟨⟨q,z⟩,hqz⟩
          · have hv := congrArg Subtype.val (Sum.inl.inj hs)
            cases hv
          · have hq : q=seedQ j := by
              have hv := congrArg Subtype.val (Sum.inl.inj hs)
              exact Vertex.q.inj hv
            subst q
            fin_cases j <;> fin_cases z
            all_goals
              simp [TannerSquarePresentation.qz,baseTannerSquarePresentation,
                baseTannerSquareData,baseBoundary2Matrix] at hqz
            all_goals first | contradiction | rfl
        right
        exact congrArg Sum.inl (Prod.ext he (Fin.ext hk))
      · simp only [subdivisionSegmentStart,dif_neg hk] at hs
        cases hs
    · change subdivisionSegmentEnd _ _ S edge k=.inl (seedQVertex j) at ht
      by_cases hk : k.val+1=S.half
      · simp only [subdivisionSegmentEnd,dif_pos hk] at ht
        have he : edge=seedRadial j := by
          rcases edge with ⟨edge,member⟩
          rcases edge with ⟨⟨x,q⟩,hxq⟩ | ⟨⟨q,z⟩,hqz⟩
          · have hq : q=seedQ j := by
              have hv := congrArg Subtype.val (Sum.inl.inj ht)
              exact Vertex.q.inj hv
            subst q
            fin_cases j <;> fin_cases x
            all_goals
              simp [TannerSquarePresentation.xq,baseTannerSquarePresentation,
                baseTannerSquareData,baseBoundary1Matrix] at hxq
            all_goals first | contradiction | rfl
          · have hv := congrArg Subtype.val (Sum.inl.inj ht)
            cases hv
        left
        have hk' : k=⟨S.half-1,by have := S.half_pos;omega⟩ := by
          apply Fin.ext
          change k.val=S.half-1
          have := S.half_pos
          omega
        exact congrArg Sum.inl (Prod.ext he hk')
      · simp only [subdivisionSegmentEnd,dif_neg hk] at ht
        cases ht
  · rcases h with hs | ht
    · apply False.elim
      apply (critical_grid_not_Q_of_interior S j f
        ⟨k.val,Nat.lt_succ_of_lt k.isLt⟩ ⟨i.val+1,by have hi := repair2_interior_succ_lt S i; omega⟩
        (Or.inr ⟨by change ((0 : Nat) < i.val + 1);omega,by change (i.val + 1 < S.half);exact repair2_interior_succ_lt S i⟩))
      exact hs
    · apply False.elim
      apply (critical_grid_not_Q_of_interior S j f
        ⟨k.val+1,by have := k.isLt;omega⟩ ⟨i.val+1,by have hi := repair2_interior_succ_lt S i; omega⟩
        (Or.inr ⟨by change ((0 : Nat) < i.val + 1);omega,by change (i.val + 1 < S.half);exact repair2_interior_succ_lt S i⟩))
      exact ht
  · rcases h with hs | ht
    · apply False.elim
      apply (critical_grid_not_Q_of_interior S j f
        ⟨i.val+1,by have hi := repair2_interior_succ_lt S i; omega⟩ ⟨k.val,Nat.lt_succ_of_lt k.isLt⟩
        (Or.inl ⟨by change ((0 : Nat) < i.val + 1);omega,by change (i.val + 1 < S.half);exact repair2_interior_succ_lt S i⟩))
      exact hs
    · apply False.elim
      apply (critical_grid_not_Q_of_interior S j f
        ⟨i.val+1,by have hi := repair2_interior_succ_lt S i; omega⟩ ⟨k.val+1,by have := k.isLt;omega⟩
        (Or.inl ⟨by change ((0 : Nat) < i.val + 1);omega,by change (i.val + 1 < S.half);exact repair2_interior_succ_lt S i⟩))
      exact ht

/-- The complete original critical star has two boundary-path segments, its
vertical edge, and its unique shifted cone. The scale remains symbolic. -/
private theorem critical_four_neighbours (S : OddScale) (j : Fin 2)
    (r : (BDL26ActualFailureReadout.RawOne S).Q) (hr : (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) r=true) :
    r=criticalRadial S j ∨ r=criticalBoundary S j ∨
      r=criticalVertical S j ∨ r=gammaCone S j := by
  change RX1 baseTannerSquarePresentation S at r
  rcases r with ⟨x,e⟩ | ⟨q,v⟩
  · have howner : x=0 := by
      rcases (old_local_incidence S _ x e).mp hr with hs | ht
      · change (x : BDL26FiniteAlternatingCore.BaseX)=0
        exact (congrArg (fun v : (BDL26ActualFailureReadout.RawOne S).X =>
          (v.1 : BDL26FiniteAlternatingCore.BaseX)) hs).symm
      · change (x : BDL26FiniteAlternatingCore.BaseX)=0
        exact (congrArg (fun v : (BDL26ActualFailureReadout.RawOne S).X =>
          (v.1 : BDL26FiniteAlternatingCore.BaseX)) ht).symm
    subst x
    rcases (old_local_incidence S _ 0 e).mp hr with hs | ht
    · have hv := eq_of_heq (Sigma.mk.inj hs).2
      rcases e with ⟨copy,edge⟩ | vertex
      · have hc : copy=0 := (congrArg Prod.fst hv).symm
        subst copy
        have h : subdivisionEdgeStart baseTannerSquarePresentation 0 S edge=
            .inl (seedQVertex j) ∨
            subdivisionEdgeEnd baseTannerSquarePresentation 0 S edge=
              .inl (seedQVertex j) := Or.inl (congrArg Prod.snd hv).symm
        rcases critical_subdivision_incident S j edge h with he | he
        · exact Or.inl (by erw [he];rfl)
        · exact Or.inr (Or.inl (by erw [he];rfl))
      · have hvertex : vertex=⟨.inl (seedQVertex j),by change xStarBoundaryVertexMember baseTannerSquarePresentation 0 (seedQVertex j).val=true; fin_cases j <;> decide⟩ := by
          apply Subtype.ext
          exact (congrArg Prod.snd hv).symm
        rw [hvertex]
        exact Or.inr (Or.inr (Or.inl rfl))
    · have hv := eq_of_heq (Sigma.mk.inj ht).2
      rcases e with ⟨copy,edge⟩ | vertex
      · have hc : copy=0 := (congrArg Prod.fst hv).symm
        subst copy
        have h : subdivisionEdgeStart baseTannerSquarePresentation 0 S edge=
            .inl (seedQVertex j) ∨
            subdivisionEdgeEnd baseTannerSquarePresentation 0 S edge=
              .inl (seedQVertex j) := Or.inr (congrArg Prod.snd hv).symm
        rcases critical_subdivision_incident S j edge h with he | he
        · exact Or.inl (by erw [he];rfl)
        · exact Or.inr (Or.inl (by erw [he];rfl))
      · have hc := congrArg Prod.fst hv
        change (0 : BDL26FiniteTannerSquare.Two)=1 at hc
        exact False.elim (by cases hc)
  · exact Or.inr (Or.inr (Or.inr (seedQNode_shifted_neighbour S j q v hr)))
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. This continuation is concatenated after the COMPLETE
31-declaration query/Phi/history closure, not imported through private aliases. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private def criticalTerminal (S : OddScale) (j : Fin 2)
    (copy : BDL26FiniteTannerSquare.Two) (r : (BDL26ActualFailureReadout.RawOne S).Q)
    (hr : (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) r=true) : (BDL26DecodingGraph.state S 2).presentation.Q :=
  .inr ⟨r,(copy,.inl (.inr ⟨seedQNode S j,hr⟩))⟩

/- Necessary actual critical-star consumer. The full four-neighbour cover
is DERIVED and the baseline zero response uses the two literal original
calls separated by the SAME single physical basis perturbation. Neither
all-query periodicity nor attainable nonzero response bits are assumed. -/
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. Exact materialized RZ incidence is used directly;
no private RX degree enumeration or symmetry of Classical.choose is used. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RZLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26LevelTwoCode
open scoped Classical BigOperators

private noncomputable def shiftedQZNeighbourEquiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    QStarEdge P q ≃ {z : RZZ P S // rzQZIncidence P A S (.inr ⟨q,v⟩) z=true} where
  toFun z := ⟨⟨z.val,qToZDoubleCylinderVertex P A q z.val z.property S v⟩,by
    change decide (∃ h : P.qz q z.val=true,
      qToZDoubleCylinderVertex P A q z.val h S v=
        qToZDoubleCylinderVertex P A q z.val z.property S v)=true
    exact decide_eq_true ⟨z.property,rfl⟩⟩
  invFun z := ⟨z.val.1,by
    have hz := z.property
    change decide (∃ h : P.qz q z.val.1=true,
      qToZDoubleCylinderVertex P A q z.val.1 h S v=z.val.2)=true at hz
    exact Classical.choose (of_decide_eq_true hz)⟩
  left_inv z := Subtype.ext rfl
  right_inv z := by
    rcases z with ⟨⟨z,t⟩,hz⟩
    change decide (∃ h : P.qz q z=true,
      qToZDoubleCylinderVertex P A q z h S v=t)=true at hz
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq (Classical.choose_spec (of_decide_eq_true hz)))

end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. Both true detector gamma cylinders are degree one.
The conditional two-leaf calculation is deliberately excluded from this
closure. No affine/periodic property of the original degree-one choice is
inferred from the degree. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RZLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26LevelTwoCode
open scoped Classical BigOperators

private theorem criticalRadial_incident (S : OddScale) (j : Fin 2) :
    (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) (criticalRadial S j)=true := by
  let e : DoubleCylinderEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S :=
    .inl (0,.inl (seedRadial j,⟨S.half-1,by have := S.half_pos;omega⟩))
  apply (old_local_incidence S (seedQNode S j) 0 e).mpr
  right
  change seedQNode S j=⟨0,(0,subdivisionSegmentEnd baseTannerSquarePresentation 0 S
    (seedRadial j) ⟨S.half-1,by have := S.half_pos;omega⟩)⟩
  have hk : S.half-1+1=S.half := by have := S.half_pos;omega
  erw [subdivisionSegmentEnd,dif_pos hk,seedRadial_end]
  rfl

/- Both ORIGINAL critical gamma ports have one-leaf local Cq graphs, for
all odd scales, both outer copies, and both critical old Q nodes. These
are full degree equalities, not upper bounds or first-pivot observations. -/
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. The critical vertical port is also degree one.
This is the genuine complete RX column, including all Q-glue checks. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26LevelTwoCode
open scoped Classical BigOperators

private def criticalBoundaryPath (S : OddScale) (j : Fin 2) :
    SubdivisionBoundaryEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S :=
  ⟨.inl (criticalQZ j,⟨0,S.half_pos⟩),by change xStarBoundaryEdgeMember baseTannerSquarePresentation 0 (criticalQZ j).val=true; fin_cases j <;> decide⟩

private def criticalVerticalVertex (S : OddScale) (j : Fin 2) :
    SubdivisionBoundaryVertex baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S :=
  ⟨.inl (seedQVertex j),by change xStarBoundaryVertexMember baseTannerSquarePresentation 0 (seedQVertex j).val=true; fin_cases j <;> decide⟩

private theorem criticalBoundaryPath_start (S : OddScale) (j : Fin 2) :
    subdivisionBoundaryEdgeStart baseTannerSquarePresentation 0 S
      (criticalBoundaryPath S j)=criticalVerticalVertex S j := by
  apply Subtype.ext
  change subdivisionSegmentStart baseTannerSquarePresentation 0 S
    (criticalQZ j) ⟨0,S.half_pos⟩=.inl (seedQVertex j)
  erw [subdivisionSegmentStart,dif_pos rfl]
  fin_cases j <;> rfl

private theorem criticalVertical_rectangle_unique (S : OddScale) (j : Fin 2)
    (b : SubdivisionBoundaryEdge baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S)
    (hb : criticalVerticalVertex S j=subdivisionBoundaryEdgeStart _ _ S b ∨
      criticalVerticalVertex S j=subdivisionBoundaryEdgeEnd _ _ S b) :
    b=criticalBoundaryPath S j := by
  have hv : subdivisionEdgeStart baseTannerSquarePresentation 0 S b.val=
      .inl (seedQVertex j) ∨
      subdivisionEdgeEnd baseTannerSquarePresentation 0 S b.val=.inl (seedQVertex j) := by
    rcases hb with hs | ht
    · left
      have hs' := congrArg Subtype.val hs
      have h := hs'.symm
      change (subdivisionBoundaryEdgeStart baseTannerSquarePresentation 0 S b).val=
        (criticalVerticalVertex S j).val at h
      exact (subdivisionBoundaryEdgeStart_value
        baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S b).symm.trans h
    · right
      have ht' := congrArg Subtype.val ht
      have h := ht'.symm
      change (subdivisionBoundaryEdgeEnd baseTannerSquarePresentation 0 S b).val=
        (criticalVerticalVertex S j).val at h
      exact (subdivisionBoundaryEdgeEnd_value
        baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S b).symm.trans h
  rcases critical_subdivision_incident S j b.val hv with hR | hB
  · have hm := b.property
    erw [hR] at hm
    change false=true at hm
    cases hm
  · exact Subtype.ext hB

/-- Zero incidence at a vertical edge different from both actual endpoints.
The matrix is unfolded only with its own generic P/x/S carrier and dictionaries. -/
private theorem repair14_vertical_rectangle_zero (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (v : SubdivisionBoundaryVertex P x S)
    (b : SubdivisionBoundaryEdge P x S)
    (hs : v≠subdivisionBoundaryEdgeStart P x S b)
    (ht : v≠subdivisionBoundaryEdgeEnd P x S b) :
    doubleCylinderFaceEdgeMatrix P x S (Sum.inr v) (Sum.inr b)=0 := by
  classical
  change ((if v=subdivisionBoundaryEdgeStart P x S b then (1 : BDL26Field) else 0)+
    (if v=subdivisionBoundaryEdgeEnd P x S b then 1 else 0))=0
  rw [if_neg hs,if_neg ht,zero_add]

private theorem criticalVertical_localMatrix (S : OddScale) (j : Fin 2)
    (f : DoubleCylinderFace baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S) :
    doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation 0 S
      (.inr (criticalVerticalVertex S j)) f=
        if f=.inr (criticalBoundaryPath S j) then 1 else 0 := by
  classical
  rcases f with ⟨copy,f⟩ | b
  · simp [doubleCylinderFaceEdgeMatrix]
  · by_cases hb : b=criticalBoundaryPath S j
    · subst b
      have hm : doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation 0 S
          (.inr (criticalVerticalVertex S j)) (.inr (criticalBoundaryPath S j))=1 := by
        rw [← criticalBoundaryPath_start S j]
        exact doubleCylinder_rectangle_vertical_start baseTannerSquarePresentation 0 S
          (criticalBoundaryPath S j) (subdivisionBoundaryEdgeStart_ne_end _ _ _ _)
      exact hm.trans (if_pos rfl).symm
    · have hs : criticalVerticalVertex S j≠subdivisionBoundaryEdgeStart _ _ S b :=
        fun h => hb (criticalVertical_rectangle_unique S j b (Or.inl h))
      have ht : criticalVerticalVertex S j≠subdivisionBoundaryEdgeEnd _ _ S b :=
        fun h => hb (criticalVertical_rectangle_unique S j b (Or.inr h))
      have hf : (Sum.inr b : DoubleCylinderFace baseTannerSquarePresentation 0 S)≠
          Sum.inr (criticalBoundaryPath S j) := fun h => hb (Sum.inr.inj h)
      exact (repair14_vertical_rectangle_zero baseTannerSquarePresentation 0 S
        (criticalVerticalVertex S j) b hs ht).trans (if_neg hf).symm

private theorem criticalVertical_qEdge_zero (S : OddScale) (j : Fin 2)
    (q : BDL26FiniteAlternatingCore.BaseQubit) (e : QDoubleCylinderEdge baseTannerSquarePresentation q S) :
    qDoubleCylinderEdgeXIncidence baseTannerSquarePresentation q 0 S
      (.inr (criticalVerticalVertex S j)) e=0 := by
  unfold qDoubleCylinderEdgeXIncidence
  by_cases hxq : baseTannerSquarePresentation.xq (0 : BDL26FiniteAlternatingCore.BaseX) q=true
  · erw [dif_pos hxq]
    have hn : (.inr (criticalVerticalVertex S j) : DoubleCylinderEdge
        baseTannerSquarePresentation (0 : BDL26FiniteAlternatingCore.BaseX) S)≠
        qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation q 0 hxq S e := by
      rcases e with ⟨copy,z,k⟩ | z
      · intro he
        cases he
      · intro he
        have hv := congrArg Subtype.val (Sum.inr.inj he)
        change (Sum.inl (seedQVertex j) : SubdivisionVertex baseTannerSquarePresentation 0 S)=
          Sum.inl ⟨Vertex.z z.val,_⟩ at hv
        have ht := congrArg Subtype.val (Sum.inl.inj hv)
        cases ht
    erw [if_neg hn]
  · erw [dif_neg hxq]

private def criticalVerticalCheck (S : OddScale) (j : Fin 2) : (BDL26ActualFailureReadout.RawOne S).Z :=
  .inl (.inl ⟨(0 : BDL26FiniteAlternatingCore.BaseX),.inr (criticalBoundaryPath S j)⟩)

private theorem criticalVertical_matrix (S : OddScale) (j : Fin 2)
    (z : (BDL26ActualFailureReadout.RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S (criticalVertical S j) z=
      if z=criticalVerticalCheck S j then 1 else 0 := by
  have h := rx_local_column_indicator baseTannerSquarePresentation S
    (0 : BDL26FiniteAlternatingCore.BaseX) (.inr (criticalVerticalVertex S j))
    (.inr (criticalBoundaryPath S j)) (criticalVertical_localMatrix S j)
    (criticalVertical_qEdge_zero S j) z
  convert h using 1 <;> congr 1

private theorem criticalVertical_degree_one (S : OddScale) (j : Fin 2) :
    (BDL26ActualFailureReadout.RawOne S).qz (criticalVertical S j) (criticalVerticalCheck S j)=true ∧
      ∀ z : (BDL26ActualFailureReadout.RawOne S).Z,(BDL26ActualFailureReadout.RawOne S).qz (criticalVertical S j) z=true →
        z=criticalVerticalCheck S j := by
  constructor
  · have ht := raw_boundary2_view S (criticalVertical S j) (criticalVerticalCheck S j)
    erw [criticalVertical_matrix,if_pos rfl] at ht
    by_contra hn
    erw [if_neg hn] at ht
    exact one_ne_zero ht
  · intro z hz
    have ht := raw_boundary2_view S (criticalVertical S j) z
    erw [criticalVertical_matrix,if_pos hz] at ht
    by_contra hn
    erw [if_neg hn] at ht
    exact one_ne_zero ht.symm

private theorem criticalVertical_incident (S : OddScale) (j : Fin 2) :
    (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) (criticalVertical S j)=true := by
  apply (old_local_incidence S (seedQNode S j) 0
    (.inr (criticalVerticalVertex S j))).mpr
  left
  rfl

/- All three non-boundary ports have genuine degree-one local Cq graphs;
this consumer establishes the vertical channel at both actual copies. -/
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. Derive the complete boundary column from the actual
perfect-pairing chain law, rather than dropping its Q-glue check. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26LevelTwoCode
open BDL26ActualFailureReadout
open scoped Classical BigOperators

private theorem criticalBoundary_incident (S : OddScale) (j : Fin 2) :
    (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) (criticalBoundary S j)=true := by
  apply (old_local_incidence S (seedQNode S j) 0
    (.inl (0,(criticalBoundaryPath S j).val))).mpr
  left
  have hs := congrArg Subtype.val (criticalBoundaryPath_start S j)
  change seedQNode S j=⟨0,(0,subdivisionEdgeStart baseTannerSquarePresentation 0 S
    (criticalBoundaryPath S j).val)⟩
  erw [subdivisionBoundaryEdgeStart_value] at hs
  exact congrArg (fun v => (⟨(0 : BDL26FiniteAlternatingCore.BaseX),((0 : BDL26FiniteTannerSquare.Two),v)⟩ :
    (BDL26ActualFailureReadout.RawOne S).X)) hs.symm

private theorem criticalRadial_ne_boundary (S : OddScale) (j : Fin 2) :
    criticalRadial S j≠criticalBoundary S j := by
  intro h
  have h' := congrArg (fun r : (BDL26ActualFailureReadout.RawOne S).Q =>
    match r with
    | .inl v => match v.2 with
        | .inl e => match e.2 with
            | .inl a => match a.1.val with | .inl _ => true | .inr _ => false
            | _ => false
        | _ => false
    | _ => false) h
  dsimp only [criticalRadial,criticalBoundary,gammaRadial,seedRadial,criticalQZ] at h'
  change true=false at h'
  cases h'

private theorem criticalBoundary_matrix_sum_zero (S : OddScale) (j : Fin 2)
    (z : (BDL26ActualFailureReadout.RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S (criticalRadial S j) z+
      rxBoundary2Matrix baseTannerSquarePresentation S (criticalBoundary S j) z+
      rxBoundary2Matrix baseTannerSquarePresentation S (criticalVertical S j) z+
      rxBoundary2Matrix baseTannerSquarePresentation S (gammaCone S j) z=0 := by
  let t : Finset (BDL26ActualFailureReadout.RawOne S).Q :=
    {criticalRadial S j,criticalBoundary S j,criticalVertical S j,gammaCone S j}
  let f : (BDL26ActualFailureReadout.RawOne S).Q → BDL26Field := fun r =>
    if (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) r && (BDL26ActualFailureReadout.RawOne S).qz r z then 1 else 0
  have houtside : ∀ r ∈ (Finset.univ : Finset (BDL26ActualFailureReadout.RawOne S).Q),r∉t → f r=0 := by
    intro r _ hnot
    have hn : (BDL26ActualFailureReadout.RawOne S).xq (seedQNode S j) r≠true := by
      intro hr
      have hc := critical_four_neighbours S j r hr
      rcases hc with h | h | h | h
      all_goals subst r; exact hnot (by simp [t])
    simp [f,hn]
  have heq : (∑ r ∈ t,f r)=∑ r : (BDL26ActualFailureReadout.RawOne S).Q,f r :=
    Finset.sum_subset (Finset.subset_univ t) houtside
  have hz := sharedQ_indicator_sum_zero (BDL26ActualFailureReadout.RawOne S) (seedQNode S j) z
  erw [← heq] at hz
  have hr := criticalRadial_incident S j
  have hb := criticalBoundary_incident S j
  have hv := criticalVertical_incident S j
  have hc := seedQNode_incident S j
  have hRV : criticalRadial S j≠criticalVertical S j := by intro h;cases h
  have hRC : criticalRadial S j≠gammaCone S j := by intro h;cases h
  have hBV : criticalBoundary S j≠criticalVertical S j := by intro h;cases h
  have hBC : criticalBoundary S j≠gammaCone S j := by intro h;cases h
  have hVC : criticalVertical S j≠gammaCone S j := by intro h;cases h
  simp only [t,Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,
    criticalRadial_ne_boundary S j,hRV,hRC,hBV,hBC,hVC,not_false_eq_true,
    or_self,Finset.sum_singleton] at hz
  simpa only [f,hr,hb,hv,hc,Bool.true_and,← raw_boundary2_view,add_assoc] using hz

/-- COMPLETE original Q/Z incidence column. The three distinct check
families include the genuine Q-glue check of the boundary port. -/
private theorem criticalBoundary_matrix (S : OddScale) (j : Fin 2)
    (z : (BDL26ActualFailureReadout.RawOne S).Z) :
    rxBoundary2Matrix baseTannerSquarePresentation S (criticalBoundary S j) z=
      (if z=seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩ then 1 else 0)+
      (if z=criticalVerticalCheck S j then 1 else 0)+
      (if z=seedConeCheck S j then 1 else 0) := by
  have hz := criticalBoundary_matrix_sum_zero S j z
  let a := rxBoundary2Matrix baseTannerSquarePresentation S (criticalRadial S j) z
  let b := rxBoundary2Matrix baseTannerSquarePresentation S (criticalBoundary S j) z
  let c := rxBoundary2Matrix baseTannerSquarePresentation S (criticalVertical S j) z
  let d := rxBoundary2Matrix baseTannerSquarePresentation S (gammaCone S j) z
  have heq : b=a+c+d := by
    calc
      b=b+0 := (add_zero b).symm
      _=b+(a+b+c+d) := by erw [show a+b+c+d=0 from hz]
      _=(b+b)+(a+c+d) := by ac_rfl
      _=a+c+d := by erw [repair3_scalar_add_self,zero_add]
  change b=_
  erw [heq]
  dsimp only [a,c,d]
  erw [seedRadial_matrix,criticalVertical_matrix,seedCone_matrix]

end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. This fragment uses the complete same-file 31-helper
closure. It derives the actual kappa class from the original complete Phi;
no potential, output bit, or zero-obstruction certificate is a caller input. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private theorem original_single_X_zero_at_Cq (x : P.X)
    (p : LocalRegionIndex ((LX).correctionRegion x)) (q : P.Q) :
    restrictWordLinear ((LQ).correctionRegion q)
      (canonicalBasisWord p.val : (CF).Cochain1 U)=0 := by
  funext v
  have hn : v.val≠p.val := by
    intro hv
    apply Finset.disjoint_left.mp (G).correction_sectors_disjoint
      (Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,p.property⟩)
    erw [(G).qCorrectionSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,hv ▸ v.property⟩
  change (canonicalBasisWord p.val : Word BDL26Field _) v.val=0
  simp [basis_value,hn]
end

section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

end
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. The actual full-Phi class determines the translated
input predicate. Equality of predicates is proved; no equivariance under a
coordinate permutation, optimality, or periodicity of Classical.choose is used. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOldXQueries
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "G" => literalData P A R S
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))

private theorem original_choose_Cq_equal_delta (q : P.Q)
    (a b : LocalQWord P A R S q)
    (h : (G).contract.rx_local_complexes.cqDelta1 q a=
      (G).contract.rx_local_complexes.cqDelta1 q b) :
    Classical.choose ((G).contract.local_boundary_weight_budgets.cq q
        ((G).contract.rx_local_complexes.cqDelta1 q a) ⟨a,rfl⟩)=
      Classical.choose ((G).contract.local_boundary_weight_budgets.cq q
        ((G).contract.rx_local_complexes.cqDelta1 q b) ⟨b,rfl⟩) := by
  have hc : ∀ (ha : (G).contract.rx_local_complexes.cqDelta1 q a∈
        LinearMap.range ((G).contract.rx_local_complexes.cqDelta1 q))
      (hb : (G).contract.rx_local_complexes.cqDelta1 q b∈
        LinearMap.range ((G).contract.rx_local_complexes.cqDelta1 q)),
      Classical.choose ((G).contract.local_boundary_weight_budgets.cq q
          ((G).contract.rx_local_complexes.cqDelta1 q a) ha)=
        Classical.choose ((G).contract.local_boundary_weight_budgets.cq q
          ((G).contract.rx_local_complexes.cqDelta1 q b) hb) := by
    erw [h]
    intro ha hb
    rfl
  exact hc ⟨a,rfl⟩ ⟨b,rfl⟩

end

section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

/- Actual fixed-Cx correlation at every Q. The constant beta is common to
all queries W. The two original choices at W+kappa and W+fullPhiTrace are
literally equal because their FULL predicates are equal. Neither choice is
replaced by a cleaner section. This is not a periodicity assertion. -/
end
end CriticalOldXQueries
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- SOURCE WORKING ONLY. This proves a limitation of a proposed argument,
not a value of Classical.choose and not a counterexample to #1631. Both
witnesses below satisfy the LITERAL original Cq predicate. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalDegreeOneBudget
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26ActualFailureReadout
open BDL26DecodingGraph
open scoped Classical BigOperators

private def bothCones (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    Word BDL26Field (QDoubleCylinderVertex P q S) := fun v => match v.2 with
  | .inl (.inl _) => 1
  | _ => 0

private theorem actual_local_delta_transport (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    (literalContract P A R S).rx_local_complexes.cqDelta1 q
      (wordEquiv (qCorrectionEquiv P S q) w)=
      wordEquiv (qSyndromeEquiv P S q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) := by
  funext e
  obtain ⟨edge,rfl⟩ := (qSyndromeEquiv P S q).surjective e
  change wordLinearMapTranspose (localCq P S q).boundary2
    (wordEquiv (qCorrectionEquiv P S q) w) _=_
  erw [localCq_delta1_apply]
  rw [LinearEquiv.symm_apply_apply]
  simp only [wordEquiv_apply,Equiv.symm_apply_apply]

end CriticalDegreeOneBudget
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- The raw word is a coordinate view of the original budget-constrained Classical.choose result. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private noncomputable def originalChoice (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  let C := literalContract P A R S
  let E := wordEquiv (qCorrectionEquiv P S q)
  E.symm (Classical.choose (C.local_boundary_weight_budgets.cq q
    (C.rx_local_complexes.cqDelta1 q (E w)) ⟨E w,rfl⟩))

private theorem originalChoice_spec (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (originalChoice P A R S q w)=
        wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w ∧
    (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S
      (originalChoice P A R S q w)))≤
        HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) := by
  let C := literalContract P A R S
  let E := wordEquiv (qCorrectionEquiv P S q)
  let f := Classical.choose (C.local_boundary_weight_budgets.cq q
    (C.rx_local_complexes.cqDelta1 q (E w)) ⟨E w,rfl⟩)
  have hf := Classical.choose_spec (C.local_boundary_weight_budgets.cq q
    (C.rx_local_complexes.cqDelta1 q (E w)) ⟨E w,rfl⟩)
  have hd : wordLinearMapTranspose (localCq P S q).boundary2 f=
      wordLinearMapTranspose (localCq P S q).boundary2 (E w) := hf.1
  refine ⟨?_,?_⟩
  · funext edge
    have he := congrFun hd (qSyndromeEquiv P S q edge)
    erw [localCq_delta1_apply,localCq_delta1_apply,LinearEquiv.symm_apply_apply] at he
    exact he
  · have hflow : HammingWeight (qFlow P S q (E.symm f))≤
        HammingWeight (wordLinearMapTranspose (localCq P S q).boundary2 (E w)) := hf.2
    erw [qFlow_weight,BDL26ReplacementSupport.rxQOutgoing_sum_weight] at hflow
    have hs : wordLinearMapTranspose (localCq P S q).boundary2 (E w)=
        wordEquiv (qSyndromeEquiv P S q)
          (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) := by
      funext e
      obtain ⟨edge,rfl⟩ := (qSyndromeEquiv P S q).surjective e
      erw [localCq_delta1_apply,LinearEquiv.symm_apply_apply]
      simp only [wordEquiv_apply,Equiv.symm_apply_apply]
    erw [hs,wordEquiv_weight] at hflow
    exact hflow

private theorem originalChoice_equal_syndrome (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w v : Word BDL26Field (QDoubleCylinderVertex P q S))
    (h : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) v) :
    originalChoice P A R S q w=originalChoice P A R S q v := by
  let E := wordEquiv (qCorrectionEquiv P S q)
  unfold originalChoice
  apply congrArg E.symm
  apply CriticalOldXQueries.original_choose_Cq_equal_delta P A R S q (E w) (E v)
  erw [CriticalDegreeOneBudget.actual_local_delta_transport,
    CriticalDegreeOneBudget.actual_local_delta_transport,h]

private theorem originalChoice_whole_constant (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    ∃ b : BDL26Field,originalChoice P A R S q w=fun v => w v+b := by
  have hd := (originalChoice_spec P A R S q w).1
  have hz : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (originalChoice P A R S q w+w)=0 := by
    rw [map_add,hd,repair3_word_add_self]
  let root : QDoubleCylinderVertex P q S := (0,.inl (.inl ()))
  let b := (originalChoice P A R S q w+w) root
  have hc := word_eq_root_of_graphCoboundary_eq_zero
    (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S) root
    (qDoubleCylinderPath P A.toTannerSquareAdmissible q S)
    (originalChoice P A R S q w+w) hz
  refine ⟨b,?_⟩
  funext v
  have hv := hc v
  change originalChoice P A R S q w v+w v=b at hv
  calc
    originalChoice P A R S q w v=
      (originalChoice P A R S q w v+w v)+w v := by
        erw [add_assoc,repair3_scalar_add_self,add_zero]
    _=b+w v := congrArg (fun a => a+w v) hv
    _=w v+b := add_comm _ _

/-- Sufficient ACTUAL original witness conditions, not a minimum assumption:
zero terminal flow and syndrome strictly below the complement's flow force
this entire returned word. The conditions are discharged for 0/cones below. -/
private theorem originalChoice_forced_zero_flow (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (hflow : (∑ z : QStarEdge P q,HammingWeight
      (rxQZDegreeOne P q z.val z.property S w))=0)
    (hsyndrome : HammingWeight (wordLinearMapTranspose
      (qDoubleCylinderBoundary1 P q S) w)<2*Fintype.card (QStarEdge P q)) :
    originalChoice P A R S q w=w := by
  obtain ⟨b,hb⟩ := originalChoice_whole_constant P A R S q w
  rcases BDL26RXQEdgePairTransport.bit_cases b with rfl | rfl
  · simpa only [add_zero] using hb
  · have hc := qLocal_terminal_weight_complement P q S w
    erw [hflow,zero_add] at hc
    have hbound := (originalChoice_spec P A R S q w).2
    erw [hb,hc] at hbound
    omega

private def coneWord (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) : Word BDL26Field (QDoubleCylinderVertex P q S) :=
  canonicalBasisWord (copy,.inl (.inl ()))

private theorem coneWord_flow_zero (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy : BDL26FiniteTannerSquare.Two) :
    (∑ z : QStarEdge P q,HammingWeight
      (rxQZDegreeOne P q z.val z.property S (coneWord P q S copy)))=0 := by
  have hz (z : QStarEdge P q) :
      rxQZDegreeOne P q z.val z.property S (coneWord P q S copy)=0 := by
    funext c
    simp [coneWord,basis_value,rxQZDegreeOne,wordPullback_apply]
  simp_rw [hz]
  simp

private theorem repair4_cone_outer (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy c : BDL26FiniteTannerSquare.Two)
    (z : QStarEdge P q) (k : Fin S.half) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (coneWord P q S copy)
      (Sum.inl (c,z,k))=(if c=copy ∧ k.val=0 then 1 else 0) := by
  rw [qLocalCoboundary_apply]
  by_cases hstart : k.val=0 <;> by_cases hend : k.val+1=S.half
  all_goals
    simp_all [coneWord,basis_value,qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd,
      qSubdivisionEdgeStart,qSubdivisionEdgeEnd,qStarEdgeStart,qStarEdgeEnd]

private theorem repair4_cone_bridge (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (coneWord P q S copy)
      (Sum.inr z)=0 := by
  rw [qLocalCoboundary_apply]
  simp [coneWord,basis_value,qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd,qStarEdgeEnd]

private theorem coneWord_syndrome_le_degree (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy : BDL26FiniteTannerSquare.Two) :
    HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (coneWord P q S copy))≤Fintype.card (QStarEdge P q) := by
  let first : QStarEdge P q → QDoubleCylinderEdge P q S :=
    fun z => Sum.inl (copy,z,⟨0,S.half_pos⟩)
  have hs : hammingSupport (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (coneWord P q S copy))⊆Finset.univ.image first := by
    intro edge he
    have hv : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (coneWord P q S copy) edge≠0 := (Finset.mem_filter.mp he).2
    rcases edge with ⟨c,z,k⟩ | z
    · rw [repair4_cone_outer] at hv
      have hc : c=copy ∧ k.val=0 := by
        by_contra h
        exact hv (if_neg h)
      rcases hc with ⟨hcopy,hk⟩
      subst c
      refine Finset.mem_image.mpr ⟨z,Finset.mem_univ _,?_⟩
      exact congrArg (fun k : Fin S.half =>
        (Sum.inl (copy,z,k) : QDoubleCylinderEdge P q S))
          (show (⟨0,S.half_pos⟩ : Fin S.half)=k from Fin.ext hk.symm)
    · rw [repair4_cone_bridge] at hv
      exact False.elim (hv rfl)
  calc
    _=(hammingSupport (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (coneWord P q S copy))).card := HammingWeight_eq_card_hammingSupport _
    _≤(Finset.univ.image first).card := Finset.card_le_card hs
    _≤(Finset.univ : Finset (QStarEdge P q)).card := Finset.card_image_le
    _=Fintype.card (QStarEdge P q) := Finset.card_univ

/-- The SAME original Classical.choose actually fixes each raw cone basis,
at BOTH copies, every genuine q and EVERY odd scale. This is an actual
returned value, derived only from the original whole graph and flow budget. -/
private theorem actual_original_choice_fixes_cone (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (copy : BDL26FiniteTannerSquare.Two) :
    originalChoice P A R S q (coneWord P q S copy)=coneWord P q S copy := by
  apply originalChoice_forced_zero_flow P A R S q
  · exact coneWord_flow_zero P q S copy
  · have hp : 0<Fintype.card (QStarEdge P q) :=
      Fintype.card_pos_iff.mpr ⟨A.toTannerSquareAdmissible.qzRoot q⟩
    have hs := coneWord_syndrome_le_degree P q S copy
    omega

private theorem actual_original_choice_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) : originalChoice P A R S q 0=0 := by
  apply originalChoice_forced_zero_flow P A R S q
  · simp [rxQZDegreeOne]
  · have hp : 0<Fintype.card (QStarEdge P q) :=
      Fintype.card_pos_iff.mpr ⟨A.toTannerSquareAdmissible.qzRoot q⟩
    erw [map_zero]
    simp only [HammingWeight, hammingSupport,Pi.zero_apply,ne_eq,not_true_eq_false,
      Finset.filter_false,Finset.card_empty]
    omega
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Returned-value response calculations for the fixed original selector. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private theorem originalChoice_add_constant (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (b : BDL26Field) :
    originalChoice P A R S q (fun v => w v+b)=originalChoice P A R S q w := by
  apply originalChoice_equal_syndrome P A R S q
  exact qLocalCoboundary_add_constant P q S w b

end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- A conditional response calculation at the same valid background and physical error, with the complete original accumulated potential. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout BDL26IndexedDecoder
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26DecodingGraph
open scoped Classical BigOperators

section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

/- A true ORIGINAL response switch conditional on a concrete actual-word
condition. The physical pair is never independently selected. No statement
here asserts that the condition occurs for an actual history, that other
ports can be selected freely, or that either full decoder has chi=1. -/
end
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Consequences of the original fixed selector choices. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private def terminalWord (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) := canonicalBasisWord (copy,.inl (.inr z))

end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- At degree three, budget violation excludes the sole other representative and forces the original returned word. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26DecodingGraph
open scoped Classical BigOperators

private theorem sum_three_leaves {V : Type} [Fintype V] [DecidableEq V]
    (a b c : V) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z=c) (f : V → Nat) :
    (∑ z : V,f z)=f a+f b+f c := by
  have hu : (Finset.univ : Finset V)={a,b,c} := by
    ext z
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    exact cover z
  change Finset.univ.sum f=_
  erw [hu]
  simp [hab,hac,hbc,add_assoc]

private theorem hamming_weight_two (f : Word BDL26Field BDL26FiniteTannerSquare.Two) :
    HammingWeight f=(if f 0=0 then 0 else 1)+(if f 1=0 then 0 else 1) := by
  simp [HammingWeight,hammingSupport,Finset.card_filter,Fin.sum_univ_two]

private def otherCopy (c : BDL26FiniteTannerSquare.Two) :
    BDL26FiniteTannerSquare.Two := if c=0 then 1 else 0

private def pairShift (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (ca cb : BDL26FiniteTannerSquare.Two) (a b : QStarEdge P q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  terminalWord P q S ca a+terminalWord P q S cb b

private def sharpQuery (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (ca cb : BDL26FiniteTannerSquare.Two) (a b c : QStarEdge P q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  if ca=cb then
    coneWord P q S (otherCopy ca)+terminalWord P q S (otherCopy ca) a+
      terminalWord P q S (otherCopy ca) b
  else coneWord P q S cb+terminalWord P q S cb a+terminalWord P q S cb c

private def firstArm (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    QDoubleCylinderEdge P q S := .inl (copy,z,⟨0,S.half_pos⟩)

private theorem halfOne_delta_arm (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (hh : S.half=1) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w (firstArm P q S copy z)=
      w (copy,.inl (.inl ()))+w (copy,.inl (.inr z)) := by
  erw [qLocalCoboundary_apply]
  simp [firstArm,qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd,
    qSubdivisionEdgeStart,qSubdivisionEdgeEnd,qStarEdgeStart,qStarEdgeEnd,hh]

private theorem delta_bridge (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (z : QStarEdge P q) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w (.inr z)=
      w (0,.inl (.inr z))+w (1,.inl (.inr z)) := by
  erw [qLocalCoboundary_apply]
  rfl

private theorem card_triple_le_three {V : Type} [DecidableEq V] (a b c : V) :
    ({a,b,c} : Finset V).card≤3 := by
  have hbc : ({b,c} : Finset V).card≤2 :=
    (Finset.card_insert_le b {c}).trans (by simp)
  exact (Finset.card_insert_le a {b,c}).trans (by omega)

/- Exact cost2/cost4 and COMPLETE three-edge syndrome supports. Copy cases
are actual constructors of the original graph, never a new finite model. -/
private theorem originalChoice_forced_cost_two_degree_three
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : P.Q)
    (hd : Fintype.card (QStarEdge P q)=3) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (hf : (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S w))=2)
    (hs : HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w)≤3) :
    originalChoice P A R S q w=w := by
  obtain ⟨b,hb⟩ := originalChoice_whole_constant P A R S q w
  rcases BDL26RXQEdgePairTransport.bit_cases b with rfl | rfl
  · simpa only [add_zero] using hb
  · have hc := qLocal_terminal_weight_complement P q S w
    erw [hf,hd] at hc
    have hbudget := (originalChoice_spec P A R S q w).2
    erw [hb] at hbudget
    omega

/- Genuine degree3 switch at one explicit FIXED k equal to two ACTUAL
selected terminal-basis outputs. Both original T values in the forced query
are derived from the true budgets; no minimum or chosen-value premise. -/
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Original two-Cx-call reduction for one physical X-local perturbation at an arbitrary valid background. No chooser linearity is assumed. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalPhysicalCx
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26ActualFailureReadout BDL26DecodingGraph
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

end
end CriticalPhysicalCx
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- A physical basis contributes to at most one actual syndrome edge at each Q owner. The literal q-to-X cylinder embedding retains both copy and vertical tags at every odd scale. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalPhysicalCx
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26ActualFailureReadout BDL26DecodingGraph
open scoped Classical BigOperators

end CriticalPhysicalCx
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Whole actual-C3 response with one physical basis, an arbitrary valid background, both original Cx/Cq totals and the complete accumulated potential. The final implication is restricted to a zero-Cx background. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Canonical record dictionaries only. Imported definition transparency is
unchanged; proof-local type views use explicit projections and transports. -/
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalPhysicalCx
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (S : OddScale)
local notation "P" => ConstructionState.presentation (BDL26DecodingGraph.state S 2)
local notation "A" => ConstructionState.admissible (BDL26DecodingGraph.state S 2)
local notation "R" => ConstructionState.regular (BDL26DecodingGraph.state S 2)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

end
end CriticalPhysicalCx
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Actual four-port star geometry for the original decoder and its unchanged local choices. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace ActualCriticalStarGeometry

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RXLocalReplacement BDL26ActualFailureReadout
open scoped Classical
noncomputable section

/-- The opposite actual corner; the two-element fact is independent of scale. -/
private def opposite (c : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two := if c=0 then 1 else 0
private theorem opposite_ne (c : BDL26FiniteTannerSquare.Two) : opposite c ≠ c := by
  exact (by decide : ∀ c : Fin 2, (if c=0 then 1 else 0) ≠ c) c

/-- Perfect pairing supplies another real shared Q, not a chosen substitute
link. Regularity is not needed for this elementary pairing consequence. -/
private theorem shared_other (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (q : P.Q) (hx : P.xq x q=true) (hz : P.qz q z=true) :
    ∃ r : P.Q, r≠q ∧ P.xq x r=true ∧ P.qz r z=true := by
  let a : SharedQ P.data x z := ⟨q,by simpa using And.intro hx hz⟩
  let fc := (P.faceCornerEquiv x z).symm a
  have hq : P.faceQ fc.1.val fc.2=q :=
    congrArg Subtype.val ((P.faceCornerEquiv x z).apply_symm_apply a)
  refine ⟨P.faceQ fc.1.val (opposite fc.2),?_,?_,?_⟩
  · intro he
    have hc : opposite fc.2=fc.2 :=
      P.faceQ_injective fc.1.val (he.trans hq.symm)
    exact opposite_ne fc.2 hc
  · simpa only [fc.1.property.1] using P.data.faceQ_xq fc.1.val (opposite fc.2)
  · simpa only [fc.1.property.2] using P.data.faceQ_qz fc.1.val (opposite fc.2)

/-- Every full RZ old-X neighbour is literally an old incident Q terminal.
This is a statement about the whole physical Q carrier, not its parity. -/
private theorem oldX_neighbour_terminal (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X) (copy : BDL26FiniteTannerSquare.Two)
    (q : RZQ P S) (hq : rzXQIncidence P A S (.inr (x,copy)) q=true) :
    ∃ r : P.Q, ∃ hr : P.xq x r=true,
      q=.inr ⟨r,(copy,.inl (.inr ⟨x,hr⟩))⟩ := by
  classical
  rcases q with ⟨z,e⟩ | ⟨r,v⟩
  · change false=true at hq
    cases hq
  · change decide (∃ f : P.Face, ∃ c : BDL26FiniteTannerSquare.Two,
      P.faceX f=x ∧ oldXFaceQ P S c (f,copy)=.inr ⟨r,v⟩)=true at hq
    obtain ⟨f,c,hx,he⟩ := of_decide_eq_true hq
    have hr : P.xq x (P.faceQ f c)=true := by
      simpa only [hx] using P.data.faceQ_xq f c
    refine ⟨P.faceQ f c,hr,?_⟩
    simpa only [oldXFaceQ,hx] using he.symm

private abbrev P (S : OddScale) := (state S 2).presentation
private noncomputable abbrev PA (S : OddScale) := (state S 2).admissible
private def x (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).X :=
  .inr (seedQNode S j,copy)
private def r (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Q :=
  CriticalOldXQueries.criticalTerminal S j copy (criticalRadial S j)
    (criticalRadial_incident S j)
private def b (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Q :=
  CriticalOldXQueries.criticalTerminal S j copy (criticalBoundary S j)
    (criticalBoundary_incident S j)
private def v (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Q :=
  CriticalOldXQueries.criticalTerminal S j copy (criticalVertical S j)
    (criticalVertical_incident S j)
private def g (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Q :=
  CriticalOldXQueries.criticalTerminal S j copy (gammaCone S j)
    (seedQNode_incident S j)

/-- Actual full-star completeness. No converse is inferred from parity. -/
private theorem full_four_cover (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (q : (P S).Q) (hq : (P S).xq (x S j copy) q=true) :
    q=r S j copy ∨ q=b S j copy ∨ q=v S j copy ∨ q=g S j copy := by
  have hraw : rzXQIncidence (RawOne S) (rxState S baseState).admissible.toTannerSquareAdmissible S
      (.inr (seedQNode S j,copy)) q=true := hq
  obtain ⟨a,ha,rfl⟩ := oldX_neighbour_terminal (RawOne S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S (seedQNode S j) copy q hraw
  rcases critical_four_neighbours S j a ha with h | h | h | h
  · subst a; exact Or.inl rfl
  · subst a; exact Or.inr (Or.inl rfl)
  · subst a; exact Or.inr (Or.inr (Or.inl rfl))
  · subst a; exact Or.inr (Or.inr (Or.inr rfl))

private theorem terminal_incident (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true) :
    (P S).xq (x S j copy)
      (CriticalOldXQueries.criticalTerminal S j copy a ha)=true := by
  let shared : SharedQ (RawOne S).data (seedQNode S j)
      ((rxState S baseState).admissible.qzRoot a).val :=
    ⟨a,by
      have hz := ((rxState S baseState).admissible.qzRoot a).property
      simpa using And.intro ha hz⟩
  let fc := ((RawOne S).faceCornerEquiv _ _).symm shared
  have he : (RawOne S).faceQ fc.1.val fc.2=a :=
    congrArg Subtype.val (((RawOne S).faceCornerEquiv _ _).apply_symm_apply shared)
  change decide (∃ f : (RawOne S).Face, ∃ c : BDL26FiniteTannerSquare.Two,
    (RawOne S).faceX f=seedQNode S j ∧
      oldXFaceQ (RawOne S) S c (f,copy)=
        CriticalOldXQueries.criticalTerminal S j copy a ha)=true
  apply decide_eq_true
  refine ⟨fc.1.val,fc.2,fc.1.property.1,?_⟩
  simp only [oldXFaceQ,CriticalOldXQueries.criticalTerminal,fc.1.property.1]
  apply congrArg Sum.inr
  refine Sigma.ext he ?_
  have ht (a a' : (RawOne S).Q) (haa' : a=a')
      (h0 : (RawOne S).xq (seedQNode S j) a=true)
      (h1 : (RawOne S).xq (seedQNode S j) a'=true) :
      HEq ((copy,.inl (.inr ⟨seedQNode S j,h0⟩)) :
        QDoubleCylinderVertex (transposePresentation (RawOne S)) a S)
        ((copy,.inl (.inr ⟨seedQNode S j,h1⟩)) :
          QDoubleCylinderVertex (transposePresentation (RawOne S)) a' S) := by
    cases haa'
    rfl
  exact ht _ _ he _ _

/-- The actual RZ embedding of the original unique check, with its complete
vertex/copy tags. The first Sigma coordinate remains exactly the old check. -/
private def shiftedZ (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz a z=true) : (P S).Z :=
  ((shiftedQZNeighbourEquiv (RawOne S) (rxState S baseState).admissible.toTannerSquareAdmissible S a
    (copy,.inl (.inr ⟨seedQNode S j,ha⟩))) ⟨z,hz⟩).val

private theorem shiftedZ_incident (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz a z=true) :
    (P S).qz (CriticalOldXQueries.criticalTerminal S j copy a ha)
      (shiftedZ S j copy a ha z hz)=true :=
  ((shiftedQZNeighbourEquiv (RawOne S) (rxState S baseState).admissible.toTannerSquareAdmissible S a
    (copy,.inl (.inr ⟨seedQNode S j,ha⟩))) ⟨z,hz⟩).property

private theorem shiftedZ_unique (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true)
    (z : (RawOne S).Z) (hz : (RawOne S).qz a z=true)
    (hu : ∀ z', (RawOne S).qz a z'=true → z'=z)
    (t : (P S).Z)
    (ht : (P S).qz (CriticalOldXQueries.criticalTerminal S j copy a ha) t=true) :
    t=shiftedZ S j copy a ha z hz := by
  let E := shiftedQZNeighbourEquiv (RawOne S) (rxState S baseState).admissible.toTannerSquareAdmissible S a
    (copy,.inl (.inr ⟨seedQNode S j,ha⟩))
  let s := E.symm ⟨t,ht⟩
  have hs : s=⟨z,hz⟩ := Subtype.ext (hu s.val s.property)
  have he := congrArg Subtype.val (E.apply_symm_apply ⟨t,ht⟩)
  have hEs : E s=E ⟨z,hz⟩ := congrArg E hs
  have hv := congrArg Subtype.val hEs
  exact he.symm.trans hv

private def zr (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Z :=
  shiftedZ S j copy (criticalRadial S j) (criticalRadial_incident S j)
    (seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩)
    (seedRadial_degree_one S j _).1
private def zv (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Z :=
  shiftedZ S j copy (criticalVertical S j) (criticalVertical_incident S j)
    (criticalVerticalCheck S j) (criticalVertical_degree_one S j).1
private def zg (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Z :=
  shiftedZ S j copy (gammaCone S j) (seedQNode_incident S j)
    (seedConeCheck S j) (seedCone_degree_one S j).1

private theorem leaf_unique (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    ((P S).qz (r S j copy) (zr S j copy)=true ∧
      ∀ z, (P S).qz (r S j copy) z=true → z=zr S j copy) ∧
    ((P S).qz (v S j copy) (zv S j copy)=true ∧
      ∀ z, (P S).qz (v S j copy) z=true → z=zv S j copy) ∧
    ((P S).qz (g S j copy) (zg S j copy)=true ∧
      ∀ z, (P S).qz (g S j copy) z=true → z=zg S j copy) := by
  exact ⟨⟨shiftedZ_incident S j copy _ _ _ _,
    shiftedZ_unique S j copy _ _ _ _ (seedRadial_degree_one S j _).2⟩,
    ⟨shiftedZ_incident S j copy _ _ _ _,
      shiftedZ_unique S j copy _ _ _ _ (criticalVertical_degree_one S j).2⟩,
    ⟨shiftedZ_incident S j copy _ _ _ _,
      shiftedZ_unique S j copy _ _ _ _ (seedCone_degree_one S j).2⟩⟩

private theorem checks_distinct (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    zr S j copy≠zv S j copy ∧ zr S j copy≠zg S j copy ∧
      zv S j copy≠zg S j copy := by
  constructor
  · intro h
    have hs := congrArg (fun z : (P S).Z => z.1) h
    change seedRadialCheck S j _=criticalVerticalCheck S j at hs
    cases hs
  constructor
  · intro h
    have hs := congrArg (fun z : (P S).Z => z.1) h
    change seedRadialCheck S j _=seedConeCheck S j at hs
    cases hs
  · intro h
    have hs := congrArg (fun z : (P S).Z => z.1) h
    change criticalVerticalCheck S j=seedConeCheck S j at hs
    cases hs

/-- The actual three leaf labels and the hub are distinct by their original
sum tags; this is not inferred from degree counts. -/
private theorem ports_distinct (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    r S j copy≠b S j copy ∧ r S j copy≠v S j copy ∧
    r S j copy≠g S j copy ∧ b S j copy≠v S j copy ∧
    b S j copy≠g S j copy ∧ v S j copy≠g S j copy := by
  have take (a a' : (RawOne S).Q)
      (ha : (RawOne S).xq (seedQNode S j) a=true)
      (ha' : (RawOne S).xq (seedQNode S j) a'=true)
      (he : CriticalOldXQueries.criticalTerminal S j copy a ha=
        CriticalOldXQueries.criticalTerminal S j copy a' ha') : a=a' := by
    exact congrArg (fun q : (P S).Q => match q with
      | .inl _ => a
      | .inr q => q.1) he
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro h; exact criticalRadial_ne_boundary S j (take _ _ _ _ h)
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalRadial,gammaRadial,criticalVertical] at h'; cases h'
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalRadial,gammaRadial,gammaCone] at h'; cases h'
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalBoundary,criticalVertical] at h'; cases h'
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalBoundary,gammaCone] at h'; cases h'
  · intro h; have h' := take _ _ _ _ h
    dsimp only [criticalVertical,gammaCone] at h'; cases h'

/-- The COMPLETE actual hub link, derived from pairing plus the already
proved full star and three unique leaves. No extra degree premise is used. -/
private theorem hub_neighbours (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (z : (P S).Z) :
    (P S).qz (b S j copy) z=true ↔
      z=zr S j copy ∨ z=zv S j copy ∨ z=zg S j copy := by
  have hr := leaf_unique S j copy
  have hd := ports_distinct S j copy
  have hz := checks_distinct S j copy
  have hx (a : (RawOne S).Q) (ha : (RawOne S).xq (seedQNode S j) a=true) :=
    terminal_incident S j copy a ha
  have hxR : (P S).xq (x S j copy) (r S j copy)=true := hx _ _
  have hxB : (P S).xq (x S j copy) (b S j copy)=true := hx _ _
  have hxV : (P S).xq (x S j copy) (v S j copy)=true := hx _ _
  have hxG : (P S).xq (x S j copy) (g S j copy)=true := hx _ _
  constructor
  · intro hb
    obtain ⟨q,hne,hqx,hqz⟩ := shared_other (P S) (x S j copy) z (b S j copy) hxB hb
    rcases full_four_cover S j copy q hqx with he | he | he | he
    · exact Or.inl (hr.1.2 z (he ▸ hqz))
    · exact False.elim (hne he)
    · exact Or.inr (Or.inl (hr.2.1.2 z (he ▸ hqz)))
    · exact Or.inr (Or.inr (hr.2.2.2 z (he ▸ hqz)))
  · intro hz'
    have pairR : (P S).qz (b S j copy) (zr S j copy)=true := by
      obtain ⟨q,hne,hqx,hqz⟩ := shared_other (P S) (x S j copy) _ (r S j copy) hxR hr.1.1
      rcases full_four_cover S j copy q hqx with he | he | he | he
      · exact False.elim (hne he)
      · exact he ▸ hqz
      · exact False.elim (hz.1 (hr.2.1.2 _ (he ▸ hqz)))
      · exact False.elim (hz.2.1 (hr.2.2.2 _ (he ▸ hqz)))
    have pairV : (P S).qz (b S j copy) (zv S j copy)=true := by
      obtain ⟨q,hne,hqx,hqz⟩ := shared_other (P S) (x S j copy) _ (v S j copy) hxV hr.2.1.1
      rcases full_four_cover S j copy q hqx with he | he | he | he
      · exact False.elim (hz.1 (hr.1.2 _ (he ▸ hqz)).symm)
      · exact he ▸ hqz
      · exact False.elim (hne he)
      · exact False.elim (hz.2.2 (hr.2.2.2 _ (he ▸ hqz)))
    have pairG : (P S).qz (b S j copy) (zg S j copy)=true := by
      obtain ⟨q,hne,hqx,hqz⟩ := shared_other (P S) (x S j copy) _ (g S j copy) hxG hr.2.2.1
      rcases full_four_cover S j copy q hqx with he | he | he | he
      · exact False.elim (hz.2.1 (hr.1.2 _ (he ▸ hqz)).symm)
      · exact he ▸ hqz
      · exact False.elim (hz.2.2 (hr.2.1.2 _ (he ▸ hqz)).symm)
      · exact False.elim (hne he)
    rcases hz' with rfl | rfl | rfl
    · exact pairR
    · exact pairV
    · exact pairG


/-- Literal shared-terminal equality in the ORIGINAL root-parameterized
Q-to-X maps. The arbitrary two Q roots disappear only at this terminal branch. -/
private theorem shared_terminal_same_image (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) (q q' : P.Q)
    (hx : P.xq x q=true) (hx' : P.xq x q'=true)
    (z : P.Z) (hz : P.qz q z=true) (hz' : P.qz q' z=true)
    (root : QStarEdge P q) (root' : QStarEdge P q') (copy : BDL26FiniteTannerSquare.Two) :
    qToXDoubleCylinderVertexAtRoot P q x hx S root (copy,.inl (.inr ⟨z,hz⟩))=
      qToXDoubleCylinderVertexAtRoot P q' x hx' S root' (copy,.inl (.inr ⟨z,hz'⟩)) := by
  apply Prod.ext
  · rfl
  · apply congrArg Sum.inl
    apply Subtype.ext
    rfl

/- Use the already-proved actual Q-edge embedding injectivity; the raw and
admissible maps have identical two constructor clauses. -/
private def faceFromShared (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (q : P.Q) (hx : P.xq x q=true) (hz : P.qz q z=true) : P.Face :=
  (((P.faceCornerEquiv x z).symm ⟨q,by simpa using And.intro hx hz⟩).1).val
private theorem faceFromShared_X (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (q : P.Q) (hx : P.xq x q=true) (hz : P.qz q z=true) :
    P.faceX (faceFromShared P x z q hx hz)=x :=
  (((P.faceCornerEquiv x z).symm ⟨q,by simpa using And.intro hx hz⟩).1).property.1
private theorem faceFromShared_Z (P : TannerSquarePresentation) (x : P.X) (z : P.Z)
    (q : P.Q) (hx : P.xq x q=true) (hz : P.qz q z=true) :
    P.faceZ (faceFromShared P x z q hx hz)=z :=
  (((P.faceCornerEquiv x z).symm ⟨q,by simpa using And.intro hx hz⟩).1).property.2

private def fr (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Face :=
  faceFromShared (P S) (x S j copy) (zr S j copy) (r S j copy)
    (terminal_incident S j copy _ _) (leaf_unique S j copy).1.1
private def fv (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Face :=
  faceFromShared (P S) (x S j copy) (zv S j copy) (v S j copy)
    (terminal_incident S j copy _ _) (leaf_unique S j copy).2.1.1
private def fg (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : (P S).Face :=
  faceFromShared (P S) (x S j copy) (zg S j copy) (g S j copy)
    (terminal_incident S j copy _ _) (leaf_unique S j copy).2.2.1

/- EVERY actual face over this X has one of the three original Z ends.
If its first corner is the hub, its distinct second corner is a genuine leaf. -/
private def cr (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two :=
  (((P S).faceCornerEquiv (x S j copy) (zr S j copy)).symm
    ⟨r S j copy,by
      change ((P S).xq (x S j copy) (r S j copy) &&
         (P S).qz (r S j copy) (zr S j copy))=true
      have hx : (P S).xq (x S j copy) (r S j copy)=true :=
        terminal_incident S j copy _ _
      have hz : (P S).qz (r S j copy) (zr S j copy)=true :=
        (leaf_unique S j copy).1.1
      rw [hx,hz]
      rfl⟩).2

private theorem fr_leaf_corner (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    (P S).faceQ (fr S j copy) (cr S j copy)=r S j copy := by
  exact congrArg Subtype.val
    (((P S).faceCornerEquiv (x S j copy) (zr S j copy)).apply_symm_apply
      ⟨r S j copy,by
        change ((P S).xq (x S j copy) (r S j copy) &&
           (P S).qz (r S j copy) (zr S j copy))=true
        have hx : (P S).xq (x S j copy) (r S j copy)=true :=
          terminal_incident S j copy _ _
        have hz : (P S).qz (r S j copy) (zr S j copy)=true :=
          (leaf_unique S j copy).1.1
        rw [hx,hz]
        rfl⟩)

private theorem fr_hub_corner (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    (P S).faceQ (fr S j copy) (opposite (cr S j copy))=b S j copy := by
  let q := (P S).faceQ (fr S j copy) (opposite (cr S j copy))
  have hfx : (P S).faceX (fr S j copy)=x S j copy :=
    faceFromShared_X (P S) (x S j copy) (zr S j copy) (r S j copy)
      (terminal_incident S j copy _ _) (leaf_unique S j copy).1.1
  have hfz : (P S).faceZ (fr S j copy)=zr S j copy :=
    faceFromShared_Z (P S) (x S j copy) (zr S j copy) (r S j copy)
      (terminal_incident S j copy _ _) (leaf_unique S j copy).1.1
  have hx : (P S).xq (x S j copy) q=true :=
    (congrArg (fun xx : (P S).X => (P S).xq xx q) hfx).symm.trans
      ((P S).data.faceQ_xq (fr S j copy) (opposite (cr S j copy)))
  have hz : (P S).qz q (zr S j copy)=true :=
    (congrArg (fun zz : (P S).Z => (P S).qz q zz) hfz).symm.trans
      ((P S).data.faceQ_qz (fr S j copy) (opposite (cr S j copy)))
  have hne : q≠r S j copy := by
    intro he
    apply opposite_ne (cr S j copy)
    exact (P S).faceQ_injective (fr S j copy)
      (he.trans (fr_leaf_corner S j copy).symm)
  have hr := leaf_unique S j copy
  have hd := checks_distinct S j copy
  rcases full_four_cover S j copy q hx with he | he | he | he
  · exact False.elim (hne he)
  · exact he
  · exact False.elim (hd.1 (hr.2.1.2 _ (he ▸ hz)))
  · exact False.elim (hd.2.1 (hr.2.2.2 _ (he ▸ hz)))

end
end ActualCriticalStarGeometry
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Full-word local-search and dual-readout calculations for both branches of the original local-first decoder. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace ActualCriticalStarGeometry

open MultiscaleDecoder BDL26FiniteTannerSquare BDL26FiniteAlternatingCore
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26LevelTwoCode
open BDL26ActualFailureReadout BDL26DecodingGraph BDL26TannerLocalRegularity
open scoped Classical BigOperators
noncomputable section

/-- The original Tanner coboundaries square to zero, directly from the original
perfect-pairing theorem. No cohomology certificate is a premise. -/
private theorem tanner_d1_d0 (T : TannerSquarePresentation) (a : Word F T.X) :
    tannerCoboundary1 T (tannerCoboundary0 T a)=0 := by
  ext z
  change (∑ q : T.Q, (∑ x : T.X,
    a x * if T.xq x q=true then 1 else 0) *
      if T.qz q z=true then 1 else 0)=0
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  calc
    (∑ q : T.Q, (a x * if T.xq x q=true then 1 else 0) *
        if T.qz q z=true then 1 else 0)=
      a x * ∑ q : T.Q, (if T.xq x q=true then 1 else 0) *
        if T.qz q z=true then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact mul_assoc _ _ _
    _=0 := by
      have hi : (∑ q : T.Q, (if T.xq x q=true then (1 : F) else 0) *
          if T.qz q z=true then 1 else 0)=0 := by
        calc
          _=∑ q : T.Q, if T.xq x q && T.qz q z then (1 : F) else 0 := by
            apply Finset.sum_congr rfl
            intro q _
            by_cases hx : T.xq x q=true <;> by_cases hz : T.qz q z=true <;>
              simp [hx,hz]
          _=0 := sharedQ_indicator_sum_zero T x z
      rw [hi,mul_zero]

/-- A local physical preimage has at most one original Q parity label. -/
private theorem local_parity_one_label (S : OddScale) (e : Word F (RawTwo S).Q)
    (he : levelTwoLocalError S e) :
    ∃ a : (RawOne S).Q, ∀ q, q≠a → rzQParity (RawOne S) S e q=0 := by
  obtain ⟨owner,ho⟩ := (levelTwoLocalError_iff_owner S e).mp he
  let a := qCoordinateOfOwner (RawOne S) (criticalRadial S 0) owner
  refine ⟨a,?_⟩
  intro q hq
  apply rzQParity_zero_of_other_owner (RawOne S) S e owner ho q
  intro h
  exact hq (qCoordinateOfOwner_of_eq (RawOne S) (criticalRadial S 0) q owner h)

/-- The original cone row's X-local contributor is exactly the original
boundary port. Together with any X-local row this excludes Q-cylinder vertices.
This uses the full actual matrix, not a support-only syndrome model. -/
private theorem BE_column_forces_boundary (S : OddScale) (j : Fin 2)
    (q : (RawOne S).Q)
    (hB : rxBoundary2Matrix baseTannerSquarePresentation S q
      (criticalVerticalCheck S j)=1)
    (hE : rxBoundary2Matrix baseTannerSquarePresentation S q (seedConeCheck S j)=1) :
    q=criticalBoundary S j := by
  change RX1 baseTannerSquarePresentation S at q
  rcases q with ⟨x,e⟩ | ⟨a,w⟩
  · change qDoubleCylinderEdgeXIncidence baseTannerSquarePresentation
      (seedQ j) x S e (.inl (0,(seedZEdge j,⟨0,S.half_pos⟩)))=1 at hE
    have hxq : baseTannerSquarePresentation.xq x (seedQ j)=true := by
      by_contra hn
      change (if h : baseTannerSquarePresentation.xq x (seedQ j)=true then
        if e=qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation
          (seedQ j) x h S (.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))) then
          (1 : F) else 0 else 0)=1 at hE
      rw [dif_neg hn] at hE
      exact zero_ne_one hE
    have hx : x=0 :=
      (by decide : ∀ j : Fin 2, ∀ x : BaseX,
        baseTannerSquarePresentation.xq x (seedQ j)=true → x=0) j x hxq
    subst x
    have he : e=qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation
        (seedQ j) 0 hxq S (.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))) := by
      by_contra hn
      change (if h : baseTannerSquarePresentation.xq 0 (seedQ j)=true then
        if e=qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation
          (seedQ j) 0 h S (.inl (0,(seedZEdge j,⟨0,S.half_pos⟩))) then
          (1 : F) else 0 else 0)=1 at hE
      rw [dif_pos hxq,if_neg hn] at hE
      exact zero_ne_one hE
    rw [he]
    fin_cases j <;> rfl
  · change (0 : F)=1 at hB
    exact False.elim (zero_ne_one hB)

private def oldPair (S : OddScale) (j : Fin 2) : Word F (RawOne S).Q :=
  canonicalBasisWord (criticalRadial S j)+canonicalBasisWord (criticalBoundary S j)

private theorem old_tanner_basis_matrix (S : OddScale)
    (q : (RawOne S).Q) (z : (RawOne S).Z) :
    tannerCoboundary1 (RawOne S) (canonicalBasisWord (F:=F) q) z=
      rxBoundary2Matrix baseTannerSquarePresentation S q z := by
  rw [tannerCoboundary1_canonicalBasis_apply]
  exact (raw_boundary2_view S q z).symm

private theorem oldPair_column (S : OddScale) (j : Fin 2)
    (z : (RawOne S).Z) :
    tannerCoboundary1 (RawOne S) (oldPair S j) z=
      (if z=criticalVerticalCheck S j then 1 else 0)+
      (if z=seedConeCheck S j then 1 else 0) := by
  rw [oldPair,map_add,Pi.add_apply,old_tanner_basis_matrix,old_tanner_basis_matrix]
  have hr : rxBoundary2Matrix baseTannerSquarePresentation S (criticalRadial S j) z=
      if z=seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩ then 1 else 0 :=
    seedRadial_matrix S j ⟨S.half-1,by have := S.half_pos;omega⟩ z
  rw [hr,criticalBoundary_matrix]
  calc
    _=((if z=seedRadialCheck S j _ then (1 : F) else 0)+
       (if z=seedRadialCheck S j _ then 1 else 0))+
      ((if z=criticalVerticalCheck S j then 1 else 0)+
       (if z=seedConeCheck S j then 1 else 0)) := by abel
    _=_ := by rw [ZModModule.add_self,zero_add]

/-- No original complete Q incidence column equals this two-check syndrome. -/
private theorem oldPair_not_single_column (S : OddScale) (j : Fin 2)
    (q : (RawOne S).Q) :
    tannerCoboundary1 (RawOne S) (canonicalBasisWord q) ≠
      tannerCoboundary1 (RawOne S) (oldPair S j) := by
  intro he
  have hBE : criticalVerticalCheck S j≠seedConeCheck S j := by
    intro h; cases h
  have hLB : seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩≠
      criticalVerticalCheck S j := by intro h; cases h
  have hLE : seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩≠
      seedConeCheck S j := by intro h; cases h
  have hB := congrFun he (criticalVerticalCheck S j)
  have hE := congrFun he (seedConeCheck S j)
  rw [oldPair_column,if_pos rfl,if_neg hBE,add_zero] at hB
  rw [oldPair_column,if_pos rfl,if_neg hBE.symm,zero_add] at hE
  have hmB : rxBoundary2Matrix baseTannerSquarePresentation S q
      (criticalVerticalCheck S j)=1 :=
    (old_tanner_basis_matrix S q (criticalVerticalCheck S j)).symm.trans hB
  have hmE : rxBoundary2Matrix baseTannerSquarePresentation S q (seedConeCheck S j)=1 :=
    (old_tanner_basis_matrix S q (seedConeCheck S j)).symm.trans hE
  have hq := BE_column_forces_boundary S j q hmB hmE
  subst q
  have hL := congrFun he (seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩)
  rw [oldPair_column,if_neg hLB,if_neg hLE,zero_add] at hL
  have hb := criticalBoundary_matrix S j
    (seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩)
  rw [if_pos rfl,if_neg hLB,if_neg hLE,add_zero,add_zero] at hb
  have hvalue := (old_tanner_basis_matrix S (criticalBoundary S j)
    (seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩)).trans hb
  exact one_ne_zero (hvalue.symm.trans hL)

private def pairWord (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) : Word F (RawTwo S).Q :=
  (canonicalBasisWord (r S j copy) : Word F (RawTwo S).Q)+
    (canonicalBasisWord (b S j copy) : Word F (RawTwo S).Q)

private theorem pairWord_parity (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    rzQParity (RawOne S) S (pairWord S j copy)=oldPair S j := by
  let vr : QDoubleCylinderVertex (transposePresentation (RawOne S)) (criticalRadial S j) S :=
    (copy,.inl (.inr ⟨seedQNode S j,criticalRadial_incident S j⟩))
  let vb : QDoubleCylinderVertex (transposePresentation (RawOne S)) (criticalBoundary S j) S :=
    (copy,.inl (.inr ⟨seedQNode S j,criticalBoundary_incident S j⟩))
  have hr := rzQParity_qBasis (RawOne S) S (criticalRadial S j) vr
  have hb := rzQParity_qBasis (RawOne S) S (criticalBoundary S j) vb
  change rzQParity (RawOne S) S
    ((canonicalBasisWord (Sum.inr ⟨criticalRadial S j,vr⟩ : RZQ (RawOne S) S))+
     (canonicalBasisWord (Sum.inr ⟨criticalBoundary S j,vb⟩ : RZQ (RawOne S) S)))=oldPair S j
  exact (map_add (rzQParity (RawOne S) S) _ _).trans
    (congrArg₂ (fun a b : Word F (RawOne S).Q => a+b) hr hb)

private theorem pairWord_original_search_none (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    BDL26LevelTwoLocalBranchEndpoint.localSearch S
      (tannerCoboundary1 (RawTwo S) (pairWord S j copy))=none := by
  apply (BDL26LevelTwoLocalBranchEndpoint.localSearch_none_iff S _).mpr
  rintro ⟨e,he,hs⟩
  obtain ⟨a,ha⟩ := local_parity_one_label S e he
  have hsupport : hammingSupport (rzQParity (RawOne S) S e) ⊆ {a} := by
    intro q hq
    apply Finset.mem_singleton.mpr
    by_contra hn
    exact (original_support_mem _ q).mp hq (ha q hn)
  obtain ⟨c,hc⟩ := BDL26RXQEdgePairTransport.scalar_singleton _ a hsupport
  have hproject : tannerCoboundary1 (RawOne S) (rzQParity (RawOne S) S e)=
      tannerCoboundary1 (RawOne S) (oldPair S j) := by
    ext z
    have hez := rzCoboundary1_blockParity (RawOne S) (rxState S baseState).admissible S e z
    have hpz := rzCoboundary1_blockParity (RawOne S) (rxState S baseState).admissible
      S (pairWord S j copy) z
    have hactual : tannerCoboundary1 (RawTwo S) e=
        tannerCoboundary1 (RawTwo S) (pairWord S j copy) := hs
    have hsum := congrArg (fun v : Word F (RawTwo S).Z =>
      ∑ vertex : ZDoubleCylinderVertex (RawOne S) z S, v ⟨z,vertex⟩) hactual
    change (∑ vertex : ZDoubleCylinderVertex (RawOne S) z S,
      tannerCoboundary1 (RawTwo S) e ⟨z,vertex⟩)=_ at hez
    change (∑ vertex : ZDoubleCylinderVertex (RawOne S) z S,
      tannerCoboundary1 (RawTwo S) (pairWord S j copy) ⟨z,vertex⟩)=_ at hpz
    exact hez.symm.trans (hsum.trans (hpz.trans
      (congrArg (fun w => tannerCoboundary1 (RawOne S) w z)
        (pairWord_parity S j copy))))
  rcases BDL26RXQEdgePairTransport.bit_cases c with h0 | h1
  · rw [hc,h0,zero_smul,map_zero] at hproject
    have hz := congrFun hproject (criticalVerticalCheck S j)
    rw [oldPair_column,if_pos rfl] at hz
    have hne : criticalVerticalCheck S j≠seedConeCheck S j := by intro h; cases h
    rw [if_neg hne,add_zero] at hz
    exact zero_ne_one hz
  · rw [hc,h1,one_smul] at hproject
    exact oldPair_not_single_column S j a hproject

/-- Arbitrary full original boundary gauge is retained, and the original D
still takes NONE. The conclusion is about the complete physical syndrome. -/
private theorem pair_plus_boundary_original_search_none (S : OddScale)
    (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) (p : Word F (RawTwo S).X) :
    BDL26LevelTwoLocalBranchEndpoint.localSearch S
      (tannerCoboundary1 (RawTwo S)
        (pairWord S j copy+tannerCoboundary0 (RawTwo S) p))=none := by
  rw [map_add,tanner_d1_d0,add_zero]
  exact pairWord_original_search_none S j copy

/-- The ORIGINAL global branch has dual zero, for this entire bad word. -/
private theorem pair_plus_boundary_original_D_dual_zero (S : OddScale)
    (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) (p : Word F (RawTwo S).X) :
    dualReadout S (BDL26LevelTwoDecoder.decode S
      (tannerCoboundary1 (RawTwo S)
        (pairWord S j copy+tannerCoboundary0 (RawTwo S) p)))=0 := by
  rw [BDL26GlobalLookupLinearity.decode_of_local_none S _
    (pair_plus_boundary_original_search_none S j copy p)]
  exact dualReadout_global_zero S _


private def radialEdge (S : OddScale) (j : Fin 2) (i : Fin S.half) :
    DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S :=
  .inl (0,.inl (seedRadial j,i))
private def boundaryEdge (S : OddScale) (j : Fin 2) :
    DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S :=
  .inl (0,.inl (criticalQZ j,⟨0,S.half_pos⟩))

/-- Complete path coefficient, by the original path recursion. It does not
execute a path search or a table decoder. -/
private theorem radialPath_coefficient (S : OddScale) (j : Fin 2) (n : Nat)
    (hn : n≤S.half) (i : Fin S.half) :
    pathChain (radialPath S j n hn) (radialEdge S j i)=
      if i.val<n then 1 else 0 := by
  revert hn
  induction n with
  | zero =>
    intro hn
    simp [radialPath,pathChain]
  | succ n ih =>
    intro hn
    let k : Fin S.half := ⟨n,by omega⟩
    have hs : pathChain (radialPath S j (n+1) hn)=
        pathChain (radialPath S j n (by omega))+
          Pi.single (radialEdge S j k) (1 : F) := rfl
    have he : radialEdge S j i=radialEdge S j k ↔ i.val=n := by
      constructor
      · intro h
        have hp := Sum.inl.inj (congrArg Prod.snd (Sum.inl.inj h))
        exact congrArg Fin.val (congrArg Prod.snd hp)
      · intro h
        have hi : i=k := Fin.ext h
        rw [hi]
    rw [hs,Pi.add_apply,ih (by omega),Pi.single_apply]
    by_cases hi : i.val<n
    · have hik : ¬i.val=n := by omega
      have his : i.val<n+1 := by omega
      simp only [if_pos hi,if_pos his,if_neg (fun h => hik (he.mp h)),add_zero]
    · by_cases hik : i.val=n
      · have heq := he.mpr hik
        have his : i.val<n+1 := by omega
        simp only [if_neg hi,if_pos heq,if_pos his,zero_add]
      · have hne : radialEdge S j i≠radialEdge S j k := fun h => hik (he.mp h)
        have his : ¬i.val<n+1 := by omega
        simp only [if_neg hi,if_neg hne,if_neg his,zero_add]

private theorem radialChain_self (S : OddScale) (j : Fin 2) (i : Fin S.half) :
    radialChain S j (radialEdge S j i)=1 := by
  exact (radialPath_coefficient S j S.half (Nat.le_refl _) i).trans (if_pos i.isLt)

private theorem radialChain_other (S : OddScale) (j k : Fin 2) (hjk : j≠k)
    (i : Fin S.half) : radialChain S j (radialEdge S k i)=0 := by
  by_contra hn
  obtain ⟨a,ha⟩ := radialPath_support S j S.half (Nat.le_refl _)
    (radialEdge S k i) hn
  have hp := Sum.inl.inj (congrArg Prod.snd (Sum.inl.inj ha))
  have he : seedRadial k=seedRadial j := congrArg Prod.fst hp
  have hi : k=j := (by decide : Function.Injective seedRadial) he
  exact hjk hi.symm

private theorem radialChain_boundary_zero (S : OddScale) (j k : Fin 2) :
    radialChain S j (boundaryEdge S k)=0 := by
  by_contra hn
  obtain ⟨i,he⟩ := radialPath_support S j S.half (Nat.le_refl _)
    (boundaryEdge S k) hn
  have hp := Sum.inl.inj (congrArg Prod.snd (Sum.inl.inj he))
  have ht := congrArg (fun a : XStarEdge baseTannerSquarePresentation (0 : BaseX) ×
      Fin S.half => a.1.val) hp
  dsimp only [criticalQZ,seedRadial,xStarFaceQZEdge,xStarFaceXQEdge] at ht
  cases ht

private theorem full_wordPairing_basis {I : Type} [Fintype I]
    (w : Word F I) (a : I) :
    wordPairing w (canonicalBasisWord (F:=F) a)=w a := by
  classical
  simp [wordPairing_apply,dotProduct,basis_value]

private theorem raw_dual_radial (S : OddScale) (j : Fin 2) :
    rawDualReadout S (canonicalBasisWord (criticalRadial S j))=1 := by
  let i : Fin S.half := ⟨S.half-1,by have := S.half_pos;omega⟩
  have hp : (fun e : DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S =>
      canonicalBasisWord (F:=F) (criticalRadial S j) (.inl ⟨0,e⟩))=
        canonicalBasisWord (radialEdge S j i) := by
    funext e
    have hi : (Sum.inl ⟨0,e⟩ : (RawOne S).Q)=criticalRadial S j ↔ e=radialEdge S j i := by
      constructor
      · intro h
        exact sigma_same_index_inj (I:=baseTannerSquarePresentation.X)
          (A:=fun x => DoubleCylinderEdge baseTannerSquarePresentation x S)
          (i:=(0:BaseX)) e (radialEdge S j i) (Sum.inl.inj h)
      · intro h
        subst e
        rfl
    by_cases he : e=radialEdge S j i
    · exact ((basis_value _ _).trans (if_pos (hi.mpr he))).trans
        ((basis_value _ _).trans (if_pos he)).symm
    · exact ((basis_value _ _).trans (if_neg (fun h => he (hi.mp h)))).trans
        ((basis_value _ _).trans (if_neg he)).symm
  have h0 : canonicalBasisWord (F:=F) (criticalRadial S j)
      (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)=0 :=
    (basis_value _ _).trans (if_neg (by
      intro h
      change (Sum.inr _ : (RawOne S).Q)=Sum.inl _ at h
      cases h))
  have h1 : canonicalBasisWord (F:=F) (criticalRadial S j)
      (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)=0 :=
    (basis_value _ _).trans (if_neg (by
      intro h
      change (Sum.inr _ : (RawOne S).Q)=Sum.inl _ at h
      cases h))
  have ht : (radialChain S 0+radialChain S 1) (radialEdge S j i)=1 := by
    change radialChain S 0 (radialEdge S j i)+radialChain S 1 (radialEdge S j i)=1
    rcases two_eq_zero_or_one j with hj | hj
    · subst j
      exact (congrArg₂ (fun a b : F => a+b)
        (radialChain_self S 0 i) (radialChain_other S 1 0 (by decide) i)).trans (add_zero 1)
    · subst j
      exact (congrArg₂ (fun a b : F => a+b)
        (radialChain_other S 0 1 (by decide) i) (radialChain_self S 1 i)).trans (zero_add 1)
  have hp' := congrArg (wordPairing (radialChain S 0+radialChain S 1)) hp
  have hpair := hp'.trans ((full_wordPairing_basis _ _).trans ht)
  change canonicalBasisWord (F:=F) (criticalRadial S j)
      (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)+
    canonicalBasisWord (F:=F) (criticalRadial S j)
      (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)+
    wordPairing (radialChain S 0+radialChain S 1)
      (fun e => canonicalBasisWord (F:=F) (criticalRadial S j) (.inl ⟨0,e⟩))=1
  exact (congrArg₂ (fun a b : F => a+b)
    (congrArg₂ (fun a b : F => a+b) h0 h1) hpair).trans (by decide)

private theorem raw_dual_boundary (S : OddScale) (j : Fin 2) :
    rawDualReadout S (canonicalBasisWord (criticalBoundary S j))=0 := by
  have hp : (fun e : DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) S =>
      canonicalBasisWord (F:=F) (criticalBoundary S j) (.inl ⟨0,e⟩))=
        canonicalBasisWord (boundaryEdge S j) := by
    funext e
    have hi : (Sum.inl ⟨0,e⟩ : (RawOne S).Q)=criticalBoundary S j ↔ e=boundaryEdge S j := by
      constructor
      · intro h
        exact sigma_same_index_inj (I:=baseTannerSquarePresentation.X)
          (A:=fun x => DoubleCylinderEdge baseTannerSquarePresentation x S)
          (i:=(0:BaseX)) e (boundaryEdge S j) (Sum.inl.inj h)
      · intro h
        subst e
        rfl
    by_cases he : e=boundaryEdge S j
    · exact ((basis_value _ _).trans (if_pos (hi.mpr he))).trans
        ((basis_value _ _).trans (if_pos he)).symm
    · exact ((basis_value _ _).trans (if_neg (fun h => he (hi.mp h)))).trans
        ((basis_value _ _).trans (if_neg he)).symm
  have h0 : canonicalBasisWord (F:=F) (criticalBoundary S j)
      (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)=0 :=
    (basis_value _ _).trans (if_neg (by
      intro h
      change (Sum.inr _ : (RawOne S).Q)=Sum.inl _ at h
      cases h))
  have h1 : canonicalBasisWord (F:=F) (criticalBoundary S j)
      (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)=0 :=
    (basis_value _ _).trans (if_neg (by
      intro h
      change (Sum.inr _ : (RawOne S).Q)=Sum.inl _ at h
      cases h))
  have ht : (radialChain S 0+radialChain S 1) (boundaryEdge S j)=0 := by
    change radialChain S 0 (boundaryEdge S j)+radialChain S 1 (boundaryEdge S j)=0
    rw [radialChain_boundary_zero,radialChain_boundary_zero,zero_add]
  have hp' := congrArg (wordPairing (radialChain S 0+radialChain S 1)) hp
  have hpair := hp'.trans ((full_wordPairing_basis _ _).trans ht)
  change canonicalBasisWord (F:=F) (criticalBoundary S j)
      (.inr ⟨(0 : BaseQubit),(0,.inl (.inl ()))⟩)+
    canonicalBasisWord (F:=F) (criticalBoundary S j)
      (.inr ⟨(1 : BaseQubit),(0,.inl (.inl ()))⟩)+
    wordPairing (radialChain S 0+radialChain S 1)
      (fun e => canonicalBasisWord (F:=F) (criticalBoundary S j) (.inl ⟨0,e⟩))=0
  exact (congrArg₂ (fun a b : F => a+b)
    (congrArg₂ (fun a b : F => a+b) h0 h1) hpair).trans (by decide)

/-- Exact dual of the FULL physical pair, with its actual Q-cylinder parities. -/
private theorem pairWord_dual (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    dualReadout S (pairWord S j copy)=1 := by
  change rawDualReadout S (rzQParity (RawOne S) S (pairWord S j copy))=1
  rw [pairWord_parity,oldPair,map_add,raw_dual_radial,raw_dual_boundary,add_zero]

/-- Complete original base endpoint for the bad full word, including BOTH D
calls and an arbitrary complete boundary gauge. No logical coefficient or
NONE conclusion is supplied as an input. -/
private theorem pair_plus_boundary_full_original_residual (S : OddScale)
    (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) (p : Word F (RawTwo S).X) :
    let h := pairWord S j copy+tannerCoboundary0 (RawTwo S) p
    let residual := h+(fun q : (RawTwo S).Q => (BDL26LevelTwoDecoder.decode S 0) q)+
      (fun q : (RawTwo S).Q => (BDL26LevelTwoDecoder.decode S (tannerCoboundary1 (RawTwo S) h)) q)
    tannerCoboundary1 (RawTwo S) residual=0 ∧
      dualReadout S residual=1 ∧
      residual ∉ LinearMap.range (tannerCoboundary0 (RawTwo S)) := by
  intro h residual
  let D0 : Word F (RawTwo S).Q := fun q => (BDL26LevelTwoDecoder.decode S 0) q
  let D1 : Word F (RawTwo S).Q := fun q =>
    (BDL26LevelTwoDecoder.decode S (tannerCoboundary1 (RawTwo S) h)) q
  have h0 : D0 = (0 : Word F (RawTwo S).Q) := by
    funext q
    exact congrFun (BDL26LevelTwoDecoder.decode_zero S) q
  have hD : tannerCoboundary1 (RawTwo S) D1 = tannerCoboundary1 (RawTwo S) h :=
    BDL26LevelTwoDecoder.decode_rightInverse S _ ⟨h,rfl⟩
  have hz : dualReadout S h=1 := by
    rw [map_add,pairWord_dual,dualReadout_boundary,add_zero]
  have hzeroDual : dualReadout S D0 = 0 :=
    (congrArg (dualReadout S) h0).trans (map_zero (dualReadout S))
  have hdecodeDual : dualReadout S D1 = 0 :=
    pair_plus_boundary_original_D_dual_zero S j copy p
  have hr : dualReadout S residual=1 := by
    calc
      dualReadout S residual =
          (dualReadout S h+dualReadout S D0)+dualReadout S D1 :=
        (map_add (dualReadout S) (h+D0) D1).trans
          (congrArg (fun a : F => a+dualReadout S D1)
            (map_add (dualReadout S) h D0))
      _ = (1+0)+0 :=
        congrArg₂ (fun a b : F => a+b)
          (congrArg₂ (fun a b : F => a+b) hz hzeroDual) hdecodeDual
      _ = 1 := by simp
  refine ⟨?_,hr,?_⟩
  · have hzeroDelta : tannerCoboundary1 (RawTwo S) D0 = 0 :=
      (congrArg (tannerCoboundary1 (RawTwo S)) h0).trans
        (map_zero (tannerCoboundary1 (RawTwo S)))
    calc
      tannerCoboundary1 (RawTwo S) residual =
          (tannerCoboundary1 (RawTwo S) h+tannerCoboundary1 (RawTwo S) D0)+
            tannerCoboundary1 (RawTwo S) D1 :=
        (map_add (tannerCoboundary1 (RawTwo S)) (h+D0) D1).trans
          (congrArg (fun a : Word F (RawTwo S).Z =>
            a+tannerCoboundary1 (RawTwo S) D1)
              (map_add (tannerCoboundary1 (RawTwo S)) h D0))
      _ = (tannerCoboundary1 (RawTwo S) h+0)+tannerCoboundary1 (RawTwo S) h :=
        congrArg₂ (fun a b : Word F (RawTwo S).Z => a+b)
          (congrArg (fun a : Word F (RawTwo S).Z =>
            tannerCoboundary1 (RawTwo S) h+a) hzeroDelta) hD
      _ = 0 := by rw [add_zero]; exact ZModModule.add_self _
  · rintro ⟨a,ha⟩
    have hb := dualReadout_boundary S a
    have hresidualZero : dualReadout S residual=0 :=
      (congrArg (dualReadout S) ha).symm.trans hb
    exact one_ne_zero (hr.symm.trans hresidualZero)

end
end ActualCriticalStarGeometry
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- The original initial state, actual step, full finite Phi sum and accumulated interval potential. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOneStepPhiBridge
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent
open BDL26ActualFailureReadout BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
noncomputable section

/-- Reprove the exported support fact; do not name the imported module's
private flip_supported helper. Proof irrelevance preserves the actual input. -/
private theorem original_flip_supported (S : OddScale) (n : Nat)
    (q : Physical S (n+2)) :
    hammingSupport (flip S n q) ⊆
      BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n)
        (elementaryCenter S n q) := by
  rw [flip_eq_basis]
  exact elementary_support S n q

/-- At n=1 the ENTIRE original accumulated interval contains exactly the one
original step potential; no quotient, boundary equivalence or gauge is used. -/
private theorem actualPotential_one_step (S : OddScale)
    (sigma : BDL26HistorySyndromeSensitivity.TopInput S 1)
    (e : (BDL26LocalizedHistoryErrorDescent.Data S 1).family.Cochain1 (TopIndex 1))
    (x : (state S 3).presentation.X)
    (he : hammingSupport e ⊆ star S 1 (TopIndex 1) x) :
    actualPotential S 1 sigma e x he 0 (TopIndex 1)=
      (step S 1 sigma (perturbTop S 1 sigma e) (0 : StepIndex 1)
        (initial S 1 sigma e x he)).potential := by
  unfold actualPotential
  change intervalPotential S 1 sigma (perturbTop S 1 sigma e)
    (initial S 1 sigma e x he) (0 : StepIndex 1).castSucc (0 : StepIndex 1).succ=_
  rw [intervalPotential_adjacent]
  change (step S 1 sigma (perturbTop S 1 sigma e) (0 : StepIndex 1)
    (path S 1 sigma (perturbTop S 1 sigma e) (initial S 1 sigma e x he)
      (TopIndex 1))).potential=_
  rw [path_top]

private theorem accumulated_eq_original_step (S : OddScale)
    (u : XSyndromeDomain S 1) (p : Physical S 3) :
    accumulated S 1 u p=
      (step S 1 (input S 1 u)
        (perturbTop S 1 (input S 1 u) (flip S 1 p)) (0 : StepIndex 1)
        (initial S 1 (input S 1 u) (flip S 1 p)
          (elementaryCenter S 1 p) (original_flip_supported S 1 p))).potential :=
  actualPotential_one_step S (input S 1 u) (flip S 1 p)
    (elementaryCenter S 1 p) (original_flip_supported S 1 p)

/-- This exact equality is the requested connection to step_RX_fixed.Phi.
Its center is the original elementaryCenter, not an assumed old-X center. -/
private theorem accumulated_eq_original_Phi (S : OddScale)
    (u : XSyndromeDomain S 1) (p : Physical S 3) :
    let sigma := input S 1 u
    let tau := perturbTop S 1 sigma (flip S 1 p)
    let top := initial S 1 sigma (flip S 1 p)
      (elementaryCenter S 1 p) (original_flip_supported S 1 p)
    accumulated S 1 u p=
      BDL26RXPhysicalStarTransport.Phi S 3 (Edge 1 (0 : StepIndex 1))
        (by decide) top.center (first S 1 sigma (0 : StepIndex 1))
          (second S 1 sigma tau (0 : StepIndex 1) top) := by
  intro sigma tau top
  exact (accumulated_eq_original_step S u p).trans
    (step_RX_fixed S 1 sigma tau (0 : StepIndex 1) (by decide) top).2.1

/- The full original finite Phi sum reduces to an effective local potential
only because every OTHER ORIGINAL updated X restriction is literally zero.
Membership of the active X in the original X0 is retained explicitly. -/
end
end OriginalOneStepPhiBridge
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


/- The localized actual descent plus both original base decodes is transported through the entire accumulated potential. This descent is not identified definitionally with the distinct global HistoryLogicalResidual.lowerWord. -/
noncomputable section
namespace QEC.Coding.BDL26ActualLocalizedResidualLift
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26OwnerIncidenceMasks
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26ActualFailureReadout BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open scoped Classical

/-- A full-word equation, rather than equality of one selected parity. -/
private theorem actual_chi_eq_localized_coefficient
    (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (w : FC.Cocycle S 2)
    (hw : w.val = (descent S n u q).word +
      (actualBase S n).decode (actualInputs S n (input S n u) 0) +
      (actualBase S n).decode
        (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0)) :
    BDL26LogicalDefectProtection.chiX S n u q =
      FC.finiteH1Equiv S 2 (FC.classOf S 2 w) := by
  let v := intervalCocycle S n 0 (TopIndex n) (Nat.zero_le _) w
  have hclass : FC.classOf S (n+2)
      (topCocycle S n (input S n u) (flip S n q)) =
      FC.classOf S (n+2) v := by
    apply (class_eq_iff_boundary S (n+2) _ _).mpr
    refine ⟨accumulated S n u q, ?_⟩
    have hi := full_history S n u q
    rw [← hw] at hi
    have hv := intervalCocycle_word S n 0 (TopIndex n) (Nat.zero_le _) w
    change v.val = intervalMap1 (SuffixData S n) 0 (TopIndex n)
      (Nat.zero_le _) w.val at hv
    change tannerCoboundary0 (state S (n+2)).presentation
      (accumulated S n u q) =
      topWord S n (input S n u) (flip S n q) - v.val
    rw [← suffix_delta0 S n (TopIndex n), hv, full_residual S n u q, hi]
    abel
  rw [chiX_top_coefficient]
  unfold topCoefficient
  rw [hclass]
  have hq := suffixEquiv_mk S n 0 (TopIndex n) (Nat.zero_le _) w
  change suffixEquiv S n 0 (TopIndex n) (FC.classOf S 2 w) =
    FC.classOf S (n+2) v at hq
  rw [← hq]
  exact coefficient_natural S n 0 (TopIndex n) (FC.classOf S 2 w)

/-- The caller supplies the independently derived full localized residual;
closedness and non-boundary are mathematical intermediate facts.  The actual
chi conclusion follows from the original complete history and finite H1. -/
private theorem actual_chi_one_of_localized_closed_not_boundary
    (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2))
    (v : (SuffixData S n).family.Cochain1 (0 : LevelIndex n))
    (hv : v = (descent S n u q).word +
      (actualBase S n).decode (actualInputs S n (input S n u) 0) +
      (actualBase S n).decode
        (actualInputs S n (perturbTop S n (input S n u) (flip S n q)) 0))
    (hc : tannerCoboundary1 (state S 2).presentation v = 0)
    (hn : ¬ ∃ f : Word BDL26Field (state S 2).presentation.X,
      tannerCoboundary0 (state S 2).presentation f = v) :
    BDL26LogicalDefectProtection.chiX S n u q = 1 := by
  let w : FC.Cocycle S 2 := ⟨v,
    (BDL26RZCohomology.mem_cocycle_iff _ _).mpr hc⟩
  have hchi := actual_chi_eq_localized_coefficient S n u q w hv
  have hnz : FC.finiteH1Equiv S 2 (FC.classOf S 2 w) ≠ 0 := by
    intro hz
    exact hn ((coefficient_zero_iff_boundary S 2 w).mp hz)
  have bits : ∀ a : BDL26Field, a = 0 ∨ a = 1 := by decide
  rcases bits (FC.finiteH1Equiv S 2 (FC.classOf S 2 w)) with h0 | h1
  · exact False.elim (hnz h0)
  · exact hchi.trans h1

end QEC.Coding.BDL26ActualLocalizedResidualLift

section OriginalCounterexampleWorking
attribute [local instance 2000] QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.xFintype
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.qFintype
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.zFintype
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  QEC.Coding.BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair3WordHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair6RegionWordHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair6C3TopHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair6C3UpperHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair6LiteralSyndromeHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair7TopLiteralCochainHAdd
  QEC.Coding.BDL26RXPrimitiveC2QEndpoint.repair7TopLiteralWordHAdd
/- Complete physical old-X response calculations for the original selector model. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
attribute [local instance 2000] BDL26FiniteTannerSquare.TannerSquareData.xFintype
  BDL26FiniteTannerSquare.TannerSquareData.qFintype
  BDL26FiniteTannerSquare.TannerSquareData.zFintype
  BDL26FiniteTannerSquare.TannerSquareData.xDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.qDecidableEq
  BDL26FiniteTannerSquare.TannerSquareData.zDecidableEq
attribute [local instance] repair3WordHAdd repair6RegionWordHAdd
  repair6C3TopHAdd repair6C3UpperHAdd repair6LiteralSyndromeHAdd
  repair7TopLiteralCochainHAdd repair7TopLiteralWordHAdd
namespace CriticalOriginalChoice
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26LevelTwoCode
open BDL26ActualFailureReadout
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private theorem sameLeafPair_actual_budgets (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (hh : S.half=1)
    (a b c : QStarEdge P q) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (cover : ∀ z : QStarEdge P q,z=a ∨ z=b ∨ z=c) :
    let k := terminalWord P q S 0 a+terminalWord P q S 1 a
    let w := coneWord P q S 0+terminalWord P q S 0 b+terminalWord P q S 1 b
    (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S k))=2 ∧
    (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S w))=2 ∧
    (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S (w+k)))=4 ∧
    HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) k)≤3 ∧
    HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w)≤3 ∧
    HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (w+k))≤3 := by
  let k := terminalWord P q S 0 a+terminalWord P q S 1 a
  let w := coneWord P q S 0+terminalWord P q S 0 b+terminalWord P q S 1 b
  have hone : (1:BDL26Field)+1=0 := repair3_scalar_add_self _
  have hf :
      (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S k))=2 ∧
      (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S w))=2 ∧
      (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S (w+k)))=4 := by
    constructor
    · erw [sum_three_leaves a b c hab hac hbc cover]
      simp_rw [hamming_weight_two]
      simp [k,terminalWord,basis_value,rxQZDegreeOne,wordPullback_apply,
        hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc,hone]
    constructor
    all_goals erw [sum_three_leaves a b c hab hac hbc cover]
    all_goals simp_rw [hamming_weight_two]
    all_goals simp [w,k,coneWord,terminalWord,basis_value,
      rxQZDegreeOne,wordPullback_apply,hab,hac,hbc,
      Ne.symm hab,Ne.symm hac,Ne.symm hbc,hone]
  let sk : Finset (QDoubleCylinderEdge P q S) :=
    {firstArm P q S 0 a,firstArm P q S 1 a}
  let sw : Finset (QDoubleCylinderEdge P q S) :=
    {firstArm P q S 0 a,firstArm P q S 0 c,firstArm P q S 1 b}
  let su : Finset (QDoubleCylinderEdge P q S) :=
    {firstArm P q S 0 c,firstArm P q S 1 a,firstArm P q S 1 b}
  have heval (e : QDoubleCylinderEdge P q S) :
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) k e=
        if e∈sk then 1 else 0) ∧
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w e=
        if e∈sw then 1 else 0) ∧
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (w+k) e=
        if e∈su then 1 else 0) := by
    rcases e with ⟨copy,z,n⟩ | z
    · have hn : n=⟨0,S.half_pos⟩ := Fin.ext (by have hi := n.isLt;omega)
      subst n
      change (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) k
          (firstArm P q S copy z)=(if firstArm P q S copy z∈sk then 1 else 0)) ∧
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w
          (firstArm P q S copy z)=(if firstArm P q S copy z∈sw then 1 else 0)) ∧
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (w+k)
          (firstArm P q S copy z)=(if firstArm P q S copy z∈su then 1 else 0))
      erw [halfOne_delta_arm P q S hh,halfOne_delta_arm P q S hh,
        halfOne_delta_arm P q S hh]
      rcases cover z with rfl | rfl | rfl
      all_goals fin_cases copy
      all_goals simp [w,k,coneWord,terminalWord,basis_value,
        sk,sw,su,firstArm,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc,hone]
    · erw [delta_bridge,delta_bridge,delta_bridge]
      rcases cover z with rfl | rfl | rfl
      all_goals simp [w,k,coneWord,terminalWord,basis_value,
        sk,sw,su,firstArm,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc,hone]
  have hbound (z : Word BDL26Field (QDoubleCylinderVertex P q S))
      (s : Finset (QDoubleCylinderEdge P q S)) (hs : s.card≤3)
      (hz : ∀ e,wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) z e=
        if e∈s then 1 else 0) :
      HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) z)≤3 := by
    have hsub : hammingSupport
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) z)⊆s := by
      intro e he
      by_contra hn
      have hv : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) z e≠0 := by
        simpa [hammingSupport] using he
      exact hv ((hz e).trans (if_neg hn))
    exact (Finset.card_le_card hsub).trans hs
  have hsk : sk.card≤3 := by
    dsimp only [sk]
    have h := Finset.card_insert_le (firstArm P q S 0 a) {firstArm P q S 1 a}
    simp only [Finset.card_singleton] at h
    omega
  exact ⟨hf.1,hf.2.1,hf.2.2,
    hbound k sk hsk (fun e => (heval e).1),
    hbound w sw (card_triple_le_three _ _ _) (fun e => (heval e).2.1),
    hbound (w+k) su (card_triple_le_three _ _ _) (fun e => (heval e).2.2)⟩

end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open scoped Classical BigOperators

/-- Proof-only support classification of an ORIGINAL outgoing word.
It says nothing about minimum weight or the decoder's selected value. -/
private theorem flow_weight_le_one_word {I : Type} [Fintype I] [DecidableEq I]
    (w : Word BDL26Field I) (hw : HammingWeight w≤1) :
    w=0 ∨ ∃ p : I,w=canonicalBasisWord p := by
  classical
  by_cases hz : w=0
  · exact Or.inl hz
  right
  obtain ⟨p,hp⟩ : ∃ p : I,w p≠0 := by
    by_contra h
    push_neg at h
    apply hz
    funext p
    exact h p
  have hp1 : w p=1 := by
    rcases BDL26RXQEdgePairTransport.bit_cases (w p) with h0 | h1
    · exact False.elim (hp h0)
    · exact h1
  refine ⟨p,?_⟩
  funext q
  by_cases hqp : q=p
  · subst q
    simpa [basis_value] using hp1
  have hq : w q=0 := by
    by_contra hq
    have hsub : ({p,q} : Finset I)⊆hammingSupport w := by
      intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩
    have hc := (Finset.card_le_card hsub).trans hw
    have hne : p≠q := Ne.symm hqp
    have hcard : ({p,q} : Finset I).card=2 := by simp [hne]
    rw [hcard] at hc
    omega
  simpa [basis_value,hqp] using hq
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RXPhysicalCoordinateTrace BDL26RXLocalReplacement BDL26RZLocalReplacement
open scoped Classical

/-- A proof-coordinate view only; it never changes the physical qubit. -/
private abbrev OldXSeed (S : OddScale) :=
  Σ x : (state S 1).presentation.X, Σ c : BDL26FiniteTannerSquare.Two,
    DoubleCylinderEdge (state S 2).presentation (oldXOwner S 1 (by decide) x c) S

private def oldXView (S : OddScale) (q : Physical S 3) : Option (OldXSeed S) :=
  match (BDL26RXDecoderAdapter.rxPhysicalQEquiv S 3 ⟨2,by omega⟩ (by decide)).symm q with
  | .inl ⟨.inr (x,c),d⟩ => some ⟨x,c,d⟩
  | _ => none

private theorem oldXView_seed (S : OddScale) (a : OldXSeed S) :
    oldXView S (oldXPhysical S 1 (by decide) a.1 a.2.1 a.2.2)=some a := by
  unfold oldXView oldXPhysical oldXOwner
  rw [Equiv.symm_apply_apply]
  rfl

private theorem oldXView_face (S : OddScale) (a : BDL26RXFaceEdgeTower.Seed S) :
    oldXView S (BDL26RXFaceEdgeTower.seedPhysical S a)=none := by
  unfold oldXView BDL26RXFaceEdgeTower.seedPhysical
  rw [Equiv.symm_apply_apply]
  rfl

private theorem oldXView_c2QEdge (S : OddScale) (a : Seed S) :
    oldXView S (c2QEdgePhysical S a.1 a.2.1 a.2.2)=none := by
  unfold oldXView c2QEdgePhysical
  rw [Equiv.symm_apply_apply]
  rfl

private theorem oldXView_rx (S : OddScale) (q : Physical S 2)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex (state S 2).presentation q S) :
    oldXView S (BDL26FirstZeroQVertexTower.rxVertex S 2 (by decide) q v)=none := by
  rw [rx_vertex_chart S 2 (by decide)]
  unfold oldXView
  rw [Equiv.symm_apply_apply]

/-- The actual parser chooses a trace, so its old-X tag is proved by chart
injectivity and exhaustive traces, not by unfolding Classical.choose. -/
private theorem trace_oldX_leaf (S : OddScale) (a : OldXSeed S)
    {b : Nat} {q : Physical S (b+2)} {leaf : Leaf S}
    (t : Trace S b q leaf) (hb : b=1)
    (hq : HEq q (oldXPhysical S 1 (by decide) a.1 a.2.1 a.2.2)) :
    leaf=.primitive (Primitive.oldX 1 (by decide) a.1 a.2.1 a.2.2) := by
  cases t with
  | c2 q => omega
  | face a' =>
    have he := congrArg (oldXView S) (eq_of_heq hq)
    rw [oldXView_face,oldXView_seed] at he
    cases he
  | rzEdge b ho z e =>
    have hb0 : b=0 := by omega
    subst b
    exact False.elim (ho (by decide))
  | higherFace j a' => omega
  | primitive p =>
    cases p with
    | c2QEdge r e d =>
      have he := congrArg (oldXView S) (eq_of_heq hq)
      change oldXView S (c2QEdgePhysical S r e d)=
        oldXView S (oldXPhysical S 1 (by decide) a.1 a.2.1 a.2.2) at he
      have he' : (none : Option (OldXSeed S))=some a :=
        (oldXView_c2QEdge S ⟨r,e,d⟩).symm.trans
          (he.trans (oldXView_seed S a))
      cases he' 
    | oldX _ ho x c d =>
      have hm : b=1 := hb
      subst b
      have he := congrArg (oldXView S) (eq_of_heq hq)
      change oldXView S (oldXPhysical S 1 ho x c d)=some a at he
      have he' : some (⟨x,c,d⟩ : OldXSeed S)=some a := by
        exact (oldXView_seed S ⟨x,c,d⟩).symm.trans he
      exact congrArg (fun z : OldXSeed S =>
        Leaf.primitive (Primitive.oldX 1 (by decide) z.1 z.2.1 z.2.2)) (Option.some.inj he')
  | @rx b q leaf t he v =>
    have hb0 : b=0 := by omega
    subst b
    have he' := congrArg (oldXView S) (eq_of_heq hq)
    rw [oldXView_rx,oldXView_seed] at he'
    cases he'
  | @rz b q leaf t ho v =>
    have hb0 : b=0 := by omega
    subst b
    exact False.elim (ho (by decide))
  | qEdgePair j a' t => omega

private theorem parse_oldX_exact (S : OddScale) (a : OldXSeed S) :
    parse S 1 (oldXPhysical S 1 (by decide) a.1 a.2.1 a.2.2)=
      .primitive (Primitive.oldX 1 (by decide) a.1 a.2.1 a.2.2) := by
  exact trace_oldX_leaf S a
    (parsedTrace S 1 (oldXPhysical S 1 (by decide) a.1 a.2.1 a.2.2)) rfl HEq.rfl
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open scoped Classical

/- Obtain the actual face from the presentation's sole perfect-pairing
field. No chosen filling or decoder conclusion is a hypothesis. -/
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open scoped Classical BigOperators

/-- The complete rectangle equation, on the actual cylinder matrix.  The
vertical endpoints are retained; neither a quotient nor a parity surrogate
is used. -/
private theorem original_rectangle_coboundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (d : SubdivisionBoundaryEdge P x S) :
    doubleCylinderCoboundary1 P x S f (Sum.inr d) =
      (f (Sum.inl (0,d.val))+f (Sum.inl (1,d.val)))+
      (f (Sum.inr (subdivisionBoundaryEdgeStart P x S d))+
       f (Sum.inr (subdivisionBoundaryEdgeEnd P x S d))) := by
  classical
  rw [doubleCylinderCoboundary1,doubleCylinderBoundary2,
    wordLinearMapTranspose_toLin'_apply]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [doubleCylinderFaceEdgeMatrix]
  have he (c : BDL26FiniteTannerSquare.Two) :
      (∑ e : SubdivisionEdge P x S,
        f (Sum.inl (c,e))*(if e=d.val then (1:BDL26Field) else 0)) =
        f (Sum.inl (c,d.val)) := by
    simp
  have hv :
      (∑ z : SubdivisionBoundaryVertex P x S,
        f (Sum.inr z)*
        ((if z=subdivisionBoundaryEdgeStart P x S d then (1:BDL26Field) else 0)+
         (if z=subdivisionBoundaryEdgeEnd P x S d then 1 else 0))) =
      f (Sum.inr (subdivisionBoundaryEdgeStart P x S d))+
      f (Sum.inr (subdivisionBoundaryEdgeEnd P x S d)) := by
    have hs (a : SubdivisionBoundaryVertex P x S) :
        (∑ z : SubdivisionBoundaryVertex P x S,
          if z=a then f (Sum.inr z) else 0)=f (Sum.inr a) := by
      calc
        _ = (if a=a then f (Sum.inr a) else 0) :=
          Finset.sum_eq_single a
            (fun z _ hza => if_neg hza)
            (fun h => False.elim (h (Finset.mem_univ a)))
        _ = f (Sum.inr a) := if_pos rfl
    simpa only [mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero,hs]
  simpa only [Fin.sum_univ_two,he,hv]

/-- Adding two ACTUAL hub rectangles removes the common vertical hub edge.
This is the scalar quotient used to force the original Cx exit, while
retaining both different Z-vertical coordinates explicitly. -/
private theorem original_rectangle_pair
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (d e : SubdivisionBoundaryEdge P x S)
    (hs : subdivisionBoundaryEdgeStart P x S d=
      subdivisionBoundaryEdgeStart P x S e) :
    doubleCylinderCoboundary1 P x S f (Sum.inr d)+
      doubleCylinderCoboundary1 P x S f (Sum.inr e) =
    (f (Sum.inl (0,d.val))+f (Sum.inl (1,d.val)))+
    (f (Sum.inl (0,e.val))+f (Sum.inl (1,e.val)))+
    (f (Sum.inr (subdivisionBoundaryEdgeEnd P x S d))+
     f (Sum.inr (subdivisionBoundaryEdgeEnd P x S e))) := by
  rw [original_rectangle_coboundary,original_rectangle_coboundary,hs]
  have hcancel := repair3_scalar_add_self
    (f (Sum.inr (subdivisionBoundaryEdgeStart P x S e)))
  calc
    _ = ((f (Sum.inl (0,d.val))+f (Sum.inl (1,d.val)))+
          (f (Sum.inl (0,e.val))+f (Sum.inl (1,e.val)))+
          (f (Sum.inr (subdivisionBoundaryEdgeEnd P x S d))+
           f (Sum.inr (subdivisionBoundaryEdgeEnd P x S e))))+
        (f (Sum.inr (subdivisionBoundaryEdgeStart P x S e))+
         f (Sum.inr (subdivisionBoundaryEdgeStart P x S e))) := by ac_rfl
    _ = _ := by rw [hcancel,add_zero]

/-- BDL26FiniteTannerSquare.Two distinct nonzero entries already cost two.  Applying this to two
adjacent Q bridge coordinates rules out a Z vertical coefficient under
an original total outgoing budget of one. -/
private theorem two_nonzero_entries_cost_two {I : Type} [Fintype I]
    [DecidableEq I] (w : Word BDL26Field I) {a b : I}
    (hab : a≠b) (ha : w a≠0) (hb : w b≠0) :
    2≤HammingWeight w := by
  have hsub : ({a,b} : Finset I)⊆hammingSupport w := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩
  have hc := Finset.card_le_card hsub
  have hcard : ({a,b} : Finset I).card=2 := by simp [hab]
  rw [hcard] at hc
  simpa only [HammingWeight_eq_card_hammingSupport] using hc
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open BDL26RXDecoderAdapter BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators

/-- A single original X-output budget prohibits two Q coordinates from
carrying one and the same nonzero Z-vertical coefficient. -/
private theorem shared_bridge_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f)≤1)
    (q r : P.Q) (hqr : q≠r)
    (hxq : P.xq x q=true) (hxr : P.xq x r=true)
    (zq : QStarEdge P q) (zr : QStarEdge P r)
    (he : qToXDoubleCylinderEdge P A q x hxq S (Sum.inr zq)=
      qToXDoubleCylinderEdge P A r x hxr S (Sum.inr zr)) :
    f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr zq))=0 := by
  classical
  let i : RX2 P S := Sum.inl (Sum.inr ⟨q,Sum.inr zq⟩)
  let j : RX2 P S := Sum.inl (Sum.inr ⟨r,Sum.inr zr⟩)
  have hij : i≠j := by
    intro h
    have h' := Sum.inr.inj (Sum.inl.inj h)
    exact hqr (congrArg Sigma.fst h')
  have hi : xFlow P S x f i=
      f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr zq)) := by
    rw [xFlow_at_q P A]
    simp only [dif_pos hxq,rxXQDegreeOne,wordPullback_apply]
  have hj : xFlow P S x f j=
      f (qToXDoubleCylinderEdge P A r x hxr S (Sum.inr zr)) := by
    rw [xFlow_at_q P A]
    simp only [dif_pos hxr,rxXQDegreeOne,wordPullback_apply]
  by_contra hn
  have htwo := two_nonzero_entries_cost_two (xFlow P S x f) hij
    (by simpa only [hi] using hn) (by simpa only [hj,← he] using hn)
  omega

/-- In six genuinely distinct outgoing coordinates, budget one and the two
rectangle parities force the first arm type.  These coordinates will be the
ACTUAL hub's r/v/g arms, not an auxiliary decoder. -/
private theorem two_parities_force_first_arm
    {I : Type} [Fintype I] [DecidableEq I]
    (w : Word BDL26Field I) (hw : HammingWeight w≤1)
    (e : Fin 3 × BDL26FiniteTannerSquare.Two → I) (hinj : Function.Injective e)
    (hrg : w (e (0,0))+w (e (0,1))+w (e (2,0))+w (e (2,1))=1)
    (hvg : w (e (1,0))+w (e (1,1))+w (e (2,0))+w (e (2,1))=0) :
    ∃ c : BDL26FiniteTannerSquare.Two,w=canonicalBasisWord (e (0,c)) := by
  rcases flow_weight_le_one_word w hw with hz | ⟨a,ha⟩
  · simp only [hz,Pi.zero_apply,zero_add] at hrg
    exact False.elim (zero_ne_one hrg)
  have hd (p q : Fin 3 × BDL26FiniteTannerSquare.Two) : e p=e q ↔ p=q := hinj.eq_iff
  subst w
  by_cases h0 : a=e (0,0)
  · exact ⟨0,congrArg canonicalBasisWord h0⟩
  by_cases h1 : a=e (0,1)
  · exact ⟨1,congrArg canonicalBasisWord h1⟩
  have h2 : a≠e (2,0) := by
    intro h
    subst a
    simp [basis_value,hd] at hvg
  have h3 : a≠e (2,1) := by
    intro h
    subst a
    simp [basis_value,hd] at hvg
  simp [basis_value,Ne.symm h0,Ne.symm h1,Ne.symm h2,Ne.symm h3] at hrg

/-- Zero rectangle parities cannot coexist with a hub-arm output under the
same original total budget.  An output on a leaf arm is left unrestricted. -/
private theorem zero_parities_no_hub_arm
    {I : Type} [Fintype I] [DecidableEq I]
    (w : Word BDL26Field I) (hw : HammingWeight w≤1)
    (e : Fin 3 × BDL26FiniteTannerSquare.Two → I) (hinj : Function.Injective e)
    (hrg : w (e (0,0))+w (e (0,1))+w (e (2,0))+w (e (2,1))=0)
    (hvg : w (e (1,0))+w (e (1,1))+w (e (2,0))+w (e (2,1))=0) :
    ∀ p : Fin 3 × BDL26FiniteTannerSquare.Two,w (e p)=0 := by
  rcases flow_weight_le_one_word w hw with hz | ⟨a,ha⟩
  · intro p
    exact congrFun hz (e p)
  have hd (p q : Fin 3 × BDL26FiniteTannerSquare.Two) : e p=e q ↔ p=q := hinj.eq_iff
  subst w
  intro p
  by_cases hp : e p=a
  · subst a
    rcases p with ⟨k,c⟩
    fin_cases k <;> fin_cases c
    all_goals simp [basis_value,hd] at hrg hvg
  · simp [basis_value,hp]
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open BDL26RXDecoderAdapter BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators

private def firstHubRectangle (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q=true) (z : QStarEdge P q) :
    SubdivisionBoundaryEdge P x S :=
  qToXSubdivisionBoundaryEdge P q x hxq S (z,⟨0,S.half_pos⟩)

private def hubArmCoordinate (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) : RX2 P S :=
  Sum.inl (Sum.inr ⟨q,Sum.inl (c,(z,⟨0,S.half_pos⟩))⟩)

private theorem hubArmCoordinate_injective
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z) :
    Function.Injective (fun p : Fin 3 × BDL26FiniteTannerSquare.Two => hubArmCoordinate P S q (z p.1) p.2) := by
  rintro ⟨i,c⟩ ⟨j,d⟩ h
  have he := Sum.inr.inj (Sum.inl.inj h)
  have he' := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have hp := Sum.inl.inj he'
  exact Prod.ext (hz (congrArg (fun t : BDL26FiniteTannerSquare.Two × QSubdivisionEdge P q S => t.2.1) hp))
    (congrArg Prod.fst hp)

private theorem firstHubRectangle_start
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true) (z t : QStarEdge P q) :
    subdivisionBoundaryEdgeStart P x S (firstHubRectangle P S x q hxq z)=
      subdivisionBoundaryEdgeStart P x S (firstHubRectangle P S x q hxq t) := by
  apply Subtype.ext
  simp only [subdivisionBoundaryEdgeStart_value,firstHubRectangle,
    qToXSubdivisionBoundaryEdge,subdivisionOriginalBoundaryEdge,
    subdivisionEdgeStart,subdivisionSegmentStart,dif_pos rfl]
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl

private theorem firstHubRectangle_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (hh : S.half=1) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true) (z : QStarEdge P q) :
    Sum.inr (subdivisionBoundaryEdgeEnd P x S (firstHubRectangle P S x q hxq z))=
      qToXDoubleCylinderEdge P A q x hxq S (Sum.inr z) := by
  apply congrArg Sum.inr
  apply Subtype.ext
  simp only [subdivisionBoundaryEdgeEnd_value,firstHubRectangle,
    qToXSubdivisionBoundaryEdge,subdivisionOriginalBoundaryEdge,
    subdivisionEdgeEnd,subdivisionSegmentEnd,hh,dif_pos]
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl

private theorem shared_Z_bridge_image
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (q r : P.Q)
    (hxq : P.xq x q=true) (hxr : P.xq x r=true)
    (zq : QStarEdge P q) (zr : QStarEdge P r) (hz : zq.val=zr.val) :
    qToXDoubleCylinderEdge P A q x hxq S (Sum.inr zq)=
      qToXDoubleCylinderEdge P A r x hxr S (Sum.inr zr) := by
  apply congrArg Sum.inr
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Subtype.ext
  exact congrArg Vertex.z hz

/-- This is the original Cx budget implication on actual Source coordinates:
if the two hub-rectangle parities are (1,0), its ENTIRE outgoing word is a
single radial-type hub arm.  Each old Z has an actual second incident leaf,
which prohibits its doubled bridge flow; no arbitrary small-support model
or minimum-weight selection is introduced. -/
private theorem actual_hub_exit_forced
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (hh : S.half=1) (x : P.X) (q : P.Q)
    (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f)≤1)
    (hrg : doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 0)))+
      doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 2)))=1)
    (hvg : doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 1)))+
      doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 2)))=0) :
    ∃ c : BDL26FiniteTannerSquare.Two,xFlow P S x f=canonicalBasisWord (hubArmCoordinate P S q (z 0) c) := by
  have hbridge (i : Fin 3) :
      f (Sum.inr (subdivisionBoundaryEdgeEnd P x S
        (firstHubRectangle P S x q hxq (z i))))=0 := by
    rw [firstHubRectangle_end P A S hh]
    exact shared_bridge_zero P A S x f hw q (leaf i) (Ne.symm (hleaf i))
      hxq (hxleaf i) (z i) (lz i)
      (shared_Z_bridge_image P A S x q (leaf i) hxq (hxleaf i)
        (z i) (lz i) (hlz i).symm)
  have hval (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
      xFlow P S x f (hubArmCoordinate P S q (z i) c)=
      f (Sum.inl (c,(firstHubRectangle P S x q hxq (z i)).val)) := by
    unfold hubArmCoordinate
    rw [xFlow_at_q P A]
    simp only [dif_pos hxq,rxXQDegreeOne,wordPullback_apply]
    rfl
  have hpair (i j : Fin 3) :
      doubleCylinderCoboundary1 P x S f
          (Sum.inr (firstHubRectangle P S x q hxq (z i)))+
        doubleCylinderCoboundary1 P x S f
          (Sum.inr (firstHubRectangle P S x q hxq (z j)))=
      xFlow P S x f (hubArmCoordinate P S q (z i) 0)+
        xFlow P S x f (hubArmCoordinate P S q (z i) 1)+
        xFlow P S x f (hubArmCoordinate P S q (z j) 0)+
        xFlow P S x f (hubArmCoordinate P S q (z j) 1) := by
    rw [original_rectangle_pair P x S f _ _
      (firstHubRectangle_start P S x q hxq (z i) (z j)),hbridge i,hbridge j]
    simp only [zero_add,add_zero,hval]
    ac_rfl
  apply two_parities_force_first_arm (xFlow P S x f) hw
    (fun p : Fin 3 × BDL26FiniteTannerSquare.Two => hubArmCoordinate P S q (z p.1) p.2)
    (hubArmCoordinate_injective P S q z hz)
  · exact (hpair 0 2).symm.trans hrg
  · exact (hpair 1 2).symm.trans hvg
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

/-- A coordinate view of the ORIGINAL total component, not a new Cx
algorithm.  The original Classical.choose remains inside cxComponentTotal. -/
private noncomputable def originalCxWord (sigma : (CF).Syndrome U) (x : P.X) :
    Word BDL26Field (DoubleCylinderEdge P x S) :=
  (wordEquiv (xCorrectionEquiv P S x)).symm
    (restrictWordLinear ((LX).correctionRegion x) (cxComponentTotal G sigma.val x))

private theorem originalCxWord_boundary (sigma : (CF).Syndrome U) (x : P.X) :
    doubleCylinderCoboundary1 P x S (originalCxWord P A R S sigma x)=
      (wordEquiv (xSyndromeEquiv P S x)).symm
        (restrictWordLinear ((LX).syndromeRegion x) sigma.val) := by
  have hr : CxLocalRangeAt G sigma.val x :=
    (G).contract.cx_local_ranges_of_syndrome sigma x
  have hd := cxComponentTotal_local_delta G sigma.val x hr
  funext face
  have he := congrFun hd (xSyndromeEquiv P S x face)
  erw [localCx_delta1_apply] at he
  exact he

private theorem originalCxWord_budget (sigma : (CF).Syndrome U) (x : P.X) :
    HammingWeight (xFlow P S x (originalCxWord P A R S sigma x))≤
      HammingWeight ((wordEquiv (xSyndromeEquiv P S x)).symm
        (restrictWordLinear ((LX).syndromeRegion x) sigma.val)) := by
  have hr : CxLocalRangeAt G sigma.val x :=
    (G).contract.cx_local_ranges_of_syndrome sigma x
  have hw := cxComponentTotal_local_flow_weight G sigma.val x hr
  change HammingWeight (xFlow P S x (originalCxWord P A R S sigma x))≤_ at hw
  exact hw.trans_eq (wordEquiv_weight (xSyndromeEquiv P S x).symm _).symm

/-- Equality of the exact query identifies the SAME choice, irrespective
of the two range proofs.  No selector linearity is claimed. -/
private theorem originalCxWord_same_query
    (sigma tau : (CF).Syndrome U) (x : P.X)
    (hquery : restrictWordLinear ((LX).syndromeRegion x) sigma.val=
      restrictWordLinear ((LX).syndromeRegion x) tau.val) :
    originalCxWord P A R S sigma x=originalCxWord P A R S tau x := by
  have hs : CxLocalRangeAt G sigma.val x :=
    (G).contract.cx_local_ranges_of_syndrome sigma x
  have ht : CxLocalRangeAt G tau.val x :=
    (G).contract.cx_local_ranges_of_syndrome tau x
  have hcs : restrictWordLinear ((LX).correctionRegion x)
      (cxComponentTotal G sigma.val x)=
      Classical.choose ((G).contract.local_boundary_weight_budgets.cx x
        (restrictWordLinear ((LX).syndromeRegion x) sigma.val) hs) := by
    have he := congrArg (restrictWordLinear ((LX).correctionRegion x))
      (cxComponentTotal_eq_explicit G sigma.val x hs)
    exact he.trans (region_restrict_extend _ _)
  have hct : restrictWordLinear ((LX).correctionRegion x)
      (cxComponentTotal G tau.val x)=
      Classical.choose ((G).contract.local_boundary_weight_budgets.cx x
        (restrictWordLinear ((LX).syndromeRegion x) tau.val) ht) := by
    have he := congrArg (restrictWordLinear ((LX).correctionRegion x))
      (cxComponentTotal_eq_explicit G tau.val x ht)
    exact he.trans (region_restrict_extend _ _)
  have hc : ∀ (h : restrictWordLinear ((LX).syndromeRegion x) sigma.val∈
      LinearMap.range ((G).contract.rx_local_complexes.cxDelta1 x)),
      Classical.choose ((G).contract.local_boundary_weight_budgets.cx x
        (restrictWordLinear ((LX).syndromeRegion x) sigma.val) h)=
      Classical.choose ((G).contract.local_boundary_weight_budgets.cx x
        (restrictWordLinear ((LX).syndromeRegion x) tau.val) ht) := by
    rw [hquery]
    intro h
    rfl
  change (wordEquiv (xCorrectionEquiv P S x)).symm
      (restrictWordLinear ((LX).correctionRegion x) (cxComponentTotal G sigma.val x))=
    (wordEquiv (xCorrectionEquiv P S x)).symm
      (restrictWordLinear ((LX).correctionRegion x) (cxComponentTotal G tau.val x))
  exact congrArg ((wordEquiv (xCorrectionEquiv P S x)).symm)
    (hcs.trans ((hc hs).trans hct.symm))
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData

/-- The first-readout bridge uses the actual selected output and the complete
physical syndrome equality.  Its premise will be proved for the explicit
σ*=δ(α+qExtend W); it is not a normalization of an old logical defect. -/
private theorem original_rx_coarse_zero_of_full_boundary
    (S : OddScale) (depth : Nat) (i : StepIndex depth) (he : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (hfull : sigma.val=(indexedFamily S depth).coboundary1 i.succ
      (rxCorrectionTotal (D := indexedDecoderData S depth) (i := i) (rxData S depth i he) sigma.val)) :
    (rxStepOutput S depth i he sigma).coarse.val=0 := by
  have hform : rxSigmaAfterCq (D := indexedDecoderData S depth) (i := i) (rxData S depth i he) sigma.val=
      sigma.val+(indexedFamily S depth).coboundary1 i.succ
        (rxCorrectionTotal (D := indexedDecoderData S depth) (i := i) (rxData S depth i he) sigma.val) := by
    unfold rxSigmaAfterCq rxSigmaAfterCx rxCorrectionTotal
    rw [map_add]
    exact add_assoc _ _ _
  have hz : rxSigmaAfterCq (D := indexedDecoderData S depth) (i := i) (rxData S depth i he) sigma.val=0 := by
    calc
      _ = sigma.val+(indexedFamily S depth).coboundary1 i.succ
          (rxCorrectionTotal (D := indexedDecoderData S depth) (i := i) (rxData S depth i he) sigma.val) := hform
      _ = sigma.val+sigma.val := congrArg (fun t => sigma.val+t) hfull.symm
      _ = 0 := by
        funext p
        exact repair3_scalar_add_self (sigma.val p)
  funext z
  rw [rxStepOutput_coarse_readout,hz]
  rfl
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private def directXExtension (x : P.X)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S)) : (CF).Cochain1 U :=
  extendWordLinear ((LX).correctionRegion x)
    (wordEquiv (xCorrectionEquiv P S x) alpha)

private def directQExtension (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) : (CF).Cochain1 U :=
  extendWordLinear ((LQ).correctionRegion q)
    (wordEquiv (qCorrectionEquiv P S q) w)

private def pureXInput (x : P.X)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S)) : (CF).Syndrome U :=
  ⟨(CF).coboundary1 U (directXExtension P A R S x alpha),
    ⟨directXExtension P A R S x alpha,rfl⟩⟩

/-- The actual background is given with its FULL physical preimage,
including the hub's Q correction sector and its outgoing Z boundary. -/
private def directInput (x : P.X) (q : P.Q)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) : (CF).Syndrome U :=
  ⟨(CF).coboundary1 U
      (directXExtension P A R S x alpha+directQExtension P A R S q w),
    ⟨directXExtension P A R S x alpha+directQExtension P A R S q w,rfl⟩⟩

private theorem directQExtension_restrict_X (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (x : P.X) :
    restrictWordLinear ((LX).correctionRegion x) (directQExtension P A R S q w)=0 := by
  apply region_restrict_extend_disjoint
  apply Finset.disjoint_left.mpr
  intro p hpQ hpX
  apply Finset.disjoint_left.mp (G).correction_sectors_disjoint
    (Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hpX⟩)
  erw [(G).qCorrectionSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,hpQ⟩

/-- ALL original Cx queries of the final explicit background coincide with
those of its X-only preimage.  This is an equality before either choose. -/
private theorem directInput_all_X_queries (x : P.X) (q : P.Q)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (y : P.X) :
    restrictWordLinear ((LX).syndromeRegion y) (directInput P A R S x q alpha w).val=
      restrictWordLinear ((LX).syndromeRegion y) (pureXInput P A R S x alpha).val := by
  have hz : restrictWordLinear ((LX).syndromeRegion y)
      ((CF).coboundary1 U (directQExtension P A R S q w))=0 := by
    erw [(G).contract.support_decomposition.cxDelta1_restriction_global,
      directQExtension_restrict_X P A R S q w y,map_zero]
    all_goals rfl
  change restrictWordLinear ((LX).syndromeRegion y)
      ((CF).coboundary1 U
        (directXExtension P A R S x alpha+directQExtension P A R S q w))=_
  have hglobal := map_add ((CF).coboundary1 U)
    (directXExtension P A R S x alpha) (directQExtension P A R S q w)
  have hrestrict := congrArg (restrictWordLinear ((LX).syndromeRegion y)) hglobal
  have hsplit := map_add (restrictWordLinear ((LX).syndromeRegion y))
    ((CF).coboundary1 U (directXExtension P A R S x alpha))
    ((CF).coboundary1 U (directQExtension P A R S q w))
  exact hrestrict.trans (hsplit.trans
    ((congrArg (fun v =>
      restrictWordLinear ((LX).syndromeRegion y)
        ((CF).coboundary1 U (directXExtension P A R S x alpha))+v) hz).trans (add_zero _)))

private theorem directInput_original_Cx (x : P.X) (q : P.Q)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (y : P.X) :
    originalCxWord P A R S (directInput P A R S x q alpha w) y=
      originalCxWord P A R S (pureXInput P A R S x alpha) y :=
  originalCxWord_same_query P A R S _ _ y
    (directInput_all_X_queries P A R S x q alpha w y)

/-- Perturb the SAME original valid background by the one X-sector word.
The Q term is retained exactly; it is not chosen anew in the second run. -/
private theorem directInput_add_physical_word (x : P.X) (q : P.Q)
    (alpha e : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    CriticalOldXQueries.addError P A R S (directInput P A R S x q alpha w)
      (directXExtension P A R S x e)=directInput P A R S x q (alpha+e) w := by
  apply Subtype.ext
  change (CF).coboundary1 U
      (directXExtension P A R S x alpha+directQExtension P A R S q w)+
        (CF).coboundary1 U (directXExtension P A R S x e)=
      (CF).coboundary1 U
        (directXExtension P A R S x (alpha+e)+directQExtension P A R S q w)
  have hx : directXExtension P A R S x (alpha+e)=
      directXExtension P A R S x alpha+directXExtension P A R S x e := by
    exact map_add
      ((extendWordLinear ((LX).correctionRegion x)).comp
        (wordEquiv (xCorrectionEquiv P S x)).toLinearMap) alpha e
  rw [hx,map_add,map_add,map_add]
  ac_rfl

private theorem directXExtension_basis (x : P.X) (e : DoubleCylinderEdge P x S) :
    directXExtension P A R S x (canonicalBasisWord e)=
      canonicalBasisWord (Sum.inl ⟨x,e⟩ : RX1 P S) := by
  change xExtend P S x (canonicalBasisWord e)=_
  funext p
  rcases p with ⟨y,d⟩ | ⟨q,v⟩
  · by_cases hy : y=x
    · subst y
      rw [xExtend_at_x]
      simp [basis_value]
    · rw [xExtend_other P S x y hy]
      simp [basis_value,hy]
  · rw [xExtend_at_q]
    simp [basis_value]
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open BDL26RXDecoderAdapter BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators
/-- Applied to the original A-query, both actual rectangle parities vanish;
therefore its hub arms all vanish while any leaf output remains original. -/
private theorem actual_hub_zero_forced
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (hh : S.half=1) (x : P.X) (q : P.Q)
    (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f)≤1)
    (hrg : doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 0)))+
      doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 2)))=0)
    (hvg : doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 1)))+
      doubleCylinderCoboundary1 P x S f
        (Sum.inr (firstHubRectangle P S x q hxq (z 2)))=0) :
    ∀ i : Fin 3,∀ c : BDL26FiniteTannerSquare.Two,xFlow P S x f (hubArmCoordinate P S q (z i) c)=0 := by
  have hbridge (i : Fin 3) :
      f (Sum.inr (subdivisionBoundaryEdgeEnd P x S
        (firstHubRectangle P S x q hxq (z i))))=0 := by
    rw [firstHubRectangle_end P A S hh]
    exact shared_bridge_zero P A S x f hw q (leaf i) (Ne.symm (hleaf i))
      hxq (hxleaf i) (z i) (lz i)
      (shared_Z_bridge_image P A S x q (leaf i) hxq (hxleaf i)
        (z i) (lz i) (hlz i).symm)
  have hval (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
      xFlow P S x f (hubArmCoordinate P S q (z i) c)=
      f (Sum.inl (c,(firstHubRectangle P S x q hxq (z i)).val)) := by
    unfold hubArmCoordinate
    rw [xFlow_at_q P A]
    simp only [dif_pos hxq,rxXQDegreeOne,wordPullback_apply]
    rfl
  have hpair (i j : Fin 3) :
      doubleCylinderCoboundary1 P x S f
          (Sum.inr (firstHubRectangle P S x q hxq (z i)))+
        doubleCylinderCoboundary1 P x S f
          (Sum.inr (firstHubRectangle P S x q hxq (z j)))=
      xFlow P S x f (hubArmCoordinate P S q (z i) 0)+
        xFlow P S x f (hubArmCoordinate P S q (z i) 1)+
        xFlow P S x f (hubArmCoordinate P S q (z j) 0)+
        xFlow P S x f (hubArmCoordinate P S q (z j) 1) := by
    rw [original_rectangle_pair P x S f _ _
      (firstHubRectangle_start P S x q hxq (z i) (z j)),hbridge i,hbridge j]
    simp only [zero_add,add_zero,hval]
    ac_rfl
  have hzero := zero_parities_no_hub_arm (xFlow P S x f) hw
    (fun p : Fin 3 × BDL26FiniteTannerSquare.Two => hubArmCoordinate P S q (z p.1) p.2)
    (hubArmCoordinate_injective P S q z hz)
    ((hpair 0 2).symm.trans hrg) ((hpair 1 2).symm.trans hvg)
  intro i c
  exact hzero (i,c)
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private theorem firstHubRectangle_injective (x : P.X) (q : P.Q)
    (hxq : P.xq x q=true) :
    Function.Injective (firstHubRectangle P S x q hxq) := by
  intro z t h
  have he := qToXSubdivisionBoundaryEdge_injective P q x hxq S h
  exact congrArg Prod.fst he

/-- On a genuine hub-rectangle basis query, the actual original Cx choice
has exactly one r-hub exit.  All syndrome and budget premises are supplied
by the ORIGINAL component's public specification, not assumed of its output. -/
private theorem original_D_query_hub_exit
    (hh : S.half=1) (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (sigma : (CF).Syndrome U)
    (hquery : (wordEquiv (xSyndromeEquiv P S x)).symm
      (restrictWordLinear ((LX).syndromeRegion x) sigma.val)=
      canonicalBasisWord (Sum.inr (firstHubRectangle P S x q hxq (z 0)))) :
    ∃ c : BDL26FiniteTannerSquare.Two,xFlow P S x (originalCxWord P A R S sigma x)=
      canonicalBasisWord (hubArmCoordinate P S q (z 0) c) := by
  have hbd := originalCxWord_boundary P A R S sigma x
  rw [hquery] at hbd
  have hw := originalCxWord_budget P A R S sigma x
  rw [hquery,repair4_basis_weight_one] at hw
  have hd : Function.Injective (fun i : Fin 3 => firstHubRectangle P S x q hxq (z i)) :=
    (firstHubRectangle_injective P S x q hxq).comp hz
  have h02 : firstHubRectangle P S x q hxq (z 0)≠
      firstHubRectangle P S x q hxq (z 2) := fun h => (by decide : (0:Fin 3)≠2) (hd h)
  have h01 : firstHubRectangle P S x q hxq (z 0)≠
      firstHubRectangle P S x q hxq (z 1) := fun h => (by decide : (0:Fin 3)≠1) (hd h)
  apply actual_hub_exit_forced P A.toTannerSquareAdmissible S hh x q hxq
    z hz leaf hleaf hxleaf lz hlz (originalCxWord P A R S sigma x) hw
  · rw [hbd]
    simp [basis_value,h02,Ne.symm h02]
  · rw [hbd]
    simp [basis_value,h01,Ne.symm h01,h02,Ne.symm h02]

/-- A copy-square basis query has zero hub parities; its original choice
may retain a leaf arm, but cannot have any hub arm. -/
private theorem original_A_query_hub_zero
    (hh : S.half=1) (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (sigma : (CF).Syndrome U) (copy : BDL26FiniteTannerSquare.Two) (face : SubdivisionFace P x S)
    (hquery : (wordEquiv (xSyndromeEquiv P S x)).symm
      (restrictWordLinear ((LX).syndromeRegion x) sigma.val)=
      canonicalBasisWord (Sum.inl (copy,face))) :
    ∀ i : Fin 3,∀ c : BDL26FiniteTannerSquare.Two,
      xFlow P S x (originalCxWord P A R S sigma x)
        (hubArmCoordinate P S q (z i) c)=0 := by
  have hbd := originalCxWord_boundary P A R S sigma x
  rw [hquery] at hbd
  have hw := originalCxWord_budget P A R S sigma x
  rw [hquery,repair4_basis_weight_one] at hw
  apply actual_hub_zero_forced P A.toTannerSquareAdmissible S hh x q hxq
    z hz leaf hleaf hxleaf lz hlz (originalCxWord P A R S sigma x) hw
  · rw [hbd]
    simp [basis_value]
  · rw [hbd]
    simp [basis_value]
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open BDL26RXDecoderAdapter BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators

/-- Complete outgoing classification for the original square query.  The
three degree-one leaves and the three hub neighbours are the actual star;
the proof checks all X/Q/Z sectors and every arm/bridge constructor. -/
private theorem actual_A_flow_leaf_only
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (hh : S.half=1) (x : P.X) (q : P.Q)
    (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (zcover : Function.Surjective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (leaf_unique : ∀ i,∀ t : QStarEdge P (leaf i),t=lz i)
    (qcover : ∀ r : P.Q,P.xq x r=true → r=q ∨ ∃ i,r=leaf i)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f)≤1)
    (hhub : ∀ i c,xFlow P S x f (hubArmCoordinate P S q (z i) c)=0) :
    xFlow P S x f=0 ∨ ∃ i : Fin 3,∃ c : BDL26FiniteTannerSquare.Two,
      xFlow P S x f=canonicalBasisWord (hubArmCoordinate P S (leaf i) (lz i) c) := by
  rcases flow_weight_le_one_word (xFlow P S x f) hw with hz | ⟨p,hp⟩
  · exact Or.inl hz
  right
  have hp1 : xFlow P S x f p=1 := by rw [hp];simp [basis_value]
  rcases p with (⟨y,d⟩ | ⟨r,e⟩) | ⟨zz,c⟩
  · rw [xFlow_at_x] at hp1
    exact False.elim (zero_ne_one hp1)
  · have hxr : P.xq x r=true := by
      by_contra hn
      rw [xFlow_at_q P A,dif_neg hn] at hp1
      exact zero_ne_one hp1
    rcases qcover r hxr with hr | ⟨i,hr⟩
    · subst r
      rcases e with ⟨c,t,k⟩ | t
      · obtain ⟨i,rfl⟩ := zcover t
        have hk : k=⟨0,S.half_pos⟩ := Fin.ext (by have hi := k.isLt;omega)
        subst k
        have hzero := hhub i c
        exact False.elim (zero_ne_one (hzero.symm.trans hp1))
      · obtain ⟨i,rfl⟩ := zcover t
        have hzero := shared_bridge_zero P A S x f hw q (leaf i)
          (Ne.symm (hleaf i)) hxq (hxleaf i) (z i) (lz i)
          (shared_Z_bridge_image P A S x q (leaf i) hxq (hxleaf i)
            (z i) (lz i) (hlz i).symm)
        rw [xFlow_at_q P A,dif_pos hxq] at hp1
        change f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr (z i)))=1 at hp1
        exact False.elim (zero_ne_one (hzero.symm.trans hp1))
    · subst r
      rcases e with ⟨c,t,k⟩ | t
      · have ht := leaf_unique i t
        subst t
        have hk : k=⟨0,S.half_pos⟩ := Fin.ext (by have hi := k.isLt;omega)
        subst k
        exact ⟨i,c,hp⟩
      · have ht := leaf_unique i t
        subst t
        have hzero := shared_bridge_zero P A S x f hw (leaf i) q
          (hleaf i) (hxleaf i) hxq (lz i) (z i)
          (shared_Z_bridge_image P A S x (leaf i) q (hxleaf i) hxq
            (lz i) (z i) (hlz i))
        rw [xFlow_at_q P A,dif_pos (hxleaf i)] at hp1
        change f (qToXDoubleCylinderEdge P A (leaf i) x (hxleaf i) S (Sum.inr (lz i)))=1 at hp1
        exact False.elim (zero_ne_one (hzero.symm.trans hp1))
  · rw [xFlow_at_z] at hp1
    exact False.elim (zero_ne_one hp1)
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private theorem originalCxComponent_eq_extension (sigma : (CF).Syndrome U) (x : P.X) :
    cxComponentTotal G sigma.val x=
      directXExtension P A R S x (originalCxWord P A R S sigma x) := by
  have hr : CxLocalRangeAt G sigma.val x :=
    (G).contract.cx_local_ranges_of_syndrome sigma x
  have he := cxComponentTotal_eq_explicit G sigma.val x hr
  have hrest := congrArg (restrictWordLinear ((LX).correctionRegion x)) he
  have hrv := hrest.trans (region_restrict_extend _ _)
  have hsupport : extendWordLinear ((LX).correctionRegion x)
      (restrictWordLinear ((LX).correctionRegion x) (cxComponentTotal G sigma.val x))=
      cxComponentTotal G sigma.val x :=
    (congrArg (extendWordLinear ((LX).correctionRegion x)) hrv).trans he.symm
  have hword := LinearEquiv.apply_symm_apply (wordEquiv (xCorrectionEquiv P S x))
    (restrictWordLinear ((LX).correctionRegion x) (cxComponentTotal G sigma.val x))
  exact hsupport.symm.trans
    (congrArg (extendWordLinear ((LX).correctionRegion x)) hword.symm)

private theorem directXExtension_boundary (x : P.X)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) :
    (CF).coboundary1 U (directXExtension P A R S x f)=
      (show (CF).Cochain2 U from fun z =>
        extendWordLinear ((LX).syndromeRegion x)
          ((G).contract.rx_local_complexes.cxDelta1 x
            (wordEquiv (xCorrectionEquiv P S x) f)) z)+
      (show (CF).Cochain2 U from fun z => xFlow P S x f z) := by
  have h := (G).contract.support_decomposition.cxDelta1_decomposition x
    (wordEquiv (xCorrectionEquiv P S x) f)
  have hi := LinearEquiv.symm_apply_apply (wordEquiv (xCorrectionEquiv P S x)) f
  have hflow : (G).contract.support_decomposition.cxFlow x
      (wordEquiv (xCorrectionEquiv P S x) f)=
      (show (CF).Cochain2 U from fun z => xFlow P S x f z) :=
    congrArg (fun w : Word BDL26Field (DoubleCylinderEdge P x S) =>
      (show (CF).Cochain2 U from fun z => xFlow P S x w z)) hi
  funext z
  exact (congrFun h z).trans
    (congrArg (fun a : BDL26Field =>
      extendWordLinear ((LX).syndromeRegion x)
        ((G).contract.rx_local_complexes.cxDelta1 x
          (wordEquiv (xCorrectionEquiv P S x) f)) z+a) (congrFun hflow z))

private theorem originalCxWord_local_delta (sigma : (CF).Syndrome U) (x : P.X) :
    (G).contract.rx_local_complexes.cxDelta1 x
      (wordEquiv (xCorrectionEquiv P S x) (originalCxWord P A R S sigma x))=
        restrictWordLinear ((LX).syndromeRegion x) sigma.val := by
  have hword := LinearEquiv.apply_symm_apply (wordEquiv (xCorrectionEquiv P S x))
    (restrictWordLinear ((LX).correctionRegion x) (cxComponentTotal G sigma.val x))
  have ha := congrArg ((G).contract.rx_local_complexes.cxDelta1 x) hword
  exact ha.trans (cxComponentTotal_local_delta G sigma.val x
    ((G).contract.cx_local_ranges_of_syndrome sigma x))

private theorem originalCx_boundary_sum (sigma : (CF).Syndrome U) :
    (CF).coboundary1 U (cxCorrectionTotal G sigma.val)=
      (show (CF).Cochain2 U from fun z =>
        ∑ x : P.X,extendWordLinear ((LX).syndromeRegion x)
          (restrictWordLinear ((LX).syndromeRegion x) sigma.val) z)+
      (show (CF).Cochain2 U from fun z =>
        ∑ x : P.X,xFlow P S x (originalCxWord P A R S sigma x) z) := by
  change (CF).coboundary1 U (∑ x : P.X,cxComponentTotal G sigma.val x)=_
  rw [map_sum]
  funext z
  simp only [Finset.sum_apply,Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have he := congrArg ((CF).coboundary1 U)
    (originalCxComponent_eq_extension P A R S sigma x)
  have hd := directXExtension_boundary P A R S x (originalCxWord P A R S sigma x)
  have hl := congrArg (fun v => extendWordLinear ((LX).syndromeRegion x) v z)
    (originalCxWord_local_delta P A R S sigma x)
  exact (congrFun (he.trans hd) z).trans
    (congrArg (fun a : BDL26Field => a+xFlow P S x (originalCxWord P A R S sigma x) z) hl)

private theorem directXExtension_restrict_same (x : P.X)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S)) :
    restrictWordLinear ((LX).correctionRegion x) (directXExtension P A R S x alpha)=
      wordEquiv (xCorrectionEquiv P S x) alpha := by
  exact region_restrict_extend _ _

private theorem directXExtension_restrict_other (x y : P.X) (hy : y≠x)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S)) :
    restrictWordLinear ((LX).correctionRegion y) (directXExtension P A R S x alpha)=0 := by
  apply region_restrict_extend_disjoint
  exact (G).cx_correction_regions_pairwise_disjoint x y (Ne.symm hy)

private theorem directInput_query_same (x : P.X) (q : P.Q)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    restrictWordLinear ((LX).syndromeRegion x) (directInput P A R S x q alpha w).val=
      (G).contract.rx_local_complexes.cxDelta1 x
        (wordEquiv (xCorrectionEquiv P S x) alpha) := by
  rw [directInput_all_X_queries]
  change restrictWordLinear ((LX).syndromeRegion x)
    ((CF).coboundary1 U (directXExtension P A R S x alpha))=_
  erw [(G).contract.support_decomposition.cxDelta1_restriction_global,
    directXExtension_restrict_same]
  all_goals rfl

private theorem directInput_query_other (x : P.X) (q : P.Q)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (y : P.X) (hy : y≠x) :
    restrictWordLinear ((LX).syndromeRegion y) (directInput P A R S x q alpha w).val=0 := by
  rw [directInput_all_X_queries]
  change restrictWordLinear ((LX).syndromeRegion y)
    ((CF).coboundary1 U (directXExtension P A R S x alpha))=0
  erw [(G).contract.support_decomposition.cxDelta1_restriction_global,
    directXExtension_restrict_other P A R S x y hy,map_zero]
  all_goals rfl

private theorem originalCx_zero_query_flow (sigma : (CF).Syndrome U) (x : P.X)
    (hquery : restrictWordLinear ((LX).syndromeRegion x) sigma.val=0) :
    xFlow P S x (originalCxWord P A R S sigma x)=0 := by
  have hw := originalCxWord_budget P A R S sigma x
  have he := congrArg ((wordEquiv (xSyndromeEquiv P S x)).symm) hquery
  have hz := he.trans (map_zero ((wordEquiv (xSyndromeEquiv P S x)).symm))
  have hnorm := congrArg HammingWeight hz
  have hw0 : HammingWeight (xFlow P S x (originalCxWord P A R S sigma x))≤0 := by
    exact hw.trans_eq (hnorm.trans (by simp [HammingWeight,hammingSupport]))
  rcases flow_weight_le_one_word _ (hw0.trans (by decide : 0≤1)) with hz | ⟨p,hp⟩
  · exact hz
  · rw [hp,repair4_basis_weight_one] at hw0
    omega

include A R

/-- Entire global post-Cx syndrome of the EXPLICIT background.  In
particular the hub W's Z-sector boundary is preserved on the right-hand
side; this is stronger than checking just local Q equations. -/
private theorem directInput_after_Cx_global (x : P.X) (q : P.Q)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    rxSigmaAfterCx G (directInput P A R S x q alpha w).val=
      (show (CF).Cochain2 U from fun z => xFlow P S x alpha z)+
        (CF).coboundary1 U (directQExtension P A R S q w)+
      (show (CF).Cochain2 U from fun z =>
        xFlow P S x (originalCxWord P A R S (directInput P A R S x q alpha w) x) z) := by
  let sigma := directInput P A R S x q alpha w
  let a : (CF).Cochain2 U := fun z =>
    extendWordLinear ((LX).syndromeRegion x)
      ((G).contract.rx_local_complexes.cxDelta1 x
        (wordEquiv (xCorrectionEquiv P S x) alpha)) z
  let b : (CF).Cochain2 U := fun z => xFlow P S x alpha z
  let v : (CF).Cochain2 U := (CF).coboundary1 U (directQExtension P A R S q w)
  let d : (CF).Cochain2 U := fun z =>
    xFlow P S x (originalCxWord P A R S sigma x) z
  have hlocal : (fun z => ∑ y : P.X,extendWordLinear ((LX).syndromeRegion y)
      (restrictWordLinear ((LX).syndromeRegion y) sigma.val) z)=a := by
    funext z
    calc
      _ = extendWordLinear ((LX).syndromeRegion x)
          (restrictWordLinear ((LX).syndromeRegion x) sigma.val) z := by
        apply Finset.sum_eq_single x
        · intro y _ hy
          have he := directInput_query_other P A R S x q alpha w y hy
          have hm := congrArg (fun s => extendWordLinear ((LX).syndromeRegion y) s z) he
          exact hm.trans (congrFun (map_zero (extendWordLinear ((LX).syndromeRegion y))) z)
        · simp
      _ = a z := congrArg (fun s => extendWordLinear ((LX).syndromeRegion x) s z)
        (directInput_query_same P A R S x q alpha w)
  have hflows : (fun z => ∑ y : P.X,xFlow P S y (originalCxWord P A R S sigma y) z)=d := by
    funext z
    apply Finset.sum_eq_single x
    · intro y _ hy
      exact congrFun (originalCx_zero_query_flow P A R S sigma y
        (directInput_query_other P A R S x q alpha w y hy)) z
    · simp
  have hsigma : sigma.val=a+b+v := by
    have he := map_add ((CF).coboundary1 U)
      (directXExtension P A R S x alpha) (directQExtension P A R S q w)
    have hx := directXExtension_boundary P A R S x alpha
    exact he.trans (congrArg (fun s : (CF).Cochain2 U => s+v) hx)
  have hc : (CF).coboundary1 U (cxCorrectionTotal G sigma.val)=a+d := by
    exact (originalCx_boundary_sum P A R S sigma).trans
      (congrArg₂ (fun s t : (CF).Cochain2 U => s+t) hlocal hflows)
  change sigma.val+(CF).coboundary1 U (cxCorrectionTotal G sigma.val)=b+v+d
  rw [hc,hsigma]
  have hcancel : a+a=0 := by
    funext p
    exact repair3_scalar_add_self (a p)
  calc
    _ = (a+a)+(b+v+d) := by ac_rfl
    _ = _ := by rw [hcancel,zero_add]

private theorem original_after_Cx_from_columns (x : P.X) (q : P.Q)
    (alpha e : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (sigma : (CF).Syndrome U) (u v : Word BDL26Field (RX2 P S))
    (hsigma : sigma=directInput P A R S x q (alpha+e) w)
    (halpha : xFlow P S x alpha=0) (he : xFlow P S x e=u)
    (hcx : xFlow P S x (originalCxWord P A R S sigma x)=v) :
    rxSigmaAfterCx G sigma.val=
      (show (CF).Cochain2 U from fun z => u z)+
        (CF).coboundary1 U (directQExtension P A R S q w)+
      (show (CF).Cochain2 U from fun z => v z) := by
  have ha := directInput_after_Cx_global P A R S x q (alpha+e) w
  have ht := congrArg (fun t : (CF).Syndrome U => rxSigmaAfterCx G t.val) hsigma
  have hflow : xFlow P S x (alpha+e)=u :=
    (map_add (xFlow P S x) alpha e).trans
      ((congrArg₂ (fun a b : Word BDL26Field (RX2 P S) => a+b) halpha he).trans
        (zero_add u))
  have hc : xFlow P S x
      (originalCxWord P A R S (directInput P A R S x q (alpha+e) w) x)=v :=
    (congrArg (fun t : (CF).Syndrome U => xFlow P S x (originalCxWord P A R S t x))
      hsigma).symm.trans hcx
  funext z
  exact (congrFun (ht.trans ha) z).trans
    (congrArg₂ (fun a b : BDL26Field => a+b)
      (congrArg₂ (fun a b : BDL26Field => a+b) (congrFun hflow z) rfl)
      (congrFun hc z))

end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Assembly order is recorded in complete-counterexample-assembly.Source.json.
   The following instantiates the preceding proof maps with the ORIGINAL
   materialized state and no extra geometric hypotheses. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26DecodingGraph
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private abbrev AP (S : OddScale) := (state S 2).presentation
private abbrev AA (S : OddScale) := (state S 2).admissible
private abbrev AR (S : OddScale) := (state S 2).regular
private abbrev AX (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  ActualCriticalStarGeometry.x S j outer
private abbrev AH (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  ActualCriticalStarGeometry.b S j outer
private def AL (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) : (AP S).Q :=
  if i=0 then ActualCriticalStarGeometry.r S j outer else
  if i=1 then ActualCriticalStarGeometry.v S j outer else
    ActualCriticalStarGeometry.g S j outer
private def AZ (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) : (AP S).Z :=
  if i=0 then ActualCriticalStarGeometry.zr S j outer else
  if i=1 then ActualCriticalStarGeometry.zv S j outer else
    ActualCriticalStarGeometry.zg S j outer

private theorem AL_incident (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    (AP S).xq (AX S j outer) (AL S j outer i)=true := by
  fin_cases i
  all_goals exact ActualCriticalStarGeometry.terminal_incident S j outer _ _
private theorem AH_incident (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (AP S).xq (AX S j outer) (AH S j outer)=true :=
  ActualCriticalStarGeometry.terminal_incident S j outer _ _
private theorem AL_ne_hub (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    AL S j outer i≠AH S j outer := by
  have h := ActualCriticalStarGeometry.ports_distinct S j outer
  fin_cases i
  · exact h.1
  · exact Ne.symm h.2.2.2.1
  · exact Ne.symm h.2.2.2.2.1
private theorem AL_check (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    (AP S).qz (AL S j outer i) (AZ S j outer i)=true := by
  have h := ActualCriticalStarGeometry.leaf_unique S j outer
  fin_cases i
  · exact h.1.1
  · exact h.2.1.1
  · exact h.2.2.1
private theorem AH_check (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    (AP S).qz (AH S j outer) (AZ S j outer i)=true := by
  apply (ActualCriticalStarGeometry.hub_neighbours S j outer _).mpr
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
private def AHZ (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    QStarEdge (AP S) (AH S j outer) := ⟨AZ S j outer i,AH_check S j outer i⟩
private def ALZ (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    QStarEdge (AP S) (AL S j outer i) := ⟨AZ S j outer i,AL_check S j outer i⟩
private theorem AHZ_injective (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Function.Injective (AHZ S j outer) := by
  intro i k he
  have h := ActualCriticalStarGeometry.checks_distinct S j outer
  have hv := congrArg Subtype.val he
  fin_cases i <;> fin_cases k
  all_goals first | rfl | exact False.elim (h.1 hv) |
    exact False.elim (h.1 hv.symm) | exact False.elim (h.2.1 hv) |
    exact False.elim (h.2.1 hv.symm) | exact False.elim (h.2.2 hv) |
    exact False.elim (h.2.2 hv.symm)
private theorem AHZ_surjective (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Function.Surjective (AHZ S j outer) := by
  intro z
  rcases (ActualCriticalStarGeometry.hub_neighbours S j outer z.val).mp z.property with
      h | h | h
  · exact ⟨0,Subtype.ext h.symm⟩
  · exact ⟨1,Subtype.ext h.symm⟩
  · exact ⟨2,Subtype.ext h.symm⟩
private theorem ALZ_unique (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (i : Fin 3) (z : QStarEdge (AP S) (AL S j outer i)) :
    z=ALZ S j outer i := by
  apply Subtype.ext
  have h := ActualCriticalStarGeometry.leaf_unique S j outer
  fin_cases i
  · exact h.1.2 z.val z.property
  · exact h.2.1.2 z.val z.property
  · exact h.2.2.2 z.val z.property
private theorem actual_Q_cover (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (q : (AP S).Q) (hq : (AP S).xq (AX S j outer) q=true) :
    q=AH S j outer ∨ ∃ i : Fin 3,q=AL S j outer i := by
  rcases ActualCriticalStarGeometry.full_four_cover S j outer q hq with h | h | h | h
  · exact Or.inr ⟨0,h⟩
  · exact Or.inl h
  · exact Or.inr ⟨1,h⟩
  · exact Or.inr ⟨2,h⟩

private abbrev ASyndrome (S : OddScale) :=
  (literalDecoderData (AP S) (AA S) (AR S) S).family.Syndrome
    (Fin.succ (0 : StepIndex 1))

/-- The actual r-hub rectangle in the materialized P2 state. -/
private def actualHubD (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    SubdivisionBoundaryEdge (AP S) (AX S j outer) S :=
  firstHubRectangle (AP S) S (AX S j outer) (AH S j outer)
    (AH_incident S j outer) (AHZ S j outer 0)

private theorem actual_D_original_exit (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (sigma : ASyndrome S)
    (hquery : (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm
      (restrictWordLinear ((literalLx (AP S) (AA S) (AR S) S).syndromeRegion
        (AX S j outer)) sigma.val)=
      canonicalBasisWord (Sum.inr (actualHubD S j outer))) :
    ∃ c : BDL26FiniteTannerSquare.Two,xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S sigma (AX S j outer))=
      canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0) c) := by
  exact original_D_query_hub_exit (AP S) (AA S) (AR S) S hh
    (AX S j outer) (AH S j outer) (AH_incident S j outer)
    (AHZ S j outer) (AHZ_injective S j outer) (AL S j outer)
    (AL_ne_hub S j outer) (AL_incident S j outer) (ALZ S j outer)
    (fun _ => rfl) sigma hquery

private theorem actual_A_original_leaf_exit (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (sigma : ASyndrome S)
    (copy : BDL26FiniteTannerSquare.Two) (face : SubdivisionFace (AP S) (AX S j outer) S)
    (hquery : (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm
      (restrictWordLinear ((literalLx (AP S) (AA S) (AR S) S).syndromeRegion
        (AX S j outer)) sigma.val)=canonicalBasisWord (Sum.inl (copy,face))) :
    xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S sigma (AX S j outer))=0 ∨
    ∃ i : Fin 3,∃ c : BDL26FiniteTannerSquare.Two,xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S sigma (AX S j outer))=
      canonicalBasisWord (hubArmCoordinate (AP S) S (AL S j outer i) (ALZ S j outer i) c) := by
  have h0 := original_A_query_hub_zero (AP S) (AA S) (AR S) S hh
    (AX S j outer) (AH S j outer) (AH_incident S j outer)
    (AHZ S j outer) (AHZ_injective S j outer) (AL S j outer)
    (AL_ne_hub S j outer) (AL_incident S j outer) (ALZ S j outer)
    (fun _ => rfl) sigma copy face hquery
  have hw := originalCxWord_budget (AP S) (AA S) (AR S) S sigma (AX S j outer)
  rw [hquery,repair4_basis_weight_one] at hw
  exact actual_A_flow_leaf_only (AP S) (AA S).toTannerSquareAdmissible S hh
    (AX S j outer) (AH S j outer) (AH_incident S j outer)
    (AHZ S j outer) (AHZ_surjective S j outer) (AL S j outer)
    (AL_ne_hub S j outer) (AL_incident S j outer) (ALZ S j outer)
    (fun _ => rfl) (ALZ_unique S j outer) (actual_Q_cover S j outer)
    (originalCxWord (AP S) (AA S) (AR S) S sigma (AX S j outer)) hw h0
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare
open scoped Classical BigOperators

private theorem doubleCylinder_basis_column
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : DoubleCylinderEdge P x S) (f : DoubleCylinderFace P x S) :
    doubleCylinderCoboundary1 P x S (canonicalBasisWord e) f=
      doubleCylinderFaceEdgeMatrix P x S e f := by
  rw [doubleCylinderCoboundary1,doubleCylinderBoundary2,
    wordLinearMapTranspose_toLin'_apply]
  simp [basis_value]

/-- At the actual half-one scale every subdivided face is its original
square. This is a proof of the original matrix formula, without enumerating
or replacing the physical carrier. -/
private theorem halfOne_subdivision_original_column
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) (hh : S.half=1)
    (e : XStarEdge P x) (f : XStarFace P x) :
    subdivisionFaceEdgeMatrix P x S (Sum.inl (e,⟨0,S.half_pos⟩))
      (f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩)=faceEdgeMatrix P e.val f.val := by
  classical
  let k : Fin S.half := ⟨0,S.half_pos⟩
  let z : Fin (S.half+1) := ⟨0,by omega⟩
  let o : Fin (S.half+1) := ⟨1,by omega⟩
  have h0 : (0 : Nat) ≠ S.half := by omega
  have h1 : (1 : Nat) = S.half := hh.symm
  have hH0 : subdivisionHorizontalEdge P x S f k z=
      Sum.inl (xStarFaceXQEdge P x f 0,k) := by
    exact dif_pos rfl
  have hV0 : subdivisionVerticalEdge P x S f z k=
      Sum.inl (xStarFaceXQEdge P x f 1,k) := by
    exact dif_pos rfl
  have hH1 : subdivisionHorizontalEdge P x S f k o=
      Sum.inl (xStarFaceQZEdge P x f 1,k) := by
    exact (dif_neg (by decide : (1:Nat)≠0)).trans (dif_pos h1)
  have hV1 : subdivisionVerticalEdge P x S f o k=
      Sum.inl (xStarFaceQZEdge P x f 0,k) := by
    exact (dif_neg (by decide : (1:Nat)≠0)).trans (dif_pos h1)
  change (((if Sum.inl (e,k)=subdivisionHorizontalEdge P x S f k z then (1:BDL26Field) else 0)+
    (if Sum.inl (e,k)=subdivisionVerticalEdge P x S f o k then 1 else 0))+
    (if Sum.inl (e,k)=subdivisionHorizontalEdge P x S f k o then 1 else 0))+
    (if Sum.inl (e,k)=subdivisionVerticalEdge P x S f z k then 1 else 0)=_
  rw [hH0,hV1,hH1,hV0]
  simp only [Sum.inl.injEq,Prod.mk.injEq,and_true,faceEdgeMatrix,
    xStarFaceXQEdge,xStarFaceQZEdge,Subtype.ext_iff]
  ac_rfl

/-- The original radial column tests the two original Q corners.  Their
injectivity excludes a duplicate contribution in characteristic two. -/
private theorem radial_cellular_column
    (P : TannerSquarePresentation) (x : P.X) (r : P.Q)
    (hx : P.xq x r=true) (f : P.Face) (hfx : P.faceX f=x) :
    faceEdgeMatrix P (Sum.inl ⟨(x,r),hx⟩) f=
      if r=P.faceQ f 0 ∨ r=P.faceQ f 1 then 1 else 0 := by
  have hn : P.faceQ f 0≠P.faceQ f 1 :=
    fun h => (by decide : (0:BDL26FiniteTannerSquare.Two)≠1) (P.faceQ_injective f h)
  by_cases h0 : r=P.faceQ f 0
  · have h1 : r≠P.faceQ f 1 := fun h => hn (h0.symm.trans h)
    simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hfx,h0,h1,hn,Ne.symm hn]
  · by_cases h1 : r=P.faceQ f 1
    · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hfx,h0,h1,hn,Ne.symm hn]
    · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hfx,h0,h1,hn,Ne.symm hn]

private theorem QZ_cellular_column
    (P : TannerSquarePresentation) (q : P.Q) (z : P.Z)
    (hq : P.qz q z=true) (f : P.Face) :
    faceEdgeMatrix P (Sum.inr ⟨(q,z),hq⟩) f=
      if z=P.faceZ f ∧ (q=P.faceQ f 0 ∨ q=P.faceQ f 1) then 1 else 0 := by
  have hn : P.faceQ f 0≠P.faceQ f 1 :=
    fun h => (by decide : (0:BDL26FiniteTannerSquare.Two)≠1) (P.faceQ_injective f h)
  by_cases hz : z=P.faceZ f
  · by_cases h0 : q=P.faceQ f 0
    · have h1 : q≠P.faceQ f 1 := fun h => hn (h0.symm.trans h)
      simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hz,h0,h1,hn,Ne.symm hn]
    · by_cases h1 : q=P.faceQ f 1
      · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hz,h0,h1,hn,Ne.symm hn]
      · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hz,h0,h1,hn,Ne.symm hn]
  · simp [faceEdgeMatrix,faceXQEdge,faceQZEdge,hz]
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26DecodingGraph
open scoped Classical BigOperators

private def actualStarFace (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    XStarFace (AP S) (AX S j outer) :=
  ⟨ActualCriticalStarGeometry.fr S j outer,by
    have hfx : (AP S).faceX (ActualCriticalStarGeometry.fr S j outer)=AX S j outer :=
      ActualCriticalStarGeometry.faceFromShared_X
        (AP S) (AX S j outer) (AZ S j outer 0) (AL S j outer 0)
        (AL_incident S j outer 0) (AL_check S j outer 0)
    simpa only [xStarFaceMember,decide_eq_true_eq] using hfx⟩
private def actualRadialStarEdge (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    XStarEdge (AP S) (AX S j outer) :=
  xStarFaceXQEdge (AP S) (AX S j outer) (actualStarFace S j outer)
    (ActualCriticalStarGeometry.cr S j outer)
private def actualHubStarEdge (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    XStarEdge (AP S) (AX S j outer) :=
  xStarBoundaryEdgeToStar (AP S) (AX S j outer)
    (qToXBoundaryEdge (AP S) (AH S j outer) (AX S j outer)
      (AH_incident S j outer) (AHZ S j outer 0))
private def actualSmallFace (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    SubdivisionFace (AP S) (AX S j outer) S :=
  (actualStarFace S j outer,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩)
private def actualAlphaEdge (S : OddScale) (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    DoubleCylinderEdge (AP S) (AX S j outer) S :=
  Sum.inl (c,Sum.inl (actualRadialStarEdge S j outer,⟨0,S.half_pos⟩))
private def actualErrorEdge (S : OddScale) (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    DoubleCylinderEdge (AP S) (AX S j outer) S :=
  Sum.inl (c,(actualHubD S j outer).val)

private theorem actualRadialStarEdge_value (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (actualRadialStarEdge S j outer).val=
      Sum.inl ⟨(AX S j outer,AL S j outer 0),AL_incident S j outer 0⟩ := by
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · change (AP S).faceX (ActualCriticalStarGeometry.fr S j outer)=AX S j outer
    exact ActualCriticalStarGeometry.faceFromShared_X (AP S) (AX S j outer)
      (AZ S j outer 0) (AL S j outer 0)
      (AL_incident S j outer 0) (AL_check S j outer 0)
  · change (AP S).faceQ (ActualCriticalStarGeometry.fr S j outer)
      (ActualCriticalStarGeometry.cr S j outer)=AL S j outer 0
    have hr : AL S j outer 0=ActualCriticalStarGeometry.r S j outer := by
      simp only [AL,if_pos rfl,if_true]
    exact (ActualCriticalStarGeometry.fr_leaf_corner S j outer).trans hr.symm

private theorem actual_radial_incident_face (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (f : XStarFace (AP S) (AX S j outer)) :
    (AL S j outer 0=(AP S).faceQ f.val 0 ∨
      AL S j outer 0=(AP S).faceQ f.val 1) ↔ f=actualStarFace S j outer := by
  constructor
  · intro hf
    have hqz : (AP S).qz (AL S j outer 0) ((AP S).faceZ f.val)=true := by
      rcases hf with h | h
      · simpa only [h] using (AP S).data.faceQ_qz f.val 0
      · simpa only [h] using (AP S).data.faceQ_qz f.val 1
    have hz : (AP S).faceZ f.val=AZ S j outer 0 :=
      (ActualCriticalStarGeometry.leaf_unique S j outer).1.2 _ hqz
    apply Subtype.ext
    apply (AR S).faceXZ_injective
    apply Prod.ext
    · exact (show (AP S).faceX f.val=AX S j outer from by
        simpa only [xStarFaceMember,decide_eq_true_eq] using f.property).trans
        (show (AP S).faceX (actualStarFace S j outer).val=AX S j outer from by
          simpa only [xStarFaceMember,decide_eq_true_eq] using (actualStarFace S j outer).property).symm
    · exact hz.trans (ActualCriticalStarGeometry.faceFromShared_Z (AP S) (AX S j outer) (AZ S j outer 0) (AL S j outer 0) (AL_incident S j outer 0) (AL_check S j outer 0)).symm
  · intro hf
    subst f
    have hr : AL S j outer 0=ActualCriticalStarGeometry.r S j outer := by
      simp only [AL,if_pos rfl,if_true]
    have h : (AP S).faceQ (actualStarFace S j outer).val
        (ActualCriticalStarGeometry.cr S j outer)=AL S j outer 0 :=
      (ActualCriticalStarGeometry.fr_leaf_corner S j outer).trans hr.symm
    have hc := two_eq_zero_or_one
      (ActualCriticalStarGeometry.cr S j outer)
    rcases hc with hc | hc
    · exact Or.inl (by simpa only [hc] using h.symm)
    · exact Or.inr (by simpa only [hc] using h.symm)

private theorem actual_radial_original_matrix (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (f : XStarFace (AP S) (AX S j outer)) :
    faceEdgeMatrix (AP S) (actualRadialStarEdge S j outer).val f.val=
      if f=actualStarFace S j outer then 1 else 0 := by
  rw [actualRadialStarEdge_value,radial_cellular_column]
  · exact indicator_iff _ _ (actual_radial_incident_face S j outer f)
  · simpa [xStarFaceMember] using f.property

private theorem actual_hub_original_matrix (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (f : XStarFace (AP S) (AX S j outer)) :
    faceEdgeMatrix (AP S) (actualHubStarEdge S j outer).val f.val=
      if f=actualStarFace S j outer then 1 else 0 := by
  change faceEdgeMatrix (AP S)
    (Sum.inr ⟨(AH S j outer,AZ S j outer 0),AH_check S j outer 0⟩) f.val=_
  rw [QZ_cellular_column]
  have hiff : (AZ S j outer 0=(AP S).faceZ f.val ∧
      (AH S j outer=(AP S).faceQ f.val 0 ∨ AH S j outer=(AP S).faceQ f.val 1)) ↔
      f=actualStarFace S j outer := by
    constructor
    · intro h
      apply Subtype.ext
      apply (AR S).faceXZ_injective
      apply Prod.ext
      · exact (show (AP S).faceX f.val=AX S j outer from by
        simpa only [xStarFaceMember,decide_eq_true_eq] using f.property).trans
          (show (AP S).faceX (actualStarFace S j outer).val=AX S j outer from by
            simpa only [xStarFaceMember,decide_eq_true_eq] using (actualStarFace S j outer).property).symm
      · exact h.1.symm.trans (ActualCriticalStarGeometry.faceFromShared_Z (AP S) (AX S j outer) (AZ S j outer 0) (AL S j outer 0) (AL_incident S j outer 0) (AL_check S j outer 0)).symm
    · intro hf
      subst f
      refine ⟨(ActualCriticalStarGeometry.faceFromShared_Z (AP S) (AX S j outer) (AZ S j outer 0) (AL S j outer 0) (AL_incident S j outer 0) (AL_check S j outer 0)).symm,?_⟩
      have h : (AP S).faceQ (actualStarFace S j outer).val
          (ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer))=
            AH S j outer := ActualCriticalStarGeometry.fr_hub_corner S j outer
      have hc := two_eq_zero_or_one
        (ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer))
      rcases hc with hc | hc
      · exact Or.inl (by simpa only [hc] using h.symm)
      · exact Or.inr (by simpa only [hc] using h.symm)
  exact indicator_iff _ _ hiff

private theorem nested_scalar_indicator (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (if q then (1:BDL26Field) else 0) else 0)=
      (if p ∧ q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp,hq,if_true,if_false,true_and,false_and,and_true,and_false]

private theorem copied_square_basis_value (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f f0 : XStarFace P x) (k : Fin S.half)
    (c d : BDL26FiniteTannerSquare.Two) :
    (canonicalBasisWord (F:=BDL26Field) (Sum.inl (c,f0,k,k)) :
      Word BDL26Field (DoubleCylinderFace P x S)) (Sum.inl (d,f,k,k))=
        (if c=d ∧ f=f0 then 1 else 0) := by
  let point : DoubleCylinderFace P x S := Sum.inl (d,f,k,k)
  let target : DoubleCylinderFace P x S := Sum.inl (c,f0,k,k)
  have hi : point=target ↔ c=d ∧ f=f0 := by
    constructor
    · intro h
      have hp : (d,f,k,k)=(c,f0,k,k) := Sum.inl.inj h
      exact ⟨(congrArg Prod.fst hp).symm,congrArg (fun z => z.2.1) hp⟩
    · rintro ⟨hc,hf⟩
      cases hc
      cases hf
      rfl
  by_cases hp : point=target
  · exact ((basis_value (I:=DoubleCylinderFace P x S) target point).trans (if_pos hp)).trans
      (if_pos (hi.mp hp)).symm
  · exact ((basis_value (I:=DoubleCylinderFace P x S) target point).trans (if_neg hp)).trans
      (if_neg (fun hq => hp (hi.mpr hq))).symm

/-- The actual alpha radial is a one-square syndrome and has no rectangle
component. The proof checks every original small face and rectangle. -/
private theorem actualAlpha_boundary (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (AP S) (AX S j outer) S
      (canonicalBasisWord (actualAlphaEdge S j outer c))=
      canonicalBasisWord (Sum.inl (c,actualSmallFace S j outer)) := by
  funext face
  rw [doubleCylinder_basis_column]
  rcases face with ⟨d,f,i,k⟩ | rect
  · have hi : i=⟨0,S.half_pos⟩ := Fin.ext (by have h := i.isLt;omega)
    have hk : k=⟨0,S.half_pos⟩ := Fin.ext (by have h := k.isLt;omega)
    subst i
    subst k
    change (if c=d then subdivisionFaceEdgeMatrix (AP S) (AX S j outer) S
      (Sum.inl (actualRadialStarEdge S j outer,⟨0,S.half_pos⟩))
      (f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩) else 0)=_
    rw [halfOne_subdivision_original_column _ _ _ hh,actual_radial_original_matrix]
    exact (nested_scalar_indicator (c=d) (f=actualStarFace S j outer)).trans
      (copied_square_basis_value (AP S) (AX S j outer) S f (actualStarFace S j outer)
        ⟨0,S.half_pos⟩ c d).symm
  · have hne : (Sum.inl (actualRadialStarEdge S j outer,⟨0,S.half_pos⟩) :
        SubdivisionEdge (AP S) (AX S j outer) S)≠rect.val := by
      intro he
      have hr := rect.property
      rw [← he] at hr
      change xStarBoundaryEdgeMember (AP S) (AX S j outer)
        (actualRadialStarEdge S j outer).val=true at hr
      rw [actualRadialStarEdge_value] at hr
      change false=true at hr
      cases hr
    change (if (Sum.inl (actualRadialStarEdge S j outer,⟨0,S.half_pos⟩) :
        SubdivisionEdge (AP S) (AX S j outer) S)=rect.val then (1:BDL26Field) else 0)=_
    have hz : (canonicalBasisWord (F:=BDL26Field) (Sum.inl (c,actualSmallFace S j outer)) :
        Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S)) (Sum.inr rect)=0 :=
      (basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
        (Sum.inl (c,actualSmallFace S j outer)) (Sum.inr rect)).trans
          (if_neg (by intro h;cases h))
    exact (if_neg hne).trans hz.symm

/-- The SAME actual hub-arm physical basis differs by the one hub
rectangle: δe=A_rc+D_r, with its full copied square term retained. -/
private theorem actualError_boundary (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (AP S) (AX S j outer) S
      (canonicalBasisWord (actualErrorEdge S j outer c))=
      canonicalBasisWord (Sum.inl (c,actualSmallFace S j outer))+
        canonicalBasisWord (Sum.inr (actualHubD S j outer)) := by
  funext face
  rw [doubleCylinder_basis_column]
  rcases face with ⟨d,f,i,k⟩ | rect
  · have hi : i=⟨0,S.half_pos⟩ := Fin.ext (by have h := i.isLt;omega)
    have hk : k=⟨0,S.half_pos⟩ := Fin.ext (by have h := k.isLt;omega)
    subst i
    subst k
    change (if c=d then subdivisionFaceEdgeMatrix (AP S) (AX S j outer) S
      (Sum.inl (actualHubStarEdge S j outer,⟨0,S.half_pos⟩))
      (f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩) else 0)=_
    rw [halfOne_subdivision_original_column _ _ _ hh,actual_hub_original_matrix]
    have hs := copied_square_basis_value (AP S) (AX S j outer) S f
      (actualStarFace S j outer) ⟨0,S.half_pos⟩ c d
    have hz : (canonicalBasisWord (F:=BDL26Field) (Sum.inr (actualHubD S j outer)) :
        Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S))
        (Sum.inl (d,f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩))=0 :=
      (basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
        (Sum.inr (actualHubD S j outer))
        (Sum.inl (d,f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩))).trans
          (if_neg (by intro h;cases h))
    exact (nested_scalar_indicator (c=d) (f=actualStarFace S j outer)).trans
      ((congrArg₂ (fun a b : BDL26Field => a+b) hs hz).trans (add_zero _)).symm
  · change (if (actualHubD S j outer).val=rect.val then (1:BDL26Field) else 0)=_
    have hs : (canonicalBasisWord (F:=BDL26Field) (Sum.inl (c,actualSmallFace S j outer)) :
        Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S)) (Sum.inr rect)=0 :=
      (basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
        (Sum.inl (c,actualSmallFace S j outer)) (Sum.inr rect)).trans
          (if_neg (by intro h;cases h))
    have he : (Sum.inr rect : DoubleCylinderFace (AP S) (AX S j outer) S)=
        Sum.inr (actualHubD S j outer) ↔ (actualHubD S j outer).val=rect.val := by
      constructor
      · intro h
        exact (congrArg Subtype.val (Sum.inr.inj h)).symm
      · intro h
        exact congrArg Sum.inr (Subtype.ext h.symm)
    have hr : (canonicalBasisWord (F:=BDL26Field) (Sum.inr (actualHubD S j outer)) :
        Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S)) (Sum.inr rect)=
          (if (actualHubD S j outer).val=rect.val then (1:BDL26Field) else 0) := by
      by_cases hp : (Sum.inr rect : DoubleCylinderFace (AP S) (AX S j outer) S)=
          Sum.inr (actualHubD S j outer)
      · exact ((basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
          (Sum.inr (actualHubD S j outer)) (Sum.inr rect)).trans (if_pos hp)).trans
            (if_pos (he.mp hp)).symm
      · exact ((basis_value (I:=DoubleCylinderFace (AP S) (AX S j outer) S)
          (Sum.inr (actualHubD S j outer)) (Sum.inr rect)).trans (if_neg hp)).trans
            (if_neg (fun hq => hp (he.mpr hq))).symm
    exact ((congrArg₂ (fun a b : BDL26Field => a+b) hs hr).trans (zero_add _)).symm
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))
private theorem pureXInput_raw_query (x : P.X)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) :
    (wordEquiv (xSyndromeEquiv P S x)).symm
      (restrictWordLinear ((LX).syndromeRegion x) (pureXInput P A R S x f).val)=
      doubleCylinderCoboundary1 P x S f := by
  have hd : restrictWordLinear ((LX).syndromeRegion x) (pureXInput P A R S x f).val=
      (G).contract.rx_local_complexes.cxDelta1 x (wordEquiv (xCorrectionEquiv P S x) f) := by
    change restrictWordLinear ((LX).syndromeRegion x)
      ((CF).coboundary1 U (directXExtension P A R S x f))=_
    erw [(G).contract.support_decomposition.cxDelta1_restriction_global,
      directXExtension_restrict_same]
    all_goals rfl
  rw [hd]
  funext face
  change (G).contract.rx_local_complexes.cxDelta1 x
    (wordEquiv (xCorrectionEquiv P S x) f) (xSyndromeEquiv P S x face)=_
  erw [localCx_delta1_apply,LinearEquiv.symm_apply_apply]
  rfl

private theorem directInput_raw_query_same (x : P.X) (q : P.Q)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    (wordEquiv (xSyndromeEquiv P S x)).symm
      (restrictWordLinear ((LX).syndromeRegion x) (directInput P A R S x q alpha w).val)=
      doubleCylinderCoboundary1 P x S alpha := by
  have hr := directInput_all_X_queries P A R S x q alpha w x
  exact (congrArg (wordEquiv (xSyndromeEquiv P S x)).symm hr).trans
    (pureXInput_raw_query P A R S x alpha)
end

private def fixedDInput (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : ASyndrome S :=
  pureXInput (AP S) (AA S) (AR S) S (AX S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer 0)+
     canonicalBasisWord (actualErrorEdge S j outer 0))

private theorem fixedDInput_raw_query (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm
      (restrictWordLinear ((literalLx (AP S) (AA S) (AR S) S).syndromeRegion
        (AX S j outer)) (fixedDInput S j outer).val)=
      canonicalBasisWord (Sum.inr (actualHubD S j outer)) := by
  have h := pureXInput_raw_query (AP S) (AA S) (AR S) S (AX S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer 0)+
      canonicalBasisWord (actualErrorEdge S j outer 0))
  have hd := (map_add (doubleCylinderCoboundary1 (AP S) (AX S j outer) S)
    (canonicalBasisWord (actualAlphaEdge S j outer 0))
    (canonicalBasisWord (actualErrorEdge S j outer 0))).trans
      (congrArg₂ (fun a b : Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S) => a+b)
        (actualAlpha_boundary S hh j outer 0) (actualError_boundary S hh j outer 0))
  refine h.trans (hd.trans ?_)
  funext face
  let a : BDL26Field := canonicalBasisWord (Sum.inl (0,actualSmallFace S j outer)) face
  let d : BDL26Field := canonicalBasisWord (Sum.inr (actualHubD S j outer)) face
  change a+(a+d)=d
  rw [← add_assoc,repair3_scalar_add_self,zero_add]

/-- This proof coordinate is defined from a FIXED, already valid D-query.
It does not run a new decoder and does not depend on the eventual error copy. -/
private noncomputable def chosenHubCopy (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two :=
  Classical.choose (actual_D_original_exit S hh j outer (fixedDInput S j outer)
    (fixedDInput_raw_query S hh j outer))
private theorem chosenHubCopy_spec (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S (fixedDInput S j outer) (AX S j outer))=
      canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0)
        (chosenHubCopy S hh j outer)) :=
  Classical.choose_spec (actual_D_original_exit S hh j outer (fixedDInput S j outer)
    (fixedDInput_raw_query S hh j outer))
private def oppositeErrorCopy (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two :=
  ActualCriticalStarGeometry.opposite (chosenHubCopy S hh j outer)
private theorem oppositeErrorCopy_ne (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    oppositeErrorCopy S hh j outer≠chosenHubCopy S hh j outer :=
  ActualCriticalStarGeometry.opposite_ne _

private def directHubW (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Word BDL26Field (QDoubleCylinderVertex (AP S) (AH S j outer) S) :=
  CriticalOriginalChoice.coneWord (AP S) (AH S j outer) S 0+
    CriticalOriginalChoice.terminalWord (AP S) (AH S j outer) S 0 (AHZ S j outer 2)+
    CriticalOriginalChoice.terminalWord (AP S) (AH S j outer) S 1 (AHZ S j outer 2)

/-- The sole final background, fixed before taking either actual history.
Its validity follows from its explicit full physical preimage. -/
private def counterexampleInput (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : ASyndrome S :=
  directInput (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer (oppositeErrorCopy S hh j outer)))
    (directHubW S j outer)

private def counterexamplePhysicalEdge (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : DoubleCylinderEdge (AP S) (AX S j outer) S :=
  actualErrorEdge S j outer (oppositeErrorCopy S hh j outer)

/-- This is literally ONE original physical coordinate. The outer owner
and the opposite new-cylinder copy are different tags and both are retained. -/
private def counterexamplePhysical (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26CSSHamiltonian.Physical S 3 :=
  BDL26RXPhysicalCoordinateTrace.oldXPhysical S 1 (by decide)
    (seedQNode S j) outer (counterexamplePhysicalEdge S hh j outer)

private theorem second_D_query_same_original_choice (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    originalCxWord (AP S) (AA S) (AR S) S
      (directInput (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
        (canonicalBasisWord (actualAlphaEdge S j outer (oppositeErrorCopy S hh j outer))+
         canonicalBasisWord (counterexamplePhysicalEdge S hh j outer))
        (directHubW S j outer)) (AX S j outer)=
    originalCxWord (AP S) (AA S) (AR S) S (fixedDInput S j outer) (AX S j outer) := by
  rw [directInput_original_Cx]
  apply originalCxWord_same_query
  apply (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm.injective
  let c := oppositeErrorCopy S hh j outer
  have h := pureXInput_raw_query (AP S) (AA S) (AR S) S (AX S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer c)+
      canonicalBasisWord (actualErrorEdge S j outer c))
  have hd := (map_add (doubleCylinderCoboundary1 (AP S) (AX S j outer) S)
    (canonicalBasisWord (actualAlphaEdge S j outer c))
    (canonicalBasisWord (actualErrorEdge S j outer c))).trans
      (congrArg₂ (fun a b : Word BDL26Field (DoubleCylinderFace (AP S) (AX S j outer) S) => a+b)
        (actualAlpha_boundary S hh j outer c) (actualError_boundary S hh j outer c))
  have hc : doubleCylinderCoboundary1 (AP S) (AX S j outer) S
      (canonicalBasisWord (actualAlphaEdge S j outer c)+
        canonicalBasisWord (actualErrorEdge S j outer c))=
      canonicalBasisWord (Sum.inr (actualHubD S j outer)) := by
    refine hd.trans ?_
    funext face
    let a : BDL26Field := canonicalBasisWord (Sum.inl (c,actualSmallFace S j outer)) face
    let d : BDL26Field := canonicalBasisWord (Sum.inr (actualHubD S j outer)) face
    change a+(a+d)=d
    rw [← add_assoc,repair3_scalar_add_self,zero_add]
  exact (h.trans hc).trans (fixedDInput_raw_query S hh j outer).symm
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private noncomputable def originalCqWord (sigma : (CF).Syndrome U) (q : P.Q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  (wordEquiv (qCorrectionEquiv P S q)).symm
    (restrictWordLinear ((LQ).correctionRegion q) (cqComponentTotal G sigma.val q))

/-- The cleaned full-background query identifies the actual ORIGINAL Cq
choice. Both ranges are proved by the unchanged decoder's contract. -/
private theorem originalCqWord_of_query (sigma : (CF).Syndrome U) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (hq : (wordEquiv (qSyndromeEquiv P S q)).symm
      (restrictWordLinear ((LQ).syndromeRegion q) (rxSigmaAfterCx G sigma.val))=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) :
    originalCqWord P A R S sigma q=CriticalOriginalChoice.originalChoice P A R S q w := by
  have hlocal : restrictWordLinear ((LQ).syndromeRegion q) (rxSigmaAfterCx G sigma.val)=
      (G).contract.rx_local_complexes.cqDelta1 q (wordEquiv (qCorrectionEquiv P S q) w) := by
    apply (wordEquiv (qSyndromeEquiv P S q)).symm.injective
    have ht := CriticalDegreeOneBudget.actual_local_delta_transport P A R S q w
    have hi := LinearEquiv.symm_apply_apply (wordEquiv (qSyndromeEquiv P S q))
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w)
    exact hq.trans ((congrArg (wordEquiv (qSyndromeEquiv P S q)).symm ht).trans hi).symm
  unfold originalCqWord
  rw [CriticalOldXQueries.actual_cq_choice P A R S sigma q
    (wordEquiv (qCorrectionEquiv P S q) w) hlocal]
  rfl

private theorem originalCqComponent_eq_extension (sigma : (CF).Syndrome U) (q : P.Q) :
    cqComponentTotal G sigma.val q=
      directQExtension P A R S q (originalCqWord P A R S sigma q) := by
  have hr : CqLocalRangeAt G sigma.val q :=
    CriticalOldXQueries.original_cq_ranges P A R S sigma q
  have he := cqComponentTotal_eq_explicit G sigma.val q hr
  have hrest := congrArg (restrictWordLinear ((LQ).correctionRegion q)) he
  have hrv := hrest.trans (region_restrict_extend _ _)
  have hsupport : extendWordLinear ((LQ).correctionRegion q)
      (restrictWordLinear ((LQ).correctionRegion q) (cqComponentTotal G sigma.val q))=
      cqComponentTotal G sigma.val q :=
    (congrArg (extendWordLinear ((LQ).correctionRegion q)) hrv).trans he.symm
  have hword := LinearEquiv.apply_symm_apply (wordEquiv (qCorrectionEquiv P S q))
    (restrictWordLinear ((LQ).correctionRegion q) (cqComponentTotal G sigma.val q))
  exact hsupport.symm.trans
    (congrArg (extendWordLinear ((LQ).correctionRegion q)) hword.symm)

private theorem originalCq_total_sum (sigma : (CF).Syndrome U) :
    cqCorrectionTotal G sigma.val=
      ∑ q : P.Q,directQExtension P A R S q (originalCqWord P A R S sigma q) := by
  change (∑ q : P.Q,cqComponentTotal G sigma.val q)=_
  apply Finset.sum_congr rfl
  intro q _
  exact originalCqComponent_eq_extension P A R S sigma q

/-- Retain the entire Q-sector global boundary, including outgoing Z.
For a forced cone only, the second term vanishes by its terminal values. -/
private theorem directQExtension_boundary (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    (CF).coboundary1 U (directQExtension P A R S q w)=
      (show (CF).Cochain2 U from fun z =>
        extendWordLinear ((LQ).syndromeRegion q)
          ((G).contract.rx_local_complexes.cqDelta1 q
            (wordEquiv (qCorrectionEquiv P S q) w)) z)+
      (show (CF).Cochain2 U from fun z => qFlow P S q w z) := by
  have h := (G).contract.support_decomposition.cqDelta1_decomposition q
    (wordEquiv (qCorrectionEquiv P S q) w)
  have hi := LinearEquiv.symm_apply_apply (wordEquiv (qCorrectionEquiv P S q)) w
  have hflow : (G).contract.support_decomposition.cqFlow q
      (wordEquiv (qCorrectionEquiv P S q) w)=
      (show (CF).Cochain2 U from fun z => qFlow P S q w z) :=
    congrArg (fun v : Word BDL26Field (QDoubleCylinderVertex P q S) =>
      (show (CF).Cochain2 U from fun z => qFlow P S q v z)) hi
  funext z
  exact (congrFun h z).trans
    (congrArg (fun a : BDL26Field =>
      extendWordLinear ((LQ).syndromeRegion q)
        ((G).contract.rx_local_complexes.cqDelta1 q
          (wordEquiv (qCorrectionEquiv P S q) w)) z+a) (congrFun hflow z))

private theorem actual_cone_global_flow_zero (q : P.Q) (copy : BDL26FiniteTannerSquare.Two) :
    qFlow P S q (CriticalOriginalChoice.coneWord P q S copy)=0 := by
  funext p
  rcases p with (⟨x,f⟩ | ⟨r,e⟩) | ⟨z,c⟩
  · exact qFlow_at_x P S q _ x f
  · exact qFlow_at_q P S q r _ e
  · rw [qFlow_at_z]
    by_cases hqz : P.qz q z=true
    · simp only [BDL26ReplacementSupport.rxQOutgoing,dif_pos hqz,
        rxQZDegreeOne,wordPullback_apply]
      change (canonicalBasisWord (F:=BDL26Field)
        (copy,Sum.inl (Sum.inl ())) : Word BDL26Field (QDoubleCylinderVertex P q S))
        (c,Sum.inl (Sum.inr (⟨z,hqz⟩ : QStarEdge P q)))=0
      exact (basis_value _ _).trans (if_neg (by intro h; cases h))
    · simp only [BDL26ReplacementSupport.rxQOutgoing,dif_neg hqz]
      rfl
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open scoped Classical BigOperators

private theorem radial_not_in_qToX_image (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X) (q : P.Q)
    (hx : P.xq x q=true) (r : XStarEdge P x)
    (hr : ∃ a : XQEdge P,r.val=Sum.inl a)
    (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) (e : QDoubleCylinderEdge P q S) :
    qToXDoubleCylinderEdge P A q x hx S e≠Sum.inl (c,Sum.inl (r,k)) := by
  let tag : DoubleCylinderEdge P x S → Bool := fun edge =>
    match edge with
    | Sum.inl (_,Sum.inl (star,_)) =>
      match star.val with
      | Sum.inl _ => true
      | Sum.inr _ => false
    | _ => false
  have hmap : tag (qToXDoubleCylinderEdge P A q x hx S e)=false := by
    rcases e with ⟨d,z,k⟩ | z <;> rfl
  have hrad : tag (Sum.inl (c,Sum.inl (r,k)))=true := by
    obtain ⟨a,ha⟩ := hr
    change (match r.val with | Sum.inl _ => true | Sum.inr _ => false)=true
    rw [ha]
  intro h
  exact Bool.false_ne_true (hmap.symm.trans ((congrArg tag h).trans hrad))

private theorem qToX_horizontal_owner (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X) (q q0 : P.Q)
    (hx : P.xq x q=true) (h0 : P.xq x q0=true)
    (z0 : QStarEdge P q0) (k0 : Fin S.half) (c0 : BDL26FiniteTannerSquare.Two)
    (e : QDoubleCylinderEdge P q S)
    (he : qToXDoubleCylinderEdge P A q x hx S e=
      qToXDoubleCylinderEdge P A q0 x h0 S (Sum.inl (c0,z0,k0))) : q=q0 := by
  rcases e with ⟨c,z,k⟩ | z
  · have hstar := congrArg Prod.fst
      (Sum.inl.inj (congrArg Prod.snd (Sum.inl.inj he)))
    have hraw := congrArg Subtype.val hstar
    have hlabel := congrArg (fun edge : Edge P =>
      match edge with | Sum.inl _ => q0 | Sum.inr ez => ez.val.1) hraw
    exact hlabel
  · cases he

private theorem qToX_horizontal_full_index (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X) (q q0 : P.Q)
    (hx : P.xq x q=true) (h0 : P.xq x q0=true)
    (z0 : QStarEdge P q0) (k0 : Fin S.half) (c0 : BDL26FiniteTannerSquare.Two)
    (e : QDoubleCylinderEdge P q S) :
    qToXDoubleCylinderEdge P A q x hx S e=
      qToXDoubleCylinderEdge P A q0 x h0 S (Sum.inl (c0,z0,k0)) ↔
      (Sigma.mk q e : Σ q : P.Q,QDoubleCylinderEdge P q S)=
        Sigma.mk q0 (Sum.inl (c0,z0,k0)) := by
  constructor
  · intro he
    have hq := qToX_horizontal_owner P A S x q q0 hx h0 z0 k0 c0 e he
    subst q
    exact congrArg (Sigma.mk q0)
      ((qToXDoubleCylinderEdge_injective P A q0 x h0 S) he)
  · intro he
    have hq : q=q0 := congrArg Sigma.fst he
    subst q
    exact congrArg (qToXDoubleCylinderEdge P A q0 x h0 S)
      (sigma_same_index_inj (I:=P.Q)
        (A:=fun r => QDoubleCylinderEdge P r S) (i:=q0)
        e (Sum.inl (c0,z0,k0)) he)

private theorem actualAlpha_flow_zero (S : OddScale) (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    xFlow (AP S) S (AX S j outer) (canonicalBasisWord (actualAlphaEdge S j outer c))=0 := by
  funext p
  rcases p with (⟨y,f⟩ | ⟨q,e⟩) | ⟨z,d⟩
  · exact xFlow_at_x (AP S) S (AX S j outer) y
      (canonicalBasisWord (actualAlphaEdge S j outer c)) f
  · have h := xFlow_at_q (AP S) (AA S).toTannerSquareAdmissible S
      (AX S j outer) (canonicalBasisWord (actualAlphaEdge S j outer c)) q e
    by_cases hx : (AP S).xq (AX S j outer) q=true
    · refine h.trans ((dif_pos hx).trans ?_)
      change canonicalBasisWord (actualAlphaEdge S j outer c)
        (qToXDoubleCylinderEdge (AP S) (AA S).toTannerSquareAdmissible q
          (AX S j outer) hx S e)=0
      exact (basis_value _ _).trans (if_neg
        (radial_not_in_qToX_image (AP S) (AA S).toTannerSquareAdmissible S
          (AX S j outer) q hx (actualRadialStarEdge S j outer)
          ⟨_,actualRadialStarEdge_value S j outer⟩ c ⟨0,S.half_pos⟩ e))
    · exact h.trans (dif_neg hx)
  · exact xFlow_at_z (AP S) S (AX S j outer)
      (canonicalBasisWord (actualAlphaEdge S j outer c)) z d

/-- The physical perturbation's ENTIRE outgoing X-flow is exactly the
single selected hub arm, including its actual owner and copied edge tags. -/
private theorem actualError_flow (S : OddScale) (j : Fin 2) (outer c : BDL26FiniteTannerSquare.Two) :
    xFlow (AP S) S (AX S j outer) (canonicalBasisWord (actualErrorEdge S j outer c))=
      canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0) c) := by
  funext p
  rcases p with (⟨y,f⟩ | ⟨q,e⟩) | ⟨z,d⟩
  · exact (xFlow_at_x (AP S) S (AX S j outer) y
      (canonicalBasisWord (actualErrorEdge S j outer c)) f).trans
        ((basis_value _ _).trans (if_neg (by intro h; cases h))).symm
  · have h := xFlow_at_q (AP S) (AA S).toTannerSquareAdmissible S
      (AX S j outer) (canonicalBasisWord (actualErrorEdge S j outer c)) q e
    have hb : canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer)
        (AHZ S j outer 0) c) (Sum.inl (Sum.inr ⟨q,e⟩))=
        if (Sigma.mk q e : Σ q : (AP S).Q,QDoubleCylinderEdge (AP S) q S)=
          Sigma.mk (AH S j outer) (Sum.inl (c,AHZ S j outer 0,⟨0,S.half_pos⟩)) then (1:BDL26Field) else 0 := by
      let target : RX2 (AP S) S := hubArmCoordinate (AP S) S (AH S j outer)
        (AHZ S j outer 0) c
      let point : RX2 (AP S) S := Sum.inl (Sum.inr ⟨q,e⟩)
      let source : Sigma (fun r : (AP S).Q => QDoubleCylinderEdge (AP S) r S) :=
        ⟨q,e⟩
      let destination : Sigma (fun r : (AP S).Q => QDoubleCylinderEdge (AP S) r S) :=
        ⟨AH S j outer,Sum.inl (c,AHZ S j outer 0,⟨0,S.half_pos⟩)⟩
      have hi : point=target ↔ source=destination := by
        constructor
        · intro he
          exact Sum.inr.inj (Sum.inl.inj he)
        · intro he
          exact congrArg (fun a : Sigma (fun r : (AP S).Q => QDoubleCylinderEdge (AP S) r S) =>
            (Sum.inl (Sum.inr a) : RX2 (AP S) S)) he
      by_cases hp : point=target
      · exact ((basis_value (I:=RX2 (AP S) S) target point).trans (if_pos hp)).trans
          (if_pos (hi.mp hp)).symm
      · exact ((basis_value (I:=RX2 (AP S) S) target point).trans (if_neg hp)).trans
          (if_neg (fun hq => hp (hi.mpr hq))).symm
    by_cases hx : (AP S).xq (AX S j outer) q=true
    · have hi := qToX_horizontal_full_index (AP S) (AA S).toTannerSquareAdmissible S
        (AX S j outer) q (AH S j outer) hx (AH_incident S j outer)
        (AHZ S j outer 0) ⟨0,S.half_pos⟩ c e
      have hs : canonicalBasisWord (F:=BDL26Field) (actualErrorEdge S j outer c)
          (qToXDoubleCylinderEdge (AP S) (AA S).toTannerSquareAdmissible q
            (AX S j outer) hx S e)=
          canonicalBasisWord (F:=BDL26Field) (hubArmCoordinate (AP S) S (AH S j outer)
            (AHZ S j outer 0) c) (Sum.inl (Sum.inr ⟨q,e⟩)) := by
        let point : DoubleCylinderEdge (AP S) (AX S j outer) S :=
          qToXDoubleCylinderEdge (AP S) (AA S).toTannerSquareAdmissible q
            (AX S j outer) hx S e
        let target : DoubleCylinderEdge (AP S) (AX S j outer) S :=
          actualErrorEdge S j outer c
        let source : Sigma (fun r : (AP S).Q => QDoubleCylinderEdge (AP S) r S) := ⟨q,e⟩
        let destination : Sigma (fun r : (AP S).Q => QDoubleCylinderEdge (AP S) r S) :=
          ⟨AH S j outer,Sum.inl (c,AHZ S j outer 0,⟨0,S.half_pos⟩)⟩
        have hi' : point=target ↔ source=destination := hi
        by_cases hp : point=target
        · exact ((basis_value (I:=DoubleCylinderEdge (AP S) (AX S j outer) S) target point).trans
            (if_pos hp)).trans (hb.trans (if_pos (hi'.mp hp))).symm
        · exact ((basis_value (I:=DoubleCylinderEdge (AP S) (AX S j outer) S) target point).trans
            (if_neg hp)).trans (hb.trans (if_neg (fun hq => hp (hi'.mpr hq)))).symm
      exact h.trans ((dif_pos hx).trans hs)
    · have hn : ¬(Sigma.mk q e : Σ q : (AP S).Q,QDoubleCylinderEdge (AP S) q S)=
          Sigma.mk (AH S j outer) (Sum.inl (c,AHZ S j outer 0,⟨0,S.half_pos⟩)) := by
        intro he
        have hq : q=AH S j outer := congrArg Sigma.fst he
        have hinc : (AP S).xq (AX S j outer) q=
            (AP S).xq (AX S j outer) (AH S j outer) :=
          congrArg (fun r : (AP S).Q => (AP S).xq (AX S j outer) r) hq
        exact hx (hinc.trans (AH_incident S j outer))
      exact (h.trans (dif_neg hx)).trans (hb.trans (if_neg hn)).symm
  · exact (xFlow_at_z (AP S) S (AX S j outer)
      (canonicalBasisWord (actualErrorEdge S j outer c)) z d).trans
        ((basis_value _ _).trans (if_neg (by intro h; cases h))).symm
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private def rawQRead (q : P.Q) : (CF).Cochain2 U →ₗ[BDL26Field]
    Word BDL26Field (QDoubleCylinderEdge P q S) :=
  ((wordEquiv (qSyndromeEquiv P S q)).symm).toLinearMap.comp
    (restrictWordLinear ((LQ).syndromeRegion q))

private theorem rawQRead_apply (q : P.Q) (s : (CF).Cochain2 U)
    (e : QDoubleCylinderEdge P q S) :
    rawQRead P A R S q s e=s (Sum.inl (Sum.inr ⟨q,e⟩)) := rfl

private theorem rawQRead_Qextension_same (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    rawQRead P A R S q ((CF).coboundary1 U (directQExtension P A R S q w))=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w := by
  have ht := directQExtension_restrict_X P A R S q w
  have h := (G).contract.support_decomposition.cqDelta1_restriction_global q
    (directQExtension P A R S q w) ht
  change (wordEquiv (qSyndromeEquiv P S q)).symm
    (restrictWordLinear ((LQ).syndromeRegion q)
      ((CF).coboundary1 U (directQExtension P A R S q w)))=_
  have hrest : restrictWordLinear ((LQ).correctionRegion q)
      (directQExtension P A R S q w)=wordEquiv (qCorrectionEquiv P S q) w :=
    region_restrict_extend _ _
  have hd := congrArg ((G).contract.rx_local_complexes.cqDelta1 q) hrest
  have hl := h.trans hd
  have ht := CriticalDegreeOneBudget.actual_local_delta_transport P A R S q w
  have hi := LinearEquiv.symm_apply_apply (wordEquiv (qSyndromeEquiv P S q))
    (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w)
  exact (congrArg (wordEquiv (qSyndromeEquiv P S q)).symm (hl.trans ht)).trans hi

private theorem rawQRead_Qextension_other (q r : P.Q) (hqr : r≠q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    rawQRead P A R S r ((CF).coboundary1 U (directQExtension P A R S q w))=0 := by
  have ht := directQExtension_restrict_X P A R S q w
  have h := (G).contract.support_decomposition.cqDelta1_restriction_global r
    (directQExtension P A R S q w) ht
  have hr : restrictWordLinear ((LQ).correctionRegion r)
      (directQExtension P A R S q w)=0 := by
    apply region_restrict_extend_disjoint
    exact (G).cq_correction_regions_pairwise_disjoint q r (Ne.symm hqr)
  change (wordEquiv (qSyndromeEquiv P S r)).symm
    (restrictWordLinear ((LQ).syndromeRegion r)
      ((CF).coboundary1 U (directQExtension P A R S q w)))=0
  have hd := congrArg ((G).contract.rx_local_complexes.cqDelta1 r) hr
  have hz := (h.trans hd).trans
    (map_zero ((G).contract.rx_local_complexes.cqDelta1 r))
  exact (congrArg (wordEquiv (qSyndromeEquiv P S r)).symm hz).trans
    (map_zero (wordEquiv (qSyndromeEquiv P S r)).symm)

private theorem rawQRead_arm_same (q : P.Q) (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) :
    rawQRead P A R S q (canonicalBasisWord (hubArmCoordinate P S q z c))=
      canonicalBasisWord (Sum.inl (c,z,⟨0,S.half_pos⟩)) := by
  funext e
  change canonicalBasisWord (F:=BDL26Field) (hubArmCoordinate P S q z c)
      (Sum.inl (Sum.inr ⟨q,e⟩))=canonicalBasisWord (Sum.inl (c,z,⟨0,S.half_pos⟩)) e
  have he : (Sum.inl (Sum.inr ⟨q,e⟩) : RX2 P S)=hubArmCoordinate P S q z c ↔
      e=Sum.inl (c,z,⟨0,S.half_pos⟩) := by
    constructor
    · intro h
      exact sigma_same_index_inj (I:=P.Q)
        (A:=fun r => QDoubleCylinderEdge P r S) (i:=q)
        e (Sum.inl (c,z,⟨0,S.half_pos⟩)) (Sum.inr.inj (Sum.inl.inj h))
    · intro h
      subst e
      rfl
  by_cases h : e=Sum.inl (c,z,⟨0,S.half_pos⟩)
  · exact ((basis_value _ _).trans (if_pos (he.mpr h))).trans
      ((basis_value _ _).trans (if_pos h)).symm
  · exact ((basis_value _ _).trans (if_neg (fun h' => h (he.mp h')))).trans
      ((basis_value _ _).trans (if_neg h)).symm

private theorem rawQRead_arm_other (q r : P.Q) (hqr : r≠q)
    (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) :
    rawQRead P A R S r (canonicalBasisWord (hubArmCoordinate P S q z c))=0 := by
  funext e
  change canonicalBasisWord (F:=BDL26Field) (hubArmCoordinate P S q z c)
    (Sum.inl (Sum.inr ⟨r,e⟩))=0
  exact (basis_value _ _).trans (if_neg (by
    intro h
    exact hqr (congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj h)))))

private theorem originalCq_two_components (sigma : (CF).Syndrome U)
    (q r : P.Q) (hqr : q≠r)
    (wq : Word BDL26Field (QDoubleCylinderVertex P q S))
    (wr : Word BDL26Field (QDoubleCylinderVertex P r S))
    (hq : originalCqWord P A R S sigma q=wq)
    (hr : originalCqWord P A R S sigma r=wr)
    (hother : ∀ t : P.Q,t≠q → t≠r → originalCqWord P A R S sigma t=0) :
    cqCorrectionTotal G sigma.val=
      directQExtension P A R S q wq+directQExtension P A R S r wr := by
  rw [originalCq_total_sum]
  calc
    _ = ∑ t : P.Q,
        ((if t=q then directQExtension P A R S q wq else 0)+
         (if t=r then directQExtension P A R S r wr else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases htq : t=q
      · subst t
        rw [hq]
        simp [hqr]
      · by_cases htr : t=r
        · subst t
          rw [hr]
          simp [htq]
        · rw [hother t htq htr]
          have hz : directQExtension P A R S t 0=0 :=
            map_zero (extendWordLinear ((LQ).correctionRegion t))
          exact hz.trans (by simp only [if_neg htq,if_neg htr,zero_add])
    _ = _ := by rw [Finset.sum_add_distrib];simp
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open scoped Classical BigOperators

private theorem extend_reindexed_basis
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Y : Finset I) (E : J ≃ LocalRegionIndex Y) (j : J) :
    extendWordLinear Y (wordEquiv E (canonicalBasisWord j))=
      canonicalBasisWord (E j).val := by
  funext p
  by_cases hp : p∈Y
  · have he : E.symm ⟨p,hp⟩=j ↔ p=(E j).val := by
      constructor
      · intro h
        have h' := congrArg (fun a => (E a).val) h
        simpa only [Equiv.apply_symm_apply] using h'
      · intro h
        have hs : (⟨p,hp⟩ : LocalRegionIndex Y)=E j := Subtype.ext h
        rw [hs,Equiv.symm_apply_apply]
    simp [extendWordLinear,extendLocalSignal,hp,wordEquiv_apply,basis_value,he]
  · have hn : p≠(E j).val := by intro h;exact hp (h ▸ (E j).property)
    simp [extendWordLinear,extendLocalSignal,hp,basis_value,hn]

namespace CriticalOriginalChoice
open BDL26RXLocalReplacement BDL26TannerLocalRegularity BDL26RXDecoderAdapter

private theorem cone_delta_single_arm (P : TannerSquarePresentation)
    (S : OddScale) (q : P.Q) (z : QStarEdge P q)
    (hu : ∀ t : QStarEdge P q,t=z) (copy : BDL26FiniteTannerSquare.Two) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (coneWord P q S copy)=
      canonicalBasisWord (firstArm P q S copy z) := by
  funext e
  rcases e with ⟨c,t,k⟩ | t
  · rw [repair4_cone_outer]
    have ht := hu t
    subst t
    have hk : k=⟨0,S.half_pos⟩ ↔ k.val=0 := by
      constructor
      · intro h;exact congrArg Fin.val h
      · intro h;exact Fin.ext h
    simp [basis_value,firstArm,hk]
  · rw [repair4_cone_bridge]
    simp [basis_value,firstArm]

/-- Exact values at the TWO actual hub queries, not only an existential
nonperiod response. All costs are proved for their full original words. -/
private theorem direct_pair_query_original_values
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : P.Q)
    (hh : S.half=1) (hd : Fintype.card (QStarEdge P q)=3)
    (a b c : QStarEdge P q) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (cover : ∀ t : QStarEdge P q,t=a ∨ t=b ∨ t=c) :
    let k := terminalWord P q S 0 a+terminalWord P q S 1 a
    let w := coneWord P q S 0+terminalWord P q S 0 b+terminalWord P q S 1 b
    originalChoice P A R S q w=w ∧
      originalChoice P A R S q (w+k)=fun v => (w+k) v+1 := by
  let k := terminalWord P q S 0 a+terminalWord P q S 1 a
  let w := coneWord P q S 0+terminalWord P q S 0 b+terminalWord P q S 1 b
  have h := sameLeafPair_actual_budgets P q S hh a b c hab hac hbc cover
  have hw : originalChoice P A R S q w=w :=
    originalChoice_forced_cost_two_degree_three P A R S q hd w h.2.1 h.2.2.2.2.1
  have hcomp : (∑ z : QStarEdge P q,HammingWeight
      (rxQZDegreeOne P q z.val z.property S (fun v => (w+k) v+1)))=2 := by
    have hc := qLocal_terminal_weight_complement P q S (w+k)
    erw [h.2.2.1,hd] at hc
    omega
  have hs : HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (fun v => (w+k) v+1))≤3 := by
    erw [qLocalCoboundary_add_constant]
    exact h.2.2.2.2.2
  refine ⟨hw,?_⟩
  calc
    originalChoice P A R S q (w+k)=
        originalChoice P A R S q (fun v => (w+k) v+1) :=
      (originalChoice_add_constant P A R S q (w+k) 1).symm
    _ = _ := originalChoice_forced_cost_two_degree_three P A R S q hd _ hcomp hs
end CriticalOriginalChoice
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private theorem cone_global_boundary_single_arm (q : P.Q) (z : QStarEdge P q)
    (hu : ∀ t : QStarEdge P q,t=z) (copy : BDL26FiniteTannerSquare.Two) :
    (CF).coboundary1 U (directQExtension P A R S q
      (CriticalOriginalChoice.coneWord P q S copy))=
      canonicalBasisWord (hubArmCoordinate P S q z copy) := by
  let w := CriticalOriginalChoice.coneWord P q S copy
  have hd := directQExtension_boundary P A R S q w
  have hflow := actual_cone_global_flow_zero P S q copy
  have ht := CriticalDegreeOneBudget.actual_local_delta_transport P A R S q w
  have hc := CriticalOriginalChoice.cone_delta_single_arm P S q z hu copy
  have he := extend_reindexed_basis ((LQ).syndromeRegion q) (qSyndromeEquiv P S q)
    (CriticalOriginalChoice.firstArm P q S copy z)
  have hl := congrArg (extendWordLinear ((LQ).syndromeRegion q))
    (ht.trans (congrArg (wordEquiv (qSyndromeEquiv P S q)) hc))
  funext p
  exact (congrFun hd p).trans
    ((congrArg₂ (fun a b : BDL26Field => a+b)
      (congrFun (hl.trans he) p) (congrFun hflow p)).trans (add_zero _))

/-- Full cancellation on the original first history. The hypotheses concern
only two specific returned local words and the complete original Cx flow;
they are instantiated below with its zero/cone alternatives, not supplied
as a counterexample certificate or an altered decoder. -/
private theorem directInput_first_residual_zero (x : P.X) (q r : P.Q) (hqr : q≠r)
    (alpha : Word BDL26Field (DoubleCylinderEdge P x S))
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (v : Word BDL26Field (QDoubleCylinderVertex P r S))
    (ha : xFlow P S x alpha=0)
    (hf : xFlow P S x (originalCxWord P A R S (directInput P A R S x q alpha w) x)=
      (CF).coboundary1 U (directQExtension P A R S r v))
    (hw : CriticalOriginalChoice.originalChoice P A R S q w=w)
    (hv : CriticalOriginalChoice.originalChoice P A R S r v=v) :
    rxSigmaAfterCq G (directInput P A R S x q alpha w).val=0 := by
  let sigma := directInput P A R S x q alpha w
  have hafter : rxSigmaAfterCx G sigma.val=
      (CF).coboundary1 U (directQExtension P A R S q w)+
      (CF).coboundary1 U (directQExtension P A R S r v) := by
    have he := directInput_after_Cx_global P A R S x q alpha w
    funext z
    exact (congrFun he z).trans
      ((congrArg₂ (fun a b : BDL26Field => a+b)
        (congrArg₂ (fun a b : BDL26Field => a+b) (congrFun ha z) rfl)
        (congrFun hf z)).trans
          (congrArg (fun a : BDL26Field => a+
            ((CF).coboundary1 U (directQExtension P A R S r v)) z)
              (zero_add (((CF).coboundary1 U (directQExtension P A R S q w)) z))))
  have hq : originalCqWord P A R S sigma q=w := by
    trans CriticalOriginalChoice.originalChoice P A R S q w
    · apply originalCqWord_of_query
      change rawQRead P A R S q (rxSigmaAfterCx G sigma.val)=_
      rw [hafter,map_add,rawQRead_Qextension_same,
        rawQRead_Qextension_other P A R S r q hqr,add_zero]
    · exact hw
  have hr : originalCqWord P A R S sigma r=v := by
    trans CriticalOriginalChoice.originalChoice P A R S r v
    · apply originalCqWord_of_query
      change rawQRead P A R S r (rxSigmaAfterCx G sigma.val)=_
      rw [hafter,map_add,rawQRead_Qextension_other P A R S q r (Ne.symm hqr),
        rawQRead_Qextension_same,zero_add]
    · exact hv
  have ho (t : P.Q) (htq : t≠q) (htr : t≠r) : originalCqWord P A R S sigma t=0 := by
    trans CriticalOriginalChoice.originalChoice P A R S t 0
    · apply originalCqWord_of_query
      change rawQRead P A R S t (rxSigmaAfterCx G sigma.val)=_
      rw [hafter,map_add,rawQRead_Qextension_other P A R S q t htq,
        rawQRead_Qextension_other P A R S r t htr,map_zero,zero_add]
    · exact CriticalOriginalChoice.actual_original_choice_zero P A R S t
  have htotal := originalCq_two_components P A R S sigma q r hqr w v hq hr ho
  change rxSigmaAfterCx G sigma.val+(CF).coboundary1 U (cqCorrectionTotal G sigma.val)=0
  rw [htotal,map_add,hafter]
  funext p
  let a : BDL26Field := ((CF).coboundary1 U (directQExtension P A R S q w)) p
  let b : BDL26Field := ((CF).coboundary1 U (directQExtension P A R S r v)) p
  change (a+b)+(a+b)=0
  exact repair3_scalar_add_self (a+b)
end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private def directHubK (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Word BDL26Field (QDoubleCylinderVertex (AP S) (AH S j outer) S) :=
  CriticalOriginalChoice.terminalWord (AP S) (AH S j outer) S 0 (AHZ S j outer 0)+
    CriticalOriginalChoice.terminalWord (AP S) (AH S j outer) S 1 (AHZ S j outer 0)

private theorem AH_degree_three (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Fintype.card (QStarEdge (AP S) (AH S j outer))=3 := by
  let E : Fin 3 ≃ QStarEdge (AP S) (AH S j outer) :=
    Equiv.ofBijective (AHZ S j outer) ⟨AHZ_injective S j outer,AHZ_surjective S j outer⟩
  simpa using (Fintype.card_congr E).symm

private theorem directHub_original_values (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    CriticalOriginalChoice.originalChoice (AP S) (AA S) (AR S) S (AH S j outer)
      (directHubW S j outer)=directHubW S j outer ∧
    CriticalOriginalChoice.originalChoice (AP S) (AA S) (AR S) S (AH S j outer)
      (directHubW S j outer+directHubK S j outer)=
      fun p => (directHubW S j outer+directHubK S j outer) p+1 := by
  have hne (i k : Fin 3) (h : i≠k) : AHZ S j outer i≠AHZ S j outer k :=
    fun he => h (AHZ_injective S j outer he)
  have hcover (t : QStarEdge (AP S) (AH S j outer)) :
      t=AHZ S j outer 0 ∨ t=AHZ S j outer 2 ∨ t=AHZ S j outer 1 := by
    obtain ⟨i,rfl⟩ := AHZ_surjective S j outer t
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  exact CriticalOriginalChoice.direct_pair_query_original_values (AP S) (AA S) (AR S) S
    (AH S j outer) hh (AH_degree_three S j outer)
    (AHZ S j outer 0) (AHZ S j outer 2) (AHZ S j outer 1)
    (hne 0 2 (by decide)) (hne 0 1 (by decide)) (hne 2 1 (by decide)) hcover

/-- The ORIGINAL explicit first history has zero COMPLETE post-Cq syndrome.
This is established before any logical normalization or use of the second
base decoder. The actual hub QW Z boundary is canceled with the same QW. -/
private theorem counterexampleInput_full_first_zero (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    rxSigmaAfterCq (literalData (AP S) (AA S) (AR S) S)
      (counterexampleInput S hh j outer).val=0 := by
  let c := oppositeErrorCopy S hh j outer
  let alpha : Word BDL26Field (DoubleCylinderEdge (AP S) (AX S j outer) S) :=
    canonicalBasisWord (actualAlphaEdge S j outer c)
  let sigma := counterexampleInput S hh j outer
  have hquery : (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm
      (restrictWordLinear ((literalLx (AP S) (AA S) (AR S) S).syndromeRegion
        (AX S j outer)) sigma.val)=
      canonicalBasisWord (Sum.inl (c,actualSmallFace S j outer)) := by
    exact (directInput_raw_query_same (AP S) (AA S) (AR S) S
      (AX S j outer) (AH S j outer) alpha (directHubW S j outer)).trans
        (actualAlpha_boundary S hh j outer c)
  have hf := actual_A_original_leaf_exit S hh j outer sigma c
    (actualSmallFace S j outer) hquery
  have hw := (directHub_original_values S hh j outer).1
  have ha : xFlow (AP S) S (AX S j outer) alpha=0 := actualAlpha_flow_zero S j outer c
  rcases hf with hf | ⟨i,d,hf⟩
  · apply directInput_first_residual_zero (AP S) (AA S) (AR S) S
      (AX S j outer) (AH S j outer) (AL S j outer 0)
      (Ne.symm (AL_ne_hub S j outer 0)) alpha (directHubW S j outer) 0 ha
    · have he : directQExtension (AP S) (AA S) (AR S) S (AL S j outer 0) 0=0 :=
        map_zero (extendWordLinear
          ((literalLq (AP S) (AA S) (AR S) S).correctionRegion (AL S j outer 0)))
      have hz := (congrArg (fun v =>
        (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
          (Fin.succ (0 : StepIndex 1)) v) he).trans
            (map_zero ((BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
              (Fin.succ (0 : StepIndex 1))))
      exact hf.trans hz.symm
    · exact hw
    · exact CriticalOriginalChoice.actual_original_choice_zero (AP S) (AA S) (AR S) S _
  · let v := CriticalOriginalChoice.coneWord (AP S) (AL S j outer i) S d
    apply directInput_first_residual_zero (AP S) (AA S) (AR S) S
      (AX S j outer) (AH S j outer) (AL S j outer i)
      (Ne.symm (AL_ne_hub S j outer i)) alpha (directHubW S j outer) v ha
    · exact hf.trans (cone_global_boundary_single_arm (AP S) (AA S) (AR S) S
        (AL S j outer i) (ALZ S j outer i) (ALZ_unique S j outer i) d).symm
    · exact hw
    · exact CriticalOriginalChoice.actual_original_choice_fixes_cone (AP S) (AA S) (AR S) S _ d
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26TannerLocalRegularity BDL26LevelTwoCode BDL26RXLocalReplacement
open BDL26IndexedDecoder BDL26ActualFailureReadout BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping
open MultiscaleDecoder.RXCoarseGraining
open MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))

private theorem full_boundary_of_first_residual_zero (sigma : (CF).Syndrome U)
    (hz : rxSigmaAfterCq G sigma.val=0) :
    sigma.val=(CF).coboundary1 U (rxCorrectionTotal G sigma.val) := by
  have hf : rxSigmaAfterCq G sigma.val=
      sigma.val+(CF).coboundary1 U (rxCorrectionTotal G sigma.val) := by
    unfold rxSigmaAfterCq rxSigmaAfterCx rxCorrectionTotal
    rw [map_add]
    exact add_assoc _ _ _
  have hp : sigma.val+(CF).coboundary1 U (rxCorrectionTotal G sigma.val)=0 :=
    hf.symm.trans hz
  funext p
  have he := congrFun hp p
  change sigma.val p+((CF).coboundary1 U (rxCorrectionTotal G sigma.val)) p=0 at he
  calc
    sigma.val p=(sigma.val p+((CF).coboundary1 U (rxCorrectionTotal G sigma.val)) p)+
        ((CF).coboundary1 U (rxCorrectionTotal G sigma.val)) p := by
      rw [add_assoc,repair3_scalar_add_self,add_zero]
    _ = _ := by rw [he,zero_add]
end

private def counterexampleActualTop (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : repair2C3Input S :=
  repair5_literal_to_actual S (counterexampleInput S hh j outer)

/-- The original XSyndromeDomain input, with the SAME physical preimage.
This is the full range witness, not an assumed legal background. -/
private def counterexampleDomain (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1 :=
  ⟨(counterexampleActualTop S hh j outer).val,by
    obtain ⟨e,he⟩ := (counterexampleActualTop S hh j outer).property
    exact ⟨e,(LinearMap.congr_fun
      (indexedFamily_coboundary1 S 3 (3 : LevelIndex 3)) e).symm.trans he⟩⟩

private theorem counterexampleDomain_input (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    repair2C3InputOfSyndrome S (counterexampleDomain S hh j outer)=
      counterexampleActualTop S hh j outer := Subtype.ext rfl

private theorem counterexample_actual_total_boundary (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (counterexampleActualTop S hh j outer).val=
      (indexedFamily S 3).coboundary1 (3 : LevelIndex 3)
        (rxCorrectionTotal (D := indexedDecoderData S 3) (i := (2 : StepIndex 3))
          (rxData S 3 (2 : StepIndex 3) (by decide))
          (counterexampleActualTop S hh j outer).val) := by
  have h := full_boundary_of_first_residual_zero (AP S) (AA S) (AR S) S
    (counterexampleInput S hh j outer)
    (counterexampleInput_full_first_zero S hh j outer)
  rw [CriticalOldXQueries.repair4_C3_total_to_literal,repair5_C3_upper_coboundary1]
  exact h

/-- FIRST=0 for the actual original history of the explicit valid background.
No modified decoder, normalized substitute, or independent Q response appears. -/
private theorem counterexample_actual_FIRST_zero (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    firstReadout S 1 (counterexampleDomain S hh j outer)=0 := by
  have hcoarse := original_rx_coarse_zero_of_full_boundary S 3 (2 : StepIndex 3)
    (by decide) (counterexampleActualTop S hh j outer)
    (counterexample_actual_total_boundary S hh j outer)
  change (actualInputs S 1
    (repair2C3InputOfSyndrome S (counterexampleDomain S hh j outer)) 0).val=0
  erw [counterexampleDomain_input,actualInputs_step S 1
    (counterexampleActualTop S hh j outer) (⟨0,by decide⟩ : StepIndex 1),
    actualInputs_top,BDL26OwnerIncidenceMasks.actualStep_rx S 3
      (2 : StepIndex 3) (by decide)]
  exact hcoarse
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26RXErrorPullback BDL26RXXStarTransport
open scoped Classical BigOperators

/-- Equality for the ORIGINAL full finite sum. It does not identify the
original localization centre by fiat: the active summand is retained with
its actual membership test. Every other summand is the provider's explicit
zero branch, not an omitted arbitrary constant potential. -/
private theorem original_fullPhi_single_active
    (S : OddScale) (depth : Nat) (i : StepIndex depth) (he : i.val%2=0)
    (X0 : Finset (BDL26DecodingGraph.state S i.val).presentation.X)
    (x : (BDL26DecodingGraph.state S i.val).presentation.X)
    (a b : Upper S depth i)
    (hother : ∀ y,y≠x → restrictWordLinear ((rxLx S depth i he).correctionRegion y)
      (updated S depth i he a b)=0) :
    BDL26RXFiniteBlockTransport.Phi S depth i he X0 a b=
      (rxContract S depth i he).support_decomposition.cxLift0 x
        (if x∈X0 then localPotential S depth i he x a b else 0) := by
  have hz (y : (BDL26DecodingGraph.state S i.val).presentation.X) (hy : y≠x) :
      localPotential S depth i he y a b=0 := by
    unfold localPotential
    rw [if_pos (hother y hy)]
  unfold BDL26RXFiniteBlockTransport.Phi
  by_cases hx : x∈X0
  · rw [if_pos hx]
    calc
      _ = potential S depth i he x a b := by
        apply Finset.sum_eq_single x
        · intro y _ hy
          unfold potential
          rw [hz y hy,map_zero]
        · intro hn
          exact False.elim (hn hx)
      _ = _ := rfl
  · rw [if_neg hx,map_zero]
    apply Finset.sum_eq_zero
    intro y hy
    have hne : y≠x := by intro h;exact hx (h ▸ hy)
    unfold potential
    rw [hz y hne,map_zero]
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXXStarTransport
open scoped Classical BigOperators

private theorem counterexamplePhysical_eq_chart (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    counterexamplePhysical S hh j outer=
      (xCorrectionEquiv (AP S) S (AX S j outer) (counterexamplePhysicalEdge S hh j outer)).val := by
  rfl

private abbrev counterSigma (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  repair2C3InputOfSyndrome S (counterexampleDomain S hh j outer)
private abbrev counterTau (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  repair2C3PerturbTop S (counterSigma S hh j outer)
    (repair2C3Flip S (counterexamplePhysical S hh j outer))
private def counterTop (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    LocalizedWord S 1 (counterSigma S hh j outer) (counterTau S hh j outer)
      (Fin.succ (0 : StepIndex 1)) :=
  initial S 1 (counterSigma S hh j outer)
    (repair2C3Flip S (counterexamplePhysical S hh j outer))
    (elementaryCenter S 1 (counterexamplePhysical S hh j outer))
    (OriginalOneStepPhiBridge.original_flip_supported S 1 (counterexamplePhysical S hh j outer))
private abbrev counterA (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Upper S 3 (2 : StepIndex 3) :=
  BDL26LocalizedHistoryErrorDescent.first S 1 (counterSigma S hh j outer) (0 : StepIndex 1)
private abbrev counterB (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Upper S 3 (2 : StepIndex 3) :=
  BDL26LocalizedHistoryErrorDescent.second S 1 (counterSigma S hh j outer)
    (counterTau S hh j outer) (0 : StepIndex 1) (counterTop S hh j outer)

/-- The original correlated two-history representatives differ by the SAME
one physical old-X coordinate. Their individual chosen preimages are not
replaced by alpha+QW, and no linearity of choose is used. -/
private theorem counter_original_representatives (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    counterA S hh j outer+counterB S hh j outer=
      repair2C3Flip S (counterexamplePhysical S hh j outer) :=
  representatives_difference S 1 (counterSigma S hh j outer) (counterTau S hh j outer)
    (0 : StepIndex 1) (counterTop S hh j outer)

private theorem counter_actual_OneX (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    OneX S 3 (2 : StepIndex 3) (by decide) (AX S j outer)
      (counterA S hh j outer) (counterB S hh j outer) := by
  unfold OneX
  rw [counter_original_representatives,repair2C3Flip_basis]
  intro p hp
  have he : p=counterexamplePhysical S hh j outer := by
    by_contra hn
    have hv : (canonicalBasisWord (counterexamplePhysical S hh j outer) :
      Word BDL26Field (BDL26CSSHamiltonian.Physical S 3)) p≠0 :=
      (Finset.mem_filter.mp hp).2
    exact hv (by simp [basis_value,hn])
  subst p
  rw [counterexamplePhysical_eq_chart]
  change (xCorrectionEquiv (AP S) S (AX S j outer)
    (counterexamplePhysicalEdge S hh j outer)).val∈
    (BDL26RXDecoderAdapter.localX (AP S) S).correctionRegion (AX S j outer)
  exact (xCorrectionEquiv (AP S) S (AX S j outer)
    (counterexamplePhysicalEdge S hh j outer)).property

/-- All other original X blocks have zero UPDATED word, so their canonical
potential is exactly the provider's zero branch, even if the original
localization centre was chosen by an unrelated trace. -/
private theorem counter_other_X_updated_zero (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (y : (AP S).X) (hy : y≠AX S j outer) :
    restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion y)
      (updated S 3 (2 : StepIndex 3) (by decide)
        (counterA S hh j outer) (counterB S hh j outer))=0 := by
  have he : BDL26RXFiniteBlockTransport.Localized S 3 (2 : StepIndex 3) (by decide)
      {AX S j outer} ∅ (counterA S hh j outer) (counterB S hh j outer) := by
    simpa [BDL26RXFiniteBlockTransport.Localized,BDL26RXFiniteBlockTransport.xBlocks,
      BDL26RXFiniteBlockTransport.qBlocks,BDL26RXXStarTransport.OneX] using
        counter_actual_OneX S hh j outer
  exact BDL26RXFiniteBlockTransport.updated_other_x_zero S 3 (2 : StepIndex 3)
    (by decide) {AX S j outer} ∅ y (by simpa using hy)
    (counterA S hh j outer) (counterB S hh j outer) he
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXXStarTransport
open scoped Classical BigOperators

private def counterX0 (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Finset (AP S).X :=
  {BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
    (counterTop S hh j outer).center}

/-- This effective potential retains the ORIGINAL localization membership.
In particular, this is not a re-chosen primitive or a zero-gauge substitute. -/
private def counterVeff (S : OddScale) (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    LocalPotential S (2 : StepIndex 3) (AX S j outer) :=
  if AX S j outer∈counterX0 S hh j outer then
    localPotential S 3 (2 : StepIndex 3) (by decide) (AX S j outer)
      (counterA S hh j outer) (counterB S hh j outer) else 0

private theorem counter_accumulated_entire (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    accumulated S 1 (counterexampleDomain S hh j outer)
        (counterexamplePhysical S hh j outer)=
      (rxContract S 3 (2 : StepIndex 3) (by decide)).support_decomposition.cxLift0
        (AX S j outer) (counterVeff S hh j outer) := by
  rw [OriginalOneStepPhiBridge.accumulated_eq_original_Phi]
  exact original_fullPhi_single_active S 3 (2 : StepIndex 3) (by decide)
    (counterX0 S hh j outer) (AX S j outer)
    (counterA S hh j outer) (counterB S hh j outer)
    (counter_other_X_updated_zero S hh j outer)

/-- The original initial star supplies the actual physical transport premise;
the original centre is retained, rather than identified with AX by fiat. -/
private theorem counter_original_localized (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26RXPhysicalStarTransport.Localized S 3 (2 : StepIndex 3)
      (counterTop S hh j outer).center
      (counterA S hh j outer) (counterB S hh j outer) := by
  change hammingSupport (counterA S hh j outer+counterB S hh j outer) ⊆ _
  rw [counter_original_representatives]
  exact (counterTop S hh j outer).supported

/-- The full original Phi has the required derivative on AX. The proof uses
the ORIGINAL remainder-zero theorem, including its complete star premise;
there is no inference from equality of the Phi sum alone. -/
private theorem counter_fullPhi_boundary_X (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
      (AX S j outer))
      ((indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
        (accumulated S 1 (counterexampleDomain S hh j outer)
          (counterexamplePhysical S hh j outer)))=
    restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
      (AX S j outer))
      (updated S 3 (2 : StepIndex 3) (by decide)
        (counterA S hh j outer) (counterB S hh j outer)) := by
  have hl := BDL26RXPhysicalStarTransport.localized_blocks S 3 (2 : StepIndex 3)
    (by decide) (counterTop S hh j outer).center
    (counterA S hh j outer) (counterB S hh j outer)
    (counter_original_localized S hh j outer)
  have hz := BDL26RXFiniteBlockTransport.remainder_x_zero S 3 (2 : StepIndex 3)
    (by decide) (counterX0 S hh j outer)
    (BDL26RXXStarTransport.incidentQ S 3 (2 : StepIndex 3)
      (BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
        (counterTop S hh j outer).center))
    (AX S j outer) (counterA S hh j outer) (counterB S hh j outer) hl
  rw [BDL26RXFiniteBlockTransport.R,map_add] at hz
  have hPhi := OriginalOneStepPhiBridge.accumulated_eq_original_Phi S
    (counterexampleDomain S hh j outer) (counterexamplePhysical S hh j outer)
  change accumulated S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)=
    BDL26RXFiniteBlockTransport.Phi S 3 (2 : StepIndex 3) (by decide)
      (counterX0 S hh j outer) (counterA S hh j outer) (counterB S hh j outer) at hPhi
  rw [← hPhi] at hz
  funext a
  have ha := congrFun hz a
  let u := (restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
      (AX S j outer)) (updated S 3 (2 : StepIndex 3) (by decide)
        (counterA S hh j outer) (counterB S hh j outer))) a
  let d := (restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
      (AX S j outer)) ((indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
        (accumulated S 1 (counterexampleDomain S hh j outer)
          (counterexamplePhysical S hh j outer)))) a
  change u+d=0 at ha
  change d=u
  calc
    d=(u+u)+d := by rw [CharTwo.add_self_eq_zero,zero_add]
    _=u+(u+d) := add_assoc _ _ _
    _=u+0 := congrArg (fun z => u+z) ha
    _=u := add_zero _

private theorem counterVeff_boundary (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (rxContract S 3 (2 : StepIndex 3) (by decide)).rx_local_complexes.cxDelta0
        (AX S j outer) (counterVeff S hh j outer)=
      restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
        (AX S j outer))
        (updated S 3 (2 : StepIndex 3) (by decide)
          (counterA S hh j outer) (counterB S hh j outer)) := by
  have h := counter_fullPhi_boundary_X S hh j outer
  rw [counter_accumulated_entire] at h
  exact ((rxContract S 3 (2 : StepIndex 3) (by decide)).support_decomposition.cxDelta0_restriction (AX S j outer) (counterVeff S hh j outer)).symm.trans h

end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXXStarTransport BDL26TannerLocalRegularity
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

/-- The whole actual updated word is viewed in the original literal carrier.
Both original correction totals remain present; only the defining history
identities and the already proved actual/literal transport are used. -/
private theorem counter_updated_literal (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    updated S 3 (2 : StepIndex 3) (by decide)
        (counterA S hh j outer) (counterB S hh j outer)=
      repair2C3Flip S (counterexamplePhysical S hh j outer)+
        rxCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (counterSigma S hh j outer).val+
        rxCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (counterTau S hh j outer).val := by
  have h := CriticalOldXQueries.actualC3_updated S (counterSigma S hh j outer)
    (counterTau S hh j outer) (counterTop S hh j outer)
  have ha := (CriticalOldXQueries.actualC3_correction S (counterSigma S hh j outer)).trans
    (CriticalOldXQueries.repair4_C3_total_to_literal S (counterSigma S hh j outer))
  have hb := (CriticalOldXQueries.actualC3_correction S (counterTau S hh j outer)).trans
    (CriticalOldXQueries.repair4_C3_total_to_literal S (counterTau S hh j outer))
  funext z
  have hz := congrFun h z
  rw [congrFun ha z,congrFun hb z] at hz
  exact hz

/-- Reading an original total at its original X chart gives exactly the
original chosen local word, including the canonical zero-query branch. -/
private theorem original_total_X_chart (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (sigma : Word BDL26Field (literalZ P S (Fin.succ (0 : StepIndex 1))))
    (hs : sigma∈LinearMap.range
      ((BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
        (Fin.succ (0 : StepIndex 1))))
    (x : P.X) (edge : DoubleCylinderEdge P x S) :
    rxCorrectionTotal (literalData P A R S) sigma
        (xCorrectionEquiv P S x edge).val=
      originalCxWord P A R S ⟨sigma,hs⟩ x edge := by
  have h := congrFun (rx_mask_total_at_x (literalData P A R S) sigma x)
    (xCorrectionEquiv P S x edge).val
  have hm : maskWord ((literalLx P A R S).correctionRegion x)
      (rxCorrectionTotal (literalData P A R S) sigma)
      (xCorrectionEquiv P S x edge).val=
      rxCorrectionTotal (literalData P A R S) sigma
        (xCorrectionEquiv P S x edge).val :=
    if_pos (xCorrectionEquiv P S x edge).property
  exact hm.symm.trans h

private theorem counterVeff_raw_boundary (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    wordLinearMapTranspose (doubleCylinderBoundary1 (AP S) (AX S j outer) S)
        (counterVeff S hh j outer)=
      canonicalBasisWord (counterexamplePhysicalEdge S hh j outer)+
        originalCxWord (AP S) (AA S) (AR S) S
          (counterexampleInput S hh j outer) (AX S j outer)+
        originalCxWord (AP S) (AA S) (AR S) S
          (repair5_actual_to_literal S (counterTau S hh j outer)) (AX S j outer) := by
  have h := counterVeff_boundary S hh j outer
  funext edge
  have hd := localCx_delta0_apply (AP S) S (AX S j outer)
    (counterVeff S hh j outer) edge
  have hv := congrFun (counter_updated_literal S hh j outer)
    (xCorrectionEquiv (AP S) S (AX S j outer) edge).val
  have hs := original_total_X_chart (AP S) (AA S) (AR S) S
    (counterexampleInput S hh j outer).val (counterexampleInput S hh j outer).property
    (AX S j outer) edge
  have ht := original_total_X_chart (AP S) (AA S) (AR S) S
    (repair5_actual_to_literal S (counterTau S hh j outer)).val
    (repair5_actual_to_literal S (counterTau S hh j outer)).property
    (AX S j outer) edge
  have hflip := congrFun (repair2C3Flip_basis S (counterexamplePhysical S hh j outer))
    (xCorrectionEquiv (AP S) S (AX S j outer) edge).val
  have hb : (canonicalBasisWord (counterexamplePhysical S hh j outer) :
      Word BDL26Field (BDL26CSSHamiltonian.Physical S 3))
      (xCorrectionEquiv (AP S) S (AX S j outer) edge).val=
      (canonicalBasisWord (counterexamplePhysicalEdge S hh j outer) :
        Word BDL26Field (DoubleCylinderEdge (AP S) (AX S j outer) S)) edge := by
    have hc := congrArg (fun q : BDL26CSSHamiltonian.Physical S 3 =>
      canonicalBasisWord (F:=BDL26Field) q
        (xCorrectionEquiv (AP S) S (AX S j outer) edge).val)
      (counterexamplePhysical_eq_chart S hh j outer)
    have hi : (xCorrectionEquiv (AP S) S (AX S j outer) edge).val=
        (xCorrectionEquiv (AP S) S (AX S j outer)
          (counterexamplePhysicalEdge S hh j outer)).val ↔
        edge=counterexamplePhysicalEdge S hh j outer := by
      constructor
      · intro he
        exact (xCorrectionEquiv (AP S) S (AX S j outer)).injective (Subtype.ext he)
      · intro he
        subst edge
        rfl
    by_cases he : edge=counterexamplePhysicalEdge S hh j outer
    · exact (hc.trans ((basis_value _ _).trans (if_pos (hi.mpr he)))).trans
        ((basis_value _ _).trans (if_pos he)).symm
    · exact (hc.trans ((basis_value _ _).trans (if_neg (fun h => he (hi.mp h))))).trans
        ((basis_value _ _).trans (if_neg he)).symm
  calc
    _ = ((rxContract S 3 (2 : StepIndex 3) (by decide)).rx_local_complexes.cxDelta0
        (AX S j outer) (counterVeff S hh j outer))
        (xCorrectionEquiv (AP S) S (AX S j outer) edge) := hd.symm
    _ = updated S 3 (2 : StepIndex 3) (by decide)
        (counterA S hh j outer) (counterB S hh j outer)
        (xCorrectionEquiv (AP S) S (AX S j outer) edge).val :=
      congrFun h (xCorrectionEquiv (AP S) S (AX S j outer) edge)
    _ = _ := hv.trans (congrArg₂ (fun a b : BDL26Field => a+b)
      (congrArg₂ (fun a b : BDL26Field => a+b) (hflip.trans hb) hs) ht)

end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26RXLocalReplacement BDL26TannerLocalRegularity
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private theorem counterTau_literal (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    repair5_actual_to_literal S (counterTau S hh j outer)=
      directInput (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
        (canonicalBasisWord (actualAlphaEdge S j outer (oppositeErrorCopy S hh j outer))+
          canonicalBasisWord (counterexamplePhysicalEdge S hh j outer))
        (directHubW S j outer) := by
  rw [← directInput_add_physical_word]
  apply Subtype.ext
  rw [repair5_C3_perturb_val,repair2C3Flip_basis]
  rw [counterexamplePhysical_eq_chart]
  change _= (counterexampleInput S hh j outer).val+_
  rw [directXExtension_basis]
  rfl

private theorem counter_first_Cx_leaf_exit (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S
        (counterexampleInput S hh j outer) (AX S j outer))=0 ∨
    ∃ i : Fin 3,∃ c : BDL26FiniteTannerSquare.Two,
      xFlow (AP S) S (AX S j outer)
        (originalCxWord (AP S) (AA S) (AR S) S
          (counterexampleInput S hh j outer) (AX S j outer))=
        canonicalBasisWord (hubArmCoordinate (AP S) S (AL S j outer i)
          (ALZ S j outer i) c) := by
  apply actual_A_original_leaf_exit S hh j outer (counterexampleInput S hh j outer)
    (oppositeErrorCopy S hh j outer) (actualSmallFace S j outer)
  exact (directInput_raw_query_same (AP S) (AA S) (AR S) S
    (AX S j outer) (AH S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer (oppositeErrorCopy S hh j outer)))
    (directHubW S j outer)).trans
      (actualAlpha_boundary S hh j outer (oppositeErrorCopy S hh j outer))

private theorem counter_second_Cx_hub_exit (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S
        (repair5_actual_to_literal S (counterTau S hh j outer)) (AX S j outer))=
      canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0)
        (chosenHubCopy S hh j outer)) := by
  rw [counterTau_literal,second_D_query_same_original_choice]
  exact chosenHubCopy_spec S hh j outer

/-- Querying the genuine global X flow is exactly the original adjacent
pullback; all other X/Q/Z coordinates remain in the whole flow word. -/
private theorem rawQRead_Xflow (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) (q : P.Q) (hx : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) :
    rawQRead P A R S q (xFlow P S x f)=
      rxXQDegreeOne P A.toTannerSquareAdmissible q x hx S f := by
  funext edge
  change xFlow P S x f (Sum.inl (Sum.inr ⟨q,edge⟩))=
    rxXQDegreeOne P A.toTannerSquareAdmissible q x hx S f edge
  exact (xFlow_at_q P A.toTannerSquareAdmissible S x f q edge).trans (dif_pos hx)

private theorem counter_first_hub_pullback_zero (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    rawQRead (AP S) (AA S) (AR S) S (AH S j outer)
      (xFlow (AP S) S (AX S j outer)
        (originalCxWord (AP S) (AA S) (AR S) S
          (counterexampleInput S hh j outer) (AX S j outer)))=0 := by
  rcases counter_first_Cx_leaf_exit S hh j outer with h0 | ⟨i,c,hc⟩
  · have h := congrArg (fun w : Word BDL26Field (RX2 (AP S) S) =>
        rawQRead (AP S) (AA S) (AR S) S (AH S j outer) (fun z => w z)) h0
    exact h.trans (map_zero (rawQRead (AP S) (AA S) (AR S) S (AH S j outer)))
  · have h := congrArg (fun w : Word BDL26Field (RX2 (AP S) S) =>
        rawQRead (AP S) (AA S) (AR S) S (AH S j outer) (fun z => w z)) hc
    exact h.trans (rawQRead_arm_other (AP S) (AA S) (AR S) S
      (AL S j outer i) (AH S j outer) (Ne.symm (AL_ne_hub S j outer i))
      (ALZ S j outer i) c)

private theorem generic_two_terminal_gradient (P : TannerSquarePresentation)
    (q : P.Q) (S : OddScale) (hh : S.half=1) (z0 : QStarEdge P q)
    (c d : BDL26FiniteTannerSquare.Two) (hcd : c≠d) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (CriticalOriginalChoice.terminalWord P q S 0 z0+
        CriticalOriginalChoice.terminalWord P q S 1 z0)=
      canonicalBasisWord (Sum.inl (c,z0,⟨0,S.half_pos⟩))+
        canonicalBasisWord (Sum.inl (d,z0,⟨0,S.half_pos⟩)) := by
  classical
  funext edge
  rcases edge with ⟨copy,z,k⟩ | z
  · have hk : k=(⟨0,S.half_pos⟩ : Fin S.half) := Fin.ext (by omega)
    subst k
    have he := CriticalOriginalChoice.halfOne_delta_arm P q S hh
      (CriticalOriginalChoice.terminalWord P q S 0 z0+
        CriticalOriginalChoice.terminalWord P q S 1 z0) copy z
    refine he.trans ?_
    fin_cases c <;> fin_cases d <;> fin_cases copy
    all_goals first | exact False.elim (hcd rfl) |
      simp [CriticalOriginalChoice.terminalWord,basis_value,Prod.mk.injEq,
        Pi.add_apply,CharTwo.add_self_eq_zero]
  · rw [CriticalOriginalChoice.delta_bridge]
    simp [CriticalOriginalChoice.terminalWord,basis_value,Pi.add_apply,
      CharTwo.add_self_eq_zero]

/-- The two opposite copies exhaust Fin2; the complete two-arm syndrome is
exactly the gradient of the SAME radial terminal-pair K. -/
private theorem directHubK_gradient (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (c d : BDL26FiniteTannerSquare.Two) (hcd : c≠d) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
      (directHubK S j outer)=
      canonicalBasisWord (Sum.inl (c,AHZ S j outer 0,⟨0,S.half_pos⟩))+
      canonicalBasisWord (Sum.inl (d,AHZ S j outer 0,⟨0,S.half_pos⟩)) := by
  unfold directHubK
  exact generic_two_terminal_gradient (AP S) (AH S j outer) S hh
    (AHZ S j outer 0) c d hcd

private def counterHubPotential (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : Word BDL26Field (QDoubleCylinderVertex (AP S) (AH S j outer) S) :=
  rxXQDegreeZero (AP S) (AA S).toTannerSquareAdmissible (AH S j outer)
    (AX S j outer) (AH_incident S j outer) S (counterVeff S hh j outer)

/-- The original FULL effective potential has a forced radial terminal-pair
on the hub, up to ONE whole-cylinder constant. This follows from the original
Cx exits and actual commuting pullback, without choosing a different Phi. -/
private theorem counter_hub_potential_gradient (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
        (counterHubPotential S hh j outer)=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
        (directHubK S j outer) := by
  let T := rxXQDegreeOne (AP S) (AA S).toTannerSquareAdmissible
    (AH S j outer) (AX S j outer) (AH_incident S j outer) S
  let e : Word BDL26Field (DoubleCylinderEdge (AP S) (AX S j outer) S) :=
    canonicalBasisWord (counterexamplePhysicalEdge S hh j outer)
  let f := originalCxWord (AP S) (AA S) (AR S) S
    (counterexampleInput S hh j outer) (AX S j outer)
  let g := originalCxWord (AP S) (AA S) (AR S) S
    (repair5_actual_to_literal S (counterTau S hh j outer)) (AX S j outer)
  let Q := rawQRead (AP S) (AA S) (AR S) S (AH S j outer)
  have hcomm := LinearMap.congr_fun (rxXQ_commutes (AP S)
    (AA S).toTannerSquareAdmissible (AH S j outer) (AX S j outer)
    (AH_incident S j outer) S) (counterVeff S hh j outer)
  have he : T e=canonicalBasisWord (Sum.inl
      (oppositeErrorCopy S hh j outer,AHZ S j outer 0,⟨0,S.half_pos⟩)) :=
    (rawQRead_Xflow (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
      (AH_incident S j outer) e).symm.trans
      ((congrArg (fun w : Word BDL26Field (RX2 (AP S) S) => Q (fun z => w z))
        (actualError_flow S j outer (oppositeErrorCopy S hh j outer))).trans
          (rawQRead_arm_same (AP S) (AA S) (AR S) S (AH S j outer)
            (AHZ S j outer 0) (oppositeErrorCopy S hh j outer)))
  have hf : T f=0 :=
    (rawQRead_Xflow (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
      (AH_incident S j outer) f).symm.trans
        (counter_first_hub_pullback_zero S hh j outer)
  have hg : T g=canonicalBasisWord (Sum.inl
      (chosenHubCopy S hh j outer,AHZ S j outer 0,⟨0,S.half_pos⟩)) :=
    (rawQRead_Xflow (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
      (AH_incident S j outer) g).symm.trans
      ((congrArg (fun w : Word BDL26Field (RX2 (AP S) S) => Q (fun z => w z))
        (counter_second_Cx_hub_exit S hh j outer)).trans
          (rawQRead_arm_same (AP S) (AA S) (AR S) S (AH S j outer)
            (AHZ S j outer 0) (chosenHubCopy S hh j outer)))
  have hlin : T (e+f+g)=(T e+T f)+T g :=
    (map_add T (e+f) g).trans (congrArg (fun w => w+T g) (map_add T e f))
  have hout : T (e+f+g)=
      canonicalBasisWord (Sum.inl
        (oppositeErrorCopy S hh j outer,AHZ S j outer 0,⟨0,S.half_pos⟩))+
      canonicalBasisWord (Sum.inl
        (chosenHubCopy S hh j outer,AHZ S j outer 0,⟨0,S.half_pos⟩)) :=
    hlin.trans ((congrArg₂ (fun a b => a+b)
      ((congrArg₂ (fun a b => a+b) he hf).trans (add_zero _)) hg))
  exact hcomm.trans ((congrArg T (counterVeff_raw_boundary S hh j outer)).trans
    (hout.trans (directHubK_gradient S hh j outer
      (oppositeErrorCopy S hh j outer) (chosenHubCopy S hh j outer)
      (oppositeErrorCopy_ne S hh j outer)).symm))

private def counterBeta (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26Field :=
  counterHubPotential S hh j outer (0,.inl (.inl ()))

private theorem counter_hub_potential_entire (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    counterHubPotential S hh j outer=
      fun v => directHubK S j outer v+counterBeta S hh j outer := by
  let f := counterHubPotential S hh j outer+directHubK S j outer
  have hf : wordLinearMapTranspose
      (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S) f=0 := by
    rw [map_add,counter_hub_potential_gradient,repair3_word_add_self]
  have hc := word_eq_root_of_graphCoboundary_eq_zero
    (qDoubleCylinderEdgeStart (AP S) (AH S j outer) S)
    (qDoubleCylinderEdgeEnd (AP S) (AH S j outer) S)
    (0,.inl (.inl ()))
    (qDoubleCylinderPath (AP S) (AA S).toTannerSquareAdmissible (AH S j outer) S) f hf
  funext v
  have hv := hc v
  have hroot : directHubK S j outer (0,.inl (.inl ()))=0 := by
    unfold directHubK CriticalOriginalChoice.terminalWord
    rw [Pi.add_apply]
    have hn0 : ((0,Sum.inl (Sum.inl ())) : QDoubleCylinderVertex (AP S) (AH S j outer) S)≠
        (0,Sum.inl (Sum.inr (AHZ S j outer 0))) := by
      intro he
      have hi := Sum.inl.inj (congrArg Prod.snd he)
      cases hi
    have hn1 : ((0,Sum.inl (Sum.inl ())) : QDoubleCylinderVertex (AP S) (AH S j outer) S)≠
        (1,Sum.inl (Sum.inr (AHZ S j outer 0))) := by
      intro he
      exact (by decide : (0:BDL26FiniteTannerSquare.Two)≠1) (congrArg Prod.fst he)
    exact (congrArg₂ (fun a b : BDL26Field => a+b)
      ((basis_value (I:=QDoubleCylinderVertex (AP S) (AH S j outer) S)
        (0,Sum.inl (Sum.inr (AHZ S j outer 0))) (0,Sum.inl (Sum.inl ()))).trans (if_neg hn0))
      ((basis_value (I:=QDoubleCylinderVertex (AP S) (AH S j outer) S)
        (1,Sum.inl (Sum.inr (AHZ S j outer 0))) (0,Sum.inl (Sum.inl ()))).trans (if_neg hn1))).trans
          (zero_add 0)
  change counterHubPotential S hh j outer v+directHubK S j outer v=
    counterHubPotential S hh j outer (0,.inl (.inl ()))+
      directHubK S j outer (0,.inl (.inl ())) at hv
  rw [hroot,add_zero] at hv
  calc
    counterHubPotential S hh j outer v=
        (counterHubPotential S hh j outer v+directHubK S j outer v)+
          directHubK S j outer v := by rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
    _=counterBeta S hh j outer+directHubK S j outer v :=
      congrArg (fun a => a+directHubK S j outer v) hv
    _=_ := add_comm _ _

end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26RXLocalReplacement BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open scoped Classical BigOperators

/-- Covariant evaluation of the actual upper coboundary on BOTH genuine
successor charts. The whole X sum is transported by a bijection. -/
private theorem actual_delta0_on_RX_charts (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (hi : i.val%2=0)
    (v : (indexedFamily S depth).Cochain0 i.succ)
    (p : RX1 (state S i.val).presentation S) :
    (indexedFamily S depth).coboundary0 i.succ v
        (rxPhysicalQEquiv S depth i hi p)=
      rxCoboundary0 (state S i.val).presentation S
        (fun r => v (rxDegreeZeroEquiv S depth i hi r)) p := by
  let P := (state S i.val).presentation
  let Pu := (state S (i.val+1)).presentation
  let Pr := rxReplacementPresentation P S
  let eX : Pr.X ≃ Pu.X := rxDegreeZeroEquiv S depth i hi
  let eQ : Pr.Q ≃ Pu.Q := rxPhysicalQEquiv S depth i hi
  let w : Word BDL26Field Pr.X := fun r => v (eX r)
  have hw : wordEquiv eX w = v := by
    funext x
    rw [wordEquiv_apply]
    change v (eX (eX.symm x)) = v x
    exact congrArg v (eX.apply_symm_apply x)
  have hinc : ∀ (r : Pr.X) (q : Pr.Q),
      Pu.xq (eX r) (eQ q) = Pr.xq r q := by
    intro r q
    exact rxPhysical_incidence S depth i hi r q
  have htransport :=
    BDL26TransposedStoppedDecoder.Coordinates.coboundary0_transport
      Pr Pu eX eQ hinc w p
  have hraw := congrFun (LinearMap.congr_fun
    (rxPresentation_coboundary0_eq P
      (state S i.val).admissible (state S i.val).regular S) w) p
  calc
    (indexedFamily S depth).coboundary0 i.succ v
        (rxPhysicalQEquiv S depth i hi p) =
        tannerCoboundary0 Pu v (eQ p) :=
      congrFun (LinearMap.congr_fun
        (indexedFamily_coboundary0 S depth i.succ) v) (eQ p)
    _ = tannerCoboundary0 Pu (wordEquiv eX w) (eQ p) :=
      congrArg (fun u : Word BDL26Field Pu.X =>
        tannerCoboundary0 Pu u (eQ p)) hw.symm
    _ = tannerCoboundary0 Pr w p := htransport
    _ = rxCoboundary0 P S w p := hraw

private theorem actual_Xlift_on_RX_chart (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (hi : i.val%2=0) (x : (state S i.val).presentation.X)
    (v : Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S)) :
    (fun r => (rxContract S depth i hi).support_decomposition.cxLift0 x v
        (rxDegreeZeroEquiv S depth i hi r))=
      xLift (state S i.val).presentation S x v := by
  funext r
  rcases r with ⟨y,a⟩
  by_cases hy : y=x
  · subst y
    rw [rxXLift_same,xLift_same]
  · rw [rxXLift_other S depth i hi x y hy,xLift_other _ _ x y hy]

/-- At an actual old-Z terminal the X-Q incidence is ONE existing shared
vertex, rather than an assumed local-to-global matrix transport. -/
private theorem terminal_incidence_indicator (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) (q : P.Q) (hx : P.xq x q=true)
    (root z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) (a : DoubleCylinderVertex P x S) :
    qDoubleCylinderVertexXIncidence P q x S a (c,.inl (.inr z))=
      if a=qToXDoubleCylinderVertexAtRoot P q x hx S root
        (c,.inl (.inr z)) then 1 else 0 := by
  rcases a with ⟨copy,a⟩
  rcases a with old | edgeInterior | faceInterior
  all_goals simp [qDoubleCylinderVertexXIncidence,qSubdivisionVertexXIncidence,
    qToXDoubleCylinderVertexAtRoot,qToXSubdivisionVertexAtRoot,qToXBoundaryVertexAtRoot,
    xStarBoundaryVertexToStar,Prod.ext_iff,Subtype.ext_iff,hx,
    xBoundaryEdgeEnd,qToXBoundaryEdge]
  all_goals split_ifs <;> simp_all only [true_and,and_true,and_false,false_and,
    if_true,if_false]
  all_goals exact False.elim ((by assumption : ¬True) True.intro)

private theorem raw_Xlift_delta_at_terminal (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) (q : P.Q) (hx : P.xq x q=true)
    (root z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two)
    (v : Word BDL26Field (DoubleCylinderVertex P x S)) :
    rxCoboundary0 P S (xLift P S x v) (.inr ⟨q,(c,.inl (.inr z))⟩)=
      v (qToXDoubleCylinderVertexAtRoot P q x hx S root (c,.inl (.inr z))) := by
  unfold rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply,Fintype.sum_sigma]
  rw [Fintype.sum_eq_single x]
  · simp only [rxBoundary1Matrix,xLift_same]
    simp_rw [terminal_incidence_indicator P S x q hx root z c]
    rw [Fintype.sum_eq_single
      (qToXDoubleCylinderVertexAtRoot P q x hx S root (c,.inl (.inr z)))]
    · simp
    · intro a ha
      simp [ha]
  · intro y hy
    apply Finset.sum_eq_zero
    intro a _
    rw [xLift_other P S x y hy v a,zero_mul]

/-- Exact entire original Phi evaluation at every terminal of the active star. -/
private theorem counter_fullPhi_terminal (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (q : (AP S).Q)
    (hx : (AP S).xq (AX S j outer) q=true)
    (root z : QStarEdge (AP S) q) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
      (BDL26ActualFailureReadout.accumulated S 1 (counterexampleDomain S hh j outer)
        (counterexamplePhysical S hh j outer))
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide)
        (.inr ⟨q,(c,.inl (.inr z))⟩))=
      counterVeff S hh j outer
        (qToXDoubleCylinderVertexAtRoot (AP S) q (AX S j outer) hx S root
          (c,.inl (.inr z))) := by
  let p := (Sum.inr ⟨q,(c,Sum.inl (Sum.inr z))⟩ : RX1 (AP S) S)
  let V := (rxContract S 3 (2 : StepIndex 3) (by decide)).support_decomposition.cxLift0
    (AX S j outer) (counterVeff S hh j outer)
  have hacc := congrArg (fun v : (indexedFamily S 3).Cochain0 (3 : LevelIndex 3) =>
    (indexedFamily S 3).coboundary0 (3 : LevelIndex 3) v
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) p))
        (counter_accumulated_entire S hh j outer)
  have hchart := actual_delta0_on_RX_charts S 3 (2 : StepIndex 3) (by decide) V p
  have hlift := actual_Xlift_on_RX_chart S 3 (2 : StepIndex 3) (by decide)
    (AX S j outer) (counterVeff S hh j outer)
  have he := congrArg (fun w : Word BDL26Field (RX0 (AP S) S) =>
    BDL26ReplacementCochainMaps.rxCoboundary0 (AP S) S w p) hlift
  exact hacc.trans (hchart.trans (he.trans
    (raw_Xlift_delta_at_terminal (AP S) S (AX S j outer) q hx root z c
      (counterVeff S hh j outer))))

private theorem counter_leaf_Phi_value (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
      (BDL26ActualFailureReadout.accumulated S 1 (counterexampleDomain S hh j outer)
        (counterexamplePhysical S hh j outer))
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide)
        (.inr ⟨AL S j outer i,(c,.inl (.inr (ALZ S j outer i)))⟩))=
      (if i=0 then 1 else 0)+counterBeta S hh j outer := by
  rw [counter_fullPhi_terminal S hh j outer (AL S j outer i)
    (AL_incident S j outer i) (ALZ S j outer i) (ALZ S j outer i) c]
  have hi := ActualCriticalStarGeometry.shared_terminal_same_image (AP S) S
    (AX S j outer) (AL S j outer i) (AH S j outer)
    (AL_incident S j outer i) (AH_incident S j outer) (AZ S j outer i)
    (AL_check S j outer i) (AH_check S j outer i)
    (ALZ S j outer i) (AHZ S j outer i) c
  change qToXDoubleCylinderVertexAtRoot (AP S) (AL S j outer i) (AX S j outer)
      (AL_incident S j outer i) S (ALZ S j outer i)
      (c,Sum.inl (Sum.inr (ALZ S j outer i)))=
    qToXDoubleCylinderVertexAtRoot (AP S) (AH S j outer) (AX S j outer)
      (AH_incident S j outer) S (AHZ S j outer i)
      (c,Sum.inl (Sum.inr (AHZ S j outer i))) at hi
  have he : counterVeff S hh j outer
      (qToXDoubleCylinderVertexAtRoot (AP S) (AH S j outer) (AX S j outer)
        (AH_incident S j outer) S (AHZ S j outer i)
        (c,.inl (.inr (AHZ S j outer i))))=
      counterHubPotential S hh j outer (c,.inl (.inr (AHZ S j outer i))) := by rfl
  calc
    _ = counterHubPotential S hh j outer (c,Sum.inl (Sum.inr (AHZ S j outer i))) :=
      (congrArg (counterVeff S hh j outer) hi).trans he
    _ = directHubK S j outer (c,Sum.inl (Sum.inr (AHZ S j outer i)))+
        counterBeta S hh j outer :=
      congrFun (counter_hub_potential_entire S hh j outer)
        (c,Sum.inl (Sum.inr (AHZ S j outer i)))
    _ = _ := by
      congr 1
      have hinj := AHZ_injective S j outer
      fin_cases i <;> rcases two_eq_zero_or_one c with hc | hc <;>
        simp [directHubK,CriticalOriginalChoice.terminalWord,
          canonicalBasisWord,Pi.single_apply,hinj.eq_iff,hc]

private theorem counter_hub_Phi_value (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
      (BDL26ActualFailureReadout.accumulated S 1 (counterexampleDomain S hh j outer)
        (counterexamplePhysical S hh j outer))
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide)
        (.inr ⟨AH S j outer,(c,.inl (.inr (AHZ S j outer i)))⟩))=
      (if i=0 then 1 else 0)+counterBeta S hh j outer := by
  rw [counter_fullPhi_terminal S hh j outer (AH S j outer) (AH_incident S j outer)
    (AHZ S j outer i) (AHZ S j outer i) c]
  change counterHubPotential S hh j outer (c,.inl (.inr (AHZ S j outer i)))=_
  rw [counter_hub_potential_entire]
  congr 1
  have hinj := AHZ_injective S j outer
  fin_cases i <;> rcases two_eq_zero_or_one c with hc | hc <;>
    simp [directHubK,CriticalOriginalChoice.terminalWord,
      canonicalBasisWord,Pi.single_apply,hinj.eq_iff,hc]

end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXLocalReplacement BDL26TannerLocalRegularity
open scoped Classical BigOperators

private theorem counterVeff_nonzero (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : counterVeff S hh j outer≠0 := by
  intro hz
  have h := counter_hub_potential_gradient S hh j outer
  have hp : counterHubPotential S hh j outer=0 := by
    unfold counterHubPotential
    rw [hz,map_zero]
  rw [hp,map_zero] at h
  have he := congrFun h (CriticalOriginalChoice.firstArm (AP S) (AH S j outer) S
    0 (AHZ S j outer 0))
  rw [CriticalOriginalChoice.halfOne_delta_arm (AP S) (AH S j outer) S hh] at he
  have hs : directHubK S j outer (0,.inl (.inl ()))+
      directHubK S j outer (0,.inl (.inr (AHZ S j outer 0)))=1 := by
    simp [directHubK,CriticalOriginalChoice.terminalWord,canonicalBasisWord,Pi.single_apply]
  rw [hs] at he
  exact zero_ne_one he

/-- The actual chosen localization parent is now IDENTIFIED BY A PROOF:
the effective local summand is nonzero. It was not assumed in Phi reduction. -/
private theorem counter_original_parent (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
      (counterTop S hh j outer).center=AX S j outer := by
  have hm : AX S j outer∈counterX0 S hh j outer := by
    by_contra hn
    apply counterVeff_nonzero S hh j outer
    exact if_neg hn
  exact (Finset.mem_singleton.mp hm).symm

private theorem counter_descent_entire_L (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (descent S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)).word=
      BDL26RXPhysicalStarTransport.L S 3 (2 : StepIndex 3) (by decide)
        (counterTop S hh j outer).center
        (counterA S hh j outer) (counterB S hh j outer) := by
  change (path S 1 (counterSigma S hh j outer) (counterTau S hh j outer)
    (counterTop S hh j outer) (0 : StepIndex 1).castSucc).word=_
  rw [path_step]
  have hp : path S 1 (counterSigma S hh j outer) (counterTau S hh j outer)
      (counterTop S hh j outer) (Fin.succ (0 : StepIndex 1))=counterTop S hh j outer :=
    path_top S 1 (counterSigma S hh j outer)
      (counterTau S hh j outer) (counterTop S hh j outer)
  rw [hp]
  exact (step_RX_fixed S 1 (counterSigma S hh j outer) (counterTau S hh j outer)
    (0 : StepIndex 1) (by decide) (counterTop S hh j outer)).1

/-- COMPLETE word support in the original four ports. This follows from the
actual physical transport and the PROVED original parent, not a parity-only
projection or a freely supplied four-coordinate error. -/
private theorem counter_descent_supported (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    hammingSupport (descent S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)).word ⊆
      {AL S j outer 0,AH S j outer,AL S j outer 1,AL S j outer 2} := by
  rw [counter_descent_entire_L]
  have hs := BDL26RXPhysicalStarTransport.lower_supported S 3 (2 : StepIndex 3)
    (by decide) (counterTop S hh j outer).center
    (counterA S hh j outer) (counterB S hh j outer)
    (counter_original_localized S hh j outer)
  rw [counter_original_parent] at hs
  intro q hq
  have hi := (BDL26RXPhysicalStarTransport.mem_physicalXStar (AP S)
    (AX S j outer) q).mp (hs hq)
  rcases actual_Q_cover S j outer q hi with h | ⟨i,h⟩
  · simp [h]
  · fin_cases i <;> simp [h]

end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26RXDecoderAdapter
open BDL26RXLocalReplacement BDL26TannerLocalRegularity
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
section
variable (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
  (R : TannerSquareCellularRegular P) (S : OddScale)
local notation "CF" => BDL26DecoderData.family (literalDecoderData P A R S)
local notation "G" => literalData P A R S
local notation "LX" => (literalLx P A R S :
  @LocalComplexData (TannerSquarePresentation.X P)
    (TannerSquareData.xFintype (TannerSquarePresentation.data P))
    (TannerSquareData.xDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "LQ" => (literalLq P A R S :
  @LocalComplexData (TannerSquarePresentation.Q P)
    (TannerSquareData.qFintype (TannerSquarePresentation.data P))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data P))
    (literalZ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.zFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.zDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (literalQ P S (Fin.succ (0 : StepIndex 1)))
    (TannerSquareData.qFintype (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1)))))
    (TannerSquareData.qDecidableEq (TannerSquarePresentation.data (literalAt P S (Fin.succ (0 : StepIndex 1))))))
local notation "U" => (Fin.succ (0 : StepIndex 1))


private theorem Cq_from_two_Q_boundaries (sigma : (CF).Syndrome U)
    (q r : P.Q) (hqr : q≠r)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (v : Word BDL26Field (QDoubleCylinderVertex P r S))
    (ha : rxSigmaAfterCx G sigma.val=(CF).coboundary1 U
      (directQExtension P A R S q w)+(CF).coboundary1 U
        (directQExtension P A R S r v))
    (hw : CriticalOriginalChoice.originalChoice P A R S q w=w)
    (hv : CriticalOriginalChoice.originalChoice P A R S r v=v) :
    cqCorrectionTotal G sigma.val=
      directQExtension P A R S q w+directQExtension P A R S r v := by
  apply originalCq_two_components P A R S sigma q r hqr w v
  · rw [originalCqWord_of_query P A R S sigma q w,hw]
    change rawQRead P A R S q (rxSigmaAfterCx G sigma.val)=_
    rw [ha,map_add,rawQRead_Qextension_same,
      rawQRead_Qextension_other P A R S r q hqr,add_zero]
  · rw [originalCqWord_of_query P A R S sigma r v,hv]
    change rawQRead P A R S r (rxSigmaAfterCx G sigma.val)=_
    rw [ha,map_add,rawQRead_Qextension_same,
      rawQRead_Qextension_other P A R S q r hqr.symm,zero_add]
  · intro a haq har
    rw [originalCqWord_of_query P A R S sigma a 0,
      CriticalOriginalChoice.actual_original_choice_zero]
    change rawQRead P A R S a (rxSigmaAfterCx G sigma.val)=_
    rw [ha,map_add,rawQRead_Qextension_other P A R S q a haq,
      rawQRead_Qextension_other P A R S r a har,zero_add,map_zero]

private theorem Cq_from_one_Q_query (sigma : (CF).Syndrome U) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (hq : rawQRead P A R S q (rxSigmaAfterCx G sigma.val)=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w)
    (ho : ∀ r : P.Q,r≠q → rawQRead P A R S r (rxSigmaAfterCx G sigma.val)=0) :
    cqCorrectionTotal G sigma.val=directQExtension P A R S q
      (CriticalOriginalChoice.originalChoice P A R S q w) := by
  have hmain := originalCqWord_of_query P A R S sigma q w hq
  have hother (r : P.Q) (hr : r≠q) : originalCqWord P A R S sigma r=0 := by
    have hzero : (wordLinearMapTranspose (qDoubleCylinderBoundary1 P r S))
        (0 : Word BDL26Field (QDoubleCylinderVertex P r S))=0 := map_zero _
    have harg : rawQRead P A R S r (rxSigmaAfterCx G sigma.val)=
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P r S))
          (0 : Word BDL26Field (QDoubleCylinderVertex P r S)) :=
      (ho r hr).trans hzero.symm
    exact (originalCqWord_of_query P A R S sigma r 0 harg).trans
      (CriticalOriginalChoice.actual_original_choice_zero P A R S r)
  calc
    cqCorrectionTotal G sigma.val =
        ∑ r : P.Q,directQExtension P A R S r (originalCqWord P A R S sigma r) :=
      originalCq_total_sum P A R S sigma
    _ = directQExtension P A R S q (originalCqWord P A R S sigma q) := by
      apply Finset.sum_eq_single q
      · intro r _ hr
        exact (congrArg (directQExtension P A R S r) (hother r hr)).trans
          (map_zero ((extendWordLinear ((LQ).correctionRegion r)).comp
            (wordEquiv (qCorrectionEquiv P S r)).toLinearMap))
      · intro h
        exact False.elim (h (Finset.mem_univ q))
    _ = _ := congrArg (directQExtension P A R S q) hmain
end

/-- The ORIGINAL first Cq total: original hub W plus at most one genuine
leaf cone. Every terminal of the latter is zero. -/
private theorem counter_first_Cq_total (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    ∃ i : Fin 3, ∃ v : Word BDL26Field (QDoubleCylinderVertex (AP S) (AL S j outer i) S),
      (∀ c z,v (c,.inl (.inr z))=0) ∧
      cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (counterexampleInput S hh j outer).val=
        directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (directHubW S j outer)+
        directQExtension (AP S) (AA S) (AR S) S (AL S j outer i) v := by
  let alpha : Word BDL26Field (DoubleCylinderEdge (AP S) (AX S j outer) S) :=
    canonicalBasisWord (actualAlphaEdge S j outer (oppositeErrorCopy S hh j outer))
  let f := originalCxWord (AP S) (AA S) (AR S) S
    (counterexampleInput S hh j outer) (AX S j outer)
  have ha := directInput_after_Cx_global (AP S) (AA S) (AR S) S
    (AX S j outer) (AH S j outer) alpha (directHubW S j outer)
  have hx (i : Fin 3) (v : Word BDL26Field (QDoubleCylinderVertex (AP S) (AL S j outer i) S))
      (hf : xFlow (AP S) S (AX S j outer) f=
        (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
          (Fin.succ (0 : StepIndex 1)) (directQExtension (AP S) (AA S) (AR S) S (AL S j outer i) v)) :
      rxSigmaAfterCx (literalData (AP S) (AA S) (AR S) S)
          (counterexampleInput S hh j outer).val=
        (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
          (Fin.succ (0 : StepIndex 1)) (directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (directHubW S j outer))+
        (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
          (Fin.succ (0 : StepIndex 1)) (directQExtension (AP S) (AA S) (AR S) S (AL S j outer i) v) := by
    funext z
    exact (congrFun ha z).trans
      ((congrArg₂ (fun a b : BDL26Field => a+b)
        (congrArg₂ (fun a b : BDL26Field => a+b)
          (congrFun (actualAlpha_flow_zero S j outer (oppositeErrorCopy S hh j outer)) z) rfl)
        (congrFun hf z)).trans
          (congrArg (fun a : BDL26Field => a+_) (zero_add _)))
  rcases counter_first_Cx_leaf_exit S hh j outer with h0 | ⟨i,c,hi⟩
  · refine ⟨0,0,?_,?_⟩
    · intro c z
      rfl
    · apply Cq_from_two_Q_boundaries (AP S) (AA S) (AR S) S
        (counterexampleInput S hh j outer) (AH S j outer) (AL S j outer 0)
        (Ne.symm (AL_ne_hub S j outer 0)) (directHubW S j outer) 0
      · have hzero : (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
            (Fin.succ (0 : StepIndex 1)) (directQExtension (AP S) (AA S) (AR S) S (AL S j outer 0) 0)=0 :=
          (congrArg ((BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
            (Fin.succ (0 : StepIndex 1)))
              (map_zero ((extendWordLinear ((literalLq (AP S) (AA S) (AR S) S).correctionRegion (AL S j outer 0))).comp
                (wordEquiv (qCorrectionEquiv (AP S) S (AL S j outer 0))).toLinearMap))).trans (map_zero _)
        exact hx 0 0 (h0.trans hzero.symm)
      · exact (directHub_original_values S hh j outer).1
      · exact CriticalOriginalChoice.actual_original_choice_zero _ _ _ _ _
  · let v := CriticalOriginalChoice.coneWord (AP S) (AL S j outer i) S c
    refine ⟨i,v,?_,?_⟩
    · intro copy z
      exact (basis_value _ _).trans (if_neg (by intro h; cases h))
    · apply Cq_from_two_Q_boundaries (AP S) (AA S) (AR S) S
        (counterexampleInput S hh j outer) (AH S j outer) (AL S j outer i)
        (Ne.symm (AL_ne_hub S j outer i)) (directHubW S j outer) v
      · exact hx i v (hi.trans
          (cone_global_boundary_single_arm (AP S) (AA S) (AR S) S
            (AL S j outer i) (ALZ S j outer i) (ALZ_unique S j outer i) c).symm)
      · exact (directHub_original_values S hh j outer).1
      · exact CriticalOriginalChoice.actual_original_choice_fixes_cone _ _ _ _ _ _

private theorem counter_second_after_Cx_entire (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    rxSigmaAfterCx (literalData (AP S) (AA S) (AR S) S) (counterTau S hh j outer).val=
      canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0)
        (oppositeErrorCopy S hh j outer))+
      (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
        (Fin.succ (0 : StepIndex 1))
          (directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (directHubW S j outer))+
      canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0)
        (chosenHubCopy S hh j outer)) := by
  exact original_after_Cx_from_columns (AP S) (AA S) (AR S) S
    (AX S j outer) (AH S j outer)
    (canonicalBasisWord (actualAlphaEdge S j outer (oppositeErrorCopy S hh j outer)))
    (canonicalBasisWord (counterexamplePhysicalEdge S hh j outer))
    (directHubW S j outer) (repair5_actual_to_literal S (counterTau S hh j outer))
    (canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0)
      (oppositeErrorCopy S hh j outer)))
    (canonicalBasisWord (hubArmCoordinate (AP S) S (AH S j outer) (AHZ S j outer 0)
      (chosenHubCopy S hh j outer)))
    (counterTau_literal S hh j outer)
    (actualAlpha_flow_zero S j outer (oppositeErrorCopy S hh j outer))
    (actualError_flow S j outer (oppositeErrorCopy S hh j outer))
    (counter_second_Cx_hub_exit S hh j outer)

/-- Only the Q query is δ(W+K). The complete post-Cx word above retains
its original Z flow and is deliberately NOT replaced by δ(Q(W+K)). -/
private theorem counter_second_Cq_total (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S) (counterTau S hh j outer).val=
      directQExtension (AP S) (AA S) (AR S) S (AH S j outer)
        (fun v => (directHubW S j outer+directHubK S j outer) v+1) := by
  have hq : rawQRead (AP S) (AA S) (AR S) S (AH S j outer)
      (rxSigmaAfterCx (literalData (AP S) (AA S) (AR S) S) (counterTau S hh j outer).val)=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
        (directHubW S j outer+directHubK S j outer) := by
    funext edge
    let p := (Sum.inl (Sum.inr ⟨AH S j outer,edge⟩) : RX2 (AP S) S)
    have ha := congrFun (counter_second_after_Cx_entire S hh j outer) p
    have he := congrFun (rawQRead_arm_same (AP S) (AA S) (AR S) S
      (AH S j outer) (AHZ S j outer 0) (oppositeErrorCopy S hh j outer)) edge
    have hw := congrFun (rawQRead_Qextension_same (AP S) (AA S) (AR S) S
      (AH S j outer) (directHubW S j outer)) edge
    have hd := congrFun (rawQRead_arm_same (AP S) (AA S) (AR S) S
      (AH S j outer) (AHZ S j outer 0) (chosenHubCopy S hh j outer)) edge
    have hk := congrFun (directHubK_gradient S hh j outer
      (oppositeErrorCopy S hh j outer) (chosenHubCopy S hh j outer)
      (oppositeErrorCopy_ne S hh j outer)) edge
    have hs := congrFun (map_add
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S))
        (directHubW S j outer) (directHubK S j outer)) edge
    calc
      _ = _ := ha
      _ = (_+_)+_ := congrArg₂ (fun a b : BDL26Field => a+b)
        (congrArg₂ (fun a b : BDL26Field => a+b) he hw) hd
      _ = (wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
          (directHubW S j outer)) edge+
          ((canonicalBasisWord (Sum.inl (oppositeErrorCopy S hh j outer,
              AHZ S j outer 0,⟨0,S.half_pos⟩)) : Word BDL26Field (QDoubleCylinderEdge (AP S) (AH S j outer) S)) edge+
           canonicalBasisWord (Sum.inl (chosenHubCopy S hh j outer,
              AHZ S j outer 0,⟨0,S.half_pos⟩)) edge) := by ac_rfl
      _ = (wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
          (directHubW S j outer)) edge+
          (wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
            (directHubK S j outer)) edge :=
        congrArg (fun a : BDL26Field =>
          (wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
            (directHubW S j outer)) edge+a) hk.symm
      _ = _ := hs.symm
  have ho (q : (AP S).Q) (hn : q≠AH S j outer) :
      rawQRead (AP S) (AA S) (AR S) S q
        (rxSigmaAfterCx (literalData (AP S) (AA S) (AR S) S) (counterTau S hh j outer).val)=0 := by
    funext edge
    let p := (Sum.inl (Sum.inr ⟨q,edge⟩) : RX2 (AP S) S)
    have ha := congrFun (counter_second_after_Cx_entire S hh j outer) p
    have he := congrFun (rawQRead_arm_other (AP S) (AA S) (AR S) S
      (AH S j outer) q hn (AHZ S j outer 0) (oppositeErrorCopy S hh j outer)) edge
    have hw := congrFun (rawQRead_Qextension_other (AP S) (AA S) (AR S) S
      (AH S j outer) q hn (directHubW S j outer)) edge
    have hd := congrFun (rawQRead_arm_other (AP S) (AA S) (AR S) S
      (AH S j outer) q hn (AHZ S j outer 0) (chosenHubCopy S hh j outer)) edge
    exact ha.trans ((congrArg₂ (fun a b : BDL26Field => a+b)
      (congrArg₂ (fun a b : BDL26Field => a+b) he hw) hd).trans
        ((congrArg (fun a : BDL26Field => a+0) (zero_add (0:BDL26Field))).trans (zero_add 0)))
  exact (Cq_from_one_Q_query (AP S) (AA S) (AR S) S
    (repair5_actual_to_literal S (counterTau S hh j outer)) (AH S j outer)
    (directHubW S j outer+directHubK S j outer) hq ho).trans
      (congrArg (directQExtension (AP S) (AA S) (AR S) S (AH S j outer))
        (directHub_original_values S hh j outer).2)

end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXLocalReplacement BDL26TannerLocalRegularity
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

private theorem directQExtension_at_same (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (v : QDoubleCylinderVertex P q S) :
    directQExtension P A R S q w (.inr ⟨q,v⟩)=w v :=
  qExtend_at_q P S q w v

private theorem directQExtension_at_other (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q r : P.Q) (hr : r≠q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (v : QDoubleCylinderVertex P r S) :
    directQExtension P A R S q w (.inr ⟨r,v⟩)=0 := qExtend_other P S q r hr w v

private theorem original_total_Q_chart (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (sigma : (BDL26DecoderData.family
      (literalDecoderData P A R S)).Cochain2 (Fin.succ (0 : StepIndex 1)))
    (q : P.Q) (v : QDoubleCylinderVertex P q S) :
    rxCorrectionTotal (literalData P A R S) sigma (.inr ⟨q,v⟩)=
      cqCorrectionTotal (literalData P A R S) sigma (.inr ⟨q,v⟩) := by
  have h := (CriticalOldXQueries.rxTotal_at_q P A R S sigma q).trans
    (CriticalOldXQueries.cqTotal_at_q P A R S sigma q).symm
  exact congrFun h (qCorrectionEquiv P S q v)

/-- At every actual Q vertex the physical edge and BOTH Cx totals vanish.
The remaining two Cq values are their original full chosen totals. -/
private theorem counter_updated_at_Q_vertex (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (q : (AP S).Q)
    (v : QDoubleCylinderVertex (AP S) q S) :
    updated S 3 (2 : StepIndex 3) (by decide)
      (counterA S hh j outer) (counterB S hh j outer)
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) (.inr ⟨q,v⟩))=
      cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (counterexampleInput S hh j outer).val (.inr ⟨q,v⟩)+
      cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (counterTau S hh j outer).val (.inr ⟨q,v⟩) := by
  let coord := rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) (Sum.inr ⟨q,v⟩)
  have hu := congrFun (counter_updated_literal S hh j outer) coord
  have hzraw := congrFun (CriticalOldXQueries.original_single_X_zero_at_Cq
    (AP S) (AA S) (AR S) S (AX S j outer)
    (xCorrectionEquiv (AP S) S (AX S j outer) (counterexamplePhysicalEdge S hh j outer)) q)
      (qCorrectionEquiv (AP S) S q v)
  have hz : (canonicalBasisWord (counterexamplePhysical S hh j outer) :
      Word BDL26Field (BDL26CSSHamiltonian.Physical S 3)) coord=0 :=
    (congrArg (fun p : BDL26CSSHamiltonian.Physical S 3 =>
      canonicalBasisWord (F:=BDL26Field) p coord)
        (counterexamplePhysical_eq_chart S hh j outer)).trans hzraw
  have hf := (congrFun (repair2C3Flip_basis S (counterexamplePhysical S hh j outer)) coord).trans hz
  have hs := original_total_Q_chart (AP S) (AA S) (AR S) S
    (counterexampleInput S hh j outer).val q v
  have ht := original_total_Q_chart (AP S) (AA S) (AR S) S
    (repair5_actual_to_literal S (counterTau S hh j outer)).val q v
  exact hu.trans ((congrArg₂ (fun a b : BDL26Field => a+b)
    (congrArg₂ (fun a b : BDL26Field => a+b) hf hs) ht).trans
      (congrArg (fun a : BDL26Field => a+
        cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (counterTau S hh j outer).val (Sum.inr ⟨q,v⟩)) (zero_add _)))

private theorem counter_first_Cq_leaf_terminal (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two)
    (z : QStarEdge (AP S) (AL S j outer i)) :
    cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (counterexampleInput S hh j outer).val
      (.inr ⟨AL S j outer i,(c,.inl (.inr z))⟩)=0 := by
  obtain ⟨k,v,hv,hq⟩ := counter_first_Cq_total S hh j outer
  let coord := (Sum.inr ⟨AL S j outer i,(c,Sum.inl (Sum.inr z))⟩ : RX1 (AP S) S)
  have he : cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (counterexampleInput S hh j outer).val coord=
      directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (directHubW S j outer) coord+
      directQExtension (AP S) (AA S) (AR S) S (AL S j outer k) v coord :=
    congrFun hq coord
  have hh0 := directQExtension_at_other (AP S) (AA S) (AR S) S
    (AH S j outer) (AL S j outer i) (AL_ne_hub S j outer i)
      (directHubW S j outer) (c,Sum.inl (Sum.inr z))
  have hv0 : directQExtension (AP S) (AA S) (AR S) S (AL S j outer k) v coord=0 := by
    by_cases hk : k=i
    · subst k
      exact (directQExtension_at_same (AP S) (AA S) (AR S) S
        (AL S j outer i) v (c,Sum.inl (Sum.inr z))).trans (hv c z)
    · have hn : AL S j outer i≠AL S j outer k := by
        intro hi
        have hinj : i=k := by
          fin_cases i <;> fin_cases k <;> first | rfl | cases hi
        exact hk hinj.symm
      exact directQExtension_at_other (AP S) (AA S) (AR S) S
        (AL S j outer k) (AL S j outer i) hn v (c,Sum.inl (Sum.inr z))
  exact he.trans ((congrArg₂ (fun a b : BDL26Field => a+b) hh0 hv0).trans (zero_add 0))

private theorem counter_second_Cq_leaf_terminal (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two)
    (z : QStarEdge (AP S) (AL S j outer i)) :
    cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (counterTau S hh j outer).val
      (.inr ⟨AL S j outer i,(c,.inl (.inr z))⟩)=0 := by
  let coord := (Sum.inr ⟨AL S j outer i,(c,Sum.inl (Sum.inr z))⟩ : RX1 (AP S) S)
  have he := congrFun (counter_second_Cq_total S hh j outer) coord
  exact he.trans (directQExtension_at_other (AP S) (AA S) (AR S) S
    (AH S j outer) (AL S j outer i) (AL_ne_hub S j outer i)
      (fun v => (directHubW S j outer+directHubK S j outer) v+1)
        (c,Sum.inl (Sum.inr z)))

private theorem counter_two_Cq_hub_terminal (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
    cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
        (counterexampleInput S hh j outer).val
        (.inr ⟨AH S j outer,(c,.inl (.inr (AHZ S j outer i)))⟩)+
      cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
        (counterTau S hh j outer).val
        (.inr ⟨AH S j outer,(c,.inl (.inr (AHZ S j outer i)))⟩)=
      (if i=0 then 1 else 0)+1 := by
  obtain ⟨k,v,hv,hq⟩ := counter_first_Cq_total S hh j outer
  let a : QDoubleCylinderVertex (AP S) (AH S j outer) S :=
    (c,Sum.inl (Sum.inr (AHZ S j outer i)))
  let coord := (Sum.inr ⟨AH S j outer,a⟩ : RX1 (AP S) S)
  have hfirst : cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (counterexampleInput S hh j outer).val coord=directHubW S j outer a := by
    have he : cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
        (counterexampleInput S hh j outer).val coord=
        directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (directHubW S j outer) coord+
        directQExtension (AP S) (AA S) (AR S) S (AL S j outer k) v coord :=
      congrFun hq coord
    exact he.trans ((congrArg₂ (fun a b : BDL26Field => a+b)
      (directQExtension_at_same (AP S) (AA S) (AR S) S (AH S j outer) (directHubW S j outer) a)
      (directQExtension_at_other (AP S) (AA S) (AR S) S (AL S j outer k) (AH S j outer)
        (Ne.symm (AL_ne_hub S j outer k)) v a)).trans (add_zero _))
  have hsecond : cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (counterTau S hh j outer).val coord=(directHubW S j outer+directHubK S j outer) a+1 :=
    (congrFun (counter_second_Cq_total S hh j outer) coord).trans
      (directQExtension_at_same (AP S) (AA S) (AR S) S (AH S j outer)
        (fun v => (directHubW S j outer+directHubK S j outer) v+1) a)
  have hbit : directHubK S j outer a=(if i=0 then 1 else 0) := by
    have hinj := AHZ_injective S j outer
    fin_cases i <;> rcases two_eq_zero_or_one c with hc | hc <;>
      simp [a,directHubK,CriticalOriginalChoice.terminalWord,basis_value,hinj.eq_iff,hc]
  calc
    _ = directHubW S j outer a+((directHubW S j outer a+directHubK S j outer a)+1) :=
      congrArg₂ (fun a b : BDL26Field => a+b) hfirst hsecond
    _ = (directHubW S j outer a+directHubW S j outer a)+(directHubK S j outer a+1) := by ac_rfl
    _ = directHubK S j outer a+1 := by rw [repair3_scalar_add_self,zero_add]
    _ = _ := congrArg (fun a : BDL26Field => a+1) hbit

/-- The ORIGINAL root-defined full lower word can be evaluated at any
terminal by the proved original Q-remainder constant theorem. -/
private theorem counter_lower_at_Q_terminal (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (q : (AP S).Q)
    (v : QDoubleCylinderVertex (AP S) q S) :
    (descent S 1 (counterexampleDomain S hh j outer)
        (counterexamplePhysical S hh j outer)).word q=
      updated S 3 (2 : StepIndex 3) (by decide)
          (counterA S hh j outer) (counterB S hh j outer)
          (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) (.inr ⟨q,v⟩))+
        (indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
          (accumulated S 1 (counterexampleDomain S hh j outer)
            (counterexamplePhysical S hh j outer))
          (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) (.inr ⟨q,v⟩)) := by
  rw [counter_descent_entire_L]
  have hl := BDL26RXPhysicalStarTransport.localized_blocks S 3 (2 : StepIndex 3)
    (by decide) (counterTop S hh j outer).center
    (counterA S hh j outer) (counterB S hh j outer)
    (counter_original_localized S hh j outer)
  have hr := BDL26RXFiniteBlockTransport.remainder_q_constant S 3 (2 : StepIndex 3)
    (by decide) (counterX0 S hh j outer)
    (BDL26RXXStarTransport.incidentQ S 3 (2 : StepIndex 3)
      (BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
        (counterTop S hh j outer).center)) q
    (counterA S hh j outer) (counterB S hh j outer) hl v
  rw [BDL26RXFiniteBlockTransport.R,Pi.add_apply,rxQVertexEquiv_val] at hr
  have hp := OriginalOneStepPhiBridge.accumulated_eq_original_Phi S
    (counterexampleDomain S hh j outer) (counterexamplePhysical S hh j outer)
  change accumulated S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)=
    BDL26RXFiniteBlockTransport.Phi S 3 (2 : StepIndex 3) (by decide)
      (counterX0 S hh j outer) (counterA S hh j outer) (counterB S hh j outer) at hp
  rw [← hp] at hr
  exact hr.symm

private theorem counter_lower_leaf_values (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    (descent S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)).word (AL S j outer i)=
      (if i=0 then 1 else 0)+counterBeta S hh j outer := by
  rw [counter_lower_at_Q_terminal S hh j outer (AL S j outer i)
    (0,.inl (.inr (ALZ S j outer i))),counter_updated_at_Q_vertex,
    counter_first_Cq_leaf_terminal,counter_second_Cq_leaf_terminal,zero_add,zero_add,
    counter_leaf_Phi_value]

private theorem counter_lower_hub_value (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (descent S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)).word (AH S j outer)=
      1+counterBeta S hh j outer := by
  rw [counter_lower_at_Q_terminal S hh j outer (AH S j outer)
    (0,.inl (.inr (AHZ S j outer 0))),counter_updated_at_Q_vertex,
    counter_two_Cq_hub_terminal,counter_hub_Phi_value]
  simp only [if_true]
  rw [CharTwo.add_self_eq_zero,zero_add]

end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

private theorem AL_injective (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Function.Injective (AL S j outer) := by
  intro i k h
  fin_cases i <;> fin_cases k <;> first | rfl | cases h

/-- This is an equality of the ENTIRE original localized descent word,
including all coordinates outside the four ports and the complete boundary
potential. It is derived from the actual single physical edge and direct
FIRST-zero background; no terminal occurrence or defect is an input. -/
private theorem counter_descent_complete_word (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (descent S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)).word=
      (canonicalBasisWord (AL S j outer 0)+canonicalBasisWord (AH S j outer))+
        tannerCoboundary0 (AP S)
          (counterBeta S hh j outer • canonicalBasisWord (AX S j outer)) := by
  funext q
  rw [Pi.add_apply,map_smul,Pi.smul_apply,tannerCoboundary0_canonicalBasis_apply]
  by_cases hq : (AP S).xq (AX S j outer) q=true
  · rw [if_pos hq,smul_eq_mul,mul_one]
    rcases actual_Q_cover S j outer q hq with hhq | ⟨i,hiq⟩
    · subst q
      rw [counter_lower_hub_value]
      simp [canonicalBasisWord,Pi.single_apply,AL_ne_hub]
    · subst q
      rw [counter_lower_leaf_values]
      have hinj := AL_injective S j outer
      fin_cases i <;> simp [canonicalBasisWord,Pi.single_apply,
        hinj.eq_iff,AL_ne_hub,fun i => Ne.symm (AL_ne_hub S j outer i),eq_comm]
  · rw [if_neg hq,smul_zero]
    have hleaf (i : Fin 3) : q≠AL S j outer i := by
      intro he
      exact hq (he ▸ AL_incident S j outer i)
    have hhub : q≠AH S j outer := by
      intro he
      exact hq (he ▸ AH_incident S j outer)
    have hz : (descent S 1 (counterexampleDomain S hh j outer)
        (counterexamplePhysical S hh j outer)).word q=0 := by
      by_contra hn
      have hs : q∈hammingSupport (descent S 1 (counterexampleDomain S hh j outer)
          (counterexamplePhysical S hh j outer)).word := by
        simpa [hammingSupport] using hn
      have hmem := counter_descent_supported S hh j outer hs
      simpa [hleaf 0,hleaf 1,hleaf 2,hhub] using hmem
    rw [hz]
    simp [canonicalBasisWord,Pi.single_apply,hleaf 0,hhub]

end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

end OriginalCounterexampleWorking

/- The complete localized descent identity is lifted through the original two base decodes and full history to the actual logical coefficient. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph BDL26LevelTwoCode
open BDL26ActualFailureReadout BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26OwnerIncidenceMasks
open BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open scoped Classical
noncomputable section

private theorem rawTwo_actual_delta0 (S : OddScale) :
    (tannerCoboundary0 (state S 2).presentation :
      Word F (RawTwo S).X →ₗ[F] Word F (RawTwo S).Q)=tannerCoboundary0 (RawTwo S) :=
  eq_of_heq (differential0_heq
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))

private theorem rawTwo_actual_delta1 (S : OddScale) :
    (tannerCoboundary1 (state S 2).presentation :
      Word F (RawTwo S).Q →ₗ[F] Word F (RawTwo S).Z)=tannerCoboundary1 (RawTwo S) := by
  have transport {T U : TannerSquarePresentation} (h : T=U) :
      HEq (tannerCoboundary1 T) (tannerCoboundary1 U) := by
    cases h
    exact HEq.rfl
  exact eq_of_heq (transport
    (congrArg ConstructionState.presentation (levelTwoState_eq_pair S)))

private theorem counterexample_chi_one_of_descent_word (S : OddScale)
    (hh : S.half=1) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (p : Word F (RawTwo S).X)
    (hword : (descent S 1 (counterexampleDomain S hh j outer)
        (counterexamplePhysical S hh j outer)).word=
      ActualCriticalStarGeometry.pairWord S j outer+tannerCoboundary0 (RawTwo S) p) :
    BDL26LogicalDefectProtection.chiX S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)=1 := by
  let u := counterexampleDomain S hh j outer
  let q := counterexamplePhysical S hh j outer
  let h := ActualCriticalStarGeometry.pairWord S j outer+tannerCoboundary0 (RawTwo S) p
  let residual := h+(fun q : (RawTwo S).Q => (BDL26LevelTwoDecoder.decode S 0) q)+
    (fun q : (RawTwo S).Q => (BDL26LevelTwoDecoder.decode S (tannerCoboundary1 (RawTwo S) h)) q)
  have hf : firstReadout S 1 u=0 := counterexample_actual_FIRST_zero S hh j outer
  have hs : tannerCoboundary1 (RawTwo S) h=secondReadout S 1 u q := by
    have hi := descent_syndrome S 1 u q
    rw [suffix_delta1] at hi
    change tannerCoboundary1 (state S 2).presentation (descent S 1 u q).word=
      firstReadout S 1 u+secondReadout S 1 u q at hi
    rw [rawTwo_actual_delta1,hword,hf,zero_add] at hi
    exact hi
  have hv : residual=(descent S 1 u q).word+
      (actualBase S 1).decode (actualInputs S 1 (input S 1 u) 0)+
      (actualBase S 1).decode
        (actualInputs S 1 (perturbTop S 1 (input S 1 u) (flip S 1 q)) 0) := by
    rw [hword,first_base_original_D,second_base_original_D,hf,← hs]
    rfl
  have hr := ActualCriticalStarGeometry.pair_plus_boundary_full_original_residual S j outer p
  apply BDL26ActualLocalizedResidualLift.actual_chi_one_of_localized_closed_not_boundary
    S 1 u q residual hv
  · rw [rawTwo_actual_delta1]
    exact hr.1
  · rintro ⟨a,ha⟩
    apply hr.2.2
    refine ⟨a,?_⟩
    rw [← rawTwo_actual_delta0]
    exact ha

end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/- Finite half-scale-one old-X obstruction for the original selector model. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace DirectOldXCounterexample
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph BDL26LevelTwoCode
open BDL26ActualFailureReadout BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26RZMap1CoordinateBridge BDL26RXPhysicalCoordinateTrace
open scoped Classical
noncomputable section

/-- Same legal original input, same one physical old-X edge, original FIRST,
entire original accumulated Phi, and BOTH unchanged original D calls. The
conclusion is finite half-scale one (ell=3); it says nothing about the paper's
sufficiently-large-ell hypothesis. -/
private theorem counterexample_actual_chi_one (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26LogicalDefectProtection.chiX S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)=1 := by
  let p : Word F (RawTwo S).X :=
    counterBeta S hh j outer • canonicalBasisWord (AX S j outer)
  have hw : (descent S 1 (counterexampleDomain S hh j outer)
      (counterexamplePhysical S hh j outer)).word=
      ActualCriticalStarGeometry.pairWord S j outer+tannerCoboundary0 (RawTwo S) p := by
    rw [← rawTwo_actual_delta0]
    exact counter_descent_complete_word S hh j outer
  exact counterexample_chi_one_of_descent_word S hh j outer p hw

/-- The witness edge belongs to the ORIGINAL physical old-X chart; neither
an arbitrary terminal pair nor a freely supplied coarse error is a witness.
The background's original validity witness is carried by XSyndromeDomain. -/
private theorem actual_single_oldX_first_zero_chi_one (S : OddScale) (hh : S.half=1)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    ∃ u : XSyndromeDomain S 1,
      ∃ edge : DoubleCylinderEdge (state S 2).presentation
        (oldXOwner S 1 (by decide) (seedQNode S j) outer) S,
      parse S 1 (oldXPhysical S 1 (by decide) (seedQNode S j) outer edge)=
        Leaf.primitive (Primitive.oldX 1 (by decide) (seedQNode S j) outer edge) ∧
      firstReadout S 1 u=0 ∧
        BDL26LogicalDefectProtection.chiX S 1 u
          (oldXPhysical S 1 (by decide) (seedQNode S j) outer edge)=1 := by
  refine ⟨counterexampleDomain S hh j outer,counterexamplePhysicalEdge S hh j outer,
    ?_,counterexample_actual_FIRST_zero S hh j outer,?_⟩
  · exact parse_oldX_exact S
      ⟨seedQNode S j,outer,counterexamplePhysicalEdge S hh j outer⟩
  · exact counterexample_actual_chi_one S hh j outer

/-- An explicit admissible ell-three counterexample to an unrestricted allOdd
zero-defect endpoint for the CURRENT original selector model. This is not a
counterexample to a theorem restricted to sufficiently large scales. -/
private theorem exists_ell_three_single_physical_first_zero_chi_one :
    ∃ S : OddScale,S.ell=3 ∧
      ∃ u : XSyndromeDomain S 1,
      ∃ edge : DoubleCylinderEdge (state S 2).presentation
          (oldXOwner S 1 (by decide) (seedQNode S 0) 0) S,
        parse S 1 (oldXPhysical S 1 (by decide) (seedQNode S 0) 0 edge)=
          Leaf.primitive (Primitive.oldX 1 (by decide) (seedQNode S 0) 0 edge) ∧
        firstReadout S 1 u=0 ∧
          BDL26LogicalDefectProtection.chiX S 1 u
            (oldXPhysical S 1 (by decide) (seedQNode S 0) 0 edge)=1 := by
  let S : OddScale := ⟨3,by decide,by decide⟩
  have hh : S.half=1 := by decide
  obtain ⟨u,edge,hparse,hf,hchi⟩ := actual_single_oldX_first_zero_chi_one S hh 0 0
  exact ⟨S,rfl,u,edge,hparse,hf,hchi⟩

end
end DirectOldXCounterexample
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RXPhysicalCoordinateTrace
open scoped Classical

/-- At half-scale one the original selector has a legal background and one
physical old-X edge with its exact original parser class, FIRST readout zero,
and actual logical defect one. Both readouts refer to the same background
and physical edge. The owner is quantified so this interface contains no
private coordinate name. -/
theorem exists_original_oldX_first_zero_chi_one (S : OddScale) (hh : S.half=1) :
    ∃ x : (state S 1).presentation.X,
      ∃ outer : BDL26FiniteTannerSquare.Two,
      ∃ u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1,
      ∃ edge : DoubleCylinderEdge (state S 2).presentation
          (oldXOwner S 1 (by decide) x outer) S,
        parse S 1 (oldXPhysical S 1 (by decide) x outer edge)=
          Leaf.primitive (Primitive.oldX 1 (by decide) x outer edge) ∧
        firstReadout S 1 u=0 ∧
          BDL26LogicalDefectProtection.chiX S 1 u
            (oldXPhysical S 1 (by decide) x outer edge)=1 := by
  obtain ⟨u,edge,hparse,hfirst,hchi⟩ :=
    DirectOldXCounterexample.actual_single_oldX_first_zero_chi_one S hh 0 0
  exact ⟨seedQNode S 0,0,u,edge,hparse,hfirst,hchi⟩

end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/-! Original-carrier cross-scale proof closure for every admissible odd scale.
The finite endpoint above remains a separate specialization. This closure
retains the complete original histories and both original base decoder calls. -/
namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open BDL26TransposedStoppedDecoder BDL26ActualFailureReadout
open scoped Classical BigOperators
noncomputable section

/-- A tail on one actual subdivided Q ray, including its original terminal.
The cut is an arbitrary actual segment, not an assumed first segment. -/
private def rayTail (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  fun v => if v.1=copy then
    match v.2 with
    | .inl (.inl _) => 0
    | .inl (.inr t) => if t=z then 1 else 0
    | .inr (t,j) => if t=z ∧ cut.val ≤ j.val then 1 else 0
  else 0

/-- Constant on a genuine end copy; the original terminal glue is retained. -/
private def wholeCopy (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) : Word BDL26Field (QDoubleCylinderVertex P q S) :=
  fun v => if v.1=copy then 1 else 0

private def rayCut (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half) :
    QDoubleCylinderEdge P q S := .inl (copy,z,cut)

private theorem threshold_difference (cut index : Nat) :
    (if cut < index then (1:BDL26Field) else 0)+
      (if cut ≤ index then 1 else 0)=(if index=cut then 1 else 0) := by
  have hone : (1:BDL26Field)+1=0 := repair3_scalar_add_self 1
  by_cases hlt : cut < index
  · have hle : cut ≤ index := Nat.le_of_lt hlt
    have hne : index≠cut := by omega
    simp [hlt,hle,hne,hone]
  · by_cases he : index=cut
    · subst index
      simp
    · have hle : ¬ cut ≤ index := by omega
      simp [hlt,hle,he]

private theorem rayTail_center (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy d : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half) :
    rayTail P q S copy z cut (d,.inl (.inl ()))=0 := by
  simp [rayTail]

private theorem rayTail_terminal (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy d : BDL26FiniteTannerSquare.Two) (z t : QStarEdge P q) (cut : Fin S.half) :
    rayTail P q S copy z cut (d,.inl (.inr t))=
      if d=copy ∧ t=z then 1 else 0 := by
  by_cases hd : d=copy <;> by_cases ht : t=z <;> simp [rayTail,hd,ht]

private theorem rayTail_at_start (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy d : BDL26FiniteTannerSquare.Two) (z t : QStarEdge P q)
    (cut index : Fin S.half) :
    rayTail P q S copy z cut (d,qSubdivisionEdgeStart P q S (t,index))=
      if d=copy ∧ t=z ∧ cut.val < index.val then 1 else 0 := by
  by_cases hi : index.val=0
  · by_cases hd : d=copy <;> by_cases ht : t=z
    all_goals simp [qSubdivisionEdgeStart,hi,qStarEdgeStart,rayTail,hd,ht]
  · have hiff : cut.val ≤ index.val-1 ↔ cut.val < index.val := by omega
    by_cases hd : d=copy <;> by_cases ht : t=z
    all_goals simp [qSubdivisionEdgeStart,hi,rayTail,hiff,hd,ht]

private theorem rayTail_at_end (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy d : BDL26FiniteTannerSquare.Two) (z t : QStarEdge P q)
    (cut index : Fin S.half) :
    rayTail P q S copy z cut (d,qSubdivisionEdgeEnd P q S (t,index))=
      if d=copy ∧ t=z ∧ cut.val ≤ index.val then 1 else 0 := by
  by_cases hi : index.val+1=S.half
  · have hc : cut.val ≤ index.val := by have := cut.isLt;omega
    by_cases hd : d=copy <;> by_cases ht : t=z
    all_goals simp [qSubdivisionEdgeEnd,hi,qStarEdgeEnd,rayTail,hc,hd,ht]
  · by_cases hd : d=copy <;> by_cases ht : t=z
    all_goals simp [qSubdivisionEdgeEnd,hi,rayTail,hd,ht]


/-- The original Q-local gradient has one chosen cut and the actual glue edge. -/
private theorem rayTail_delta (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (rayTail P q S copy z cut)=
      canonicalBasisWord (F:=BDL26Field) (rayCut P q S copy z cut)+
        canonicalBasisWord (F:=BDL26Field) (Sum.inr z) := by
  funext edge
  rw [qLocalCoboundary_apply]
  rcases edge with ⟨d,t,index⟩ | t
  · change rayTail P q S copy z cut (d,qSubdivisionEdgeStart P q S (t,index))+
        rayTail P q S copy z cut (d,qSubdivisionEdgeEnd P q S (t,index))=_
    rw [rayTail_at_start,rayTail_at_end]
    by_cases hd : d=copy
    · subst d
      by_cases ht : t=z
      · subst t
        simpa [rayCut,basis_value,Prod.mk.injEq,Fin.ext_iff] using
          threshold_difference cut.val index.val
      · simp [ht,rayCut,basis_value,Prod.mk.injEq]
    · simp [hd,rayCut,basis_value,Prod.mk.injEq]
  · fin_cases copy
    all_goals simp [qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd,qStarEdgeEnd,
      rayTail,rayCut,basis_value]

private theorem rayTail_delta_arm (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy d : BDL26FiniteTannerSquare.Two) (z t : QStarEdge P q)
    (cut index : Fin S.half) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (rayTail P q S copy z cut) (rayCut P q S d t index)=
      canonicalBasisWord (F:=BDL26Field) (rayCut P q S copy z cut)
        (rayCut P q S d t index) := by
  rw [rayTail_delta,Pi.add_apply]
  simp [rayCut,basis_value]

private theorem rayTail_delta_glue (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy : BDL26FiniteTannerSquare.Two) (z t : QStarEdge P q) (cut : Fin S.half) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (rayTail P q S copy z cut) (Sum.inr t)=
      if t=z then 1 else 0 := by
  rw [rayTail_delta,Pi.add_apply]
  simp [rayCut,basis_value]

private theorem wholeCopy_delta_arm (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy d : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (index : Fin S.half) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (wholeCopy P q S copy) (rayCut P q S d z index)=0 := by
  rw [qLocalCoboundary_apply]
  change ((if d=copy then (1 : BDL26Field) else 0)+
    (if d=copy then (1 : BDL26Field) else 0))=0
  exact repair3_scalar_add_self _

private theorem wholeCopy_delta_glue (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (wholeCopy P q S copy) (Sum.inr z)=1 := by
  rw [qLocalCoboundary_apply]
  fin_cases copy
  all_goals simp [wholeCopy,qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd]

private def toggleWord (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (a : QStarEdge P q) (cut0 cut1 : Fin S.half) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  rayTail P q S 0 a cut0+rayTail P q S 1 a cut1

private def switchWord (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (a b c : QStarEdge P q) (cut0 : Fin S.half) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  wholeCopy P q S 0+rayTail P q S 0 a cut0+
    rayTail P q S 0 c ⟨0,S.half_pos⟩+rayTail P q S 1 b ⟨0,S.half_pos⟩

private theorem toggleWord_delta (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (a : QStarEdge P q) (cut0 cut1 : Fin S.half) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (toggleWord P q S a cut0 cut1)=
      canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 a cut0)+
        canonicalBasisWord (F:=BDL26Field) (rayCut P q S 1 a cut1) := by
  rw [toggleWord,map_add,rayTail_delta,rayTail_delta]
  have hg := repair3_word_add_self
    (canonicalBasisWord (F:=BDL26Field) (Sum.inr a) :
      Word BDL26Field (QDoubleCylinderEdge P q S))
  calc
    _=(canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 a cut0)+
       canonicalBasisWord (F:=BDL26Field) (rayCut P q S 1 a cut1))+
      (canonicalBasisWord (F:=BDL26Field) (Sum.inr a)+
       canonicalBasisWord (F:=BDL26Field) (Sum.inr a)) := by abel
    _=_ := by rw [hg,add_zero]

private theorem switchWord_delta (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (a b c : QStarEdge P q)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (cover : ∀ z : QStarEdge P q,z=a ∨ z=b ∨ z=c) (cut0 : Fin S.half) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (switchWord P q S a b c cut0)=
      (canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 a cut0)+
       canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 c ⟨0,S.half_pos⟩))+
        canonicalBasisWord (F:=BDL26Field) (rayCut P q S 1 b ⟨0,S.half_pos⟩) := by
  unfold switchWord
  rw [map_add,map_add,map_add]
  funext edge
  rcases edge with ⟨d,z,index⟩ | z
  · simp only [Pi.add_apply]
    have h0 := wholeCopy_delta_arm P q S 0 d z index
    have h1 := rayTail_delta_arm P q S 0 d a z cut0 index
    have h2 := rayTail_delta_arm P q S 0 d c z ⟨0,S.half_pos⟩ index
    have h3 := rayTail_delta_arm P q S 1 d b z ⟨0,S.half_pos⟩ index
    dsimp only [rayCut] at h0 h1 h2 h3
    dsimp only [rayCut]
    rw [h0,h1,h2,h3,zero_add]
  · simp only [Pi.add_apply]
    rw [wholeCopy_delta_glue,rayTail_delta_glue,rayTail_delta_glue,rayTail_delta_glue]
    rcases cover z with rfl | rfl | rfl
    all_goals simp [rayCut,basis_value,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc,CharTwo.add_self_eq_zero]

private theorem switch_toggle_delta (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (a b c : QStarEdge P q)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (cover : ∀ z : QStarEdge P q,z=a ∨ z=b ∨ z=c)
    (cut0 cut1 : Fin S.half) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1)=
      (canonicalBasisWord (F:=BDL26Field) (rayCut P q S 1 a cut1)+
       canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 c ⟨0,S.half_pos⟩))+
        canonicalBasisWord (F:=BDL26Field) (rayCut P q S 1 b ⟨0,S.half_pos⟩) := by
  rw [map_add,switchWord_delta P q S a b c hab hac hbc cover,toggleWord_delta]
  have hs := repair3_word_add_self
    (canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 a cut0) :
      Word BDL26Field (QDoubleCylinderEdge P q S))
  calc
    _=(canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 a cut0)+
       canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 a cut0))+
      ((canonicalBasisWord (F:=BDL26Field) (rayCut P q S 1 a cut1)+
        canonicalBasisWord (F:=BDL26Field) (rayCut P q S 0 c ⟨0,S.half_pos⟩))+
        canonicalBasisWord (F:=BDL26Field) (rayCut P q S 1 b ⟨0,S.half_pos⟩)) := by abel
    _=_ := by rw [hs,zero_add]

private theorem three_basis_weight_le {I : Type} [Fintype I] [DecidableEq I]
    (a b c : I) :
    HammingWeight ((canonicalBasisWord (F:=BDL26Field) a+
      canonicalBasisWord (F:=BDL26Field) b)+canonicalBasisWord (F:=BDL26Field) c) ≤ 3 := by
  have hs : hammingSupport ((canonicalBasisWord (F:=BDL26Field) a+
      canonicalBasisWord (F:=BDL26Field) b)+canonicalBasisWord (F:=BDL26Field) c)⊆{a,b,c} := by
    intro i hi
    by_contra hn
    have ha : i≠a := by intro h;apply hn;simp [h]
    have hb : i≠b := by intro h;apply hn;simp [h]
    have hc : i≠c := by intro h;apply hn;simp [h]
    have hv : ((canonicalBasisWord (F:=BDL26Field) a+
        canonicalBasisWord (F:=BDL26Field) b)+canonicalBasisWord (F:=BDL26Field) c) i≠0 := by
      simpa [hammingSupport] using hi
    simp [basis_value,ha,hb,hc] at hv
  exact (Finset.card_le_card hs).trans (CriticalOriginalChoice.card_triple_le_three a b c)

/-- These are the ACTUAL outgoing terminal weights, not raw mask sizes. -/
private theorem switch_terminal_costs (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (a b c : QStarEdge P q)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (cover : ∀ z : QStarEdge P q,z=a ∨ z=b ∨ z=c)
    (cut0 cut1 : Fin S.half) :
    (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S
      (switchWord P q S a b c cut0)))=2 ∧
    (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S
      (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1)))=4 := by
  constructor
  all_goals erw [CriticalOriginalChoice.sum_three_leaves a b c hab hac hbc cover]
  all_goals simp_rw [CriticalOriginalChoice.hamming_weight_two]
  all_goals simp [switchWord,toggleWord,wholeCopy,rayTail,
    rxQZDegreeOne,wordPullback_apply,hab,hac,hbc,
    Ne.symm hab,Ne.symm hac,Ne.symm hbc,CharTwo.add_self_eq_zero]

/-- A true constant-switch theorem for the unchanged ORIGINAL Cq selector,
with arbitrary actual cut positions at every odd scale. -/
private theorem original_switch_words (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (hd : Fintype.card (QStarEdge P q)=3)
    (a b c : QStarEdge P q) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (cover : ∀ z : QStarEdge P q,z=a ∨ z=b ∨ z=c)
    (cut0 cut1 : Fin S.half) :
    CriticalOriginalChoice.originalChoice P A R S q (switchWord P q S a b c cut0)=
      switchWord P q S a b c cut0 ∧
    CriticalOriginalChoice.originalChoice P A R S q
      (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1)=
      fun v => (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1) v+1 := by
  have ht := switch_terminal_costs P q S a b c hab hac hbc cover cut0 cut1
  have hw : HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (switchWord P q S a b c cut0)) ≤ 3 := by
    rw [switchWord_delta P q S a b c hab hac hbc cover]
    exact three_basis_weight_le _ _ _
  have hk : HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1)) ≤ 3 := by
    rw [switch_toggle_delta P q S a b c hab hac hbc cover]
    exact three_basis_weight_le _ _ _
  constructor
  · exact CriticalOriginalChoice.originalChoice_forced_cost_two_degree_three
      P A R S q hd _ ht.1 hw
  · have hc := qLocal_terminal_weight_complement P q S
      (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1)
    have hcomp : (∑ z : QStarEdge P q,HammingWeight (rxQZDegreeOne P q z.val z.property S
        (fun v => (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1) v+1)))=2 := by
      erw [ht.2,hd] at hc
      omega
    have hbound : HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun v => (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1) v+1)) ≤ 3 := by
      rw [qLocalCoboundary_add_constant]
      exact hk
    calc
      _=CriticalOriginalChoice.originalChoice P A R S q
          (fun v => (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1) v+1) :=
        (CriticalOriginalChoice.originalChoice_add_constant P A R S q
          (switchWord P q S a b c cut0+toggleWord P q S a cut0 cut1) 1).symm
      _=_ := CriticalOriginalChoice.originalChoice_forced_cost_two_degree_three
        P A R S q hd _ hcomp hbound

end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter
open scoped Classical BigOperators
noncomputable section

private theorem binary_path_sum (f : Nat → BDL26Field) (n : Nat) :
    (∑ i : Fin n,(f i.val+f (i.val+1)))=f 0+f n := by
  induction n with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin n,(f i.val+f (i.val+1)))+(f n+f (n+1))=f 0+f (n+1)
    rw [ih]
    calc
      _=f 0+(f n+f n)+f (n+1) := by abel
      _=_ := by rw [repair3_scalar_add_self,add_zero]

private def armValue (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (i : Nat) : BDL26Field :=
  if hi : i < S.half then w (copy,qSubdivisionEdgeStart P q S (z,⟨i,hi⟩))
  else w (copy,.inl (.inr z))

private theorem armValue_zero (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    armValue P q S w copy z 0=w (copy,.inl (.inl ())) := by
  simp [armValue,S.half_pos,qSubdivisionEdgeStart,qStarEdgeStart]

private theorem armValue_last (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    armValue P q S w copy z S.half=w (copy,.inl (.inr z)) := by
  simp [armValue]

private theorem armValue_step (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (i : Fin S.half) :
    armValue P q S w copy z (i.val+1)=w (copy,qSubdivisionEdgeEnd P q S (z,i)) := by
  by_cases hi : i.val+1 < S.half
  · have hl : i.val+1≠S.half := by omega
    have hz : i.val+1≠0 := by omega
    simp [armValue,hi,qSubdivisionEdgeStart,qSubdivisionEdgeEnd,hl,hz]
  · have hl : i.val+1=S.half := by have := i.isLt;omega
    simp [armValue,hi,qSubdivisionEdgeEnd,hl,qStarEdgeEnd]

/-- Telescope along ALL actual segments of one original Q ray. -/
private theorem q_ray_coboundary_sum (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) :
    (∑ k : Fin S.half,wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w
      (rayCut P q S copy z k))=w (copy,.inl (.inl ()))+w (copy,.inl (.inr z)) := by
  calc
    _=(∑ k : Fin S.half,(armValue P q S w copy z k.val+
        armValue P q S w copy z (k.val+1))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [qLocalCoboundary_apply,armValue_step]
      simp [armValue,k.isLt,rayCut,qDoubleCylinderEdgeStart,qDoubleCylinderEdgeEnd]
    _=armValue P q S w copy z 0+armValue P q S w copy z S.half := binary_path_sum _ _
    _=_ := by rw [armValue_zero,armValue_last]

/-- Original Q-subdivision vertices retain actual X-boundary subtype labels. -/
private def qBoundaryVertex (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q=true) (S : OddScale)
    (v : QSubdivisionVertex P q S) : SubdivisionBoundaryVertex P x S := by
  refine ⟨qToXSubdivisionVertex P A q x hxq S v,?_⟩
  rcases v with v | ⟨z,k⟩
  · simpa [qToXSubdivisionVertex,subdivisionBoundaryVertexMember,
      xStarBoundaryVertexToStar] using (qToXBoundaryVertex P A q x hxq v).property
  · simpa [qToXSubdivisionVertex,subdivisionBoundaryVertexMember,
      xStarBoundaryEdgeToStar] using (qToXBoundaryEdge P q x hxq z).property

private theorem qBoundaryVertex_start (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q=true) (S : OddScale) (z : QStarEdge P q) (k : Fin S.half) :
    qBoundaryVertex P A q x hxq S (qSubdivisionEdgeStart P q S (z,k))=
      subdivisionBoundaryEdgeStart P x S (qToXSubdivisionBoundaryEdge P q x hxq S (z,k)) := by
  apply Subtype.ext
  change qToXSubdivisionVertex P A q x hxq S (qSubdivisionEdgeStart P q S (z,k))=_
  rw [subdivisionBoundaryEdgeStart_value]
  exact qToXSubdivisionEdge_start P A q x hxq S (z,k)

private theorem qBoundaryVertex_end (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q=true) (S : OddScale) (z : QStarEdge P q) (k : Fin S.half) :
    qBoundaryVertex P A q x hxq S (qSubdivisionEdgeEnd P q S (z,k))=
      subdivisionBoundaryEdgeEnd P x S (qToXSubdivisionBoundaryEdge P q x hxq S (z,k)) := by
  apply Subtype.ext
  change qToXSubdivisionVertex P A q x hxq S (qSubdivisionEdgeEnd P q S (z,k))=_
  rw [subdivisionBoundaryEdgeEnd_value]
  exact qToXSubdivisionEdge_end P A q x hxq S (z,k)

private theorem qBoundaryVertex_terminal (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q=true) (S : OddScale) (z : QStarEdge P q) :
    (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inr z))) : DoubleCylinderEdge P x S)=
      qToXDoubleCylinderEdge P A q x hxq S (Sum.inr z) := by
  apply congrArg Sum.inr
  apply Subtype.ext
  rfl

private def rayImage (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (z : QStarEdge P q) (copy : BDL26FiniteTannerSquare.Two) (k : Fin S.half) : RX2 P S :=
  .inl (.inr ⟨q,rayCut P q S copy z k⟩)

private def rayFlowSum (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (q : P.Q) (z : QStarEdge P q) : BDL26Field :=
  ∑ copy : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,xFlow P S x f (rayImage P q S z copy k)

private theorem rayImage_value (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (z : QStarEdge P q) (copy : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    xFlow P S x f (rayImage P q S z copy k)=
      f (Sum.inl (copy,(qToXSubdivisionBoundaryEdge P q x hxq S (z,k)).val)) := by
  unfold rayImage rayCut
  rw [xFlow_at_q P A]
  simp only [dif_pos hxq,rxXQDegreeOne,wordPullback_apply]
  rfl

/-- This is readback of the actual vertical coordinates of f, not an
independently chosen potential or a new graph. -/
private def verticalReadback (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) :
    Word BDL26Field (QDoubleCylinderVertex P q S) :=
  fun v => f (Sum.inr (qBoundaryVertex P A q x hxq S v.2))

private theorem rectangle_ray_step (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (z : QStarEdge P q) (k : Fin S.half) :
    doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z,k)))=
      (xFlow P S x f (rayImage P q S z 0 k)+xFlow P S x f (rayImage P q S z 1 k))+
        wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
          (verticalReadback P A S x q hxq f) (rayCut P q S 0 z k) := by
  rw [original_rectangle_coboundary,rayImage_value P A,rayImage_value P A,
    qLocalCoboundary_apply]
  change _=(_+_)+(f (Sum.inr (qBoundaryVertex P A q x hxq S
      (qSubdivisionEdgeStart P q S (z,k))))+
    f (Sum.inr (qBoundaryVertex P A q x hxq S (qSubdivisionEdgeEnd P q S (z,k)))))
  rw [qBoundaryVertex_start,qBoundaryVertex_end]

/-- The shared-center term is RETAINED on each complete actual ray. -/
private theorem rectangle_ray_sum (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) (z : QStarEdge P q) :
    (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
      (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z,k))))=
      rayFlowSum P S x f q z+
        (f (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inl ()))))+
          f (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inr z))))) := by
  calc
    _=((∑ k : Fin S.half,xFlow P S x f (rayImage P q S z 0 k))+
        (∑ k : Fin S.half,xFlow P S x f (rayImage P q S z 1 k)))+
      (∑ k : Fin S.half,wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (verticalReadback P A S x q hxq f) (rayCut P q S 0 z k)) := by
      simp_rw [rectangle_ray_step P A S x q hxq f]
      simp only [Finset.sum_add_distrib]
    _=_ := by
      rw [q_ray_coboundary_sum]
      simp only [rayFlowSum,Fin.sum_univ_two,verticalReadback]

/-- Only after pairing complete rays is the common center canceled. -/
private theorem rectangle_ray_pair (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (q : P.Q) (hxq : P.xq x q=true)
    (f : Word BDL26Field (DoubleCylinderEdge P x S)) (z t : QStarEdge P q)
    (hz : f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr z))=0)
    (ht : f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr t))=0) :
    (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
      (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z,k))))+
    (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
      (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (t,k))))=
      rayFlowSum P S x f q z+rayFlowSum P S x f q t := by
  rw [rectangle_ray_sum P A S x q hxq f z,rectangle_ray_sum P A S x q hxq f t,
    qBoundaryVertex_terminal,qBoundaryVertex_terminal,hz,ht]
  simp only [add_zero]
  calc
    _=(rayFlowSum P S x f q z+rayFlowSum P S x f q t)+
      (f (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inl ()))))+
       f (Sum.inr (qBoundaryVertex P A q x hxq S (.inl (.inl ()))))) := by abel
    _=_ := by rw [repair3_scalar_add_self,add_zero]

private theorem rayImage_injective (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z) :
    Function.Injective (fun p : Fin 3 × BDL26FiniteTannerSquare.Two × Fin S.half =>
      rayImage P q S (z p.1) p.2.1 p.2.2) := by
  rintro ⟨i,c,k⟩ ⟨j,d,l⟩ h
  have hq := Sum.inr.inj (Sum.inl.inj h)
  have he := sigma_same_index_inj (I:=P.Q)
    (A:=fun r => QDoubleCylinderEdge P r S) (i:=q)
    (rayCut P q S c (z i) k) (rayCut P q S d (z j) l) hq
  change (rayCut P q S c (z i) k)=(rayCut P q S d (z j) l) at he
  have hp := Sum.inl.inj he
  have hc : c=d := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  have hi : i=j := hz (congrArg Prod.fst hr)
  have hk : k=l := congrArg Prod.snd hr
  exact Prod.ext hi (Prod.ext hc hk)

private theorem two_ray_parities_force_actual_cut
    {I : Type} [Fintype I] [DecidableEq I] (S : OddScale)
    (w : Word BDL26Field I) (hw : HammingWeight w ≤ 1)
    (e : Fin 3 × BDL26FiniteTannerSquare.Two × Fin S.half → I) (hinj : Function.Injective e)
    (h02 : (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (0,c,k)))+
      (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (2,c,k)))=1)
    (h12 : (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (1,c,k)))+
      (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (2,c,k)))=0) :
    ∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,w=canonicalBasisWord (F:=BDL26Field) (e (0,c,k)) := by
  rcases flow_weight_le_one_word w hw with hzero | ⟨a,ha⟩
  · simp only [hzero,Pi.zero_apply,Finset.sum_const_zero,zero_add] at h02
    exact False.elim (zero_ne_one h02)
  subst w
  have hex : ∃ i : Fin 3,∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,a=e (i,c,k) := by
    by_contra hn
    have hval (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
        canonicalBasisWord (F:=BDL26Field) a (e (i,c,k))=0 := by
      have hne : e (i,c,k)≠a := by intro h;exact hn ⟨i,c,k,h.symm⟩
      simp [basis_value,hne]
    simp [hval] at h02
  obtain ⟨i,c,k,hi⟩ := hex
  subst a
  have hsum (j : Fin 3) :
      (∑ d : BDL26FiniteTannerSquare.Two,∑ l : Fin S.half,
        canonicalBasisWord (F:=BDL26Field) (e (i,c,k)) (e (j,d,l)))=
        if j=i then 1 else 0 := by
    have hinner (d : BDL26FiniteTannerSquare.Two) :
        (∑ l : Fin S.half,canonicalBasisWord (F:=BDL26Field) (e (i,c,k)) (e (j,d,l)))=
          if j=i ∧ d=c then 1 else 0 := by
      rw [Fintype.sum_eq_single k]
      · simp [basis_value,hinj.eq_iff,Prod.mk.injEq]
      · intro l hl
        simp [basis_value,hinj.eq_iff,Prod.mk.injEq,hl]
    rw [Fin.sum_univ_two,hinner,hinner]
    by_cases hji : j=i <;> fin_cases c <;> simp [hji]
  rw [hsum,hsum] at h02 h12
  fin_cases i
  · exact ⟨c,k,rfl⟩
  · simp at h02
  · simp at h12

/-- The original whole xFlow budget is applied only after the COMPLETE ray
rectangle equations, including the shared-center cancellation. -/
private theorem actual_Cx_hub_ray_exit
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f) ≤ 1)
    (h02 : (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z 0,k))))+
      (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z 2,k))))=1)
    (h12 : (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z 1,k))))+
      (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z 2,k))))=0) :
    ∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,
      xFlow P S x f=canonicalBasisWord (F:=BDL26Field) (rayImage P q S (z 0) c k) := by
  have hterm (i : Fin 3) : f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr (z i)))=0 :=
    shared_bridge_zero P A S x f hw q (leaf i) (Ne.symm (hleaf i))
      hxq (hxleaf i) (z i) (lz i)
      (shared_Z_bridge_image P A S x q (leaf i) hxq (hxleaf i)
        (z i) (lz i) (hlz i).symm)
  have hp02 := rectangle_ray_pair P A S x q hxq f (z 0) (z 2) (hterm 0) (hterm 2)
  have hp12 := rectangle_ray_pair P A S x q hxq f (z 1) (z 2) (hterm 1) (hterm 2)
  apply two_ray_parities_force_actual_cut S (xFlow P S x f) hw
    (fun p : Fin 3 × BDL26FiniteTannerSquare.Two × Fin S.half => rayImage P q S (z p.1) p.2.1 p.2.2)
    (rayImage_injective P q S z hz)
  · exact hp02.symm.trans h02
  · exact hp12.symm.trans h12

end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open scoped Classical BigOperators
noncomputable section

/-- Actual horizontal strip, radial side included and opposite hub side
excluded. Every internal horizontal coordinate of the row is retained. -/
private def horizontalStrip (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) : Word BDL26Field (SubdivisionEdge P x S)
  | .inl (e,k) => if e=xStarFaceXQEdge P x f 0 ∧ k.val=0 then 1 else 0
  | .inr (.inl (g,i,_)) => if g=f ∧ i.val=0 then 1 else 0
  | .inr (.inr _) => 0

/-- The transpose-direction actual strip, with no boundary/glue shortcut. -/
private def verticalStrip (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) : Word BDL26Field (SubdivisionEdge P x S)
  | .inl (e,k) => if e=xStarFaceXQEdge P x f 1 ∧ k.val=0 then 1 else 0
  | .inr (.inl _) => 0
  | .inr (.inr (g,_,j)) => if g=f ∧ j.val=0 then 1 else 0

private def copiedStrip (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (w : Word BDL26Field (SubdivisionEdge P x S)) :
    Word BDL26Field (DoubleCylinderEdge P x S)
  | .inl (d,e) => if d=copy then w e else 0
  | .inr _ => 0

/-- All four actual small-square boundary slots, with the copy tag explicit. -/
private theorem actual_square_coboundary (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (copy : BDL26FiniteTannerSquare.Two) (f : XStarFace P x) (i j : Fin S.half) :
    doubleCylinderCoboundary1 P x S w (Sum.inl (copy,f,i,j))=
      (w (Sum.inl (copy,subdivisionHorizontalEdge P x S f i (finCastGrid j)))+
       w (Sum.inl (copy,subdivisionVerticalEdge P x S f (finSuccGrid i) j)))+
      (w (Sum.inl (copy,subdivisionHorizontalEdge P x S f i (finSuccGrid j)))+
       w (Sum.inl (copy,subdivisionVerticalEdge P x S f (finCastGrid i) j))) := by
  rw [doubleCylinderCoboundary1,doubleCylinderBoundary2,
    wordLinearMapTranspose_toLin'_apply]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [doubleCylinderFaceEdgeMatrix,mul_ite,mul_zero,Finset.sum_const_zero,add_zero]
  have hc :
      (∑ d : BDL26FiniteTannerSquare.Two,∑ e : SubdivisionEdge P x S,
        if d=copy then w (Sum.inl (d,e))*subdivisionFaceEdgeMatrix P x S e (f,i,j) else 0)=
      ∑ e : SubdivisionEdge P x S,
        w (Sum.inl (copy,e))*subdivisionFaceEdgeMatrix P x S e (f,i,j) := by
    rw [Fintype.sum_eq_single copy]
    · simp
    · intro d hd
      simp [hd]
  rw [hc]
  simp only [subdivisionFaceEdgeMatrix,mul_add,Finset.sum_add_distrib,
    mul_ite,mul_one,mul_zero]
  simp
  exact add_assoc _ _ _

private theorem horizontalStrip_on_horizontal (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 0 → g=f ∧ c=0)
    (g : XStarFace P x) (i : Fin S.half) (j : Fin (S.half+1)) :
    horizontalStrip P x S f (subdivisionHorizontalEdge P x S g i j)=
      if g=f ∧ i.val=0 ∧ j.val < S.half then 1 else 0 := by
  by_cases hj0 : j.val=0
  · have he : xStarFaceXQEdge P x g 0=xStarFaceXQEdge P x f 0 ↔ g=f :=
      ⟨fun h => (hunique g 0 h).1,by intro h;subst g;rfl⟩
    simp [subdivisionHorizontalEdge,hj0,horizontalStrip,he,S.half_pos]
  · by_cases hjm : j.val=S.half
    · simp [subdivisionHorizontalEdge,hj0,hjm,horizontalStrip,
        xStarFaceQZEdge,xStarFaceXQEdge,Nat.ne_of_gt S.half_pos]
    · have hj : j.val < S.half := by have := j.isLt;omega
      simp [subdivisionHorizontalEdge,hj0,hjm,horizontalStrip,hj]

private theorem horizontalStrip_on_vertical (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 0 → g=f ∧ c=0)
    (g : XStarFace P x) (i : Fin (S.half+1)) (j : Fin S.half) :
    horizontalStrip P x S f (subdivisionVerticalEdge P x S g i j)=0 := by
  by_cases hi0 : i.val=0
  · have he : xStarFaceXQEdge P x g 1≠xStarFaceXQEdge P x f 0 := by
      intro h
      exact (by decide : (1:BDL26FiniteTannerSquare.Two)≠0) (hunique g 1 h).2
    simp [subdivisionVerticalEdge,hi0,horizontalStrip,he]
  · by_cases him : i.val=S.half
    all_goals simp [subdivisionVerticalEdge,hi0,him,horizontalStrip,
      xStarFaceQZEdge,xStarFaceXQEdge,Nat.ne_of_gt S.half_pos]

private theorem verticalStrip_on_vertical (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 1 → g=f ∧ c=1)
    (g : XStarFace P x) (i : Fin (S.half+1)) (j : Fin S.half) :
    verticalStrip P x S f (subdivisionVerticalEdge P x S g i j)=
      if g=f ∧ j.val=0 ∧ i.val < S.half then 1 else 0 := by
  by_cases hi0 : i.val=0
  · have he : xStarFaceXQEdge P x g 1=xStarFaceXQEdge P x f 1 ↔ g=f :=
      ⟨fun h => (hunique g 1 h).1,by intro h;subst g;rfl⟩
    simp [subdivisionVerticalEdge,hi0,verticalStrip,he,S.half_pos]
  · by_cases him : i.val=S.half
    · simp [subdivisionVerticalEdge,hi0,him,verticalStrip,
        xStarFaceQZEdge,xStarFaceXQEdge,Nat.ne_of_gt S.half_pos]
    · have hi : i.val < S.half := by have := i.isLt;omega
      simp [subdivisionVerticalEdge,hi0,him,verticalStrip,hi]

private theorem verticalStrip_on_horizontal (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 1 → g=f ∧ c=1)
    (g : XStarFace P x) (i : Fin S.half) (j : Fin (S.half+1)) :
    verticalStrip P x S f (subdivisionHorizontalEdge P x S g i j)=0 := by
  by_cases hj0 : j.val=0
  · have he : xStarFaceXQEdge P x g 0≠xStarFaceXQEdge P x f 1 := by
      intro h
      exact (by decide : (0:BDL26FiniteTannerSquare.Two)≠1) (hunique g 0 h).2
    simp [subdivisionHorizontalEdge,hj0,verticalStrip,he]
  · by_cases hjm : j.val=S.half
    all_goals simp [subdivisionHorizontalEdge,hj0,hjm,verticalStrip,
      xStarFaceQZEdge,xStarFaceXQEdge,Nat.ne_of_gt S.half_pos]

private def lastSegment (S : OddScale) : Fin S.half := ⟨S.half-1,by have := S.half_pos;omega⟩
private def firstSegment (S : OddScale) : Fin S.half := ⟨0,S.half_pos⟩

private theorem horizontalStrip_boundary_zero (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (e : SubdivisionBoundaryEdge P x S) :
    horizontalStrip P x S f e.val=0 := by
  rcases e with ⟨e,he⟩
  rcases e with ⟨a,k⟩ | e
  · have hne : a≠xStarFaceXQEdge P x f 0 := by
      intro h
      subst a
      change false=true at he
      cases he
    simp [horizontalStrip,hne]
  · simp [subdivisionBoundaryEdgeMember] at he

private theorem verticalStrip_boundary_zero (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x) (e : SubdivisionBoundaryEdge P x S) :
    verticalStrip P x S f e.val=0 := by
  rcases e with ⟨e,he⟩
  rcases e with ⟨a,k⟩ | e
  · have hne : a≠xStarFaceXQEdge P x f 1 := by
      intro h
      subst a
      change false=true at he
      cases he
    simp [verticalStrip,hne]
  · simp [subdivisionBoundaryEdgeMember] at he

private theorem copiedStrip_rectangle_zero (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (copy : BDL26FiniteTannerSquare.Two)
    (w : Word BDL26Field (SubdivisionEdge P x S))
    (hw : ∀ e : SubdivisionBoundaryEdge P x S,w e.val=0)
    (e : SubdivisionBoundaryEdge P x S) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy w) (Sum.inr e)=0 := by
  rw [original_rectangle_coboundary]
  simp [copiedStrip,hw]

private theorem copiedStrip_flow_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (S : OddScale) (copy : BDL26FiniteTannerSquare.Two)
    (w : Word BDL26Field (SubdivisionEdge P x S))
    (hw : ∀ e : SubdivisionBoundaryEdge P x S,w e.val=0) :
    xFlow P S x (copiedStrip P x S copy w)=0 := by
  funext p
  rcases p with (⟨y,f⟩ | ⟨q,e⟩) | ⟨z,d⟩
  · exact xFlow_at_x P S x y (copiedStrip P x S copy w) f
  · have h := xFlow_at_q P A S x (copiedStrip P x S copy w) q e
    by_cases hx : P.xq x q=true
    · refine h.trans ((dif_pos hx).trans ?_)
      change copiedStrip P x S copy w (qToXDoubleCylinderEdge P A q x hx S e)=0
      rcases e with ⟨c,z,k⟩ | z
      · simp [qToXDoubleCylinderEdge,copiedStrip,hw]
      · simp [qToXDoubleCylinderEdge,copiedStrip]
    · exact h.trans (dif_neg hx)
  · exact xFlow_at_z P S x (copiedStrip P x S copy w) z d

private theorem horizontalStrip_copied_square (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 0 → g=f ∧ c=0)
    (copy d : BDL26FiniteTannerSquare.Two) (g : XStarFace P x) (i j : Fin S.half) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy (horizontalStrip P x S f))
      (Sum.inl (d,g,i,j))=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (copy,f,firstSegment S,lastSegment S) : DoubleCylinderFace P x S) (Sum.inl (d,g,i,j)) := by
  rw [actual_square_coboundary]
  by_cases hd : d=copy
  · subst d
    simp only [copiedStrip,if_true]
    rw [horizontalStrip_on_horizontal P x S f hunique,
      horizontalStrip_on_vertical P x S f hunique,
      horizontalStrip_on_horizontal P x S f hunique,
      horizontalStrip_on_vertical P x S f hunique]
    have hj : j.val < S.half := j.isLt
    have hji : j.val+1=S.half ↔ j=lastSegment S := by
      simp only [lastSegment,Fin.ext_iff]
      have := j.isLt
      have := S.half_pos
      omega
    have hii : i.val=0 ↔ i=firstSegment S := by simp [firstSegment,Fin.ext_iff]
    by_cases hg : g=f
    · subst g
      by_cases hi : i.val=0
      · by_cases hjlast : j.val+1=S.half
        · have he : j=lastSegment S := hji.mp hjlast
          have ie : i=firstSegment S := hii.mp hi
          subst j
          subst i
          have hl : S.half-1+1=S.half := Nat.sub_add_cancel (by have := S.half_pos;omega)
          simp [finCastGrid,finSuccGrid,firstSegment,lastSegment,basis_value,Prod.mk.injEq,
            S.half_pos,hl]
        · have hjnext : j.val+1 < S.half := by omega
          have hne : j≠lastSegment S := fun he => hjlast (hji.mpr he)
          simp [finCastGrid,finSuccGrid,hj,hjnext,hi,basis_value,Prod.mk.injEq,hne,
            CharTwo.add_self_eq_zero]
      · have hne : i≠firstSegment S := fun he => hi (hii.mpr he)
        simp [finCastGrid,finSuccGrid,hi,basis_value,Prod.mk.injEq,hne]
    · simp [hg,basis_value,Prod.mk.injEq]
  · simp [copiedStrip,hd,basis_value,Prod.mk.injEq]

private theorem verticalStrip_copied_square (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 1 → g=f ∧ c=1)
    (copy d : BDL26FiniteTannerSquare.Two) (g : XStarFace P x) (i j : Fin S.half) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy (verticalStrip P x S f))
      (Sum.inl (d,g,i,j))=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (copy,f,lastSegment S,firstSegment S) : DoubleCylinderFace P x S) (Sum.inl (d,g,i,j)) := by
  rw [actual_square_coboundary]
  by_cases hd : d=copy
  · subst d
    simp only [copiedStrip,if_true]
    rw [verticalStrip_on_horizontal P x S f hunique,
      verticalStrip_on_vertical P x S f hunique,
      verticalStrip_on_horizontal P x S f hunique,
      verticalStrip_on_vertical P x S f hunique]
    have hi : i.val < S.half := i.isLt
    have hii : i.val+1=S.half ↔ i=lastSegment S := by
      simp only [lastSegment,Fin.ext_iff]
      have := i.isLt
      have := S.half_pos
      omega
    have hji : j.val=0 ↔ j=firstSegment S := by simp [firstSegment,Fin.ext_iff]
    by_cases hg : g=f
    · subst g
      by_cases hj : j.val=0
      · by_cases hilast : i.val+1=S.half
        · have he : i=lastSegment S := hii.mp hilast
          have je : j=firstSegment S := hji.mp hj
          subst i
          subst j
          have hl : S.half-1+1=S.half := Nat.sub_add_cancel (by have := S.half_pos;omega)
          simp [finCastGrid,finSuccGrid,firstSegment,lastSegment,basis_value,Prod.mk.injEq,
            S.half_pos,hl]
        · have hinext : i.val+1 < S.half := by omega
          have hne : i≠lastSegment S := fun he => hilast (hii.mpr he)
          simp [finCastGrid,finSuccGrid,hi,hinext,hj,basis_value,Prod.mk.injEq,hne,
            CharTwo.add_self_eq_zero]
      · have hne : j≠firstSegment S := fun he => hj (hji.mpr he)
        simp [finCastGrid,finSuccGrid,hj,basis_value,Prod.mk.injEq,hne]
    · simp [hg,basis_value,Prod.mk.injEq]
  · simp [copiedStrip,hd,basis_value,Prod.mk.injEq]

private theorem horizontalStrip_whole_boundary (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 0 → g=f ∧ c=0) (copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy (horizontalStrip P x S f))=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (copy,f,firstSegment S,lastSegment S)) := by
  funext face
  rcases face with ⟨d,g,i,j⟩ | e
  · exact horizontalStrip_copied_square P x S f hunique copy d g i j
  · rw [copiedStrip_rectangle_zero P x S copy _ (horizontalStrip_boundary_zero P x S f)]
    simp [basis_value]

private theorem verticalStrip_whole_boundary (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hunique : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceXQEdge P x g c=xStarFaceXQEdge P x f 1 → g=f ∧ c=1) (copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 P x S (copiedStrip P x S copy (verticalStrip P x S f))=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (copy,f,lastSegment S,firstSegment S)) := by
  funext face
  rcases face with ⟨d,g,i,j⟩ | e
  · exact verticalStrip_copied_square P x S f hunique copy d g i j
  · rw [copiedStrip_rectangle_zero P x S copy _ (verticalStrip_boundary_zero P x S f)]
    simp [basis_value]

/-- New coordinates are (0,h-1)/(h-1,0), not the old finite (0,0). -/
private def scaledSmallFace (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    SubdivisionFace (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer) S :=
  if ActualCriticalStarGeometry.cr S j outer=0 then
    (DirectOldXCounterexample.actualStarFace S j outer,firstSegment S,lastSegment S)
  else (DirectOldXCounterexample.actualStarFace S j outer,lastSegment S,firstSegment S)

private def scaledAlpha (S : OddScale) (j : Fin 2) (outer copy : BDL26FiniteTannerSquare.Two) :
    Word BDL26Field (DoubleCylinderEdge (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S) :=
  if ActualCriticalStarGeometry.cr S j outer=0 then
    copiedStrip _ _ S copy (horizontalStrip _ _ S (DirectOldXCounterexample.actualStarFace S j outer))
  else copiedStrip _ _ S copy (verticalStrip _ _ S (DirectOldXCounterexample.actualStarFace S j outer))

private theorem scaledAlpha_actual_flow_zero (S : OddScale) (j : Fin 2) (outer copy : BDL26FiniteTannerSquare.Two) :
    xFlow (DirectOldXCounterexample.AP S) S (DirectOldXCounterexample.AX S j outer)
      (scaledAlpha S j outer copy)=0 := by
  unfold scaledAlpha
  split_ifs
  · exact copiedStrip_flow_zero _ (DirectOldXCounterexample.AA S).toTannerSquareAdmissible
      _ S copy _ (horizontalStrip_boundary_zero _ _ S _)
  · exact copiedStrip_flow_zero _ (DirectOldXCounterexample.AA S).toTannerSquareAdmissible
      _ S copy _ (verticalStrip_boundary_zero _ _ S _)

end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open scoped Classical BigOperators
noncomputable section

private theorem two_opposite_of_ne (c d : BDL26FiniteTannerSquare.Two) (h : c≠d) :
    c=ActualCriticalStarGeometry.opposite d := by
  fin_cases c <;> fin_cases d
  all_goals simp [ActualCriticalStarGeometry.opposite] at *

/-- Discharge the generic strip's corner uniqueness in the ACTUAL star.
Neither an isolated face nor a radial incidence law is an endpoint premise. -/
private theorem actual_radial_corner_unique (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (g : XStarFace (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer))
    (c : BDL26FiniteTannerSquare.Two)
    (he : xStarFaceXQEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) g c=
      DirectOldXCounterexample.actualRadialStarEdge S j outer) :
    g=DirectOldXCounterexample.actualStarFace S j outer ∧
      c=ActualCriticalStarGeometry.cr S j outer := by
  have hQ : (DirectOldXCounterexample.AP S).faceQ g.val c=
      DirectOldXCounterexample.AL S j outer 0 := by
    have h := congrArg (fun e : XStarEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) =>
      match e.val with | .inl a => a.val.2 | .inr a => a.val.1) he
    simpa [xStarFaceXQEdge,faceXQEdge,
      DirectOldXCounterexample.actualRadialStarEdge_value] using h
  have hg : g=DirectOldXCounterexample.actualStarFace S j outer := by
    apply (DirectOldXCounterexample.actual_radial_incident_face S j outer g).mp
    rcases two_eq_zero_or_one c with hc | hc
    · exact Or.inl (by simpa [hc] using hQ.symm)
    · exact Or.inr (by simpa [hc] using hQ.symm)
  refine ⟨hg,?_⟩
  subst g
  by_contra hc
  have ho := two_opposite_of_ne c (ActualCriticalStarGeometry.cr S j outer) hc
  have hhub : (DirectOldXCounterexample.AP S).faceQ
      (DirectOldXCounterexample.actualStarFace S j outer).val c=
        DirectOldXCounterexample.AH S j outer := by
    simpa [DirectOldXCounterexample.actualStarFace,ho] using
      ActualCriticalStarGeometry.fr_hub_corner S j outer
  exact DirectOldXCounterexample.AL_ne_hub S j outer 0 (hQ.symm.trans hhub)

private theorem scaledAlpha_actual_boundary (S : OddScale) (j : Fin 2) (outer copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S (scaledAlpha S j outer copy)=
      canonicalBasisWord (F:=BDL26Field) (Sum.inl (copy,scaledSmallFace S j outer)) := by
  by_cases hc : ActualCriticalStarGeometry.cr S j outer=0
  · have hu : ∀ (g : XStarFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)) (c : BDL26FiniteTannerSquare.Two),
        xStarFaceXQEdge _ _ g c=xStarFaceXQEdge _ _
          (DirectOldXCounterexample.actualStarFace S j outer) 0 →
        g=DirectOldXCounterexample.actualStarFace S j outer ∧ c=0 := by
      intro g c he
      have hr : xStarFaceXQEdge _ _ g c=DirectOldXCounterexample.actualRadialStarEdge S j outer := by
        simpa [DirectOldXCounterexample.actualRadialStarEdge,hc] using he
      simpa [hc] using actual_radial_corner_unique S j outer g c hr
    simpa [scaledAlpha,scaledSmallFace,hc] using
      horizontalStrip_whole_boundary (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S
        (DirectOldXCounterexample.actualStarFace S j outer) hu copy
  · have hc1 : ActualCriticalStarGeometry.cr S j outer=1 :=
      (two_eq_zero_or_one _).resolve_left hc
    have hu : ∀ (g : XStarFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)) (c : BDL26FiniteTannerSquare.Two),
        xStarFaceXQEdge _ _ g c=xStarFaceXQEdge _ _
          (DirectOldXCounterexample.actualStarFace S j outer) 1 →
        g=DirectOldXCounterexample.actualStarFace S j outer ∧ c=1 := by
      intro g c he
      have hr : xStarFaceXQEdge _ _ g c=DirectOldXCounterexample.actualRadialStarEdge S j outer := by
        simpa [DirectOldXCounterexample.actualRadialStarEdge,hc1] using he
      simpa [hc1] using actual_radial_corner_unique S j outer g c hr
    simpa [scaledAlpha,scaledSmallFace,hc] using
      verticalStrip_whole_boundary (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S
        (DirectOldXCounterexample.actualStarFace S j outer) hu copy

private theorem actual_hub_corner_unique (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (g : XStarFace (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer))
    (c : BDL26FiniteTannerSquare.Two)
    (he : xStarFaceQZEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) g c=
      DirectOldXCounterexample.actualHubStarEdge S j outer) :
    g=DirectOldXCounterexample.actualStarFace S j outer ∧
      c=ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer) := by
  have hQ : (DirectOldXCounterexample.AP S).faceQ g.val c=
      DirectOldXCounterexample.AH S j outer := by
    have h := congrArg (fun e : XStarEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) =>
      match e.val with | .inl a => a.val.2 | .inr a => a.val.1) he
    simpa [xStarFaceQZEdge,faceQZEdge,DirectOldXCounterexample.actualHubStarEdge,
      qToXBoundaryEdge,xStarBoundaryEdgeToStar,DirectOldXCounterexample.AHZ] using h
  have hZ : (DirectOldXCounterexample.AP S).faceZ g.val=
      DirectOldXCounterexample.AZ S j outer 0 := by
    have h := congrArg (fun e : XStarEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) =>
      match e.val with | .inl _ => none | .inr a => some a.val.2) he
    simpa [xStarFaceQZEdge,faceQZEdge,DirectOldXCounterexample.actualHubStarEdge,
      qToXBoundaryEdge,xStarBoundaryEdgeToStar,DirectOldXCounterexample.AHZ] using h
  have hg : g=DirectOldXCounterexample.actualStarFace S j outer := by
    apply Subtype.ext
    apply (DirectOldXCounterexample.AR S).faceXZ_injective
    apply Prod.ext
    · exact (show (DirectOldXCounterexample.AP S).faceX g.val=
        DirectOldXCounterexample.AX S j outer from by
          simpa [xStarFaceMember] using g.property).trans
        (show (DirectOldXCounterexample.AP S).faceX
          (DirectOldXCounterexample.actualStarFace S j outer).val=
            DirectOldXCounterexample.AX S j outer from by
          simpa [xStarFaceMember] using (DirectOldXCounterexample.actualStarFace S j outer).property).symm
    · exact hZ.trans (ActualCriticalStarGeometry.faceFromShared_Z
        (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer)
        (DirectOldXCounterexample.AZ S j outer 0) (DirectOldXCounterexample.AL S j outer 0)
        (DirectOldXCounterexample.AL_incident S j outer 0)
        (DirectOldXCounterexample.AL_check S j outer 0)).symm
  refine ⟨hg,?_⟩
  apply two_opposite_of_ne
  intro hc
  subst g
  have hleaf : (DirectOldXCounterexample.AP S).faceQ
      (DirectOldXCounterexample.actualStarFace S j outer).val c=
        DirectOldXCounterexample.AL S j outer 0 := by
    have hr : DirectOldXCounterexample.AL S j outer 0=ActualCriticalStarGeometry.r S j outer := by
      simp [DirectOldXCounterexample.AL]
    simpa [DirectOldXCounterexample.actualStarFace,hc,hr] using
      ActualCriticalStarGeometry.fr_leaf_corner S j outer
  exact DirectOldXCounterexample.AL_ne_hub S j outer 0 (hleaf.symm.trans hQ)

/-- Matrix column of the genuine upper hub edge in the horizontal orientation. -/
private theorem hub_horizontal_matrix (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hu : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceQZEdge P x g c=xStarFaceQZEdge P x f 1 → g=f ∧ c=1)
    (g : XStarFace P x) (i j : Fin S.half) :
    subdivisionFaceEdgeMatrix P x S
      (Sum.inl (xStarFaceQZEdge P x f 1,firstSegment S)) (g,i,j)=
      if g=f ∧ i=firstSegment S ∧ j=lastSegment S then 1 else 0 := by
  let e : SubdivisionEdge P x S := Sum.inl (xStarFaceQZEdge P x f 1,firstSegment S)
  have heq (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two) :
      xStarFaceQZEdge P x f 1=xStarFaceQZEdge P x g c ↔ g=f ∧ c=1 :=
    ⟨fun h => hu g c h.symm,by rintro ⟨rfl,rfl⟩;rfl⟩
  have hne (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two) :
      xStarFaceQZEdge P x f 1≠xStarFaceXQEdge P x g c := by
    intro h
    have hh := congrArg Subtype.val h
    cases hh
  have hi0 : i.val+1≠0 := by omega
  have hj0 : j.val+1≠0 := by omega
  have hil : i.val≠S.half := Nat.ne_of_lt i.isLt
  have hjl : j.val≠S.half := Nat.ne_of_lt j.isLt
  have hlast : j.val+1=S.half ↔ j=lastSegment S := by
    simp only [lastSegment,Fin.ext_iff]
    have := S.half_pos
    have := j.isLt
    omega
  have hHlo : e≠subdivisionHorizontalEdge P x S g i (finCastGrid j) := by
    by_cases hz : j.val=0
    all_goals simp [e,subdivisionHorizontalEdge,finCastGrid,hz,hjl,hne,Prod.mk.injEq]
  have hVlo : e≠subdivisionVerticalEdge P x S g (finCastGrid i) j := by
    by_cases hz : i.val=0
    all_goals simp [e,subdivisionVerticalEdge,finCastGrid,hz,hil,hne,Prod.mk.injEq]
  have hVhi : e≠subdivisionVerticalEdge P x S g (finSuccGrid i) j := by
    have hn : xStarFaceQZEdge P x f 1≠xStarFaceQZEdge P x g 0 := by
      intro h
      exact (by decide : (0 : BDL26FiniteTannerSquare.Two)≠1) (hu g 0 h.symm).2
    by_cases hm : i.val+1=S.half
    all_goals
      have hhalf : S.half≠0 := Nat.ne_of_gt S.half_pos
      simp [e,subdivisionVerticalEdge,finSuccGrid,hi0,hm,hn,hhalf,Prod.mk.injEq]
  have hHhi : e=subdivisionHorizontalEdge P x S g i (finSuccGrid j) ↔
      g=f ∧ i=firstSegment S ∧ j=lastSegment S := by
    by_cases hm : j.val+1=S.half
    · dsimp only [e,subdivisionHorizontalEdge,finSuccGrid]
      rw [dif_neg hj0,dif_pos hm]
      simp only [Sum.inl.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨he,hi⟩
        exact ⟨((heq g 1).mp he).1,hi.symm,hlast.mp hm⟩
      · rintro ⟨hg,hi,hj⟩
        subst g
        subst i
        exact ⟨rfl,rfl⟩
    · have hn : j≠lastSegment S := fun h => hm (hlast.mpr h)
      simp [e,subdivisionHorizontalEdge,finSuccGrid,hj0,hm,hn]
  change (((if e=subdivisionHorizontalEdge P x S g i (finCastGrid j) then (1 : BDL26Field) else 0)+
    (if e=subdivisionVerticalEdge P x S g (finSuccGrid i) j then 1 else 0))+
    (if e=subdivisionHorizontalEdge P x S g i (finSuccGrid j) then 1 else 0))+
    (if e=subdivisionVerticalEdge P x S g (finCastGrid i) j then 1 else 0)=_
  simp only [if_neg hHlo,if_neg hVhi,if_neg hVlo,zero_add,add_zero]
  exact indicator_iff _ _ hHhi

private theorem hub_vertical_matrix (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (f : XStarFace P x)
    (hu : ∀ (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceQZEdge P x g c=xStarFaceQZEdge P x f 0 → g=f ∧ c=0)
    (g : XStarFace P x) (i j : Fin S.half) :
    subdivisionFaceEdgeMatrix P x S
      (Sum.inl (xStarFaceQZEdge P x f 0,firstSegment S)) (g,i,j)=
      if g=f ∧ i=lastSegment S ∧ j=firstSegment S then 1 else 0 := by
  let e : SubdivisionEdge P x S := Sum.inl (xStarFaceQZEdge P x f 0,firstSegment S)
  have heq (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two) :
      xStarFaceQZEdge P x f 0=xStarFaceQZEdge P x g c ↔ g=f ∧ c=0 :=
    ⟨fun h => hu g c h.symm,by rintro ⟨rfl,rfl⟩;rfl⟩
  have hne (g : XStarFace P x) (c : BDL26FiniteTannerSquare.Two) :
      xStarFaceQZEdge P x f 0≠xStarFaceXQEdge P x g c := by
    intro h
    have hh := congrArg Subtype.val h
    cases hh
  have hi0 : i.val+1≠0 := by omega
  have hj0 : j.val+1≠0 := by omega
  have hil : i.val≠S.half := Nat.ne_of_lt i.isLt
  have hjl : j.val≠S.half := Nat.ne_of_lt j.isLt
  have hlast : i.val+1=S.half ↔ i=lastSegment S := by
    simp only [lastSegment,Fin.ext_iff]
    have := S.half_pos
    have := i.isLt
    omega
  have hHlo : e≠subdivisionHorizontalEdge P x S g i (finCastGrid j) := by
    by_cases hz : j.val=0
    all_goals simp [e,subdivisionHorizontalEdge,finCastGrid,hz,hjl,hne,Prod.mk.injEq]
  have hVlo : e≠subdivisionVerticalEdge P x S g (finCastGrid i) j := by
    by_cases hz : i.val=0
    all_goals simp [e,subdivisionVerticalEdge,finCastGrid,hz,hil,hne,Prod.mk.injEq]
  have hHhi : e≠subdivisionHorizontalEdge P x S g i (finSuccGrid j) := by
    have hn : xStarFaceQZEdge P x f 0≠xStarFaceQZEdge P x g 1 := by
      intro h
      exact (by decide : (1 : BDL26FiniteTannerSquare.Two)≠0) (hu g 1 h.symm).2
    by_cases hm : j.val+1=S.half
    all_goals
      have hhalf : S.half≠0 := Nat.ne_of_gt S.half_pos
      simp [e,subdivisionHorizontalEdge,finSuccGrid,hj0,hm,hn,hhalf,Prod.mk.injEq]
  have hVhi : e=subdivisionVerticalEdge P x S g (finSuccGrid i) j ↔
      g=f ∧ i=lastSegment S ∧ j=firstSegment S := by
    by_cases hm : i.val+1=S.half
    · dsimp only [e,subdivisionVerticalEdge,finSuccGrid]
      rw [dif_neg hi0,dif_pos hm]
      simp only [Sum.inl.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨he,hj⟩
        exact ⟨((heq g 0).mp he).1,hlast.mp hm,hj.symm⟩
      · rintro ⟨hg,hi,hj⟩
        subst g
        subst j
        exact ⟨rfl,rfl⟩
    · have hn : i≠lastSegment S := fun h => hm (hlast.mpr h)
      simp [e,subdivisionVerticalEdge,finSuccGrid,hi0,hm,hn]
  change (((if e=subdivisionHorizontalEdge P x S g i (finCastGrid j) then (1 : BDL26Field) else 0)+
    (if e=subdivisionVerticalEdge P x S g (finSuccGrid i) j then 1 else 0))+
    (if e=subdivisionHorizontalEdge P x S g i (finSuccGrid j) then 1 else 0))+
    (if e=subdivisionVerticalEdge P x S g (finCastGrid i) j then 1 else 0)=_
  simp only [if_neg hHlo,if_neg hHhi,if_neg hVlo,zero_add,add_zero]
  exact indicator_iff _ _ hVhi


/-- The actual hub star side is the opposite corner of the same true face. -/
private theorem actual_hub_side (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    DirectOldXCounterexample.actualHubStarEdge S j outer=
      xStarFaceQZEdge (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)
        (DirectOldXCounterexample.actualStarFace S j outer)
        (ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer)) := by
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Subtype.ext
  apply Prod.ext
  · exact (ActualCriticalStarGeometry.fr_hub_corner S j outer).symm
  · exact (ActualCriticalStarGeometry.faceFromShared_Z
      (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer)
      (DirectOldXCounterexample.AZ S j outer 0) (DirectOldXCounterexample.AL S j outer 0)
      (DirectOldXCounterexample.AL_incident S j outer 0)
      (DirectOldXCounterexample.AL_check S j outer 0)).symm

private theorem actual_error_small_column (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (g : XStarFace (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer))
    (i k : Fin S.half) :
    subdivisionFaceEdgeMatrix (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S
      (Sum.inl (DirectOldXCounterexample.actualHubStarEdge S j outer,firstSegment S)) (g,i,k)=
      if (g,i,k)=scaledSmallFace S j outer then 1 else 0 := by
  by_cases hc : ActualCriticalStarGeometry.cr S j outer=0
  · have hs : ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer)=1 := by
      simp [hc,ActualCriticalStarGeometry.opposite]
    have hu : ∀ (g : XStarFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceQZEdge _ _ g c=xStarFaceQZEdge _ _
        (DirectOldXCounterexample.actualStarFace S j outer) 1 →
        g=DirectOldXCounterexample.actualStarFace S j outer ∧ c=1 := by
      intro g c he
      have he' : xStarFaceQZEdge _ _ g c=DirectOldXCounterexample.actualHubStarEdge S j outer :=
        he.trans (by rw [actual_hub_side,hs])
      simpa [hs] using actual_hub_corner_unique S j outer g c he'
    rw [actual_hub_side,hs,hub_horizontal_matrix _ _ S _ hu]
    simp [scaledSmallFace,hc,Prod.mk.injEq]
  · have hc1 : ActualCriticalStarGeometry.cr S j outer=1 := (two_eq_zero_or_one _).resolve_left hc
    have hs : ActualCriticalStarGeometry.opposite (ActualCriticalStarGeometry.cr S j outer)=0 := by
      simp [hc1,ActualCriticalStarGeometry.opposite]
    have hu : ∀ (g : XStarFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer)) (c : BDL26FiniteTannerSquare.Two),
      xStarFaceQZEdge _ _ g c=xStarFaceQZEdge _ _
        (DirectOldXCounterexample.actualStarFace S j outer) 0 →
        g=DirectOldXCounterexample.actualStarFace S j outer ∧ c=0 := by
      intro g c he
      have he' : xStarFaceQZEdge _ _ g c=DirectOldXCounterexample.actualHubStarEdge S j outer :=
        he.trans (by rw [actual_hub_side,hs])
      simpa [hs] using actual_hub_corner_unique S j outer g c he'
    rw [actual_hub_side,hs,hub_vertical_matrix _ _ S _ hu]
    simp [scaledSmallFace,hc,Prod.mk.injEq]

private theorem actual_single_error_whole_boundary (S : OddScale) (j : Fin 2)
    (outer copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S
      (canonicalBasisWord (F:=BDL26Field) (DirectOldXCounterexample.actualErrorEdge S j outer copy))=
      canonicalBasisWord (F:=BDL26Field) (Sum.inl (copy,scaledSmallFace S j outer))+
      canonicalBasisWord (F:=BDL26Field) (Sum.inr (DirectOldXCounterexample.actualHubD S j outer)) := by
  funext face
  rw [QEC.Coding.BDL26RXPrimitiveC2QEndpoint.doubleCylinder_basis_column]
  rcases face with ⟨d,g,i,k⟩ | rect
  · change (if copy=d then subdivisionFaceEdgeMatrix (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S
        (Sum.inl (DirectOldXCounterexample.actualHubStarEdge S j outer,firstSegment S)) (g,i,k) else 0)=_
    rw [actual_error_small_column]
    simp only [Pi.add_apply,basis_value,Sum.inl.injEq,Sum.inl_ne_inr,if_false,add_zero]
    by_cases hd : copy=d
    · subst d
      simp only [Prod.mk.injEq,true_and,if_pos rfl,if_true]
    · have hd' : d≠copy := Ne.symm hd
      simp only [if_neg hd,Prod.mk.injEq,hd',false_and,if_false]
  · change (if (DirectOldXCounterexample.actualHubD S j outer).val=rect.val then (1:BDL26Field) else 0)=_
    have he : (Sum.inr rect : DoubleCylinderFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S)=
        Sum.inr (DirectOldXCounterexample.actualHubD S j outer) ↔
        (DirectOldXCounterexample.actualHubD S j outer).val=rect.val := by
      constructor
      · intro h
        exact (congrArg Subtype.val (Sum.inr.inj h)).symm
      · intro h
        exact congrArg Sum.inr (Subtype.ext h.symm)
    simp [basis_value,he]

/-- Both copies induce the very SAME nonzero original rectangle query. -/
private theorem scaled_fixed_D_query (S : OddScale) (j : Fin 2) (outer copy : BDL26FiniteTannerSquare.Two) :
    doubleCylinderCoboundary1 (DirectOldXCounterexample.AP S)
      (DirectOldXCounterexample.AX S j outer) S
      (scaledAlpha S j outer copy+
        canonicalBasisWord (F:=BDL26Field) (DirectOldXCounterexample.actualErrorEdge S j outer copy))=
      canonicalBasisWord (F:=BDL26Field) (Sum.inr (DirectOldXCounterexample.actualHubD S j outer)) := by
  rw [map_add,scaledAlpha_actual_boundary,actual_single_error_whole_boundary]
  have hs := repair3_word_add_self
    (canonicalBasisWord (F:=BDL26Field) (Sum.inl (copy,scaledSmallFace S j outer)) :
      Word BDL26Field (DoubleCylinderFace (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AX S j outer) S))
  rw [← add_assoc,hs,zero_add]

end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open MultiscaleDecoder.RXCoarseGraining
open scoped Classical BigOperators
noncomputable section

private theorem two_zero_ray_parities
    {I : Type} [Fintype I] [DecidableEq I] (S : OddScale)
    (w : Word BDL26Field I) (hw : HammingWeight w ≤ 1)
    (e : Fin 3 × BDL26FiniteTannerSquare.Two × Fin S.half → I) (hinj : Function.Injective e)
    (h02 : (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (0,c,k)))+
      (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (2,c,k)))=0)
    (h12 : (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (1,c,k)))+
      (∑ c : BDL26FiniteTannerSquare.Two,∑ k : Fin S.half,w (e (2,c,k)))=0) :
    ∀ i : Fin 3,∀ c : BDL26FiniteTannerSquare.Two,∀ k : Fin S.half,w (e (i,c,k))=0 := by
  rcases flow_weight_le_one_word w hw with hz | ⟨a,ha⟩
  · intro i c k
    exact congrFun hz _
  subst w
  intro i c k
  by_cases he : e (i,c,k)=a
  · subst a
    have hsum (j : Fin 3) :
        (∑ d : BDL26FiniteTannerSquare.Two,∑ l : Fin S.half,
          canonicalBasisWord (F:=BDL26Field) (e (i,c,k)) (e (j,d,l)))=
          if j=i then 1 else 0 := by
      have hinner (d : BDL26FiniteTannerSquare.Two) :
          (∑ l : Fin S.half,canonicalBasisWord (F:=BDL26Field) (e (i,c,k)) (e (j,d,l)))=
            if j=i ∧ d=c then 1 else 0 := by
        rw [Fintype.sum_eq_single k]
        · simp [basis_value,hinj.eq_iff,Prod.mk.injEq]
        · intro l hl
          simp [basis_value,hinj.eq_iff,Prod.mk.injEq,hl]
      rw [Fin.sum_univ_two,hinner,hinner]
      by_cases hji : j=i <;> fin_cases c <;> simp [hji]
    rw [hsum,hsum] at h02 h12
    fin_cases i
    all_goals simp at h02 h12
  · simp [basis_value,he]

private theorem actual_Cx_zero_hub_rays
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (hz : Function.Injective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f) ≤ 1)
    (hrect : ∀ (i : Fin 3) (k : Fin S.half),
      doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x hxq S (z i,k)))=0) :
    ∀ i : Fin 3,∀ c : BDL26FiniteTannerSquare.Two,∀ k : Fin S.half,
      xFlow P S x f (rayImage P q S (z i) c k)=0 := by
  have hterm (i : Fin 3) : f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr (z i)))=0 :=
    shared_bridge_zero P A S x f hw q (leaf i) (Ne.symm (hleaf i))
      hxq (hxleaf i) (z i) (lz i)
      (shared_Z_bridge_image P A S x q (leaf i) hxq (hxleaf i)
        (z i) (lz i) (hlz i).symm)
  have hp02 := rectangle_ray_pair P A S x q hxq f (z 0) (z 2) (hterm 0) (hterm 2)
  have hp12 := rectangle_ray_pair P A S x q hxq f (z 1) (z 2) (hterm 1) (hterm 2)
  have h02 : rayFlowSum P S x f q (z 0)+rayFlowSum P S x f q (z 2)=0 := by
    rw [← hp02]
    simp [hrect]
  have h12 : rayFlowSum P S x f q (z 1)+rayFlowSum P S x f q (z 2)=0 := by
    rw [← hp12]
    simp [hrect]
  exact two_zero_ray_parities S (xFlow P S x f) hw
    (fun p : Fin 3 × BDL26FiniteTannerSquare.Two × Fin S.half => rayImage P q S (z p.1) p.2.1 p.2.2)
    (rayImage_injective P q S z hz) h02 h12

/-- Exhaust the ACTUAL outgoing X/Q/Z sectors and all ray positions. -/
private theorem actual_Cx_A_leaf_classification
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q=true)
    (z : Fin 3 → QStarEdge P q) (zcover : Function.Surjective z)
    (leaf : Fin 3 → P.Q) (hleaf : ∀ i,leaf i≠q)
    (hxleaf : ∀ i,P.xq x (leaf i)=true)
    (lz : ∀ i,QStarEdge P (leaf i)) (hlz : ∀ i,(lz i).val=(z i).val)
    (leaf_unique : ∀ i,∀ t : QStarEdge P (leaf i),t=lz i)
    (qcover : ∀ r : P.Q,P.xq x r=true → r=q ∨ ∃ i,r=leaf i)
    (f : Word BDL26Field (DoubleCylinderEdge P x S))
    (hw : HammingWeight (xFlow P S x f) ≤ 1)
    (hhub : ∀ i c k,xFlow P S x f (rayImage P q S (z i) c k)=0) :
    xFlow P S x f=0 ∨ ∃ i : Fin 3,∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,
      xFlow P S x f=canonicalBasisWord (F:=BDL26Field) (rayImage P (leaf i) S (lz i) c k) := by
  rcases flow_weight_le_one_word (xFlow P S x f) hw with hz | ⟨p,hp⟩
  · exact Or.inl hz
  right
  have hp1 : xFlow P S x f p=1 := by rw [hp];simp [basis_value]
  rcases p with (⟨y,d⟩ | ⟨r,e⟩) | ⟨zz,c⟩
  · rw [xFlow_at_x] at hp1
    exact False.elim (zero_ne_one hp1)
  · have hxr : P.xq x r=true := by
      by_contra hn
      rw [xFlow_at_q P A,dif_neg hn] at hp1
      exact zero_ne_one hp1
    rcases qcover r hxr with hr | ⟨i,hr⟩
    · subst r
      rcases e with ⟨c,t,k⟩ | t
      · obtain ⟨i,rfl⟩ := zcover t
        exact False.elim (zero_ne_one ((hhub i c k).symm.trans hp1))
      · obtain ⟨i,rfl⟩ := zcover t
        have hzero := shared_bridge_zero P A S x f hw q (leaf i)
          (Ne.symm (hleaf i)) hxq (hxleaf i) (z i) (lz i)
          (shared_Z_bridge_image P A S x q (leaf i) hxq (hxleaf i)
            (z i) (lz i) (hlz i).symm)
        rw [xFlow_at_q P A,dif_pos hxq] at hp1
        change f (qToXDoubleCylinderEdge P A q x hxq S (Sum.inr (z i)))=1 at hp1
        exact False.elim (zero_ne_one (hzero.symm.trans hp1))
    · subst r
      rcases e with ⟨c,t,k⟩ | t
      · have ht := leaf_unique i t
        subst t
        exact ⟨i,c,k,hp⟩
      · have ht := leaf_unique i t
        subst t
        have hzero := shared_bridge_zero P A S x f hw (leaf i) q
          (hleaf i) (hxleaf i) hxq (lz i) (z i)
          (shared_Z_bridge_image P A S x (leaf i) q (hxleaf i) hxq
            (lz i) (z i) (hlz i))
        rw [xFlow_at_q P A,dif_pos (hxleaf i)] at hp1
        change f (qToXDoubleCylinderEdge P A (leaf i) x (hxleaf i) S (Sum.inr (lz i)))=1 at hp1
        exact False.elim (zero_ne_one (hzero.symm.trans hp1))
  · rw [xFlow_at_z] at hp1
    exact False.elim (zero_ne_one hp1)

private def scaledFixedDInput (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    DirectOldXCounterexample.ASyndrome S :=
  DirectOldXCounterexample.pureXInput (DirectOldXCounterexample.AP S)
    (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
    (DirectOldXCounterexample.AX S j outer)
    (scaledAlpha S j outer 0+canonicalBasisWord (F:=BDL26Field)
      (DirectOldXCounterexample.actualErrorEdge S j outer 0))

private theorem scaledFixedDInput_raw_query (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (wordEquiv (xSyndromeEquiv (DirectOldXCounterexample.AP S) S
      (DirectOldXCounterexample.AX S j outer))).symm
      (restrictWordLinear ((literalLx (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S).syndromeRegion
        (DirectOldXCounterexample.AX S j outer)) (scaledFixedDInput S j outer).val)=
      canonicalBasisWord (F:=BDL26Field) (Sum.inr (DirectOldXCounterexample.actualHubD S j outer)) :=
  (DirectOldXCounterexample.pureXInput_raw_query (DirectOldXCounterexample.AP S)
    (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
    (DirectOldXCounterexample.AX S j outer) _).trans (scaled_fixed_D_query S j outer 0)

/-- The basis nonzero query and original whole flow budget now instantiate
the all-segment theorem, before the eventual background or error copy. -/
private theorem scaledFixedDInput_actual_exit (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    ∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,
      xFlow (DirectOldXCounterexample.AP S) S (DirectOldXCounterexample.AX S j outer)
        (DirectOldXCounterexample.originalCxWord (DirectOldXCounterexample.AP S)
          (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
          (scaledFixedDInput S j outer) (DirectOldXCounterexample.AX S j outer))=
        canonicalBasisWord (F:=BDL26Field) (rayImage (DirectOldXCounterexample.AP S)
          (DirectOldXCounterexample.AH S j outer) S (DirectOldXCounterexample.AHZ S j outer 0) c k) := by
  let P := DirectOldXCounterexample.AP S
  let A := DirectOldXCounterexample.AA S
  let R := DirectOldXCounterexample.AR S
  let x := DirectOldXCounterexample.AX S j outer
  let q := DirectOldXCounterexample.AH S j outer
  let z := DirectOldXCounterexample.AHZ S j outer
  let f := DirectOldXCounterexample.originalCxWord P A R S (scaledFixedDInput S j outer) x
  have hbd := DirectOldXCounterexample.originalCxWord_boundary P A R S (scaledFixedDInput S j outer) x
  rw [scaledFixedDInput_raw_query] at hbd
  have hw := DirectOldXCounterexample.originalCxWord_budget P A R S (scaledFixedDInput S j outer) x
  rw [scaledFixedDInput_raw_query,repair4_basis_weight_one] at hw
  have hsum (i : Fin 3) :
      (∑ k : Fin S.half,doubleCylinderCoboundary1 P x S f
        (Sum.inr (qToXSubdivisionBoundaryEdge P q x
          (DirectOldXCounterexample.AH_incident S j outer) S (z i,k))))=
        if i=0 then 1 else 0 := by
    rw [hbd]
    have hi := qToXSubdivisionBoundaryEdge_injective P q x
      (DirectOldXCounterexample.AH_incident S j outer) S
    have hz := DirectOldXCounterexample.AHZ_injective S j outer
    rw [Fintype.sum_eq_single (firstSegment S)]
    · have heq : qToXSubdivisionBoundaryEdge P q x
          (DirectOldXCounterexample.AH_incident S j outer) S (z i,firstSegment S)=
          DirectOldXCounterexample.actualHubD S j outer ↔ i=0 := by
        constructor
        · intro h
          change qToXSubdivisionBoundaryEdge P q x
            (DirectOldXCounterexample.AH_incident S j outer) S (z i,firstSegment S)=
            qToXSubdivisionBoundaryEdge P q x
              (DirectOldXCounterexample.AH_incident S j outer) S (z 0,firstSegment S) at h
          exact hz (congrArg Prod.fst (hi h))
        · intro h
          subst i
          rfl
      simp only [basis_value,Sum.inr.injEq,heq]
    · intro k hk
      have hn : (Sum.inr (qToXSubdivisionBoundaryEdge P q x
          (DirectOldXCounterexample.AH_incident S j outer) S (z i,k)) :
          DoubleCylinderFace P x S)≠Sum.inr (DirectOldXCounterexample.actualHubD S j outer) := by
        intro h
        have he := Sum.inr.inj h
        change qToXSubdivisionBoundaryEdge P q x
          (DirectOldXCounterexample.AH_incident S j outer) S (z i,k)=
          qToXSubdivisionBoundaryEdge P q x
            (DirectOldXCounterexample.AH_incident S j outer) S (z 0,firstSegment S) at he
        exact hk (congrArg Prod.snd (hi he))
      exact (basis_value _ _).trans (if_neg hn)
  apply actual_Cx_hub_ray_exit P A.toTannerSquareAdmissible S x q
    (DirectOldXCounterexample.AH_incident S j outer) z
    (DirectOldXCounterexample.AHZ_injective S j outer)
    (DirectOldXCounterexample.AL S j outer) (DirectOldXCounterexample.AL_ne_hub S j outer)
    (DirectOldXCounterexample.AL_incident S j outer) (DirectOldXCounterexample.ALZ S j outer)
    (fun _ => rfl) f hw
  · rw [hsum,hsum]
    decide
  · rw [hsum,hsum]
    decide

private theorem scaledFixedDInput_actual_pair (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    ∃ p : BDL26FiniteTannerSquare.Two × Fin S.half,
      xFlow (DirectOldXCounterexample.AP S) S (DirectOldXCounterexample.AX S j outer)
        (DirectOldXCounterexample.originalCxWord (DirectOldXCounterexample.AP S)
          (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
          (scaledFixedDInput S j outer) (DirectOldXCounterexample.AX S j outer))=
        canonicalBasisWord (F:=BDL26Field) (rayImage (DirectOldXCounterexample.AP S)
          (DirectOldXCounterexample.AH S j outer) S
          (DirectOldXCounterexample.AHZ S j outer 0) p.1 p.2) := by
  obtain ⟨c,k,h⟩ := scaledFixedDInput_actual_exit S j outer
  exact ⟨(c,k),h⟩

/-- Coordinate readback of the ORIGINAL fixed-query Cx word. This choice
selects its proven copy/segment description, not a new decoder word. -/
private def actualSelectedCut (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two × Fin S.half :=
  Classical.choose (scaledFixedDInput_actual_pair S j outer)

private theorem actualSelectedCut_spec (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    xFlow (DirectOldXCounterexample.AP S) S (DirectOldXCounterexample.AX S j outer)
      (DirectOldXCounterexample.originalCxWord (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
        (scaledFixedDInput S j outer) (DirectOldXCounterexample.AX S j outer))=
      canonicalBasisWord (F:=BDL26Field) (rayImage (DirectOldXCounterexample.AP S)
        (DirectOldXCounterexample.AH S j outer) S
        (DirectOldXCounterexample.AHZ S j outer 0)
        (actualSelectedCut S j outer).1 (actualSelectedCut S j outer).2) :=
  Classical.choose_spec (scaledFixedDInput_actual_pair S j outer)

private def actualOppositeCopy (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26FiniteTannerSquare.Two :=
  ActualCriticalStarGeometry.opposite (actualSelectedCut S j outer).1

private theorem actualOppositeCopy_ne (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    actualOppositeCopy S j outer≠(actualSelectedCut S j outer).1 :=
  ActualCriticalStarGeometry.opposite_ne _

private def actualCutZero (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : Fin S.half :=
  if (actualSelectedCut S j outer).1=0 then (actualSelectedCut S j outer).2 else firstSegment S
private def actualCutOne (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : Fin S.half :=
  if (actualSelectedCut S j outer).1=1 then (actualSelectedCut S j outer).2 else firstSegment S

/-- Fixed labels match the original finite witness: a=AHZ0,b=AHZ2,c=AHZ1. -/
private def scaledHubW (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  switchWord (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AH S j outer) S
    (DirectOldXCounterexample.AHZ S j outer 0) (DirectOldXCounterexample.AHZ S j outer 2)
    (DirectOldXCounterexample.AHZ S j outer 1) (actualCutZero S j outer)
private def scaledHubK (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  toggleWord (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AH S j outer) S
    (DirectOldXCounterexample.AHZ S j outer 0)
    (actualCutZero S j outer) (actualCutOne S j outer)

/-- The same full original directInput constructor supplies an explicit
physical preimage. W is chosen only after the fixed D-driver readback. -/
private def scaledInput (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    DirectOldXCounterexample.ASyndrome S :=
  DirectOldXCounterexample.directInput (DirectOldXCounterexample.AP S)
    (DirectOldXCounterexample.AA S) (DirectOldXCounterexample.AR S) S
    (DirectOldXCounterexample.AX S j outer) (DirectOldXCounterexample.AH S j outer)
    (scaledAlpha S j outer (actualOppositeCopy S j outer)) (scaledHubW S j outer)

private def scaledPhysicalEdge (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    DoubleCylinderEdge (DirectOldXCounterexample.AP S) (DirectOldXCounterexample.AX S j outer) S :=
  DirectOldXCounterexample.actualErrorEdge S j outer (actualOppositeCopy S j outer)

/-- Still ONE original physical old-X coordinate, not a strip perturbation. -/
private def scaledPhysical (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26CSSHamiltonian.Physical S 3 :=
  BDL26RXPhysicalCoordinateTrace.oldXPhysical S 1 (by decide) (seedQNode S j) outer
    (scaledPhysicalEdge S j outer)

end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open DirectOldXCounterexample
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26IndexedDecoder BDL26ActualFailureReadout BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
noncomputable section

/-- The true leaf prefix may end at ANY selected subdivision segment. -/
private def leafPrefix (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half) :=
  wholeCopy P q S copy+rayTail P q S copy z cut

private theorem leafPrefix_terminal (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half)
    (hu : ∀ t : QStarEdge P q,t=z) (d : BDL26FiniteTannerSquare.Two) (t : QStarEdge P q) :
    leafPrefix P q S copy z cut (d,.inl (.inr t))=0 := by
  rw [leafPrefix,Pi.add_apply,rayTail_terminal,hu t]
  simp [wholeCopy,CharTwo.add_self_eq_zero]

private theorem leafPrefix_delta (P : TannerSquarePresentation) (q : P.Q)
    (S : OddScale) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q) (cut : Fin S.half)
    (hu : ∀ t : QStarEdge P q,t=z) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
      (leafPrefix P q S copy z cut)=canonicalBasisWord (F:=BDL26Field)
        (rayCut P q S copy z cut) := by
  rw [leafPrefix,map_add]
  funext edge
  rcases edge with ⟨d,t,k⟩ | t
  · change wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (wholeCopy P q S copy) (rayCut P q S d t k)+
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (rayTail P q S copy z cut) (rayCut P q S d t k)=_
    rw [wholeCopy_delta_arm,rayTail_delta_arm,zero_add]
    rfl
  · rw [hu t]
    change wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (wholeCopy P q S copy) (Sum.inr z)+
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (rayTail P q S copy z cut) (Sum.inr z)=_
    rw [wholeCopy_delta_glue,rayTail_delta_glue]
    simp [rayCut,basis_value,CharTwo.add_self_eq_zero]

private theorem terminal_zero_global_flow (P : TannerSquarePresentation)
    (S : OddScale) (q : P.Q) (v : Word BDL26Field (QDoubleCylinderVertex P q S))
    (hv : ∀ c z,v (c,.inl (.inr z))=0) : qFlow P S q v=0 := by
  funext p
  rcases p with (⟨x,f⟩ | ⟨r,e⟩) | ⟨z,c⟩
  · exact qFlow_at_x P S q v x f
  · exact qFlow_at_q P S q r v e
  · rw [qFlow_at_z]
    by_cases hqz : P.qz q z=true
    · simp only [BDL26ReplacementSupport.rxQOutgoing,dif_pos hqz,
        rxQZDegreeOne,wordPullback_apply]
      exact hv c ⟨z,hqz⟩
    · simp only [BDL26ReplacementSupport.rxQOutgoing,dif_neg hqz]
      rfl

private theorem original_leafPrefix (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q)
    (cut : Fin S.half) (hu : ∀ t : QStarEdge P q,t=z) :
    CriticalOriginalChoice.originalChoice P A R S q (leafPrefix P q S copy z cut)=
      leafPrefix P q S copy z cut := by
  apply CriticalOriginalChoice.originalChoice_forced_zero_flow P A R S q
  · have hzero (t : QStarEdge P q) :
        rxQZDegreeOne P q t.val t.property S (leafPrefix P q S copy z cut)=0 := by
      funext d
      exact leafPrefix_terminal P q S copy z cut hu d t
    simp_rw [hzero]
    simp
  · rw [leafPrefix_delta P q S copy z cut hu,repair4_basis_weight_one]
    have hd : 0 < Fintype.card (QStarEdge P q) :=
      Fintype.card_pos_iff.mpr ⟨z⟩
    omega

private theorem leafPrefix_global_boundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (copy : BDL26FiniteTannerSquare.Two) (z : QStarEdge P q)
    (cut : Fin S.half) (hu : ∀ t : QStarEdge P q,t=z) :
    (BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
      (Fin.succ (0 : StepIndex 1))
      (directQExtension P A R S q (leafPrefix P q S copy z cut))=
      canonicalBasisWord (F:=BDL26Field) (rayImage P q S z copy cut) := by
  let v := leafPrefix P q S copy z cut
  have hd := directQExtension_boundary P A R S q v
  have hf := terminal_zero_global_flow P S q v
    (leafPrefix_terminal P q S copy z cut hu)
  have ht := CriticalDegreeOneBudget.actual_local_delta_transport P A R S q v
  have hc := leafPrefix_delta P q S copy z cut hu
  have he := extend_reindexed_basis ((literalLq P A R S).syndromeRegion q)
    (qSyndromeEquiv P S q) (rayCut P q S copy z cut)
  have hl := congrArg (extendWordLinear ((literalLq P A R S).syndromeRegion q))
    (ht.trans (congrArg (wordEquiv (qSyndromeEquiv P S q)) hc))
  funext p
  exact (congrFun hd p).trans
    ((congrArg₂ (fun a b : BDL26Field => a+b)
      (congrFun (hl.trans he) p) (congrFun hf p)).trans (add_zero _))

private theorem scaledHub_original_values (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    CriticalOriginalChoice.originalChoice (AP S) (AA S) (AR S) S (AH S j outer)
      (scaledHubW S j outer)=scaledHubW S j outer ∧
    CriticalOriginalChoice.originalChoice (AP S) (AA S) (AR S) S (AH S j outer)
      (scaledHubW S j outer+scaledHubK S j outer)=
      fun v => (scaledHubW S j outer+scaledHubK S j outer) v+1 := by
  have hn (i k : Fin 3) (h : i≠k) : AHZ S j outer i≠AHZ S j outer k :=
    fun he => h (AHZ_injective S j outer he)
  have cover (z : QStarEdge (AP S) (AH S j outer)) :
      z=AHZ S j outer 0 ∨ z=AHZ S j outer 2 ∨ z=AHZ S j outer 1 := by
    obtain ⟨i,rfl⟩ := AHZ_surjective S j outer z
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  exact original_switch_words (AP S) (AA S) (AR S) S (AH S j outer)
    (AH_degree_three S j outer) (AHZ S j outer 0) (AHZ S j outer 2)
    (AHZ S j outer 1) (hn 0 2 (by decide)) (hn 0 1 (by decide))
    (hn 2 1 (by decide)) cover (actualCutZero S j outer) (actualCutOne S j outer)

/-- The actual A query has no rectangle component at ANY ray segment. -/
private theorem scaled_first_Cx_leaf_exit (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S (scaledInput S j outer) (AX S j outer))=0 ∨
    ∃ i : Fin 3,∃ c : BDL26FiniteTannerSquare.Two,∃ k : Fin S.half,
      xFlow (AP S) S (AX S j outer)
        (originalCxWord (AP S) (AA S) (AR S) S (scaledInput S j outer) (AX S j outer))=
        canonicalBasisWord (F:=BDL26Field) (rayImage (AP S) (AL S j outer i) S
          (ALZ S j outer i) c k) := by
  let f := originalCxWord (AP S) (AA S) (AR S) S (scaledInput S j outer) (AX S j outer)
  have hquery : (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm
      (restrictWordLinear ((literalLx (AP S) (AA S) (AR S) S).syndromeRegion
        (AX S j outer)) (scaledInput S j outer).val)=
      canonicalBasisWord (F:=BDL26Field)
        (Sum.inl (actualOppositeCopy S j outer,scaledSmallFace S j outer)) :=
    (directInput_raw_query_same (AP S) (AA S) (AR S) S
      (AX S j outer) (AH S j outer) _ _).trans
        (scaledAlpha_actual_boundary S j outer (actualOppositeCopy S j outer))
  have hw := originalCxWord_budget (AP S) (AA S) (AR S) S
    (scaledInput S j outer) (AX S j outer)
  rw [hquery,repair4_basis_weight_one] at hw
  have hb := originalCxWord_boundary (AP S) (AA S) (AR S) S
    (scaledInput S j outer) (AX S j outer)
  rw [hquery] at hb
  have hr (i : Fin 3) (k : Fin S.half) :
      doubleCylinderCoboundary1 (AP S) (AX S j outer) S f
        (Sum.inr (qToXSubdivisionBoundaryEdge (AP S) (AH S j outer)
          (AX S j outer) (AH_incident S j outer) S (AHZ S j outer i,k)))=0 := by
    rw [hb]
    simp [basis_value]
  have hh := actual_Cx_zero_hub_rays (AP S) (AA S).toTannerSquareAdmissible S
    (AX S j outer) (AH S j outer) (AH_incident S j outer)
    (AHZ S j outer) (AHZ_injective S j outer)
    (AL S j outer) (AL_ne_hub S j outer) (AL_incident S j outer)
    (ALZ S j outer) (fun _ => rfl) f hw hr
  exact actual_Cx_A_leaf_classification (AP S) (AA S).toTannerSquareAdmissible S
    (AX S j outer) (AH S j outer) (AH_incident S j outer)
    (AHZ S j outer) (AHZ_surjective S j outer)
    (AL S j outer) (AL_ne_hub S j outer) (AL_incident S j outer)
    (ALZ S j outer) (fun _ => rfl) (ALZ_unique S j outer)
    (actual_Q_cover S j outer) f hw hh

/-- Full original first Cq total, retaining the optional arbitrary-cut leaf prefix. -/
private theorem scaled_first_Cq_total (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    ∃ i : Fin 3,∃ v : Word BDL26Field (QDoubleCylinderVertex (AP S) (AL S j outer i) S),
      (∀ c z,v (c,.inl (.inr z))=0) ∧
      cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S) (scaledInput S j outer).val=
        directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (scaledHubW S j outer)+
        directQExtension (AP S) (AA S) (AR S) S (AL S j outer i) v := by
  let P := AP S
  let A := AA S
  let R := AR S
  let x := AX S j outer
  let q := AH S j outer
  let alpha := scaledAlpha S j outer (actualOppositeCopy S j outer)
  let w := scaledHubW S j outer
  let f := originalCxWord P A R S (scaledInput S j outer) x
  have ha := directInput_after_Cx_global P A R S x q alpha w
  have hx (i : Fin 3) (v : Word BDL26Field (QDoubleCylinderVertex P (AL S j outer i) S))
      (hf : xFlow P S x f=(BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
        (Fin.succ (0 : StepIndex 1)) (directQExtension P A R S (AL S j outer i) v)) :
      rxSigmaAfterCx (literalData P A R S) (scaledInput S j outer).val=
        (BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
          (Fin.succ (0 : StepIndex 1)) (directQExtension P A R S q w)+
        (BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
          (Fin.succ (0 : StepIndex 1)) (directQExtension P A R S (AL S j outer i) v) := by
    funext z
    exact (congrFun ha z).trans
      ((congrArg₂ (fun a b : BDL26Field => a+b)
        (congrArg₂ (fun a b : BDL26Field => a+b)
          (congrFun (scaledAlpha_actual_flow_zero S j outer (actualOppositeCopy S j outer)) z) rfl)
        (congrFun hf z)).trans
          (congrArg (fun a : BDL26Field => a+_) (zero_add _)))
  rcases scaled_first_Cx_leaf_exit S j outer with hz | ⟨i,c,k,hi⟩
  · refine ⟨0,0,fun _ _ => rfl,?_⟩
    apply Cq_from_two_Q_boundaries P A R S (scaledInput S j outer) q (AL S j outer 0)
      (Ne.symm (AL_ne_hub S j outer 0)) w 0
    · apply hx 0 0
      have he : directQExtension P A R S (AL S j outer 0) 0=0 :=
        map_zero ((extendWordLinear ((literalLq P A R S).correctionRegion (AL S j outer 0))).comp
          (wordEquiv (qCorrectionEquiv P S (AL S j outer 0))).toLinearMap)
      have hb : (BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
          (Fin.succ (0 : StepIndex 1)) (directQExtension P A R S (AL S j outer 0) 0)=0 :=
        (congrArg ((BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
          (Fin.succ (0 : StepIndex 1))) he).trans (map_zero _)
      exact hz.trans hb.symm
    · exact (scaledHub_original_values S j outer).1
    · exact CriticalOriginalChoice.actual_original_choice_zero P A R S _
  · let v := leafPrefix P (AL S j outer i) S c (ALZ S j outer i) k
    refine ⟨i,v,leafPrefix_terminal P (AL S j outer i) S c (ALZ S j outer i) k
      (ALZ_unique S j outer i),?_⟩
    apply Cq_from_two_Q_boundaries P A R S (scaledInput S j outer) q (AL S j outer i)
      (Ne.symm (AL_ne_hub S j outer i)) w v
    · exact hx i v (hi.trans (leafPrefix_global_boundary P A R S (AL S j outer i)
        c (ALZ S j outer i) k (ALZ_unique S j outer i)).symm)
    · exact (scaledHub_original_values S j outer).1
    · exact original_leafPrefix P A R S (AL S j outer i) c (ALZ S j outer i) k
        (ALZ_unique S j outer i)

/-- Complete post-Cq cancellation, before FIRST normalization or either base D. -/
private theorem scaledInput_full_first_zero (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    rxSigmaAfterCq (literalData (AP S) (AA S) (AR S) S) (scaledInput S j outer).val=0 := by
  let P := AP S
  let A := AA S
  let R := AR S
  let x := AX S j outer
  let q := AH S j outer
  let alpha := scaledAlpha S j outer (actualOppositeCopy S j outer)
  let w := scaledHubW S j outer
  have ha := scaledAlpha_actual_flow_zero S j outer (actualOppositeCopy S j outer)
  have hw := (scaledHub_original_values S j outer).1
  rcases scaled_first_Cx_leaf_exit S j outer with hz | ⟨i,c,k,hi⟩
  · apply directInput_first_residual_zero P A R S x q (AL S j outer 0)
      (Ne.symm (AL_ne_hub S j outer 0)) alpha w 0 ha
    · have he : directQExtension P A R S (AL S j outer 0) 0=0 :=
        map_zero ((extendWordLinear ((literalLq P A R S).correctionRegion (AL S j outer 0))).comp
          (wordEquiv (qCorrectionEquiv P S (AL S j outer 0))).toLinearMap)
      have hb : (BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
          (Fin.succ (0 : StepIndex 1)) (directQExtension P A R S (AL S j outer 0) 0)=0 :=
        (congrArg ((BDL26DecoderData.family (literalDecoderData P A R S)).coboundary1
          (Fin.succ (0 : StepIndex 1))) he).trans (map_zero _)
      exact hz.trans hb.symm
    · exact hw
    · exact CriticalOriginalChoice.actual_original_choice_zero P A R S _
  · let v := leafPrefix P (AL S j outer i) S c (ALZ S j outer i) k
    apply directInput_first_residual_zero P A R S x q (AL S j outer i)
      (Ne.symm (AL_ne_hub S j outer i)) alpha w v ha
    · exact hi.trans (leafPrefix_global_boundary P A R S (AL S j outer i)
        c (ALZ S j outer i) k (ALZ_unique S j outer i)).symm
    · exact hw
    · exact original_leafPrefix P A R S (AL S j outer i) c (ALZ S j outer i) k
        (ALZ_unique S j outer i)

private def scaledActualTop (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : repair2C3Input S :=
  repair5_literal_to_actual S (scaledInput S j outer)

private def scaledDomain (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26TransposedStoppedDecoder.XSyndromeDomain S 1 :=
  ⟨(scaledActualTop S j outer).val,by
    obtain ⟨e,he⟩ := (scaledActualTop S j outer).property
    exact ⟨e,(LinearMap.congr_fun
      (indexedFamily_coboundary1 S 3 (3 : LevelIndex 3)) e).symm.trans he⟩⟩

private theorem scaledDomain_input (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    repair2C3InputOfSyndrome S (scaledDomain S j outer)=scaledActualTop S j outer :=
  Subtype.ext rfl

private theorem scaled_actual_total_boundary (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (scaledActualTop S j outer).val=(indexedFamily S 3).coboundary1 (3 : LevelIndex 3)
      (rxCorrectionTotal (D:=indexedDecoderData S 3) (i:=(2 : StepIndex 3))
        (rxData S 3 (2 : StepIndex 3) (by decide)) (scaledActualTop S j outer).val) := by
  have h := full_boundary_of_first_residual_zero (AP S) (AA S) (AR S) S
    (scaledInput S j outer) (scaledInput_full_first_zero S j outer)
  rw [CriticalOldXQueries.repair4_C3_total_to_literal,repair5_C3_upper_coboundary1]
  exact h

/-- The legal range witness above has FULL original FIRST=0 at every odd scale. -/
private theorem scaled_actual_FIRST_zero (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    firstReadout S 1 (scaledDomain S j outer)=0 := by
  have hcoarse := original_rx_coarse_zero_of_full_boundary S 3 (2 : StepIndex 3)
    (by decide) (scaledActualTop S j outer) (scaled_actual_total_boundary S j outer)
  change (actualInputs S 1 (repair2C3InputOfSyndrome S (scaledDomain S j outer)) 0).val=0
  erw [scaledDomain_input,actualInputs_step S 1 (scaledActualTop S j outer)
    (⟨0,by decide⟩ : StepIndex 1),actualInputs_top,
    BDL26OwnerIncidenceMasks.actualStep_rx S 3 (2 : StepIndex 3) (by decide)]
  exact hcoarse

end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RXDecoderAdapter BDL26DecodingGraph
open DirectOldXCounterexample
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open BDL26IndexedDecoder BDL26ActualFailureReadout BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26LocalizedHistoryErrorDescent
open BDL26RXErrorPullback BDL26RXXStarTransport
open scoped Classical BigOperators
noncomputable section

private theorem scaledPhysical_eq_chart (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    scaledPhysical S j outer=
      (xCorrectionEquiv (AP S) S (AX S j outer) (scaledPhysicalEdge S j outer)).val := by
  rfl

private abbrev scaledSigma (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  repair2C3InputOfSyndrome S (scaledDomain S j outer)
private abbrev scaledTau (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :=
  repair2C3PerturbTop S (scaledSigma S j outer)
    (repair2C3Flip S (scaledPhysical S j outer))
private def scaledTop (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    LocalizedWord S 1 (scaledSigma S j outer) (scaledTau S j outer)
      (Fin.succ (0 : StepIndex 1)) :=
  initial S 1 (scaledSigma S j outer)
    (repair2C3Flip S (scaledPhysical S j outer))
    (elementaryCenter S 1 (scaledPhysical S j outer))
    (OriginalOneStepPhiBridge.original_flip_supported S 1 (scaledPhysical S j outer))
private abbrev scaledA (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Upper S 3 (2 : StepIndex 3) :=
  BDL26LocalizedHistoryErrorDescent.first S 1 (scaledSigma S j outer) (0 : StepIndex 1)
private abbrev scaledB (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Upper S 3 (2 : StepIndex 3) :=
  BDL26LocalizedHistoryErrorDescent.second S 1 (scaledSigma S j outer)
    (scaledTau S j outer) (0 : StepIndex 1) (scaledTop S j outer)

/-- The original correlated two-history representatives differ by the SAME
one physical old-X coordinate. Their individual chosen preimages are not
replaced by alpha+QW, and no linearity of choose is used. -/
private theorem counter_original_representatives (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    scaledA S j outer+scaledB S j outer=
      repair2C3Flip S (scaledPhysical S j outer) :=
  representatives_difference S 1 (scaledSigma S j outer) (scaledTau S j outer)
    (0 : StepIndex 1) (scaledTop S j outer)

private theorem counter_actual_OneX (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    OneX S 3 (2 : StepIndex 3) (by decide) (AX S j outer)
      (scaledA S j outer) (scaledB S j outer) := by
  unfold OneX
  rw [counter_original_representatives,repair2C3Flip_basis]
  intro p hp
  have he : p=scaledPhysical S j outer := by
    by_contra hn
    have hv : (canonicalBasisWord (scaledPhysical S j outer) :
      Word BDL26Field (BDL26CSSHamiltonian.Physical S 3)) p≠0 :=
      (Finset.mem_filter.mp hp).2
    exact hv (by simp [basis_value,hn])
  subst p
  rw [scaledPhysical_eq_chart]
  change (xCorrectionEquiv (AP S) S (AX S j outer)
    (scaledPhysicalEdge S j outer)).val∈
    (BDL26RXDecoderAdapter.localX (AP S) S).correctionRegion (AX S j outer)
  exact (xCorrectionEquiv (AP S) S (AX S j outer)
    (scaledPhysicalEdge S j outer)).property

/-- All other original X blocks have zero UPDATED word, so their canonical
potential is exactly the provider's zero branch, even if the original
localization centre was chosen by an unrelated trace. -/
private theorem counter_other_X_updated_zero (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (y : (AP S).X) (hy : y≠AX S j outer) :
    restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion y)
      (updated S 3 (2 : StepIndex 3) (by decide)
        (scaledA S j outer) (scaledB S j outer))=0 := by
  have he : BDL26RXFiniteBlockTransport.Localized S 3 (2 : StepIndex 3) (by decide)
      {AX S j outer} ∅ (scaledA S j outer) (scaledB S j outer) := by
    simpa [BDL26RXFiniteBlockTransport.Localized,BDL26RXFiniteBlockTransport.xBlocks,
      BDL26RXFiniteBlockTransport.qBlocks,BDL26RXXStarTransport.OneX] using
        counter_actual_OneX S j outer
  exact BDL26RXFiniteBlockTransport.updated_other_x_zero S 3 (2 : StepIndex 3)
    (by decide) {AX S j outer} ∅ y (by simpa using hy)
    (scaledA S j outer) (scaledB S j outer) he

private theorem scaledTau_literal (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    repair5_actual_to_literal S (scaledTau S j outer)=
      directInput (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
        (scaledAlpha S j outer (actualOppositeCopy S j outer)+
          canonicalBasisWord (F:=BDL26Field) (scaledPhysicalEdge S j outer))
        (scaledHubW S j outer) := by
  rw [← directInput_add_physical_word]
  apply Subtype.ext
  rw [repair5_C3_perturb_val,repair2C3Flip_basis,scaledPhysical_eq_chart]
  change _=(scaledInput S j outer).val+_
  rw [directXExtension_basis]
  rfl

/-- Both histories invoke the SAME ORIGINAL Cx chooser on the same D query.
The background hub word was selected only after this fixed driver's coordinate. -/
private theorem scaled_second_original_Cx (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    originalCxWord (AP S) (AA S) (AR S) S
      (repair5_actual_to_literal S (scaledTau S j outer)) (AX S j outer)=
    originalCxWord (AP S) (AA S) (AR S) S
      (scaledFixedDInput S j outer) (AX S j outer) := by
  rw [scaledTau_literal,directInput_original_Cx]
  apply originalCxWord_same_query
  apply (wordEquiv (xSyndromeEquiv (AP S) S (AX S j outer))).symm.injective
  exact ((pureXInput_raw_query (AP S) (AA S) (AR S) S (AX S j outer) _).trans
    (scaled_fixed_D_query S j outer (actualOppositeCopy S j outer))).trans
      (scaledFixedDInput_raw_query S j outer).symm

private theorem scaled_second_Cx_hub_exit (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    xFlow (AP S) S (AX S j outer)
      (originalCxWord (AP S) (AA S) (AR S) S
        (repair5_actual_to_literal S (scaledTau S j outer)) (AX S j outer))=
      canonicalBasisWord (F:=BDL26Field) (rayImage (AP S) (AH S j outer) S
        (AHZ S j outer 0) (actualSelectedCut S j outer).1 (actualSelectedCut S j outer).2) := by
  rw [scaled_second_original_Cx]
  exact actualSelectedCut_spec S j outer

private theorem rawQRead_ray_same (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : P.Q) (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    rawQRead P A R S q (canonicalBasisWord (F:=BDL26Field) (rayImage P q S z c k))=
      canonicalBasisWord (F:=BDL26Field) (rayCut P q S c z k) := by
  funext e
  change canonicalBasisWord (F:=BDL26Field) (rayImage P q S z c k)
      (Sum.inl (Sum.inr ⟨q,e⟩))=canonicalBasisWord (F:=BDL26Field) (rayCut P q S c z k) e
  have he : (Sum.inl (Sum.inr ⟨q,e⟩) : RX2 P S)=rayImage P q S z c k ↔
      e=rayCut P q S c z k := by
    constructor
    · intro h
      exact sigma_same_index_inj (I:=P.Q) (A:=fun r => QDoubleCylinderEdge P r S)
        (i:=q) e (rayCut P q S c z k) (Sum.inr.inj (Sum.inl.inj h))
    · intro h
      subst e
      rfl
  by_cases h : e=rayCut P q S c z k
  · exact ((basis_value _ _).trans (if_pos (he.mpr h))).trans
      ((basis_value _ _).trans (if_pos h)).symm
  · exact ((basis_value _ _).trans (if_neg (fun h' => h (he.mp h')))).trans
      ((basis_value _ _).trans (if_neg h)).symm

private theorem rawQRead_ray_other (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q r : P.Q) (hr : r≠q)
    (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two) (k : Fin S.half) :
    rawQRead P A R S r (canonicalBasisWord (F:=BDL26Field) (rayImage P q S z c k))=0 := by
  funext e
  change canonicalBasisWord (F:=BDL26Field) (rayImage P q S z c k)
    (Sum.inl (Sum.inr ⟨r,e⟩))=0
  exact (basis_value _ _).trans (if_neg (by
    intro h
    exact hr (congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj h)))))

private theorem scaledHubK_gradient (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
      (scaledHubK S j outer)=
      canonicalBasisWord (F:=BDL26Field) (rayCut (AP S) (AH S j outer) S
        (actualOppositeCopy S j outer) (AHZ S j outer 0) (firstSegment S))+
      canonicalBasisWord (F:=BDL26Field) (rayCut (AP S) (AH S j outer) S
        (actualSelectedCut S j outer).1 (AHZ S j outer 0) (actualSelectedCut S j outer).2) := by
  rw [scaledHubK,toggleWord_delta]
  rcases two_eq_zero_or_one (actualSelectedCut S j outer).1 with hc | hc
  · simp only [actualCutZero,actualCutOne,actualOppositeCopy,hc,if_pos rfl,
      show ¬(0 : BDL26FiniteTannerSquare.Two)=1 from by decide,if_false]
    simp only [ActualCriticalStarGeometry.opposite]
    exact add_comm _ _
  · simp only [actualCutZero,actualCutOne,actualOppositeCopy,hc,if_pos rfl,
      show ¬(1 : BDL26FiniteTannerSquare.Two)=0 from by decide,if_false]
    rfl

/-- Complete post-Cx word: its outgoing Z part is retained in the middle term. -/
private theorem scaled_second_after_Cx_entire (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    rxSigmaAfterCx (literalData (AP S) (AA S) (AR S) S) (scaledTau S j outer).val=
      (show (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).Cochain2
        (Fin.succ (0 : StepIndex 1)) from fun z =>
          canonicalBasisWord (F:=BDL26Field) (rayImage (AP S) (AH S j outer) S
            (AHZ S j outer 0) (actualOppositeCopy S j outer) (firstSegment S)) z)+
      (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
        (Fin.succ (0 : StepIndex 1))
          (directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (scaledHubW S j outer))+
      (show (BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).Cochain2
        (Fin.succ (0 : StepIndex 1)) from fun z =>
          canonicalBasisWord (F:=BDL26Field) (rayImage (AP S) (AH S j outer) S
            (AHZ S j outer 0) (actualSelectedCut S j outer).1 (actualSelectedCut S j outer).2) z) := by
  apply original_after_Cx_from_columns (AP S) (AA S) (AR S) S
    (AX S j outer) (AH S j outer)
    (scaledAlpha S j outer (actualOppositeCopy S j outer))
    (canonicalBasisWord (F:=BDL26Field) (scaledPhysicalEdge S j outer))
    (scaledHubW S j outer) (repair5_actual_to_literal S (scaledTau S j outer))
  · exact scaledTau_literal S j outer
  · exact scaledAlpha_actual_flow_zero S j outer (actualOppositeCopy S j outer)
  · exact actualError_flow S j outer (actualOppositeCopy S j outer)
  · exact scaled_second_Cx_hub_exit S j outer

/-- Only the genuine hub Q query is δ(W+K); no outgoing Z coordinate is erased. -/
private theorem scaled_second_Cq_total (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S) (scaledTau S j outer).val=
      directQExtension (AP S) (AA S) (AR S) S (AH S j outer)
        (fun v => (scaledHubW S j outer+scaledHubK S j outer) v+1) := by
  have hraw (q : (AP S).Q) :
      rawQRead (AP S) (AA S) (AR S) S q
        (rxSigmaAfterCx (literalData (AP S) (AA S) (AR S) S) (scaledTau S j outer).val)=
      rawQRead (AP S) (AA S) (AR S) S q
        (canonicalBasisWord (F:=BDL26Field) (rayImage (AP S) (AH S j outer) S
          (AHZ S j outer 0) (actualOppositeCopy S j outer) (firstSegment S)))+
      rawQRead (AP S) (AA S) (AR S) S q
        ((BDL26DecoderData.family (literalDecoderData (AP S) (AA S) (AR S) S)).coboundary1
          (Fin.succ (0 : StepIndex 1))
            (directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (scaledHubW S j outer)))+
      rawQRead (AP S) (AA S) (AR S) S q
        (canonicalBasisWord (F:=BDL26Field) (rayImage (AP S) (AH S j outer) S
          (AHZ S j outer 0) (actualSelectedCut S j outer).1 (actualSelectedCut S j outer).2)) := by
    funext e
    exact congrFun (scaled_second_after_Cx_entire S j outer) (Sum.inl (Sum.inr ⟨q,e⟩))
  have hq : rawQRead (AP S) (AA S) (AR S) S (AH S j outer)
      (rxSigmaAfterCx (literalData (AP S) (AA S) (AR S) S) (scaledTau S j outer).val)=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
        (scaledHubW S j outer+scaledHubK S j outer) := by
    rw [hraw,rawQRead_ray_same,rawQRead_Qextension_same,rawQRead_ray_same,
      map_add,scaledHubK_gradient]
    abel
  have ho (q : (AP S).Q) (hn : q≠AH S j outer) :
      rawQRead (AP S) (AA S) (AR S) S q
        (rxSigmaAfterCx (literalData (AP S) (AA S) (AR S) S) (scaledTau S j outer).val)=0 := by
    rw [hraw,rawQRead_ray_other (AP S) (AA S) (AR S) S _ q hn,
      rawQRead_Qextension_other (AP S) (AA S) (AR S) S _ q hn,
      rawQRead_ray_other (AP S) (AA S) (AR S) S _ q hn,zero_add,zero_add]
  exact (Cq_from_one_Q_query (AP S) (AA S) (AR S) S
    (repair5_actual_to_literal S (scaledTau S j outer)) (AH S j outer)
    (scaledHubW S j outer+scaledHubK S j outer) hq ho).trans
      (congrArg (directQExtension (AP S) (AA S) (AR S) S (AH S j outer))
        (scaledHub_original_values S j outer).2)

private theorem scaled_first_hub_pullback_zero (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    rawQRead (AP S) (AA S) (AR S) S (AH S j outer)
      (xFlow (AP S) S (AX S j outer)
        (originalCxWord (AP S) (AA S) (AR S) S (scaledInput S j outer) (AX S j outer)))=0 := by
  rcases scaled_first_Cx_leaf_exit S j outer with h0 | ⟨i,c,k,hc⟩
  · exact (congrArg (rawQRead (AP S) (AA S) (AR S) S (AH S j outer)) h0).trans (map_zero _)
  · exact (congrArg (rawQRead (AP S) (AA S) (AR S) S (AH S j outer)) hc).trans
      (rawQRead_ray_other (AP S) (AA S) (AR S) S (AL S j outer i) (AH S j outer)
        (Ne.symm (AL_ne_hub S j outer i)) (ALZ S j outer i) c k)

end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
namespace OriginalOldXScaleExtension
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26RXDecoderAdapter
open BDL26DecodingGraph BDL26LocalizedHistoryErrorDescent BDL26ActualFailureReadout
open BDL26RXErrorPullback BDL26RXXStarTransport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26OwnerIncidenceMasks BDL26CSSHamiltonian
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26RXPhysicalCoordinateTrace
open DirectOldXCounterexample
open MultiscaleDecoder.RXCoarseGraining MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section

/- Full original Phi and lower-word closure. Original localization membership,
chosen physical preimages, both base D calls, and all coordinates are retained. -/

private def scaledX0 (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    Finset (AP S).X :=
  {BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
    (scaledTop S j outer).center}


private def scaledVeff (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    LocalPotential S (2 : StepIndex 3) (AX S j outer) :=
  if AX S j outer∈scaledX0 S j outer then
    localPotential S 3 (2 : StepIndex 3) (by decide) (AX S j outer)
      (scaledA S j outer) (scaledB S j outer) else 0

private theorem scaled_accumulated_entire (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    accumulated S 1 (scaledDomain S j outer)
        (scaledPhysical S j outer)=
      (rxContract S 3 (2 : StepIndex 3) (by decide)).support_decomposition.cxLift0
        (AX S j outer) (scaledVeff S j outer) := by
  rw [OriginalOneStepPhiBridge.accumulated_eq_original_Phi]
  exact original_fullPhi_single_active S 3 (2 : StepIndex 3) (by decide)
    (scaledX0 S j outer) (AX S j outer)
    (scaledA S j outer) (scaledB S j outer)
    (counter_other_X_updated_zero S j outer)


private theorem scaled_original_localized (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26RXPhysicalStarTransport.Localized S 3 (2 : StepIndex 3)
      (scaledTop S j outer).center
      (scaledA S j outer) (scaledB S j outer) := by
  change hammingSupport (scaledA S j outer+scaledB S j outer) ⊆ _
  rw [counter_original_representatives]
  exact (scaledTop S j outer).supported


private theorem scaled_fullPhi_boundary_X (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
      (AX S j outer))
      ((indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
        (accumulated S 1 (scaledDomain S j outer)
          (scaledPhysical S j outer)))=
    restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
      (AX S j outer))
      (updated S 3 (2 : StepIndex 3) (by decide)
        (scaledA S j outer) (scaledB S j outer)) := by
  have hl := BDL26RXPhysicalStarTransport.localized_blocks S 3 (2 : StepIndex 3)
    (by decide) (scaledTop S j outer).center
    (scaledA S j outer) (scaledB S j outer)
    (scaled_original_localized S j outer)
  have hz := BDL26RXFiniteBlockTransport.remainder_x_zero S 3 (2 : StepIndex 3)
    (by decide) (scaledX0 S j outer)
    (BDL26RXXStarTransport.incidentQ S 3 (2 : StepIndex 3)
      (BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
        (scaledTop S j outer).center))
    (AX S j outer) (scaledA S j outer) (scaledB S j outer) hl
  rw [BDL26RXFiniteBlockTransport.R,map_add] at hz
  have hPhi := OriginalOneStepPhiBridge.accumulated_eq_original_Phi S
    (scaledDomain S j outer) (scaledPhysical S j outer)
  change accumulated S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)=
    BDL26RXFiniteBlockTransport.Phi S 3 (2 : StepIndex 3) (by decide)
      (scaledX0 S j outer) (scaledA S j outer) (scaledB S j outer) at hPhi
  rw [← hPhi] at hz
  funext a
  have ha := congrFun hz a
  let u := (restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
      (AX S j outer)) (updated S 3 (2 : StepIndex 3) (by decide)
        (scaledA S j outer) (scaledB S j outer))) a
  let d := (restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
      (AX S j outer)) ((indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
        (accumulated S 1 (scaledDomain S j outer)
          (scaledPhysical S j outer)))) a
  change u+d=0 at ha
  change d=u
  calc
    d=(u+u)+d := by rw [CharTwo.add_self_eq_zero,zero_add]
    _=u+(u+d) := add_assoc _ _ _
    _=u+0 := congrArg (fun z => u+z) ha
    _=u := add_zero _

private theorem scaledVeff_boundary (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (rxContract S 3 (2 : StepIndex 3) (by decide)).rx_local_complexes.cxDelta0
        (AX S j outer) (scaledVeff S j outer)=
      restrictWordLinear ((rxLx S 3 (2 : StepIndex 3) (by decide)).correctionRegion
        (AX S j outer))
        (updated S 3 (2 : StepIndex 3) (by decide)
          (scaledA S j outer) (scaledB S j outer)) := by
  have h := scaled_fullPhi_boundary_X S j outer
  rw [scaled_accumulated_entire] at h
  exact ((rxContract S 3 (2 : StepIndex 3) (by decide)).support_decomposition.cxDelta0_restriction (AX S j outer) (scaledVeff S j outer)).symm.trans h

private theorem scaled_updated_literal (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    updated S 3 (2 : StepIndex 3) (by decide)
        (scaledA S j outer) (scaledB S j outer)=
      repair2C3Flip S (scaledPhysical S j outer)+
        rxCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (scaledSigma S j outer).val+
        rxCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (scaledTau S j outer).val := by
  have h := CriticalOldXQueries.actualC3_updated S (scaledSigma S j outer)
    (scaledTau S j outer) (scaledTop S j outer)
  have ha := (CriticalOldXQueries.actualC3_correction S (scaledSigma S j outer)).trans
    (CriticalOldXQueries.repair4_C3_total_to_literal S (scaledSigma S j outer))
  have hb := (CriticalOldXQueries.actualC3_correction S (scaledTau S j outer)).trans
    (CriticalOldXQueries.repair4_C3_total_to_literal S (scaledTau S j outer))
  funext z
  have hz := congrFun h z
  rw [congrFun ha z,congrFun hb z] at hz
  exact hz


private theorem scaledVeff_raw_boundary (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    wordLinearMapTranspose (doubleCylinderBoundary1 (AP S) (AX S j outer) S)
        (scaledVeff S j outer)=
      canonicalBasisWord (scaledPhysicalEdge S j outer)+
        originalCxWord (AP S) (AA S) (AR S) S
          (scaledInput S j outer) (AX S j outer)+
        originalCxWord (AP S) (AA S) (AR S) S
          (repair5_actual_to_literal S (scaledTau S j outer)) (AX S j outer) := by
  have h := scaledVeff_boundary S j outer
  funext edge
  have hd := localCx_delta0_apply (AP S) S (AX S j outer)
    (scaledVeff S j outer) edge
  have hv := congrFun (scaled_updated_literal S j outer)
    (xCorrectionEquiv (AP S) S (AX S j outer) edge).val
  have hs := original_total_X_chart (AP S) (AA S) (AR S) S
    (scaledInput S j outer).val (scaledInput S j outer).property
    (AX S j outer) edge
  have ht := original_total_X_chart (AP S) (AA S) (AR S) S
    (repair5_actual_to_literal S (scaledTau S j outer)).val
    (repair5_actual_to_literal S (scaledTau S j outer)).property
    (AX S j outer) edge
  have hflip := congrFun (repair2C3Flip_basis S (scaledPhysical S j outer))
    (xCorrectionEquiv (AP S) S (AX S j outer) edge).val
  have hb : (canonicalBasisWord (scaledPhysical S j outer) :
      Word BDL26Field (BDL26CSSHamiltonian.Physical S 3))
      (xCorrectionEquiv (AP S) S (AX S j outer) edge).val=
      (canonicalBasisWord (scaledPhysicalEdge S j outer) :
        Word BDL26Field (DoubleCylinderEdge (AP S) (AX S j outer) S)) edge := by
    have hc := congrArg (fun q : BDL26CSSHamiltonian.Physical S 3 =>
      canonicalBasisWord (F:=BDL26Field) q
        (xCorrectionEquiv (AP S) S (AX S j outer) edge).val)
      (scaledPhysical_eq_chart S j outer)
    have hi : (xCorrectionEquiv (AP S) S (AX S j outer) edge).val=
        (xCorrectionEquiv (AP S) S (AX S j outer)
          (scaledPhysicalEdge S j outer)).val ↔
        edge=scaledPhysicalEdge S j outer := by
      constructor
      · intro he
        exact (xCorrectionEquiv (AP S) S (AX S j outer)).injective (Subtype.ext he)
      · intro he
        subst edge
        rfl
    by_cases he : edge=scaledPhysicalEdge S j outer
    · exact (hc.trans ((basis_value _ _).trans (if_pos (hi.mpr he)))).trans
        ((basis_value _ _).trans (if_pos he)).symm
    · exact (hc.trans ((basis_value _ _).trans (if_neg (fun h => he (hi.mp h))))).trans
        ((basis_value _ _).trans (if_neg he)).symm
  calc
    _ = ((rxContract S 3 (2 : StepIndex 3) (by decide)).rx_local_complexes.cxDelta0
        (AX S j outer) (scaledVeff S j outer))
        (xCorrectionEquiv (AP S) S (AX S j outer) edge) := hd.symm
    _ = updated S 3 (2 : StepIndex 3) (by decide)
        (scaledA S j outer) (scaledB S j outer)
        (xCorrectionEquiv (AP S) S (AX S j outer) edge).val :=
      congrFun h (xCorrectionEquiv (AP S) S (AX S j outer) edge)
    _ = _ := hv.trans (congrArg₂ (fun a b : BDL26Field => a+b)
      (congrArg₂ (fun a b : BDL26Field => a+b) (hflip.trans hb) hs) ht)

private def scaledHubPotential (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : Word BDL26Field (QDoubleCylinderVertex (AP S) (AH S j outer) S) :=
  rxXQDegreeZero (AP S) (AA S).toTannerSquareAdmissible (AH S j outer)
    (AX S j outer) (AH_incident S j outer) S (scaledVeff S j outer)


private theorem scaled_hub_potential_gradient (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
      (scaledHubPotential S j outer)=
    wordLinearMapTranspose (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S)
      (scaledHubK S j outer) := by
  let T := rxXQDegreeOne (AP S) (AA S).toTannerSquareAdmissible
    (AH S j outer) (AX S j outer) (AH_incident S j outer) S
  let e : Word BDL26Field (DoubleCylinderEdge (AP S) (AX S j outer) S) :=
    canonicalBasisWord (scaledPhysicalEdge S j outer)
  let f := originalCxWord (AP S) (AA S) (AR S) S (scaledInput S j outer) (AX S j outer)
  let g := originalCxWord (AP S) (AA S) (AR S) S
    (repair5_actual_to_literal S (scaledTau S j outer)) (AX S j outer)
  let Q := rawQRead (AP S) (AA S) (AR S) S (AH S j outer)
  have hcomm := LinearMap.congr_fun (rxXQ_commutes (AP S)
    (AA S).toTannerSquareAdmissible (AH S j outer) (AX S j outer)
    (AH_incident S j outer) S) (scaledVeff S j outer)
  have he : T e=canonicalBasisWord (F:=BDL26Field)
      (rayCut (AP S) (AH S j outer) S (actualOppositeCopy S j outer)
        (AHZ S j outer 0) (firstSegment S)) :=
    (rawQRead_Xflow (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
      (AH_incident S j outer) e).symm.trans
      ((congrArg Q (actualError_flow S j outer (actualOppositeCopy S j outer))).trans
        (rawQRead_ray_same (AP S) (AA S) (AR S) S (AH S j outer)
          (AHZ S j outer 0) (actualOppositeCopy S j outer) (firstSegment S)))
  have hf : T f=0 :=
    (rawQRead_Xflow (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
      (AH_incident S j outer) f).symm.trans (scaled_first_hub_pullback_zero S j outer)
  have hg : T g=canonicalBasisWord (F:=BDL26Field)
      (rayCut (AP S) (AH S j outer) S (actualSelectedCut S j outer).1
        (AHZ S j outer 0) (actualSelectedCut S j outer).2) :=
    (rawQRead_Xflow (AP S) (AA S) (AR S) S (AX S j outer) (AH S j outer)
      (AH_incident S j outer) g).symm.trans
      ((congrArg Q (scaled_second_Cx_hub_exit S j outer)).trans
        (rawQRead_ray_same (AP S) (AA S) (AR S) S (AH S j outer)
          (AHZ S j outer 0) (actualSelectedCut S j outer).1 (actualSelectedCut S j outer).2))
  have hout : T (e+f+g)=
      canonicalBasisWord (F:=BDL26Field)
        (rayCut (AP S) (AH S j outer) S (actualOppositeCopy S j outer)
          (AHZ S j outer 0) (firstSegment S))+
      canonicalBasisWord (F:=BDL26Field)
        (rayCut (AP S) (AH S j outer) S (actualSelectedCut S j outer).1
          (AHZ S j outer 0) (actualSelectedCut S j outer).2) := by
    rw [map_add,map_add,he,hf,hg,add_zero]
  exact hcomm.trans ((congrArg T (scaledVeff_raw_boundary S j outer)).trans
    (hout.trans (scaledHubK_gradient S j outer).symm))

private def scaledBeta (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) : BDL26Field :=
  scaledHubPotential S j outer (0,.inl (.inl ()))

private theorem scaled_hub_potential_entire (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    scaledHubPotential S j outer=
      fun v => scaledHubK S j outer v+scaledBeta S j outer := by
  let f := scaledHubPotential S j outer+scaledHubK S j outer
  have hf : wordLinearMapTranspose
      (qDoubleCylinderBoundary1 (AP S) (AH S j outer) S) f=0 := by
    rw [map_add,scaled_hub_potential_gradient,repair3_word_add_self]
  have hc := word_eq_root_of_graphCoboundary_eq_zero
    (qDoubleCylinderEdgeStart (AP S) (AH S j outer) S)
    (qDoubleCylinderEdgeEnd (AP S) (AH S j outer) S)
    (0,.inl (.inl ()))
    (qDoubleCylinderPath (AP S) (AA S).toTannerSquareAdmissible (AH S j outer) S) f hf
  funext v
  have hv := hc v
  have hroot : scaledHubK S j outer (0,.inl (.inl ()))=0 := by
    unfold scaledHubK toggleWord
    rw [Pi.add_apply,rayTail_center,rayTail_center,zero_add]
  change scaledHubPotential S j outer v+scaledHubK S j outer v=
    scaledHubPotential S j outer (0,.inl (.inl ()))+
      scaledHubK S j outer (0,.inl (.inl ())) at hv
  rw [hroot,add_zero] at hv
  calc
    scaledHubPotential S j outer v=
        (scaledHubPotential S j outer v+scaledHubK S j outer v)+
          scaledHubK S j outer v := by rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
    _=scaledBeta S j outer+scaledHubK S j outer v :=
      congrArg (fun a => a+scaledHubK S j outer v) hv
    _=_ := add_comm _ _

private theorem scaled_fullPhi_terminal (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (q : (AP S).Q)
    (hx : (AP S).xq (AX S j outer) q=true)
    (root z : QStarEdge (AP S) q) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
      (BDL26ActualFailureReadout.accumulated S 1 (scaledDomain S j outer)
        (scaledPhysical S j outer))
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide)
        (.inr ⟨q,(c,.inl (.inr z))⟩))=
      scaledVeff S j outer
        (qToXDoubleCylinderVertexAtRoot (AP S) q (AX S j outer) hx S root
          (c,.inl (.inr z))) := by
  let p := (Sum.inr ⟨q,(c,Sum.inl (Sum.inr z))⟩ : RX1 (AP S) S)
  let V := (rxContract S 3 (2 : StepIndex 3) (by decide)).support_decomposition.cxLift0
    (AX S j outer) (scaledVeff S j outer)
  have hacc := congrArg (fun v : (indexedFamily S 3).Cochain0 (3 : LevelIndex 3) =>
    (indexedFamily S 3).coboundary0 (3 : LevelIndex 3) v
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) p))
        (scaled_accumulated_entire S j outer)
  have hchart := actual_delta0_on_RX_charts S 3 (2 : StepIndex 3) (by decide) V p
  have hlift := actual_Xlift_on_RX_chart S 3 (2 : StepIndex 3) (by decide)
    (AX S j outer) (scaledVeff S j outer)
  have he := congrArg (fun w : Word BDL26Field (RX0 (AP S) S) =>
    BDL26ReplacementCochainMaps.rxCoboundary0 (AP S) S w p) hlift
  exact hacc.trans (hchart.trans (he.trans
    (raw_Xlift_delta_at_terminal (AP S) S (AX S j outer) q hx root z c
      (scaledVeff S j outer))))

private theorem scaled_leaf_Phi_value (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
      (BDL26ActualFailureReadout.accumulated S 1 (scaledDomain S j outer)
        (scaledPhysical S j outer))
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide)
        (.inr ⟨AL S j outer i,(c,.inl (.inr (ALZ S j outer i)))⟩))=
      (if i=0 then 1 else 0)+scaledBeta S j outer := by
  rw [scaled_fullPhi_terminal S j outer (AL S j outer i)
    (AL_incident S j outer i) (ALZ S j outer i) (ALZ S j outer i) c]
  have hi := ActualCriticalStarGeometry.shared_terminal_same_image (AP S) S
    (AX S j outer) (AL S j outer i) (AH S j outer)
    (AL_incident S j outer i) (AH_incident S j outer) (AZ S j outer i)
    (AL_check S j outer i) (AH_check S j outer i)
    (ALZ S j outer i) (AHZ S j outer i) c
  change qToXDoubleCylinderVertexAtRoot (AP S) (AL S j outer i) (AX S j outer)
      (AL_incident S j outer i) S (ALZ S j outer i)
      (c,Sum.inl (Sum.inr (ALZ S j outer i)))=
    qToXDoubleCylinderVertexAtRoot (AP S) (AH S j outer) (AX S j outer)
      (AH_incident S j outer) S (AHZ S j outer i)
      (c,Sum.inl (Sum.inr (AHZ S j outer i))) at hi
  have he : scaledVeff S j outer
      (qToXDoubleCylinderVertexAtRoot (AP S) (AH S j outer) (AX S j outer)
        (AH_incident S j outer) S (AHZ S j outer i)
        (c,.inl (.inr (AHZ S j outer i))))=
      scaledHubPotential S j outer (c,.inl (.inr (AHZ S j outer i))) := by rfl
  calc
    _ = scaledHubPotential S j outer (c,Sum.inl (Sum.inr (AHZ S j outer i))) :=
      (congrArg (scaledVeff S j outer) hi).trans he
    _ = scaledHubK S j outer (c,Sum.inl (Sum.inr (AHZ S j outer i)))+
        scaledBeta S j outer :=
      congrFun (scaled_hub_potential_entire S j outer)
        (c,Sum.inl (Sum.inr (AHZ S j outer i)))
    _ = _ := by
      congr 1
      have hinj := AHZ_injective S j outer
      fin_cases i <;> rcases two_eq_zero_or_one c with hc | hc <;>
        simp [scaledHubK,toggleWord,rayTail,
          canonicalBasisWord,Pi.single_apply,hinj.eq_iff,hc]

private theorem scaled_hub_Phi_value (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
      (BDL26ActualFailureReadout.accumulated S 1 (scaledDomain S j outer)
        (scaledPhysical S j outer))
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide)
        (.inr ⟨AH S j outer,(c,.inl (.inr (AHZ S j outer i)))⟩))=
      (if i=0 then 1 else 0)+scaledBeta S j outer := by
  rw [scaled_fullPhi_terminal S j outer (AH S j outer) (AH_incident S j outer)
    (AHZ S j outer i) (AHZ S j outer i) c]
  change scaledHubPotential S j outer (c,.inl (.inr (AHZ S j outer i)))=_
  rw [scaled_hub_potential_entire]
  congr 1
  have hinj := AHZ_injective S j outer
  fin_cases i <;> rcases two_eq_zero_or_one c with hc | hc <;>
    simp [scaledHubK,toggleWord,rayTail,
      canonicalBasisWord,Pi.single_apply,hinj.eq_iff,hc]

private theorem scaledVeff_nonzero (S : OddScale) (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    scaledVeff S j outer≠0 := by
  intro hz
  have h := scaled_hub_potential_gradient S j outer
  have hp : scaledHubPotential S j outer=0 := by
    unfold scaledHubPotential
    rw [hz,map_zero]
  rw [hp,map_zero,scaledHubK_gradient] at h
  have he := congrFun h (rayCut (AP S) (AH S j outer) S
    (actualOppositeCopy S j outer) (AHZ S j outer 0) (firstSegment S))
  have hn : rayCut (AP S) (AH S j outer) S (actualOppositeCopy S j outer)
      (AHZ S j outer 0) (firstSegment S)≠
    rayCut (AP S) (AH S j outer) S (actualSelectedCut S j outer).1
      (AHZ S j outer 0) (actualSelectedCut S j outer).2 := by
    intro hh
    exact actualOppositeCopy_ne S j outer
      (congrArg (fun e : QDoubleCylinderEdge (AP S) (AH S j outer) S =>
        match e with | .inl p => p.1 | .inr _ => 0) hh)
  have he' : (0 : BDL26Field)=1 := by
    simpa [Pi.add_apply,basis_value,hn] using he
  exact zero_ne_one he'

private theorem scaled_original_parent (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
      (scaledTop S j outer).center=AX S j outer := by
  have hm : AX S j outer∈scaledX0 S j outer := by
    by_contra hn
    apply scaledVeff_nonzero S j outer
    exact if_neg hn
  exact (Finset.mem_singleton.mp hm).symm

private theorem scaled_descent_entire_L (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (descent S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)).word=
      BDL26RXPhysicalStarTransport.L S 3 (2 : StepIndex 3) (by decide)
        (scaledTop S j outer).center
        (scaledA S j outer) (scaledB S j outer) := by
  change (path S 1 (scaledSigma S j outer) (scaledTau S j outer)
    (scaledTop S j outer) (0 : StepIndex 1).castSucc).word=_
  rw [path_step]
  have hp : path S 1 (scaledSigma S j outer) (scaledTau S j outer)
      (scaledTop S j outer) (Fin.succ (0 : StepIndex 1))=scaledTop S j outer :=
    path_top S 1 (scaledSigma S j outer)
      (scaledTau S j outer) (scaledTop S j outer)
  rw [hp]
  exact (step_RX_fixed S 1 (scaledSigma S j outer) (scaledTau S j outer)
    (0 : StepIndex 1) (by decide) (scaledTop S j outer)).1


private theorem scaled_descent_supported (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    hammingSupport (descent S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)).word ⊆
      {AL S j outer 0,AH S j outer,AL S j outer 1,AL S j outer 2} := by
  rw [scaled_descent_entire_L]
  have hs := BDL26RXPhysicalStarTransport.lower_supported S 3 (2 : StepIndex 3)
    (by decide) (scaledTop S j outer).center
    (scaledA S j outer) (scaledB S j outer)
    (scaled_original_localized S j outer)
  rw [scaled_original_parent] at hs
  intro q hq
  have hi := (BDL26RXPhysicalStarTransport.mem_physicalXStar (AP S)
    (AX S j outer) q).mp (hs hq)
  rcases actual_Q_cover S j outer q hi with h | ⟨i,h⟩
  · simp [h]
  · fin_cases i <;> simp [h]

private theorem scaled_updated_at_Q_vertex (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (q : (AP S).Q)
    (v : QDoubleCylinderVertex (AP S) q S) :
    updated S 3 (2 : StepIndex 3) (by decide)
      (scaledA S j outer) (scaledB S j outer)
      (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) (.inr ⟨q,v⟩))=
      cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (scaledInput S j outer).val (.inr ⟨q,v⟩)+
      cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (scaledTau S j outer).val (.inr ⟨q,v⟩) := by
  let coord := rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) (Sum.inr ⟨q,v⟩)
  have hu := congrFun (scaled_updated_literal S j outer) coord
  have hzraw := congrFun (CriticalOldXQueries.original_single_X_zero_at_Cq
    (AP S) (AA S) (AR S) S (AX S j outer)
    (xCorrectionEquiv (AP S) S (AX S j outer) (scaledPhysicalEdge S j outer)) q)
      (qCorrectionEquiv (AP S) S q v)
  have hz : (canonicalBasisWord (scaledPhysical S j outer) :
      Word BDL26Field (BDL26CSSHamiltonian.Physical S 3)) coord=0 :=
    (congrArg (fun p : BDL26CSSHamiltonian.Physical S 3 =>
      canonicalBasisWord (F:=BDL26Field) p coord)
        (scaledPhysical_eq_chart S j outer)).trans hzraw
  have hf := (congrFun (repair2C3Flip_basis S (scaledPhysical S j outer)) coord).trans hz
  have hs := original_total_Q_chart (AP S) (AA S) (AR S) S
    (scaledInput S j outer).val q v
  have ht := original_total_Q_chart (AP S) (AA S) (AR S) S
    (repair5_actual_to_literal S (scaledTau S j outer)).val q v
  exact hu.trans ((congrArg₂ (fun a b : BDL26Field => a+b)
    (congrArg₂ (fun a b : BDL26Field => a+b) hf hs) ht).trans
      (congrArg (fun a : BDL26Field => a+
        cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
          (scaledTau S j outer).val (Sum.inr ⟨q,v⟩)) (zero_add _)))

private theorem scaled_first_Cq_leaf_terminal (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two)
    (z : QStarEdge (AP S) (AL S j outer i)) :
    cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (scaledInput S j outer).val
      (.inr ⟨AL S j outer i,(c,.inl (.inr z))⟩)=0 := by
  obtain ⟨k,v,hv,hq⟩ := scaled_first_Cq_total S j outer
  let coord := (Sum.inr ⟨AL S j outer i,(c,Sum.inl (Sum.inr z))⟩ : RX1 (AP S) S)
  have he : cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (scaledInput S j outer).val coord=
      directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (scaledHubW S j outer) coord+
      directQExtension (AP S) (AA S) (AR S) S (AL S j outer k) v coord :=
    congrFun hq coord
  have hh0 := directQExtension_at_other (AP S) (AA S) (AR S) S
    (AH S j outer) (AL S j outer i) (AL_ne_hub S j outer i)
      (scaledHubW S j outer) (c,Sum.inl (Sum.inr z))
  have hv0 : directQExtension (AP S) (AA S) (AR S) S (AL S j outer k) v coord=0 := by
    by_cases hk : k=i
    · subst k
      exact (directQExtension_at_same (AP S) (AA S) (AR S) S
        (AL S j outer i) v (c,Sum.inl (Sum.inr z))).trans (hv c z)
    · have hn : AL S j outer i≠AL S j outer k := by
        intro hi
        have hinj : i=k := by
          fin_cases i <;> fin_cases k <;> first | rfl | cases hi
        exact hk hinj.symm
      exact directQExtension_at_other (AP S) (AA S) (AR S) S
        (AL S j outer k) (AL S j outer i) hn v (c,Sum.inl (Sum.inr z))
  exact he.trans ((congrArg₂ (fun a b : BDL26Field => a+b) hh0 hv0).trans (zero_add 0))

private theorem scaled_second_Cq_leaf_terminal (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two)
    (z : QStarEdge (AP S) (AL S j outer i)) :
    cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (scaledTau S j outer).val
      (.inr ⟨AL S j outer i,(c,.inl (.inr z))⟩)=0 := by
  let coord := (Sum.inr ⟨AL S j outer i,(c,Sum.inl (Sum.inr z))⟩ : RX1 (AP S) S)
  have he := congrFun (scaled_second_Cq_total S j outer) coord
  exact he.trans (directQExtension_at_other (AP S) (AA S) (AR S) S
    (AH S j outer) (AL S j outer i) (AL_ne_hub S j outer i)
      (fun v => (scaledHubW S j outer+scaledHubK S j outer) v+1)
        (c,Sum.inl (Sum.inr z)))

private theorem scaled_two_Cq_hub_terminal (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) (c : BDL26FiniteTannerSquare.Two) :
    cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
        (scaledInput S j outer).val
        (.inr ⟨AH S j outer,(c,.inl (.inr (AHZ S j outer i)))⟩)+
      cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
        (scaledTau S j outer).val
        (.inr ⟨AH S j outer,(c,.inl (.inr (AHZ S j outer i)))⟩)=
      (if i=0 then 1 else 0)+1 := by
  obtain ⟨k,v,hv,hq⟩ := scaled_first_Cq_total S j outer
  let a : QDoubleCylinderVertex (AP S) (AH S j outer) S :=
    (c,Sum.inl (Sum.inr (AHZ S j outer i)))
  let coord := (Sum.inr ⟨AH S j outer,a⟩ : RX1 (AP S) S)
  have hfirst : cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (scaledInput S j outer).val coord=scaledHubW S j outer a := by
    have he : cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
        (scaledInput S j outer).val coord=
        directQExtension (AP S) (AA S) (AR S) S (AH S j outer) (scaledHubW S j outer) coord+
        directQExtension (AP S) (AA S) (AR S) S (AL S j outer k) v coord :=
      congrFun hq coord
    exact he.trans ((congrArg₂ (fun a b : BDL26Field => a+b)
      (directQExtension_at_same (AP S) (AA S) (AR S) S (AH S j outer) (scaledHubW S j outer) a)
      (directQExtension_at_other (AP S) (AA S) (AR S) S (AL S j outer k) (AH S j outer)
        (Ne.symm (AL_ne_hub S j outer k)) v a)).trans (add_zero _))
  have hsecond : cqCorrectionTotal (literalData (AP S) (AA S) (AR S) S)
      (scaledTau S j outer).val coord=(scaledHubW S j outer+scaledHubK S j outer) a+1 :=
    (congrFun (scaled_second_Cq_total S j outer) coord).trans
      (directQExtension_at_same (AP S) (AA S) (AR S) S (AH S j outer)
        (fun v => (scaledHubW S j outer+scaledHubK S j outer) v+1) a)
  have hbit : scaledHubK S j outer a=(if i=0 then 1 else 0) := by
    have hinj := AHZ_injective S j outer
    fin_cases i <;> rcases two_eq_zero_or_one c with hc | hc <;>
      simp [a,scaledHubK,toggleWord,rayTail,basis_value,hinj.eq_iff,hc]
  calc
    _ = scaledHubW S j outer a+((scaledHubW S j outer a+scaledHubK S j outer a)+1) :=
      congrArg₂ (fun a b : BDL26Field => a+b) hfirst hsecond
    _ = (scaledHubW S j outer a+scaledHubW S j outer a)+(scaledHubK S j outer a+1) := by ac_rfl
    _ = scaledHubK S j outer a+1 := by rw [repair3_scalar_add_self,zero_add]
    _ = _ := congrArg (fun a : BDL26Field => a+1) hbit


private theorem scaled_lower_at_Q_terminal (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (q : (AP S).Q)
    (v : QDoubleCylinderVertex (AP S) q S) :
    (descent S 1 (scaledDomain S j outer)
        (scaledPhysical S j outer)).word q=
      updated S 3 (2 : StepIndex 3) (by decide)
          (scaledA S j outer) (scaledB S j outer)
          (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) (.inr ⟨q,v⟩))+
        (indexedFamily S 3).coboundary0 (3 : LevelIndex 3)
          (accumulated S 1 (scaledDomain S j outer)
            (scaledPhysical S j outer))
          (rxPhysicalQEquiv S 3 (2 : StepIndex 3) (by decide) (.inr ⟨q,v⟩)) := by
  rw [scaled_descent_entire_L]
  have hl := BDL26RXPhysicalStarTransport.localized_blocks S 3 (2 : StepIndex 3)
    (by decide) (scaledTop S j outer).center
    (scaledA S j outer) (scaledB S j outer)
    (scaled_original_localized S j outer)
  have hr := BDL26RXFiniteBlockTransport.remainder_q_constant S 3 (2 : StepIndex 3)
    (by decide) (scaledX0 S j outer)
    (BDL26RXXStarTransport.incidentQ S 3 (2 : StepIndex 3)
      (BDL26RXPhysicalStarTransport.parentX S 3 (2 : StepIndex 3) (by decide)
        (scaledTop S j outer).center)) q
    (scaledA S j outer) (scaledB S j outer) hl v
  rw [BDL26RXFiniteBlockTransport.R,Pi.add_apply,rxQVertexEquiv_val] at hr
  have hp := OriginalOneStepPhiBridge.accumulated_eq_original_Phi S
    (scaledDomain S j outer) (scaledPhysical S j outer)
  change accumulated S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)=
    BDL26RXFiniteBlockTransport.Phi S 3 (2 : StepIndex 3) (by decide)
      (scaledX0 S j outer) (scaledA S j outer) (scaledB S j outer) at hp
  rw [← hp] at hr
  exact hr.symm

private theorem scaled_lower_leaf_values (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) (i : Fin 3) :
    (descent S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)).word (AL S j outer i)=
      (if i=0 then 1 else 0)+scaledBeta S j outer := by
  rw [scaled_lower_at_Q_terminal S j outer (AL S j outer i)
    (0,.inl (.inr (ALZ S j outer i))),scaled_updated_at_Q_vertex,
    scaled_first_Cq_leaf_terminal,scaled_second_Cq_leaf_terminal,zero_add,zero_add,
    scaled_leaf_Phi_value]

private theorem scaled_lower_hub_value (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (descent S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)).word (AH S j outer)=
      1+scaledBeta S j outer := by
  rw [scaled_lower_at_Q_terminal S j outer (AH S j outer)
    (0,.inl (.inr (AHZ S j outer 0))),scaled_updated_at_Q_vertex,
    scaled_two_Cq_hub_terminal,scaled_hub_Phi_value]
  simp only [if_true]
  rw [CharTwo.add_self_eq_zero,zero_add]

private theorem scaled_descent_complete_word (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    (descent S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)).word=
      (canonicalBasisWord (AL S j outer 0)+canonicalBasisWord (AH S j outer))+
        tannerCoboundary0 (AP S)
          (scaledBeta S j outer • canonicalBasisWord (AX S j outer)) := by
  funext q
  rw [Pi.add_apply,map_smul,Pi.smul_apply,tannerCoboundary0_canonicalBasis_apply]
  by_cases hq : (AP S).xq (AX S j outer) q=true
  · rw [if_pos hq,smul_eq_mul,mul_one]
    rcases actual_Q_cover S j outer q hq with hhq | ⟨i,hiq⟩
    · subst q
      rw [scaled_lower_hub_value]
      simp [canonicalBasisWord,Pi.single_apply,AL_ne_hub]
    · subst q
      rw [scaled_lower_leaf_values]
      have hinj := AL_injective S j outer
      fin_cases i <;> simp [canonicalBasisWord,Pi.single_apply,
        hinj.eq_iff,AL_ne_hub,fun i => Ne.symm (AL_ne_hub S j outer i),eq_comm]
  · rw [if_neg hq,smul_zero]
    have hleaf (i : Fin 3) : q≠AL S j outer i := by
      intro he
      exact hq (he ▸ AL_incident S j outer i)
    have hhub : q≠AH S j outer := by
      intro he
      exact hq (he ▸ AH_incident S j outer)
    have hz : (descent S 1 (scaledDomain S j outer)
        (scaledPhysical S j outer)).word q=0 := by
      by_contra hn
      have hs : q∈hammingSupport (descent S 1 (scaledDomain S j outer)
          (scaledPhysical S j outer)).word := by
        simpa [hammingSupport] using hn
      have hmem := scaled_descent_supported S j outer hs
      simpa [hleaf 0,hleaf 1,hleaf 2,hhub] using hmem
    rw [hz]
    simp [canonicalBasisWord,Pi.single_apply,hleaf 0,hhub]

private theorem scaled_chi_one_of_descent_word (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two)
    (p : Word F (RawTwo S).X)
    (hword : (descent S 1 (scaledDomain S j outer)
        (scaledPhysical S j outer)).word=
      ActualCriticalStarGeometry.pairWord S j outer+tannerCoboundary0 (RawTwo S) p) :
    BDL26LogicalDefectProtection.chiX S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)=1 := by
  let u := scaledDomain S j outer
  let q := scaledPhysical S j outer
  let h := ActualCriticalStarGeometry.pairWord S j outer+tannerCoboundary0 (RawTwo S) p
  let residual := h+(fun q : (RawTwo S).Q => (BDL26LevelTwoDecoder.decode S 0) q)+
    (fun q : (RawTwo S).Q => (BDL26LevelTwoDecoder.decode S (tannerCoboundary1 (RawTwo S) h)) q)
  have hf : firstReadout S 1 u=0 := scaled_actual_FIRST_zero S j outer
  have hs : tannerCoboundary1 (RawTwo S) h=secondReadout S 1 u q := by
    have hi := descent_syndrome S 1 u q
    rw [BDL26HistoryLogicalResidual.suffix_delta1] at hi
    change tannerCoboundary1 (state S 2).presentation (descent S 1 u q).word=
      firstReadout S 1 u+secondReadout S 1 u q at hi
    rw [rawTwo_actual_delta1,hword,hf,zero_add] at hi
    exact hi
  have hv : residual=(descent S 1 u q).word+
      (actualBase S 1).decode (actualInputs S 1 (input S 1 u) 0)+
      (actualBase S 1).decode
        (actualInputs S 1 (perturbTop S 1 (input S 1 u) (flip S 1 q)) 0) := by
    rw [hword,first_base_original_D,second_base_original_D,hf,← hs]
    rfl
  have hr := ActualCriticalStarGeometry.pair_plus_boundary_full_original_residual S j outer p
  apply BDL26ActualLocalizedResidualLift.actual_chi_one_of_localized_closed_not_boundary
    S 1 u q residual hv
  · rw [rawTwo_actual_delta1]
    exact hr.1
  · rintro ⟨a,ha⟩
    apply hr.2.2
    refine ⟨a,?_⟩
    rw [← rawTwo_actual_delta0]
    exact ha

private theorem scaled_actual_chi_one (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    BDL26LogicalDefectProtection.chiX S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)=1 := by
  let p : Word F (RawTwo S).X :=
    scaledBeta S j outer • canonicalBasisWord (AX S j outer)
  have hw : (descent S 1 (scaledDomain S j outer)
      (scaledPhysical S j outer)).word=
      ActualCriticalStarGeometry.pairWord S j outer+tannerCoboundary0 (RawTwo S) p := by
    rw [← rawTwo_actual_delta0]
    exact scaled_descent_complete_word S j outer
  exact scaled_chi_one_of_descent_word S j outer p hw


private theorem actual_single_oldX_all_odd_first_zero_chi_one (S : OddScale)
    (j : Fin 2) (outer : BDL26FiniteTannerSquare.Two) :
    ∃ u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1,
      ∃ edge : DoubleCylinderEdge (state S 2).presentation
        (oldXOwner S 1 (by decide) (seedQNode S j) outer) S,
      parse S 1 (oldXPhysical S 1 (by decide) (seedQNode S j) outer edge)=
        Leaf.primitive (Primitive.oldX 1 (by decide) (seedQNode S j) outer edge) ∧
      firstReadout S 1 u=0 ∧
        BDL26LogicalDefectProtection.chiX S 1 u
          (oldXPhysical S 1 (by decide) (seedQNode S j) outer edge)=1 := by
  refine ⟨scaledDomain S j outer,scaledPhysicalEdge S j outer,
    ?_,scaled_actual_FIRST_zero S j outer,?_⟩
  · exact parse_oldX_exact S
      ⟨seedQNode S j,outer,scaledPhysicalEdge S j outer⟩
  · exact scaled_actual_chi_one S j outer



end
end OriginalOldXScaleExtension
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint


namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RXPhysicalCoordinateTrace
open scoped Classical

/-- For every admissible odd scale, at N=1 the original model has one legal
background and one physical old-X error in Physical S 3 with exact parser class,
FIRST readout zero, and actual logical defect one. The same background and error
occur in all three conclusions. This is the single RX suffix from C3 to C2;
the old-X edge chart belongs to state S 2. No arbitrary-depth or lifetime claim
is made. The public statement quantifies the owner with no private coordinates. -/
theorem exists_original_oldX_all_odd_first_zero_chi_one (S : OddScale) :
    ∃ x : (state S 1).presentation.X,
      ∃ outer : BDL26FiniteTannerSquare.Two,
      ∃ u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1,
      ∃ edge : DoubleCylinderEdge (state S 2).presentation
          (oldXOwner S 1 (by decide) x outer) S,
        parse S 1 (oldXPhysical S 1 (by decide) x outer edge)=
          Leaf.primitive (Primitive.oldX 1 (by decide) x outer edge) ∧
        firstReadout S 1 u=0 ∧
          BDL26LogicalDefectProtection.chiX S 1 u
            (oldXPhysical S 1 (by decide) x outer edge)=1 := by
  obtain ⟨u,edge,hparse,hfirst,hchi⟩ :=
    OriginalOldXScaleExtension.actual_single_oldX_all_odd_first_zero_chi_one S 0 0
  exact ⟨seedQNode S 0,0,u,edge,hparse,hfirst,hchi⟩

end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/-!
# A weight-two failure witness for the current canonical base lookup

This extension concerns the current specific BDL26LevelTwoDecoder.decode.
It supplies an actual Physical S 2 error and the full original residual.
It establishes no paper radius-two contract, distance lower bound, paper
counterexample, arbitrary-depth statement, or lifetime conclusion.
The full actual error, syndrome and residual use the same original lookup.
-/

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
namespace BaseDecoderTwoErrorWitness
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26CSSHamiltonian
open scoped Classical
noncomputable section

/-- These are two coordinates of the actual physical state, before any RawTwo
word view is taken. The selector and decoder have not been changed. -/
private def actualPairError (S : OddScale) : Word BDL26Field (Physical S 2) :=
  canonicalBasisWord (F:=BDL26Field) (ActualCriticalStarGeometry.r S 0 0)+
    canonicalBasisWord (F:=BDL26Field) (ActualCriticalStarGeometry.b S 0 0)

private theorem actual_pair_ports_ne (S : OddScale) :
    ActualCriticalStarGeometry.r S 0 0≠ActualCriticalStarGeometry.b S 0 0 := by
  intro h
  have hh :
      (Sum.inr ⟨criticalRadial S 0,
        ((0 : BDL26FiniteTannerSquare.Two),.inl (.inr
          ⟨seedQNode S 0,criticalRadial_incident S 0⟩))⟩ :
        BDL26RZLocalReplacement.RZQ (RawOne S) S)=
      Sum.inr ⟨criticalBoundary S 0,
        ((0 : BDL26FiniteTannerSquare.Two),.inl (.inr
          ⟨seedQNode S 0,criticalBoundary_incident S 0⟩))⟩ := h
  exact criticalRadial_ne_boundary S 0 (congrArg Sigma.fst (Sum.inr.inj hh))

private theorem two_actual_bases_weight {I : Type} [Fintype I]
    (a b : I) (hab : a≠b) :
    HammingWeight (canonicalBasisWord (F:=BDL26Field) a+
      canonicalBasisWord (F:=BDL26Field) b)=2 := by
  classical
  have hs : hammingSupport (canonicalBasisWord (F:=BDL26Field) a+
      canonicalBasisWord (F:=BDL26Field) b)={a,b} := by
    ext i
    by_cases ha : i=a
    · subst i
      simp [hammingSupport,basis_value,hab]
    · by_cases hb : i=b
      · subst i
        simp [hammingSupport,basis_value,hab.symm]
      · simp [hammingSupport,basis_value,ha,hb]
  rw [HammingWeight_eq_card_hammingSupport,hs]
  simp [hab]

private theorem actualPairError_weight (S : OddScale) :
    HammingWeight (actualPairError S)=2 :=
  two_actual_bases_weight _ _ (actual_pair_ports_ne S)

/-- Coefficient identity on the original materialized Q carrier. The actual
error was defined on Physical S 2, rather than merely asserted to be physical. -/
private theorem actual_pair_raw_word (S : OddScale) :
    (fun q : (RawTwo S).Q => actualPairError S q)=
      ActualCriticalStarGeometry.pairWord S 0 0 := rfl

/-- The entire actual syndrome differential is the original RawTwo one. Its
proof is the existing full presentation transport, not just an incidence mask. -/
private theorem actual_word_raw_syndrome (S : OddScale)
    (w : Word BDL26Field (Physical S 2)) :
    (fun z : (RawTwo S).Z => zSyndrome S 2 w z)=
      QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (fun q : (RawTwo S).Q => w q) :=
  LinearMap.congr_fun (DirectOldXCounterexample.rawTwo_actual_delta1 S) w

private theorem actual_pair_raw_syndrome (S : OddScale) :
    (fun z : (RawTwo S).Z => zSyndrome S 2 (actualPairError S) z)=
      QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (ActualCriticalStarGeometry.pairWord S 0 0) :=
  (actual_word_raw_syndrome S (actualPairError S)).trans
    (congrArg (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S)) (actual_pair_raw_word S))

/-- Only the actual syndrome argument is transported. This is the exact same
original global/local canonical lookup, with no alternative decoder instance. -/
private theorem actual_pair_original_decode_raw (S : OddScale) :
    (fun q : (RawTwo S).Q =>
      BDL26LevelTwoDecoder.decode S (zSyndrome S 2 (actualPairError S)) q)=
    (fun q : (RawTwo S).Q => BDL26LevelTwoDecoder.decode S
      (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (ActualCriticalStarGeometry.pairWord S 0 0)) q) :=
  congrArg (fun sigma : Word BDL26Field (RawTwo S).Z =>
    fun q : (RawTwo S).Q => BDL26LevelTwoDecoder.decode S sigma q)
      (actual_pair_raw_syndrome S)

private def actualPairResidual (S : OddScale) : Word BDL26Field (Physical S 2) :=
  actualPairError S+(fun q : Physical S 2 =>
    BDL26LevelTwoDecoder.decode S (zSyndrome S 2 (actualPairError S)) q)

/-- Retain both original D calls while applying the already proved complete
RawTwo result. The original D(0)=0 fact is used explicitly in the word bridge. -/
private def rawPairResidual (S : OddScale) : Word BDL26Field (RawTwo S).Q :=
  (ActualCriticalStarGeometry.pairWord S 0 0+
    (fun q : (RawTwo S).Q => BDL26LevelTwoDecoder.decode S 0 q))+
    (fun q : (RawTwo S).Q => BDL26LevelTwoDecoder.decode S
      (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (ActualCriticalStarGeometry.pairWord S 0 0)) q)

private theorem raw_pair_full_residual_spec (S : OddScale) :
    QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (rawPairResidual S)=0 ∧
      rawPairResidual S ∉ LinearMap.range (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0 (RawTwo S)) := by
  have hr := ActualCriticalStarGeometry.pair_plus_boundary_full_original_residual
    S 0 0 (0 : Word BDL26Field (RawTwo S).X)
  simp only [map_zero,add_zero] at hr
  exact ⟨hr.1,hr.2.2⟩

private theorem actual_residual_raw_word (S : OddScale) :
    (fun q : (RawTwo S).Q => actualPairResidual S q)=rawPairResidual S := by
  funext q
  calc
    actualPairResidual S q=actualPairError S q+
        BDL26LevelTwoDecoder.decode S (zSyndrome S 2 (actualPairError S)) q := rfl
    _=ActualCriticalStarGeometry.pairWord S 0 0 q+
        BDL26LevelTwoDecoder.decode S
          (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (ActualCriticalStarGeometry.pairWord S 0 0)) q :=
      congrArg₂ (fun a b : BDL26Field => a+b)
        (congrFun (actual_pair_raw_word S) q)
        (congrFun (actual_pair_original_decode_raw S) q)
    _=rawPairResidual S q := by
      have h0 := congrFun (BDL26LevelTwoDecoder.decode_zero S) q
      change ActualCriticalStarGeometry.pairWord S 0 0 q+
        BDL26LevelTwoDecoder.decode S
          (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (ActualCriticalStarGeometry.pairWord S 0 0)) q=
        (ActualCriticalStarGeometry.pairWord S 0 0 q+
          BDL26LevelTwoDecoder.decode S 0 q)+
        BDL26LevelTwoDecoder.decode S
          (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S) (ActualCriticalStarGeometry.pairWord S 0 0)) q
      have zero_slot (a b c : BDL26Field) (hc : c=0) :
          a+b=(a+c)+b :=
        ((congrArg (fun t : BDL26Field => (a+t)+b) hc).trans
          (congrArg (fun t : BDL26Field => t+b) (add_zero a))).symm
      exact zero_slot _ _ _ h0

/-- The full actual physical boundary map is transported, including the entire
potential carrier. A caller never supplies a logical coefficient or nonboundary. -/
private theorem actual_word_raw_boundary (S : OddScale)
    (a : Word BDL26Field (state S 2).presentation.X) :
    (fun q : (RawTwo S).Q => QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S 2).presentation a q)=
      QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0 (RawTwo S) (fun x : (RawTwo S).X => a x) :=
  LinearMap.congr_fun (DirectOldXCounterexample.rawTwo_actual_delta0 S) a

private theorem actual_pair_full_residual_spec (S : OddScale) :
    zSyndrome S 2 (actualPairResidual S)=0 ∧
      actualPairResidual S ∉
        LinearMap.range (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0 (state S 2).presentation) := by
  obtain ⟨hc,hnb⟩ := raw_pair_full_residual_spec S
  have hw := actual_residual_raw_word S
  refine ⟨?_,?_⟩
  · funext z
    exact (congrFun (actual_word_raw_syndrome S (actualPairResidual S)) z).trans
      ((congrFun (congrArg (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (RawTwo S)) hw) z).trans
        (congrFun hc z))
  · rintro ⟨a,ha⟩
    apply hnb
    refine ⟨(fun x : (RawTwo S).X => a x),?_⟩
    exact (actual_word_raw_boundary S a).symm.trans
      ((congrArg (fun w : Word BDL26Field (Physical S 2) =>
        fun q : (RawTwo S).Q => w q) ha).trans hw)

end
end BaseDecoderTwoErrorWitness

/-- At every OddScale the current specific canonical base lookup has an actual
weight-two Physical S 2 error with a valid actual syndrome whose complete
original error-plus-decoding residual is closed and is not an actual boundary.
This is a statement about this implementation, not a paper radius-two decoder
contract, a distance lower bound, or a counterexample to a paper theorem. -/
theorem exists_weight_two_original_levelTwoDecoder_failure (S : OddScale) :
    ∃ e : Word BDL26Field (BDL26CSSHamiltonian.Physical S 2),
      HammingWeight e=2 ∧
      BDL26CSSHamiltonian.zSyndrome S 2 e ∈
        LinearMap.range (BDL26CSSHamiltonian.zSyndrome S 2) ∧
      let residual : Word BDL26Field (BDL26CSSHamiltonian.Physical S 2) :=
        e+(fun q : BDL26CSSHamiltonian.Physical S 2 =>
          BDL26LevelTwoDecoder.decode S (BDL26CSSHamiltonian.zSyndrome S 2 e) q)
      BDL26CSSHamiltonian.zSyndrome S 2 residual=0 ∧
        residual ∉ LinearMap.range
          (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0 (BDL26DecodingGraph.state S 2).presentation) := by
  obtain ⟨hc,hnb⟩ := BaseDecoderTwoErrorWitness.actual_pair_full_residual_spec S
  exact ⟨BaseDecoderTwoErrorWitness.actualPairError S,
    BaseDecoderTwoErrorWitness.actualPairError_weight S,
    ⟨BaseDecoderTwoErrorWitness.actualPairError S,rfl⟩,hc,hnb⟩

end QEC.Coding.BDL26RXPrimitiveC2QEndpoint

/-!
# Actual base-pair geometry on the two distinct Tanner levels

Only the fixed M8 physical coordinates and full original degree-one map are
used. The S2 Tanner skeleton belongs to GraphVertex S 3. Canonical S2 base
owners belong to GraphVertex S 2 and the predecessor S1 Tanner skeleton.
The geometric conclusions below distinguish these carriers and also distinguish
undirected adjacency from directed incoming neighborhoods. No decoder choice,
correctability, paper-domain equivalence or distance lower bound is assumed.
-/

noncomputable section
namespace QEC.Coding.BDL26BaseGeometricDomain
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open scoped Classical

/-- The existing closed X-star Q carrier is characterized by a genuine shared
Q corner, with both incidences derived from the presented square. -/
theorem q_in_closed_Xstar_iff (P : TannerSquarePresentation) (x : P.X) (q : P.Q) :
    xStarVertexMember P x (.q q)=true ↔
      ∃ z : P.Z, P.xq x q=true ∧ P.qz q z=true := by
  constructor
  · intro h
    obtain ⟨f,hf,hq⟩ := of_decide_eq_true h
    have hx : P.faceX f=x := of_decide_eq_true hf
    rcases hq with hq | hq
    · subst q
      refine ⟨P.faceZ f,?_,P.data.faceQ_qz f 0⟩
      exact (congrArg (fun a => P.xq a (P.faceQ f 0)) hx).symm.trans
        (P.data.faceQ_xq f 0)
    · subst q
      refine ⟨P.faceZ f,?_,P.data.faceQ_qz f 1⟩
      exact (congrArg (fun a => P.xq a (P.faceQ f 1)) hx).symm.trans
        (P.data.faceQ_xq f 1)
  · rintro ⟨z,hx,hz⟩
    let shared : SharedQ P.data x z := ⟨q,by simpa using And.intro hx hz⟩
    let fc := (P.faceCornerEquiv x z).symm shared
    have hq : P.faceQ fc.1.val fc.2=q :=
      congrArg Subtype.val ((P.faceCornerEquiv x z).apply_symm_apply shared)
    change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧
      (q=P.faceQ f 0 ∨ q=P.faceQ f 1))=true
    apply decide_eq_true
    refine ⟨fc.1.val,decide_eq_true fc.1.property.1,?_⟩
    have two_cases (c : BDL26FiniteTannerSquare.Two) : c=0 ∨ c=1 := by fin_cases c <;> simp
    rcases two_cases fc.2 with hc | hc
    · left
      rw [← hc]
      exact hq.symm
    · right
      rw [← hc]
      exact hq.symm

/-- The closed X-star Z carrier is exactly the actual two-incidence path. -/
theorem z_in_closed_Xstar_iff (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    xStarVertexMember P x (.z z)=true ↔
      ∃ q : P.Q, P.xq x q=true ∧ P.qz q z=true := by
  constructor
  · intro h
    obtain ⟨f,hf,hz⟩ := of_decide_eq_true h
    have hx : P.faceX f=x := of_decide_eq_true hf
    subst z
    refine ⟨P.faceQ f 0,?_,P.data.faceQ_qz f 0⟩
    exact (congrArg (fun a => P.xq a (P.faceQ f 0)) hx).symm.trans
      (P.data.faceQ_xq f 0)
  · rintro ⟨q,hx,hz⟩
    let shared : SharedQ P.data x z := ⟨q,by simpa using And.intro hx hz⟩
    let fc := (P.faceCornerEquiv x z).symm shared
    change decide (∃ f : P.Face, xStarFaceMember P x f=true ∧ z=P.faceZ f)=true
    apply decide_eq_true
    exact ⟨fc.1.val,decide_eq_true fc.1.property.1,fc.1.property.2.symm⟩

/-- A precise at-most-two-edge undirected walk in the EXISTING skeleton;
no new graph or radius/owner identification is introduced. -/
theorem closed_Xstar_vertex_walk (P : TannerSquarePresentation) (x : P.X)
    (v : Vertex P) (hv : xStarVertexMember P x v=true) :
    v=.x x ∨ (tannerSkeleton P).adjacent (.x x) v ∨
      ∃ w : Vertex P, (tannerSkeleton P).adjacent (.x x) w ∧
        (tannerSkeleton P).adjacent w v := by
  cases v with
  | x y =>
    have hy : y=x := of_decide_eq_true hv
    subst y
    exact Or.inl rfl
  | q q =>
    obtain ⟨z,hx,_hz⟩ := (q_in_closed_Xstar_iff P x q).mp hv
    exact Or.inr (Or.inl hx)
  | z z =>
    obtain ⟨q,hx,hz⟩ := (z_in_closed_Xstar_iff P x z).mp hv
    exact Or.inr (Or.inr ⟨.q q,hx,hz⟩)

/-- The ORIGINAL bounded directed-distance search from a terminal vertex
returns zero exactly at that vertex, and infinity elsewhere. The induction
uses the original search; it does not introduce another graph or search. -/
theorem distance_from_terminal {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (u : V) (hu : ∀ w, G.edge u w=false) (v : V) :
    G.distance u v=(if u=v then 0 else ⊤) := by
  have hreach : ∀ steps, G.reachableWithin steps u v=decide (u=v) := by
    intro steps
    induction steps with
    | zero => rfl
    | succ steps ih =>
      simp [DirectedGraph.reachableWithin,ih,hu]
  have haux : ∀ steps, G.distanceAux u v steps=(if u=v then some 0 else none) := by
    intro steps
    induction steps with
    | zero => simp [DirectedGraph.distanceAux,hreach]
    | succ steps ih =>
      rw [DirectedGraph.distanceAux,ih]
      by_cases he : u=v
      · simp only [if_pos he]
      · simp only [if_neg he,hreach,decide_eq_true_eq]
  simp only [DirectedGraph.distance,haux]
  by_cases he : u=v <;> simp [he]

/-- A terminal source belongs to an ORIGINAL incoming region of any finite
radius exactly when it is the region centre. -/
theorem terminal_in_incoming_iff {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (u : V) (hu : ∀ w, G.edge u w=false)
    (v : V) (radius : Nat) :
    u ∈ LocalRegion.directedNeighborhood G v radius ↔ u=v := by
  simp only [LocalRegion.directedNeighborhood,Finset.mem_filter,
    Finset.mem_univ,true_and]
  rw [distance_from_terminal G u hu v]
  by_cases he : u=v <;> simp [he]

/-- This applies to every original Tanner presentation, without a bound on
its number of vertices: Z vertices are terminal in X-to-Q-to-Z orientation. -/
theorem tanner_z_in_incoming_iff (P : TannerSquarePresentation)
    (z : P.Z) (v : Vertex P) (radius : Nat) :
    Vertex.z z ∈ LocalRegion.directedNeighborhood (tannerLevel P).graph v radius ↔
      Vertex.z z=v := by
  apply terminal_in_incoming_iff
  intro w
  rw [tannerLevel_edge]
  cases w <;> rfl

/-- A Z source has no directed outgoing edges. Incoming neighborhoods are
therefore fundamentally different from the undirected balls above. -/
theorem z_in_incoming_radius_two_iff (S : OddScale) (n : Nat)
    (z : (state S n).presentation.Z) (v : Vertex (state S n).presentation) :
    Vertex.z z ∈ LocalRegion.directedNeighborhood
      (tannerLevel (state S n).presentation).graph v 2 ↔ Vertex.z z=v := by
  exact tanner_z_in_incoming_iff (state S n).presentation z v 2

/-- EVERY original canonical base-syndrome owner is a Z vertex. Thus its
incoming-region membership is equality with the centre, independent of any
support classification or choice of two surviving syndrome checks. -/
theorem base_syndrome_owner_in_incoming_iff (S : OddScale) (n : Nat)
    (p : BDL26IndexedDecoder.FamilyZ S (n+2)
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n)))
    (center : GraphVertex S 2) (radius : Nat) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S n p ∈
      LocalRegion.directedNeighborhood (level S 2).graph center radius ↔
        BDL26CanonicalHistoryMarks.baseSyndromeOwner S n p=center := by
  change Vertex.z (BDL26ReplacementSupport.rzSyndromeOwner
      (state S 1).presentation S p) ∈ LocalRegion.directedNeighborhood
      (tannerLevel (state S 1).presentation).graph center radius ↔
    Vertex.z (BDL26ReplacementSupport.rzSyndromeOwner
      (state S 1).presentation S p)=center
  exact tanner_z_in_incoming_iff (state S 1).presentation _ center radius

end QEC.Coding.BDL26BaseGeometricDomain
end

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint.ActualCriticalStarGeometry
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RZMap1CoordinateBridge
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26RZLocalReplacement
open BDL26BaseGeometricDomain
open scoped Classical
noncomputable section

/-- Actual function addition of two distinct canonical basis words has
three disjoint value regions. This is uniform in the carrier; no concrete
state-dependent equality predicate is rewritten by a caller. -/
private theorem distinct_basis_pair_values {I : Type} (u v : I) (hne : u≠v) :
    (canonicalBasisWord u+canonicalBasisWord v : Word BDL26Field I) u=1 ∧
    (canonicalBasisWord u+canonicalBasisWord v : Word BDL26Field I) v=1 ∧
    ∀ q : I, q≠u → q≠v →
      (canonicalBasisWord u+canonicalBasisWord v : Word BDL26Field I) q=0 := by
  constructor
  · change canonicalBasisWord (F:=BDL26Field) u u+
      canonicalBasisWord (F:=BDL26Field) v u=1
    simp [canonicalBasisWord,hne,Ne.symm hne]
  · constructor
    · change canonicalBasisWord (F:=BDL26Field) u v+
        canonicalBasisWord (F:=BDL26Field) v v=1
      simp [canonicalBasisWord,hne,Ne.symm hne]
    · intro q hqu hqv
      change canonicalBasisWord (F:=BDL26Field) u q+
        canonicalBasisWord (F:=BDL26Field) v q=0
      simp [canonicalBasisWord,hqu,hqv,Ne.symm hqu,Ne.symm hqv]

/-- The exact support law is proved once on an abstract finite carrier from
actual basis values. It needs no locality hypothesis or assumed support. -/
private theorem distinct_basis_pair_support {I : Type} [Fintype I]
    (u v : I) (hne : u≠v) :
    hammingSupport (canonicalBasisWord u+canonicalBasisWord v : Word BDL26Field I)=
      {u,v} := by
  have hvalues := distinct_basis_pair_values u v hne
  apply Finset.ext
  intro q
  rw [original_support_mem]
  constructor
  · intro hq
    by_cases hu : q=u
    · exact Finset.mem_insert.mpr (Or.inl hu)
    · by_cases hv : q=v
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hv))
      · exact False.elim (hq (hvalues.2.2 q hu hv))
  · intro hq
    rcases Finset.mem_insert.mp hq with hu | hv
    · subst q
      exact fun hz => one_ne_zero (hvalues.1.symm.trans hz)
    · have he : q=v := Finset.mem_singleton.mp hv
      subst q
      exact fun hz => one_ne_zero (hvalues.2.1.symm.trans hz)

private def geometric_sigma (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    Word BDL26Field (P S).Z :=
  QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (P S) (pairWord S j copy)

private theorem geometric_pair_value (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (q : (P S).Q) :
    pairWord S j copy q=(if q=r S j copy then 1 else 0)+
      (if q=b S j copy then 1 else 0) := by
  have hsum := congrArg₂ (fun a b : BDL26Field => a+b)
    (basis_value (r S j copy) q) (basis_value (b S j copy) q)
  change canonicalBasisWord (F:=BDL26Field) (r S j copy) q+
    canonicalBasisWord (F:=BDL26Field) (b S j copy) q=_
  by_cases hr : q=r S j copy
  · by_cases hb : q=b S j copy
    · simpa only [if_pos hr,if_pos hb] using hsum
    · simpa only [if_pos hr,if_neg hb] using hsum
  · by_cases hb : q=b S j copy
    · simpa only [if_neg hr,if_pos hb] using hsum
    · simpa only [if_neg hr,if_neg hb] using hsum

private theorem geometric_pair_support (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    hammingSupport (pairWord S j copy)={r S j copy,b S j copy} := by
  change hammingSupport
    (canonicalBasisWord (r S j copy)+canonicalBasisWord (b S j copy) :
      Word BDL26Field (RawTwo S).Q)={r S j copy,b S j copy}
  exact distinct_basis_pair_support (r S j copy) (b S j copy)
    (ports_distinct S j copy).1

/-- Both full finite sums are evaluated by the original actual canonical-basis
equation. The common radial check cancels in characteristic two; no other
physical check is omitted. -/
private theorem geometric_full_sigma_value (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (z : (P S).Z) :
    geometric_sigma S j copy z=(if z=zv S j copy then 1 else 0)+
      (if z=zg S j copy then 1 else 0) := by
  have hleaf := (leaf_unique S j copy).1
  have hr : (P S).qz (r S j copy) z=true ↔ z=zr S j copy := by
    exact ⟨hleaf.2 z,fun hz => by rw [hz]; exact hleaf.1⟩
  have hd := checks_distinct S j copy
  have hsum : geometric_sigma S j copy z=
      (if (P S).qz (r S j copy) z=true then 1 else 0)+
      (if (P S).qz (b S j copy) z=true then 1 else 0) := by
    calc
      _ = QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (P S)
            (canonicalBasisWord (r S j copy)) z+
          QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (P S)
            (canonicalBasisWord (b S j copy)) z :=
        congrArg (fun word : Word BDL26Field (P S).Z => word z)
          (map_add (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (P S)) _ _)
      _ = _ := congrArg₂ (fun a b : BDL26Field => a+b)
        (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
          (P S) (r S j copy) z)
        (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
          (P S) (b S j copy) z)
  rw [hsum]
  simp only [hr,hub_neighbours]
  by_cases hz : z=zr S j copy
  · subst z
    simp [hd.1,hd.2.1,CharTwo.add_self_eq_zero]
  · by_cases hv : z=zv S j copy
    · subst z
      simp [hd.1.symm,hd.2.2]
    · by_cases hg : z=zg S j copy
      · subst z
        simp [hd.2.1.symm,hd.2.2.symm]
      · simp [hz,hv,hg]

private theorem geometric_sigma_support (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    hammingSupport (geometric_sigma S j copy)={zv S j copy,zg S j copy} := by
  apply Finset.ext
  intro z
  have hne := (checks_distinct S j copy).2.2
  simp only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton,geometric_full_sigma_value]
  by_cases hv : z=zv S j copy
  · subst z
    simp [hne]
  · by_cases hg : z=zg S j copy
    · subst z
      simp [hne.symm]
    · simp [hv,hg]

private theorem geometric_sigma_at_checks (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    geometric_sigma S j copy (zv S j copy)=1 ∧
      geometric_sigma S j copy (zg S j copy)=1 := by
  have hne := (checks_distinct S j copy).2.2
  constructor
  · simp [geometric_full_sigma_value,hne]
  · simp [geometric_full_sigma_value,hne.symm]

/-- The SAME two physical coordinates are the opposite Q corners of one
genuine actual S2 face. Its X endpoint is the X-star center. -/
private theorem geometric_pair_same_face (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    ∃ f : (P S).Face, ∃ c : BDL26FiniteTannerSquare.Two,
      (P S).faceX f=x S j copy ∧ (P S).faceQ f c=r S j copy ∧
        (P S).faceQ f (QEC.Coding.BDL26RXPrimitiveC2QEndpoint.ActualCriticalStarGeometry.opposite c)=b S j copy := by
  refine ⟨fr S j copy,cr S j copy,?_,fr_leaf_corner S j copy,fr_hub_corner S j copy⟩
  exact faceFromShared_X (P S) (x S j copy) (zr S j copy) (r S j copy)
    (terminal_incident S j copy _ _) (leaf_unique S j copy).1.1

private theorem geometric_pair_in_actual_Xstar (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (q : (P S).Q) (hq : q ∈ hammingSupport (pairWord S j copy)) :
    xStarVertexMember (P S) (x S j copy) (.q q)=true ∧
      (level S 3).skeleton.adjacent (.x (x S j copy)) (.q q) := by
  rw [geometric_pair_support] at hq
  rcases Finset.mem_insert.mp hq with hq | hq
  · subst q
    have hx : (P S).xq (x S j copy) (r S j copy)=true := terminal_incident S j copy _ _
    exact ⟨(q_in_closed_Xstar_iff _ _ _).mpr ⟨zr S j copy,hx,(leaf_unique S j copy).1.1⟩,hx⟩
  · have he := Finset.mem_singleton.mp hq
    subst q
    have hx : (P S).xq (x S j copy) (b S j copy)=true := terminal_incident S j copy _ _
    have hz : (P S).qz (b S j copy) (zr S j copy)=true :=
      (hub_neighbours S j copy _).mpr (Or.inl rfl)
    exact ⟨(q_in_closed_Xstar_iff _ _ _).mpr ⟨zr S j copy,hx,hz⟩,hx⟩

private theorem geometric_sigma_in_actual_Xstar (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (z : (P S).Z) (hz : z ∈ hammingSupport (geometric_sigma S j copy)) :
    xStarVertexMember (P S) (x S j copy) (.z z)=true ∧
      (level S 3).graph.reachableWithin 2 (.x (x S j copy)) (.z z)=true := by
  have hlabels : z=zv S j copy ∨ z=zg S j copy := by
    simpa only [geometric_sigma_support,Finset.mem_insert,Finset.mem_singleton] using hz
  have hx : (P S).xq (x S j copy) (b S j copy)=true := terminal_incident S j copy _ _
  have hqz : (P S).qz (b S j copy) z=true := by
    apply (hub_neighbours S j copy z).mpr
    exact Or.inr hlabels
  refine ⟨(z_in_closed_Xstar_iff _ _ _).mpr ⟨b S j copy,hx,hqz⟩,?_⟩
  exact (reachable_two (P S) (.x (x S j copy)) (.z z)).mpr
    (Or.inr (Or.inr ⟨.q (b S j copy),hx,hqz⟩))

/-- The canonical base ownership map has the genuine predecessor-level labels.
These are G2 vertices, not the physical S2 Tanner vertices in G3. -/
private theorem geometric_zv_owner (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 (zv S j copy)=
      Vertex.z (criticalVerticalCheck S j) := rfl

private theorem geometric_zg_owner (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 (zg S j copy)=
      Vertex.z (seedConeCheck S j) := rfl

private theorem geometric_owner_checks_distinct (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 (zv S j copy) ≠
      BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 (zg S j copy) := by
  rw [geometric_zv_owner,geometric_zg_owner]
  intro h
  have he := Vertex.z.inj h
  cases he

/-- The full original boundary column supplies BOTH surviving owner checks.
The radial check is a third, distinct check and is not silently dropped. -/
private theorem geometric_old_boundary_incident (S : OddScale) (j : Fin 2) :
    (RawOne S).qz (criticalBoundary S j) (criticalVerticalCheck S j)=true ∧
      (RawOne S).qz (criticalBoundary S j) (seedConeCheck S j)=true := by
  have hvr : criticalVerticalCheck S j ≠
      seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩ := by intro h; cases h
  have hvc : criticalVerticalCheck S j ≠ seedConeCheck S j := by intro h; cases h
  have hgr : seedConeCheck S j ≠
      seedRadialCheck S j ⟨S.half-1,by have := S.half_pos;omega⟩ := by intro h; cases h
  have hv := criticalBoundary_matrix S j (criticalVerticalCheck S j)
  have hg := criticalBoundary_matrix S j (seedConeCheck S j)
  rw [if_neg hvr,if_pos rfl,if_neg hvc,zero_add,add_zero] at hv
  rw [if_neg hgr,if_neg hvc.symm,if_pos rfl,zero_add,zero_add] at hg
  constructor
  · by_contra hn
    rw [raw_boundary2_view,if_neg hn] at hv
    exact zero_ne_one hv
  · by_contra hn
    rw [raw_boundary2_view,if_neg hn] at hg
    exact zero_ne_one hg

/-- Every owner of a nonzero SAME full syndrome lies at one undirected edge
from a concrete old Q vertex in G2. -/
private theorem geometric_sigma_owner_one_edge (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two)
    (z : (P S).Z) (hz : z ∈ hammingSupport (geometric_sigma S j copy)) :
    (level S 2).skeleton.adjacent (.q (criticalBoundary S j))
      (BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z) := by
  have hlabels : z=zv S j copy ∨ z=zg S j copy := by
    simpa only [geometric_sigma_support,Finset.mem_insert,Finset.mem_singleton] using hz
  rcases hlabels with rfl | rfl
  · rw [geometric_zv_owner]
    exact (geometric_old_boundary_incident S j).1
  · rw [geometric_zg_owner]
    exact (geometric_old_boundary_incident S j).2

/-- The pair is outside the ACTUAL owner-fibre correctability predicate.
This is proved from its two nonzero values and different real RZ owners. -/
private theorem geometric_pair_not_F17_owner_local (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    ¬ BDL26LevelTwoDistance.levelTwoLocalError S (pairWord S j copy) := by
  intro hlocal
  obtain ⟨center,hcenter⟩ := (levelTwoLocalError_iff_owner S (pairWord S j copy)).mp hlocal
  have hd := (ports_distinct S j copy).1
  have hr : pairWord S j copy (r S j copy)≠0 := by simp [geometric_pair_value,hd]
  have hb : pairWord S j copy (b S j copy)≠0 := by simp [geometric_pair_value,hd.symm]
  have he := (hcenter (r S j copy) hr).trans (hcenter (b S j copy) hb).symm
  change Vertex.q (criticalRadial S j)=Vertex.q (criticalBoundary S j) at he
  exact criticalRadial_ne_boundary S j (Vertex.q.inj he)

private theorem geometric_sigma_not_one_owner (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    ¬ ∃ center : GraphVertex S 2,
      ∀ z ∈ hammingSupport (geometric_sigma S j copy),
        BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z=center := by
  rintro ⟨center,hcenter⟩
  have hv : zv S j copy ∈ hammingSupport (geometric_sigma S j copy) := by
    rw [geometric_sigma_support]
    simp
  have hg : zg S j copy ∈ hammingSupport (geometric_sigma S j copy) := by
    rw [geometric_sigma_support]
    simp
  exact geometric_owner_checks_distinct S j copy ((hcenter _ hv).trans (hcenter _ hg).symm)

/-- No single directed INCOMING G2 radius-two ball contains the two distinct
Z-source owners. This does not negate their undirected one-edge containment. -/
private theorem geometric_sigma_no_incoming_ball (S : OddScale) (j : Fin 2) (copy : BDL26FiniteTannerSquare.Two) :
    ¬ ∃ center : GraphVertex S 2,
      ∀ z ∈ hammingSupport (geometric_sigma S j copy),
        BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z ∈
          LocalRegion.directedNeighborhood (level S 2).graph center 2 := by
  rintro ⟨center,hcenter⟩
  apply geometric_sigma_not_one_owner S j copy
  refine ⟨center,?_⟩
  intro z hz
  exact (base_syndrome_owner_in_incoming_iff S 0 z center 2).mp (hcenter z hz)

end
end QEC.Coding.BDL26RXPrimitiveC2QEndpoint.ActualCriticalStarGeometry

namespace QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout
open scoped Classical

/-- For every OddScale, one SAME actual S2 error and its SAME full actual
syndrome have exact supports inside one genuine closed X-star. The explicit
G3 and canonical-owner G2 geometric conclusions keep their carriers separate.
The error is outside current F17 owner-fibre locality; the syndrome owners
fit an undirected one-edge G2 ball but no directed incoming radius-two ball.
No decoder-correctability, paper-domain or large-scale-distance claim follows. -/
theorem exists_actual_S2_pair_full_syndrome_geometric_domain (S : OddScale) :
    ∃ x : (state S 2).presentation.X,
      ∃ qr qb : (state S 2).presentation.Q,
      ∃ za zb : (state S 2).presentation.Z,
      ∃ oldq : (state S 1).presentation.Q,
        let e : Word BDL26Field (state S 2).presentation.Q :=
          canonicalBasisWord qr+canonicalBasisWord qb
        let sigma : Word BDL26Field (state S 2).presentation.Z :=
          QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1 (state S 2).presentation e
        qr≠qb ∧ za≠zb ∧ hammingSupport e={qr,qb} ∧
        hammingSupport sigma={za,zb} ∧
        (∃ f : (state S 2).presentation.Face, ∃ c : BDL26FiniteTannerSquare.Two,
          (state S 2).presentation.faceX f=x ∧
          (state S 2).presentation.faceQ f c=qr ∧
          (state S 2).presentation.faceQ f (if c=0 then 1 else 0)=qb) ∧
        (∀ q ∈ hammingSupport e,
          xStarVertexMember (state S 2).presentation x (.q q)=true ∧
          (level S 3).skeleton.adjacent (.x x) (.q q)) ∧
        (∀ z ∈ hammingSupport sigma,
          xStarVertexMember (state S 2).presentation x (.z z)=true ∧
          (level S 3).graph.reachableWithin 2 (.x x) (.z z)=true) ∧
        (∀ z ∈ hammingSupport sigma,
          (level S 2).skeleton.adjacent (.q oldq)
            (BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z)) ∧
        ¬ BDL26LevelTwoDistance.levelTwoLocalError S e ∧
        (¬ ∃ center : GraphVertex S 2,
          ∀ z ∈ hammingSupport sigma,
            BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z=center) ∧
        (¬ ∃ center : GraphVertex S 2,
          ∀ z ∈ hammingSupport sigma,
            BDL26CanonicalHistoryMarks.baseSyndromeOwner S 0 z ∈
              LocalRegion.directedNeighborhood (level S 2).graph center 2) := by
  refine ⟨ActualCriticalStarGeometry.x S 0 0,
    ActualCriticalStarGeometry.r S 0 0,ActualCriticalStarGeometry.b S 0 0,
    ActualCriticalStarGeometry.zv S 0 0,ActualCriticalStarGeometry.zg S 0 0,
    criticalBoundary S 0,?_⟩
  change (ActualCriticalStarGeometry.r S 0 0≠ActualCriticalStarGeometry.b S 0 0) ∧ _
  exact ⟨(ActualCriticalStarGeometry.ports_distinct S 0 0).1,
    (ActualCriticalStarGeometry.checks_distinct S 0 0).2.2,
    ActualCriticalStarGeometry.geometric_pair_support S 0 0,
    ActualCriticalStarGeometry.geometric_sigma_support S 0 0,
    (by
      obtain ⟨f,c,hx,hqr,hqb⟩ :=
        ActualCriticalStarGeometry.geometric_pair_same_face S 0 0
      exact ⟨f,c,hx,hqr,by
        simpa only [ActualCriticalStarGeometry.opposite] using hqb⟩),
    ActualCriticalStarGeometry.geometric_pair_in_actual_Xstar S 0 0,
    ActualCriticalStarGeometry.geometric_sigma_in_actual_Xstar S 0 0,
    ActualCriticalStarGeometry.geometric_sigma_owner_one_edge S 0 0,
    ActualCriticalStarGeometry.geometric_pair_not_F17_owner_local S 0 0,
    ActualCriticalStarGeometry.geometric_sigma_not_one_owner S 0 0,
    ActualCriticalStarGeometry.geometric_sigma_no_incoming_ball S 0 0⟩

end QEC.Coding.BDL26RXPrimitiveC2QEndpoint
