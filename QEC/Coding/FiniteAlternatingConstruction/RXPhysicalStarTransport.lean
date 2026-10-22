import QEC.Coding.FiniteAlternatingConstruction.RXFiniteBlockTransport
import QEC.Coding.FiniteAlternatingConstruction.GraphQuantitativeBounds
import Mathlib.Tactic

/-!
# Actual RX physical-X-star confinement

Project-derived internal refinement of registered BDL26 v1 `paper.tex:1559–1614,
2325–2384,2430–2461,3136–3185,3455–3481` (file SHA256
66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b).
The adjacent parent is computed from the actual upper X coordinate. The
original two runs, fixed same-U potential, both copies and complete lower
word are retained. A physical incidence star is not a raw owner-parent fibre;
positive-dimensional connector coordinates remain unparented. No component,
stability, logical-protection, embedding or lifetime conclusion is asserted.
-/
noncomputable section
namespace QEC.Coding.BDL26RXPhysicalStarTransport

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

/-- The physical Q-coordinate slice of the original closed X face star. -/
def physicalXStar (P : TannerSquarePresentation) (x : P.X) : Finset P.Q :=
  Finset.univ.filter fun q => P.xq x q=true

@[simp] theorem mem_physicalXStar (P : TannerSquarePresentation) (x : P.X) (q : P.Q) :
    q ∈ physicalXStar P x ↔ P.xq x q=true := by simp [physicalXStar]

/-- Face existence is reconstructed by the actual perfect pairing. -/
theorem physicalXStar_face_iff (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) :
    q ∈ physicalXStar P x ↔ ∃ f : P.Face, ∃ c : Fin 2,
      P.faceX f=x ∧ P.faceQ f c=q := by
  rw [mem_physicalXStar]
  constructor
  · intro h
    let z := A.qzRoot q
    let shared : SharedQ P.data x z.1 := ⟨q,by simp [h,z.2]⟩
    obtain ⟨⟨f,c⟩,hc⟩ := (P.perfectPairing x z.1).2 shared
    exact ⟨f.1,c,f.2.1,congrArg Subtype.val hc⟩
  · rintro ⟨f,c,rfl,rfl⟩
    exact P.data.faceQ_xq f c

/-- The full global basis boundary, including connecting terms, has this exact support. -/
theorem basis_boundary_support (P : TannerSquarePresentation) (x : P.X) :
    hammingSupport (tannerCoboundary0 P (canonicalBasisWord x))=physicalXStar P x := by
  ext q
  simp only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    tannerCoboundary0_canonicalBasis_apply,mem_physicalXStar]
  by_cases h : P.xq x q=true <;> simp [h]

/-- Materialized local edges retain their old X endpoint owner. -/
theorem raw_local_edge_owner (P : TannerSquarePresentation) (S : OddScale)
    (u : RX0 P S) (e : Σ x : P.X, DoubleCylinderEdge P x S)
    (hu : rxXQIncidence P S u (Sum.inl e)=true) : u.1=e.1 := by
  obtain ⟨f,c,hf,hq⟩ := (rxXQIncidence_eq_true_iff P S u (Sum.inl e)).mp hu
  obtain ⟨endpoint,he⟩ := rxFaceX_eq_endpoint_of_faceQ_eq_xEdge P S f c e.1 e.2 hq
  have hh := congrArg Sigma.fst (hf.symm.trans he)
  exact hh

/-- Glue and retained-face incidences project to the original X-Q incidence. -/
theorem raw_q_vertex_owner (P : TannerSquarePresentation) (S : OddScale)
    (u : RX0 P S) (q : P.Q) (v : QDoubleCylinderVertex P q S)
    (hu : rxXQIncidence P S u (Sum.inr ⟨q,v⟩)=true) : P.xq u.1 q=true := by
  obtain ⟨face,corner,hx,hq⟩ :=
    (rxXQIncidence_eq_true_iff P S u (Sum.inr ⟨q,v⟩)).mp hu
  rcases face with localFace | glue | oldFace
  · rcases localFace with ⟨oldX,cell,material⟩
    fin_cases corner <;> simp [rxFaceQ,localFaceQAt,localFaceQ0,localFaceQ1] at hq
  · rcases glue with ⟨edge,qEdge,endpoint⟩
    have hx' : edge.1.1=u.1 := congrArg Sigma.fst hx
    fin_cases corner
    · simp [rxFaceQ,glueFaceQ0] at hq
    · have hq' : edge.1.2=q := congrArg Sigma.fst (Sum.inr.inj hq)
      simpa [hx',hq'] using edge.2
  · rcases oldFace with ⟨f,copy⟩
    have hx' : P.faceX f=u.1 := congrArg Sigma.fst hx
    have hq' : P.faceQ f corner=q := congrArg Sigma.fst (Sum.inr.inj hq)
    simpa [hx',hq'] using P.data.faceQ_xq f corner

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

/-- The original X owner of this actual upper degree-zero coordinate. -/
def parentX (u : FamilyX S depth i.succ) : XCoord S i :=
  ((rxDegreeZeroEquiv S depth i h).symm u).1

/-- Literal actual upper physical star; no alternate decoder input is created. -/
def upperStar (u : FamilyX S depth i.succ) : Finset (FamilyQ S depth i.succ) :=
  physicalXStar (state S (i.val+1)).presentation u

def Localized (u : FamilyX S depth i.succ) (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ upperStar S depth i u

/-- The lifted local singleton is exactly the global basis at its actual X chart coordinate. -/
theorem lift_singleton_eq_basis (x : XCoord S i)
    (v : DoubleCylinderVertex (state S i.val).presentation x S) :
    (rxContract S depth i h).support_decomposition.cxLift0 x (Pi.single v 1) =
      canonicalBasisWord (rxDegreeZeroEquiv S depth i h ⟨x,v⟩) := by
  funext u
  obtain ⟨⟨y,w⟩,rfl⟩ := (rxDegreeZeroEquiv S depth i h).surjective u
  by_cases hy : y=x
  · subst y
    rw [rxXLift_same]
    by_cases hw : w=v
    · subst w
      simp [canonicalBasisWord]
    · have hn : rxDegreeZeroEquiv S depth i h ⟨x,w⟩ ≠
          rxDegreeZeroEquiv S depth i h ⟨x,v⟩ := by
        intro hh
        have he := (rxDegreeZeroEquiv S depth i h).injective hh
        exact hw (by cases he; rfl)
      simp [Pi.single_apply,hw,canonicalBasisWord,hn]
  · rw [rxXLift_other S depth i h x y hy]
    have hn : rxDegreeZeroEquiv S depth i h ⟨y,w⟩ ≠
        rxDegreeZeroEquiv S depth i h ⟨x,v⟩ := by
      intro hh
      exact hy (congrArg Sigma.fst ((rxDegreeZeroEquiv S depth i h).injective hh))
    simp [canonicalBasisWord,hn]

/-- The existing partial graph parent of an X centre is computed, not supplied. -/
theorem parent_chart (x : XCoord S i)
    (v : DoubleCylinderVertex (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.x (rxDegreeZeroEquiv S depth i h ⟨x,v⟩)) =
      some (Vertex.x x) := by
  exact rxDegreeZero_parent S depth i h x v

theorem parent_computed (u : FamilyX S depth i.succ) :
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x (parentX S depth i h u)) := by
  obtain ⟨⟨x,v⟩,rfl⟩ := (rxDegreeZeroEquiv S depth i h).surjective u
  simpa [parentX] using parent_chart S depth i h x v

/-- Only upper X coordinates are identified with this parent fibre. -/
theorem degreeZeroBlock_parent_iff (x : XCoord S i) (u : FamilyX S depth i.succ) :
    u ∈ degreeZeroBlock S depth i h x ↔
      parent S (i.val+1) (Vertex.x u)=some (Vertex.x x) := by
  obtain ⟨⟨y,v⟩,rfl⟩ := (rxDegreeZeroEquiv S depth i h).surjective u
  rw [parent_chart]
  simp only [degreeZeroBlock,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨w,hw⟩
    have hxy : x=y := congrArg Sigma.fst ((rxDegreeZeroEquiv S depth i h).injective hw)
    exact congrArg (fun t => some (Vertex.x t)) hxy.symm
  · intro hy
    have hyx : y=x := Vertex.x.inj (Option.some.inj hy)
    subst y
    exact ⟨v,rfl⟩

/-- The genuine physical star is contained in the original decoder block star.
The proof uses the actual full materialized coboundary, not an ownership oracle. -/
theorem upperStar_subset_star (u : FamilyX S depth i.succ) :
    upperStar S depth i u ⊆ star1 S depth i h (parentX S depth i h u) := by
  obtain ⟨⟨x,v⟩,rfl⟩ := (rxDegreeZeroEquiv S depth i h).surjective u
  have hs := lift_boundary_supported S depth i h x (Pi.single v 1)
  rw [lift_singleton_eq_basis,indexedFamily_coboundary0,basis_boundary_support] at hs
  simpa [upperStar,parentX] using hs

@[simp] theorem neighbors_parent (x : XCoord S i) :
    BDL26RXFiniteBlockTransport.neighbors S depth i {x} (incidentQ S depth i x)=
      physicalXStar (state S i.val).presentation x := by
  simp [BDL26RXFiniteBlockTransport.neighbors,physicalXStar,incidentQ]

@[simp] theorem block_star_parent (x : XCoord S i) :
    BDL26RXFiniteBlockTransport.star S depth i h {x} (incidentQ S depth i x)=
      star1 S depth i h x := by
  unfold BDL26RXFiniteBlockTransport.star
  rw [neighbors_parent]
  simp [BDL26RXFiniteBlockTransport.xBlocks,BDL26RXFiniteBlockTransport.qBlocks,
    physicalXStar,incidentQ,star1,starQ]

/-- The only supplied support premise concerns the original error difference. -/
theorem localized_blocks (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    BDL26RXFiniteBlockTransport.Localized S depth i h {parentX S depth i h u}
      (incidentQ S depth i (parentX S depth i h u)) a b := by
  simpa [BDL26RXFiniteBlockTransport.Localized,BDL26RXFiniteBlockTransport.xBlocks,
    BDL26RXFiniteBlockTransport.qBlocks,star1,starQ] using
      he.trans (upperStar_subset_star S depth i h u)

/-- The potential and lower word are the fixed merged same-U definitions. -/
def Phi (u : FamilyX S depth i.succ) (a b : Upper S depth i) :=
  BDL26RXFiniteBlockTransport.Phi S depth i h {parentX S depth i h u} a b

def R (u : FamilyX S depth i.succ) (a b : Upper S depth i) :=
  BDL26RXFiniteBlockTransport.R S depth i h {parentX S depth i h u} a b

def L (u : FamilyX S depth i.succ) (a b : Upper S depth i) :=
  BDL26RXFiniteBlockTransport.L S depth i h {parentX S depth i h u} a b

theorem map1_eq_remainder (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=R S depth i h u a b :=
  BDL26RXFiniteBlockTransport.map1_eq_remainder S depth i h _ _ a b
    (localized_blocks S depth i h u a b he)

theorem map1_with_potential (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) :=
  BDL26RXFiniteBlockTransport.map1_with_potential S depth i h _ _ a b
    (localized_blocks S depth i h u a b he)

theorem lower_syndrome (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=
      (coarseSum S depth i h a b).val :=
  BDL26RXFiniteBlockTransport.lower_syndrome S depth i h _ _ a b
    (localized_blocks S depth i h u a b he)

theorem correction_difference_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star1 S depth i h (parentX S depth i h u) := by
  simpa using BDL26RXFiniteBlockTransport.correction_difference_supported S depth i h _ _ a b
    (localized_blocks S depth i h u a b he)

theorem updated_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport (updated S depth i h a b) ⊆ star1 S depth i h (parentX S depth i h u) := by
  simpa using BDL26RXFiniteBlockTransport.updated_supported S depth i h _ _ a b
    (localized_blocks S depth i h u a b he)

theorem phi_boundary_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i) :
    hammingSupport ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b)) ⊆
      star1 S depth i h (parentX S depth i h u) := by
  rw [Phi,BDL26RXFiniteBlockTransport.phi_singleton]
  exact potential_boundary_supported S depth i h _ a b

theorem phi_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i) :
    hammingSupport (Phi S depth i h u a b) ⊆ degreeZeroBlock S depth i h (parentX S depth i h u) := by
  rw [Phi,BDL26RXFiniteBlockTransport.phi_singleton]
  exact potential_supported S depth i h _ a b

theorem lower_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport (L S depth i h u a b) ⊆
      physicalXStar (state S i.val).presentation (parentX S depth i h u) := by
  exact (BDL26RXFiniteBlockTransport.lower_supported S depth i h _ _ a b
    (localized_blocks S depth i h u a b he)).trans (by rw [neighbors_parent])

theorem incident_card_le_seven (x : XCoord S i) :
    (physicalXStar (state S i.val).presentation x).card ≤ 7 := by
  have hd := BDL26GraphQuantitativeBounds.state_tannerDegree_le S i.val (Vertex.x x)
  rw [BDL26GraphQuantitativeBounds.tannerDegree,
    Fintype.card_congr (BDL26GraphQuantitativeBounds.xNeighborEquiv _ x)] at hd
  simpa [physicalXStar,Fintype.card_subtype] using hd

theorem lower_weight (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    HammingWeight (L S depth i h u a b) ≤
        (physicalXStar (state S i.val).presentation (parentX S depth i h u)).card ∧
      (physicalXStar (state S i.val).presentation (parentX S depth i h u)).card ≤ 7 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact ⟨Finset.card_le_card (lower_supported S depth i h u a b he),incident_card_le_seven S depth i _⟩

theorem coarse_apply (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      ∑ q ∈ physicalXStar (state S i.val).presentation (parentX S depth i h u),
        L S depth i h u a b q * (if (state S i.val).presentation.qz q z=true then 1 else 0) := by
  simpa [L] using BDL26RXFiniteBlockTransport.coarse_apply S depth i h _ _ a b
    (localized_blocks S depth i h u a b he) z

def neighborZ (u : FamilyX S depth i.succ) : Finset (ZCoord S i) :=
  Finset.univ.filter fun z => ∃ q ∈ physicalXStar (state S i.val).presentation (parentX S depth i h u),
    (state S i.val).presentation.qz q z=true

theorem coarse_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) : hammingSupport (coarseSum S depth i h a b).val ⊆
      neighborZ S depth i h u := by
  simpa [neighborZ,BDL26RXFiniteBlockTransport.neighborZ] using
    BDL26RXFiniteBlockTransport.coarse_supported S depth i h _ _ a b
      (localized_blocks S depth i h u a b he)

/-- One complete same-run error/correction/stabilizer theorem. -/
theorem two_run (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x (parentX S depth i h u)) ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=
      (coarseSum S depth i h a b).val ∧
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star1 S depth i h (parentX S depth i h u) ∧
    hammingSupport (Phi S depth i h u a b) ⊆ degreeZeroBlock S depth i h (parentX S depth i h u) ∧
    hammingSupport (L S depth i h u a b) ⊆
      physicalXStar (state S i.val).presentation (parentX S depth i h u) ∧
    HammingWeight (L S depth i h u a b) ≤ 7 := by
  exact ⟨parent_computed S depth i h u,map1_with_potential S depth i h u a b he,
    lower_syndrome S depth i h u a b he,correction_difference_supported S depth i h u a b he,
    phi_supported S depth i h u a b,lower_supported S depth i h u a b he,
    (lower_weight S depth i h u a b he).1.trans (lower_weight S depth i h u a b he).2⟩

/-- Existing selected image retains both labels/copies, including cancellation. -/
theorem selected_image_support_eq (a b : Upper S depth i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val)=
      (hammingSupport (coarseSum S depth i h a b).val).biUnion (zPairImage (rxData S depth i h)) :=
  BDL26RXFiniteBlockTransport.selected_image_support_eq S depth i h a b

theorem selected_image_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) ⊆
      (neighborZ S depth i h u).biUnion (zPairImage (rxData S depth i h)) := by
  rw [selected_image_support_eq]
  intro p hp
  obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨z,coarse_supported S depth i h u a b he hz,hp⟩

theorem selected_image_pair (a b : Upper S depth i) (z : ZCoord S i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val
      ((rxData S depth i h).induced.zPairEquiv (z,copy)).val=(coarseSum S depth i h a b).val z :=
  BDL26RXFiniteBlockTransport.selected_image_pair S depth i h a b z copy

theorem selected_image_exterior (a b : Upper S depth i) (p : FamilyZ S depth i.succ)
    (hp : p ∉ (rxData S depth i h).zSector) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val p=0 :=
  BDL26RXFiniteBlockTransport.selected_image_exterior S depth i h a b p hp

theorem updated_syndrome (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b)=
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val :=
  BDL26RXErrorPullback.updated_delta S depth i h a b

@[simp] theorem phi_self (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    Phi S depth i h u a a=0 := by simp [Phi]

@[simp] theorem remainder_self (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    R S depth i h u a a=0 := by simp [R]

@[simp] theorem lower_self (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    L S depth i h u a a=0 := by simp [L]

theorem self_localized (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    Localized S depth i u a a := by
  change hammingSupport (a+a) ⊆ _
  have ha : a+a=(0 : Upper S depth i) := by
    funext p
    exact CharTwo.add_self_eq_zero (a p)
  rw [ha]
  simp [hammingSupport]

/-- Internally derived from actual admissibility, not a supplied centre. -/
def perturbationCenter (p : FamilyQ S depth i.succ) : FamilyX S depth i.succ :=
  ((state S (i.val+1)).admissible.toTannerSquareAdmissible.xqRoot p).1

theorem perturbationCenter_incident (p : FamilyQ S depth i.succ) :
    p ∈ upperStar S depth i (perturbationCenter S depth i p) :=
  (mem_physicalXStar _ _ _).mpr
    ((state S (i.val+1)).admissible.toTannerSquareAdmissible.xqRoot p).2

private theorem shift_error (a e : Upper S depth i) : a+(a+e)=e := by
  rw [← add_assoc,word_add_self,zero_add]

theorem basis_shift_localized (p : FamilyQ S depth i.succ) (a : Upper S depth i) :
    Localized S depth i (perturbationCenter S depth i p) a (a+canonicalBasisWord p) := by
  change hammingSupport (a+(a+canonicalBasisWord p)) ⊆ _
  rw [shift_error]
  intro q hq
  have hqp : q=p := by
    by_contra hn
    have hz : (canonicalBasisWord p : Upper S depth i) q=0 := by simp [canonicalBasisWord,hn]
    exact (by simpa [hammingSupport] using hq : (canonicalBasisWord p : Upper S depth i) q≠0) hz
  subst q
  exact perturbationCenter_incident S depth i p

/-- The complete single-physical-perturbation relation includes its actual computed parent. -/
theorem single_perturbation (p : FamilyQ S depth i.succ) (a : Upper S depth i) :
    let u := perturbationCenter S depth i p
    let b := a+canonicalBasisWord p
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x (parentX S depth i h u)) ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=
      (coarseSum S depth i h a b).val ∧
    hammingSupport (L S depth i h u a b) ⊆
      physicalXStar (state S i.val).presentation (parentX S depth i h u) ∧
    HammingWeight (L S depth i h u a b) ≤ 7 := by
  dsimp only
  have he := basis_shift_localized S depth i p a
  exact ⟨parent_computed S depth i h _,map1_with_potential S depth i h _ _ _ he,
    lower_syndrome S depth i h _ _ _ he,lower_supported S depth i h _ _ _ he,
    (lower_weight S depth i h _ _ _ he).1.trans (lower_weight S depth i h _ _ _ he).2⟩

/-- The full global degree-zero basis boundary; the connecting Q part is retained. -/
def gradient (u : FamilyX S depth i.succ) : Upper S depth i :=
  (indexedFamily S depth).coboundary0 i.succ (canonicalBasisWord u)

theorem gradient_support (u : FamilyX S depth i.succ) :
    hammingSupport (gradient S depth i u)=upperStar S depth i u := by
  rw [gradient,indexedFamily_coboundary0,basis_boundary_support]
  rfl

theorem gradient_localized (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    Localized S depth i u a (a+gradient S depth i u) := by
  change hammingSupport (a+(a+gradient S depth i u)) ⊆ _
  rw [shift_error,gradient_support]

theorem gradient_cocycle (u : FamilyX S depth i.succ) :
    (indexedFamily S depth).coboundary1 i.succ (gradient S depth i u)=0 :=
  potential_cocycle S depth i (canonicalBasisWord u)

theorem gradient_run_eq (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    run S depth i h (a+gradient S depth i u)=run S depth i h a := by
  have hs : errorSyndrome S depth i (a+gradient S depth i u)=errorSyndrome S depth i a := by
    apply Subtype.ext
    simp only [errorSyndrome,map_add,gradient_cocycle,add_zero]
  unfold run
  rw [hs]

theorem gradient_updated (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    updated S depth i h a (a+gradient S depth i u)=gradient S depth i u := by
  unfold updated
  rw [gradient_run_eq,shift_error,add_assoc,word_add_self,add_zero]

theorem gradient_coarse_zero (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    (coarseSum S depth i h a (a+gradient S depth i u)).val=0 := by
  change (run S depth i h a).coarse.val+(run S depth i h (a+gradient S depth i u)).coarse.val=0
  rw [gradient_run_eq,word_add_self]

/-- Explicit copy-zero boundary centre, valid for every original X owner. -/
def boundaryCenter (x : XCoord S i) : FamilyX S depth i.succ :=
  rxDegreeZeroEquiv S depth i h ⟨x,(0,(boundaryVertex S depth i x).val)⟩

@[simp] theorem boundaryCenter_parent (x : XCoord S i) :
    parentX S depth i h (boundaryCenter S depth i h x)=x := by simp [parentX,boundaryCenter]

/-- Its global singleton is exactly the lift of the explicit nonzero vertical-gradient witness. -/
theorem boundaryCenter_basis (x : XCoord S i) :
    canonicalBasisWord (boundaryCenter S depth i h x)=
      (rxContract S depth i h).support_decomposition.cxLift0 x (boundarySingleton S depth i x) :=
  (lift_singleton_eq_basis S depth i h x (0,(boundaryVertex S depth i x).val)).symm

theorem boundaryCenter_gradient_restriction (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      (gradient S depth i (boundaryCenter S depth i h x))=boundaryGradient S depth i h x := by
  rw [gradient,boundaryCenter_basis]
  exact (rxContract S depth i h).support_decomposition.cxDelta0_restriction x _

theorem boundaryCenter_gradient_nonzero (x : XCoord S i) :
    gradient S depth i (boundaryCenter S depth i h x)≠0 := by
  intro hz
  have hr := boundaryCenter_gradient_restriction S depth i h x
  rw [hz,map_zero] at hr
  exact boundaryGradient_nonzero S depth i h x hr.symm

/-- Nonzero original closed error and nonzero fixed potential boundary, for arbitrary backgrounds. -/
theorem boundaryCenter_nonzero_transport (x : XCoord S i) (a : Upper S depth i) :
    let u := boundaryCenter S depth i h x
    let b := a+gradient S depth i u
    gradient S depth i u≠0 ∧ updated S depth i h a b≠0 ∧
    (run S depth i h b).correction=(run S depth i h a).correction ∧
    (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b)≠0 ∧
    (coarseSum S depth i h a b).val=0 ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=0 ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      gradient S depth i u+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) := by
  dsimp only
  have he := gradient_localized S depth i (boundaryCenter S depth i h x) a
  have hn := boundaryCenter_gradient_nonzero S depth i h x
  have hp : (indexedFamily S depth).coboundary0 i.succ
      (Phi S depth i h (boundaryCenter S depth i h x) a
        (a+gradient S depth i (boundaryCenter S depth i h x)))≠0 := by
    intro hz
    have hb := BDL26RXFiniteBlockTransport.phi_boundary_x S depth i h {x} x
      (by simp) a (a+gradient S depth i (boundaryCenter S depth i h x))
    change restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      ((indexedFamily S depth).coboundary0 i.succ
        (BDL26RXFiniteBlockTransport.Phi S depth i h {x} a
          (a+gradient S depth i (boundaryCenter S depth i h x)))) = _ at hb
    have hz' : (indexedFamily S depth).coboundary0 i.succ
        (BDL26RXFiniteBlockTransport.Phi S depth i h {x} a
          (a+gradient S depth i (boundaryCenter S depth i h x)))=0 := by
      simpa [Phi] using hz
    rw [hz',map_zero,gradient_updated,boundaryCenter_gradient_restriction] at hb
    exact boundaryGradient_nonzero S depth i h x hb.symm
  refine ⟨hn,?_,congrArg AssemblyStepOutput.correction (gradient_run_eq S depth i h _ a),hp,
    gradient_coarse_zero S depth i h _ a,?_,?_⟩
  · rw [gradient_updated]
    exact hn
  · rw [lower_syndrome S depth i h _ _ _ he,gradient_coarse_zero]
  · rw [map1_with_potential S depth i h _ _ _ he,gradient_updated]


/-- The actual successor equality is the defining parity branch, not an input. -/
theorem successor_state_eq (even : i.val % 2=0) :
    state S (i.val+1)=rxState S (state S i.val) := by
  change nextState S i.val (state S i.val)=_
  exact if_pos even

/-- Transport the complete raw physical carrier along the defining successor equality. -/
def upperQChart : RX1 (state S i.val).presentation S ≃ FamilyQ S depth i.succ :=
  Equiv.cast (congrArg (fun C : ConstructionState => C.presentation.Q)
    (successor_state_eq S depth i h)).symm

theorem chart_incidence (r : RX0 (state S i.val).presentation S)
    (p : RX1 (state S i.val).presentation S) :
    (state S (i.val+1)).presentation.xq (rxDegreeZeroEquiv S depth i h r)
      (upperQChart S depth i h p)=rxXQIncidence (state S i.val).presentation S r p := by
  exact rxPhysical_incidence S depth i h r p

/-- Local-edge physical coordinates are genuinely unparented, unlike their X centres. -/
theorem local_edge_parent_none (x : XCoord S i)
    (e : DoubleCylinderEdge (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.q (upperQChart S depth i h (Sum.inl ⟨x,e⟩)))=none := by
  exact rxPhysical_localEdge_parent_none S depth i h x e

/-- The literal vertical connector of the explicit boundary vertex. -/
def verticalPhysical (x : XCoord S i) : FamilyQ S depth i.succ :=
  upperQChart S depth i h (Sum.inl ⟨x,Sum.inr (boundaryVertex S depth i x)⟩)

theorem vertical_incident (x : XCoord S i) :
    verticalPhysical S depth i h x ∈ upperStar S depth i (boundaryCenter S depth i h x) := by
  apply (mem_physicalXStar _ _ _).mpr
  rw [boundaryCenter,verticalPhysical,chart_incidence]
  have hi := BDL26RXLocalReplacement.rxPresentation_xEdge_endpoint_incidence
    (state S i.val).presentation (state S i.val).admissible.toTannerSquareAdmissibleV3 S x
    (Sum.inr (boundaryVertex S depth i x)) 0
  simpa [BDL26RXLocalReplacement.edgeEndpoint,
    BDL26RXLocalReplacement.twoSelect,tannerDoubleCylinderEdgeStart] using hi

theorem vertical_unparented (x : XCoord S i) :
    parent S (i.val+1) (Vertex.q (verticalPhysical S depth i h x))=none :=
  local_edge_parent_none S depth i h x _

/-- One nonzero actual connector perturbation, with all transport outputs retained. -/
theorem vertical_perturbation (x : XCoord S i) (a : Upper S depth i) :
    let u := boundaryCenter S depth i h x
    let p := verticalPhysical S depth i h x
    let b := a+canonicalBasisWord p
    (canonicalBasisWord p : Upper S depth i)≠0 ∧
    parent S (i.val+1) (Vertex.q p)=none ∧
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x x) ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=
      (coarseSum S depth i h a b).val ∧
    hammingSupport (L S depth i h u a b) ⊆ physicalXStar (state S i.val).presentation x ∧
    HammingWeight (L S depth i h u a b) ≤ 7 := by
  dsimp only
  have he : Localized S depth i (boundaryCenter S depth i h x) a
      (a+canonicalBasisWord (verticalPhysical S depth i h x)) := by
    change hammingSupport (a+(a+canonicalBasisWord _)) ⊆ _
    rw [shift_error]
    intro q hq
    have hqp : q=verticalPhysical S depth i h x := by
      by_contra hn
      have hz : (canonicalBasisWord (verticalPhysical S depth i h x) : Upper S depth i) q=0 := by
        simp [canonicalBasisWord,hn]
      exact (by simpa [hammingSupport] using hq :
        (canonicalBasisWord (verticalPhysical S depth i h x) : Upper S depth i) q≠0) hz
    subst q
    exact vertical_incident S depth i h x
  have ht := two_run S depth i h _ _ _ he
  refine ⟨?_,vertical_unparented S depth i h x,?_,ht.2.1,ht.2.2.1,?_,ht.2.2.2.2.2.2⟩
  · intro hz
    have hv := congrFun hz (verticalPhysical S depth i h x)
    have hh : (canonicalBasisWord (verticalPhysical S depth i h x) : Upper S depth i)
        (verticalPhysical S depth i h x)=1 := by simp [canonicalBasisWord]
    exact one_ne_zero (hh.symm.trans hv)
  · simpa using ht.1
  · simpa using ht.2.2.2.2.2.1

end QEC.Coding.BDL26RXPhysicalStarTransport
