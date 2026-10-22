import QEC.Coding.FiniteAlternatingConstruction.RZErrorPullback

/-!
# Actual RZ pullback with finite physical block support

The lower word is the original finite Q-cylinder parity, not a selected
preimage of the coarse syndrome. All Q-edge and Z-face fillings are constructed
inside the derived finite incidence neighbourhood. The original canonical
corrections, including possible nonzero zero-residual cycles, are retained.
This is an internal refinement of BDL26 paper.tex:2521–2654,3465–3481.
It supplies no upper-star parent identification or component-mask theorem.
-/
noncomputable section
namespace QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical

private theorem twice {α : Type*} (w : Word (ZMod 2) α) : w+w=0 := by
  funext x
  exact CharTwo.add_self_eq_zero _

private theorem zero_off {α : Type*} [Fintype α]
    (w : Word (ZMod 2) α) (Y : Finset α) (h : hammingSupport w ⊆ Y)
    (x : α) (hx : x ∉ Y) : w x=0 := by
  by_contra hn
  exact hx (h (by simpa [hammingSupport] using hn))

private theorem supported {α : Type*} [Fintype α]
    (w : Word (ZMod 2) α) (Y : Finset α) (h : ∀ x, x ∉ Y → w x=0) :
    hammingSupport w ⊆ Y := by
  intro x hx
  by_contra hn
  exact (show w x≠0 by simpa [hammingSupport] using hx) (h x hn)

private theorem zero_support {α : Type*} [Fintype α] :
    hammingSupport (0 : Word (ZMod 2) α)=∅ := by
  ext x
  simp [hammingSupport]

private theorem add_supported {α : Type*} [Fintype α]
    (a b : Word (ZMod 2) α) (Y : Finset α)
    (ha : hammingSupport a ⊆ Y) (hb : hammingSupport b ⊆ Y) :
    hammingSupport (a+b) ⊆ Y := by
  apply supported
  intro x hx
  simp only [Pi.add_apply,zero_off a Y ha x hx,zero_off b Y hb x hx,zero_add]

private theorem sum_supported {α β : Type*} [Fintype β]
    (J : Finset α) (f : α → Word (ZMod 2) β) (Y : Finset β)
    (hf : ∀ a ∈ J, hammingSupport (f a) ⊆ Y) :
    hammingSupport (∑ a ∈ J, f a) ⊆ Y := by
  apply supported
  intro x hx
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun a ha => zero_off _ _ (hf a ha) x hx)

private theorem push_supported {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) (w : Word (ZMod 2) α)
    (Y : Finset β) (hf : ∀ a, f a ∈ Y) :
    hammingSupport (wordPushforward f w) ⊆ Y := by
  apply supported
  intro x hx
  rw [wordPushforward_apply]
  apply Finset.sum_eq_zero
  intro a _
  exact if_neg (fun he => hx (by simpa only [he] using hf a))

private theorem delta1_zero_of (U : TannerSquarePresentation)
    (w : Word BDL26FiniteTannerSquare.Field U.Q) (z : U.Z)
    (h : ∀ q, U.qz q z=true → w q=0) : tannerCoboundary1 U w z=0 := by
  change (∑ q : U.Q, w q * if U.qz q z=true then 1 else 0)=0
  apply Finset.sum_eq_zero
  intro q _
  by_cases hi : U.qz q z=true
  · rw [if_pos hi,h q hi,zero_mul]
  · rw [if_neg hi,mul_zero]

private theorem z_incidence_owner (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (z z' : P.Z)
    (e : ZDoubleCylinderEdge P z S) (v : ZDoubleCylinderVertex P z' S)
    (h : rzQZIncidence P A S (.inl ⟨z,e⟩) ⟨z',v⟩=true) : z'=z := by
  change decide (∃ he : z'=z,
    doubleCylinderEdgeVertexMatrix (transposePresentation P) z S (he ▸ v) e=1)=true at h
  obtain ⟨he,_⟩ := of_decide_eq_true h
  exact he

private theorem q_incidence_neighbor (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) (z : P.Z)
    (u : QDoubleCylinderVertex (transposePresentation P) q S)
    (v : ZDoubleCylinderVertex P z S)
    (h : rzQZIncidence P A S (.inr ⟨q,u⟩) ⟨z,v⟩=true) : P.qz q z=true := by
  change decide (∃ hqz : P.qz q z=true,
    qToZDoubleCylinderVertex P A q z hqz S u=v)=true at h
  obtain ⟨he,_⟩ := of_decide_eq_true h
  exact he

namespace Coordinates
variable (P : TannerSquarePresentation) (S : OddScale)

def qBlocks (Q0 : Finset P.Q) : Finset (RZQ P S) :=
  Finset.univ.filter fun p => match p with
    | .inl _ => False
    | .inr ⟨q,_⟩ => q ∈ Q0

def zBlocks (Z0 : Finset P.Z) : Finset (RZQ P S) :=
  Finset.univ.filter fun p => match p with
    | .inl ⟨z,_⟩ => z ∈ Z0
    | .inr _ => False

def neighborZ (Q0 : Finset P.Q) : Finset P.Z :=
  Finset.univ.filter fun z => ∃ q ∈ Q0, P.qz q z=true

def zplus (Q0 : Finset P.Q) (Z0 : Finset P.Z) : Finset P.Z := Z0 ∪ neighborZ P Q0

def inputBlocks (Q0 : Finset P.Q) (Z0 : Finset P.Z) : Finset (RZQ P S) :=
  qBlocks P S Q0 ∪ zBlocks P S Z0

def star (Q0 : Finset P.Q) (Z0 : Finset P.Z) : Finset (RZQ P S) :=
  inputBlocks P S Q0 (zplus P Q0 Z0)

def potentialStar (Q0 : Finset P.Q) (Z0 : Finset P.Z) : Finset (RZX P S) :=
  Finset.univ.filter fun p => match p with
    | .inl (.inl ⟨z,_⟩) => z ∈ zplus P Q0 Z0
    | .inl (.inr ⟨q,_⟩) => q ∈ Q0
    | .inr _ => False

def syndromeBlocks (Z0 : Finset P.Z) : Finset (RZZ P S) :=
  Finset.univ.filter fun p => p.1 ∈ Z0

@[simp] theorem mem_qBlocks_q (Q0 : Finset P.Q) (q : P.Q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    (Sum.inr ⟨q,v⟩ : RZQ P S) ∈ qBlocks P S Q0 ↔ q ∈ Q0 := by simp [qBlocks]
@[simp] theorem mem_zBlocks_z (Z0 : Finset P.Z) (z : P.Z)
    (e : ZDoubleCylinderEdge P z S) :
    (Sum.inl ⟨z,e⟩ : RZQ P S) ∈ zBlocks P S Z0 ↔ z ∈ Z0 := by simp [zBlocks]
@[simp] theorem mem_input_q (Q0 : Finset P.Q) (Z0 : Finset P.Z) (q : P.Q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    (Sum.inr ⟨q,v⟩ : RZQ P S) ∈ inputBlocks P S Q0 Z0 ↔ q ∈ Q0 := by
  simp [inputBlocks,qBlocks,zBlocks]
@[simp] theorem mem_input_z (Q0 : Finset P.Q) (Z0 : Finset P.Z) (z : P.Z)
    (e : ZDoubleCylinderEdge P z S) :
    (Sum.inl ⟨z,e⟩ : RZQ P S) ∈ inputBlocks P S Q0 Z0 ↔ z ∈ Z0 := by
  simp [inputBlocks,qBlocks,zBlocks]
@[simp] theorem oldX_not_potentialStar (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (x : P.X) (copy : BDL26FiniteTannerSquare.Two) : (Sum.inr (x,copy) : RZX P S) ∉ potentialStar P S Q0 Z0 := by
  simp [potentialStar]

theorem input_subset_star (Q0 : Finset P.Q) (Z0 : Finset P.Z) :
    inputBlocks P S Q0 Z0 ⊆ star P S Q0 Z0 := by
  intro p hp
  rcases p with ⟨z,e⟩ | ⟨q,v⟩
  · exact (mem_input_z P S _ _ _ _).mpr
      (Finset.mem_union_left _ ((mem_input_z P S _ _ _ _).mp hp))
  · exact (mem_input_q P S _ _ _ _).mpr ((mem_input_q P S _ _ _ _).mp hp)

theorem zBlocks_subset_star (Q0 : Finset P.Q) (Z0 : Finset P.Z) :
    zBlocks P S (zplus P Q0 Z0) ⊆ star P S Q0 Z0 := Finset.subset_union_right

/-- Actual incidence, including every outgoing Q-to-Z term. -/
theorem syndrome_support (A : TannerSquareAdmissibleV4 P)
    (Q0 : Finset P.Q) (Z0 : Finset P.Z) (w : Word BDL26FiniteTannerSquare.Field (RZQ P S))
    (hw : hammingSupport w ⊆ inputBlocks P S Q0 Z0) :
    hammingSupport (rzCoboundary1 P A S w) ⊆ syndromeBlocks P S (zplus P Q0 Z0) := by
  apply supported
  rintro ⟨z,v⟩ hz
  have hz' : z ∉ zplus P Q0 Z0 := by
    simpa only [syndromeBlocks,Finset.mem_filter,Finset.mem_univ,true_and] using hz
  apply delta1_zero_of (rzReplacementPresentation P A.toTannerSquareAdmissible S)
  intro p hi
  change rzQZIncidence P A.toTannerSquareAdmissible S p ⟨z,v⟩=true at hi
  by_contra hp
  have hin := hw (by simpa only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hp)
  rcases p with ⟨z',e⟩ | ⟨q,u⟩
  · have hmem : z' ∈ Z0 := (mem_input_z P S _ _ _ _).mp hin
    have he := z_incidence_owner P A.toTannerSquareAdmissible S z' z e v hi
    exact hz' (Finset.mem_union_left _ (he.symm ▸ hmem))
  · have hq : q ∈ Q0 := (mem_input_q P S _ _ _ _).mp hin
    have hqz := q_incidence_neighbor P A.toTannerSquareAdmissible S q z u v hi
    exact hz' (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,q,hq,hqz⟩))

theorem parity_support (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (w : Word BDL26FiniteTannerSquare.Field (RZQ P S)) (hw : hammingSupport w ⊆ inputBlocks P S Q0 Z0) :
    hammingSupport (rzQParity P S w) ⊆ Q0 := by
  apply supported
  intro q hq
  apply Finset.sum_eq_zero
  intro v _
  exact zero_off w _ hw (.inr ⟨q,v⟩) (by simpa using hq)

theorem lower_syndrome_support (Q0 : Finset P.Q) (w : Word BDL26FiniteTannerSquare.Field P.Q)
    (hw : hammingSupport w ⊆ Q0) :
    hammingSupport (tannerCoboundary1 P w) ⊆ neighborZ P Q0 := by
  apply supported
  intro z hz
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q ∈ Q0
  · have hqz : ¬ P.qz q z=true := fun hh => hz
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,q,hq,hh⟩)
    simp [hqz]
  · simp [zero_off w Q0 hw q hq]

private theorem basis_image_support (A : TannerSquareAdmissibleV4 P)
    (Q0 : Finset P.Q) (Z0 : Finset P.Z) (q : P.Q) (hq : q ∈ Q0) :
    hammingSupport (map1BasisImage P A S q) ⊆ star P S Q0 Z0 := by
  intro p hp
  have hne : map1BasisImage P A S q p≠0 := by
    simpa only [hammingSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  have hp := (map1BasisImage_ne_zero_iff_mem_parentRegion P A S q p).mp hne
  rcases p with ⟨z,e⟩ | ⟨q',v⟩
  · obtain ⟨hqz,_⟩ := (Finset.mem_filter.mp hp).2
    apply (mem_input_z P S _ _ _ _).mpr
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,q,hq,hqz⟩)
  · have he : (⟨q',v⟩ : Σ q : P.Q, QDoubleCylinderVertex (transposePresentation P) q S)=
        ⟨q,rzMap1QRoot P q S⟩ := (Finset.mem_filter.mp hp).2
    have hqq : q'=q := congrArg Sigma.fst he
    exact (mem_input_q P S _ _ _ _).mpr (hqq.symm ▸ hq)

theorem map1_support (A : TannerSquareAdmissibleV4 P)
    (Q0 : Finset P.Q) (Z0 : Finset P.Z) (w : Word BDL26FiniteTannerSquare.Field P.Q)
    (hw : hammingSupport w ⊆ Q0) :
    hammingSupport (map1Coord P A S w) ⊆ star P S Q0 Z0 := by
  have hdecomp : w=∑ q : P.Q, w q • canonicalBasisWord q := by
    funext q
    simp [canonicalBasisWord,Finset.sum_apply,Pi.single_apply]
  rw [hdecomp,map_sum]
  apply sum_supported
  intro q _
  rw [map_smul,map1Coord_canonicalBasis]
  by_cases hq : q ∈ Q0
  · apply supported
    intro p hp
    simp [zero_off _ _ (basis_image_support P S A Q0 Z0 q hq) p hp]
  · simp [zero_off w Q0 hw q hq,hammingSupport]

private theorem qPotential_support (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (q : P.Q) (hq : q ∈ Q0)
    (e : Word BDL26FiniteTannerSquare.Field (QDoubleCylinderEdge (transposePresentation P) q S)) :
    hammingSupport (extendRZQEdgeWord P S q e) ⊆ potentialStar P S Q0 Z0 := by
  apply push_supported
  intro a
  simp [rzMap1QEdgeX,potentialStar,hq]

private theorem zPotential_support (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (z : P.Z) (hz : z ∈ zplus P Q0 Z0)
    (f : Word BDL26FiniteTannerSquare.Field (ZDoubleCylinderFace P z S)) :
    hammingSupport (extendRZFaceWord P S z f) ⊆ potentialStar P S Q0 Z0 := by
  apply push_supported
  intro a
  simp [potentialStar,hz]

private theorem qVertex_support (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (q : P.Q) (hq : q ∈ Q0)
    (w : Word BDL26FiniteTannerSquare.Field
      (QDoubleCylinderVertex (transposePresentation P) q S)) :
    hammingSupport (extendRZQVertexWord P S q w) ⊆ star P S Q0 Z0 := by
  change hammingSupport (wordPushforward
    (fun v => (Sum.inr ⟨q,v⟩ : RZQ P S)) w) ⊆ star P S Q0 Z0
  apply push_supported
  intro v
  exact (mem_input_q P S Q0 (zplus P Q0 Z0) q v).mpr hq

private theorem qPotential_boundary_support (A : TannerSquareAdmissibleV4 P)
    (Q0 : Finset P.Q) (Z0 : Finset P.Z) (q : P.Q) (hq : q ∈ Q0)
    (e : Word BDL26FiniteTannerSquare.Field (QDoubleCylinderEdge (transposePresentation P) q S)) :
    hammingSupport (rzCoboundary0 P A S (extendRZQEdgeWord P S q e)) ⊆ star P S Q0 Z0 := by
  apply supported
  intro p hp
  have h := congrFun (rzCoboundary0_extendRZQEdgeWord P A S q e) p
  rw [h]
  simp only [Pi.add_apply,Finset.sum_apply]
  have hqzero : extendRZQVertexWord P S q
      (graphBoundary (qDoubleCylinderEdgeStart (transposePresentation P) q S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S) e) p=0 := by
    exact zero_off _ _ (qVertex_support P S Q0 Z0 q hq _) p hp
  rw [hqzero,zero_add]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hqz : P.qz q z=true
  · rw [dif_pos hqz,extendRZLocalEdgeWord_eq]
    apply BDL26RZSupportedBoundary.extendEdge_supported
    intro hin
    apply hp
    have hz : z ∈ zplus P Q0 Z0 := Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,q,hq,hqz⟩)
    have ho : rzCorrectionOwner P S p=Vertex.z z :=
      (Finset.mem_filter.mp hin).2
    rcases p with ⟨z',edge⟩ | ⟨q',vertex⟩
    · have he : z'=z := Vertex.z.inj ho
      exact (mem_input_z P S _ _ _ _).mpr (he.symm ▸ hz)
    · exact False.elim (by
        change Vertex.q q'=Vertex.z z at ho
        cases ho)
  · rw [dif_neg hqz]
    rfl

/-- The full potential is constructed only from Q0 graph edges and Zplus faces. -/
theorem supported_filling (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (w : Word BDL26FiniteTannerSquare.Field (RZQ P S)) (hc : rzCoboundary1 P A S w=0)
    (hp : rzQParity P S w=0) (hw : hammingSupport w ⊆ star P S Q0 Z0) :
    ∃ p : Word BDL26FiniteTannerSquare.Field (RZX P S), rzCoboundary0 P A S p=w ∧
      hammingSupport p ⊆ potentialStar P S Q0 Z0 := by
  obtain ⟨edges,he⟩ := Classical.skolem.mp
    (rzQParity_zero_has_qFillings P A.toTannerSquareAdmissible S w hp)
  let pq := ∑ q ∈ Q0, extendRZQEdgeWord P S q (edges q)
  have hpqs : hammingSupport pq ⊆ potentialStar P S Q0 Z0 :=
    sum_supported Q0 _ _ (fun q hq => qPotential_support P S Q0 Z0 q hq _)
  have hdqs : hammingSupport (rzCoboundary0 P A S pq) ⊆ star P S Q0 Z0 := by
    dsimp only [pq]
    rw [map_sum]
    exact sum_supported Q0 _ _ (fun q hq => qPotential_boundary_support P S A Q0 Z0 q hq _)
  have hq (q : P.Q) (v : QDoubleCylinderVertex (transposePresentation P) q S) :
      rzCoboundary0 P A S pq (.inr ⟨q,v⟩)=w (.inr ⟨q,v⟩) := by
    dsimp only [pq]
    rw [map_sum]
    simp only [Finset.sum_apply,rzQEdge_coboundary_apply_q,he]
    by_cases hmem : q ∈ Q0
    · rw [Finset.sum_eq_single q]
      · simp [extendRZQVertexWord,wordPushforward_apply]
      · intro q' _ hne
        simp [extendRZQVertexWord,wordPushforward_apply,hne,Ne.symm hne,Sigma.mk.injEq]
      · simp [hmem]
    · have hwq : w (.inr ⟨q,v⟩)=0 := zero_off w _ hw _ (by simpa [star] using hmem)
      rw [hwq]
      apply Finset.sum_eq_zero
      intro q' hq'
      have hne : q≠q' := fun hh => hmem (by simpa only [hh] using hq')
      simp [extendRZQVertexWord,wordPushforward_apply,hne,Ne.symm hne,Sigma.mk.injEq]
  let r := w+rzCoboundary0 P A S pq
  have hrs : hammingSupport r ⊆ star P S Q0 Z0 := add_supported _ _ _ hw hdqs
  have hrq (q : P.Q) (v : QDoubleCylinderVertex (transposePresentation P) q S) :
      r (.inr ⟨q,v⟩)=0 := by
    simp only [r,Pi.add_apply,hq]
    exact CharTwo.add_self_eq_zero _
  have hrc : rzCoboundary1 P A S r=0 := by
    dsimp only [r]
    rw [map_add,hc,zero_add]
    exact LinearMap.congr_fun
      (tannerCoboundary_squared (rzReplacementPresentation P A.toTannerSquareAdmissible S)) pq
  have hf (z : P.Z) : ∃ f : Word BDL26FiniteTannerSquare.Field (ZDoubleCylinderFace P z S),
      doubleCylinderBoundary2 (transposePresentation P) z S f=
        fun e => r (.inl ⟨z,e⟩) :=
    zCylinder_cycle_has_filling P A.toTannerSquareAdmissibleV3 R z S _
      (rzLocal_cycle_of_cocycle_q_zero P A S r hrc hrq z)
  choose faces hfaces using hf
  let pz := ∑ z ∈ zplus P Q0 Z0, extendRZFaceWord P S z (faces z)
  have hpzs : hammingSupport pz ⊆ potentialStar P S Q0 Z0 :=
    sum_supported _ _ _ (fun z hz => zPotential_support P S Q0 Z0 z hz _)
  have hpz : rzCoboundary0 P A S pz=r := by
    dsimp only [pz]
    rw [map_sum]
    simp only [rzCoboundary0_extendRZFaceWord,extendRZLocalEdgeWord_eq,hfaces]
    funext p
    rw [Finset.sum_apply]
    rcases p with ⟨z,e⟩ | ⟨q,v⟩
    · by_cases hz : z ∈ zplus P Q0 Z0
      · rw [Finset.sum_eq_single z]
        · simp [extendZEdgeWord]
        · intro z' _ hne
          simp [extendZEdgeWord,Ne.symm hne]
        · simp [hz]
      · rw [zero_off r _ hrs _ (by simpa [star] using hz)]
        apply Finset.sum_eq_zero
        intro z' hz'
        have hne : z≠z' := fun hh => hz (by simpa only [hh] using hz')
        simp [extendZEdgeWord,hne]
    · simp only [extendZEdgeWord,Finset.sum_const_zero,hrq]
  refine ⟨pz+pq,?_,add_supported _ _ _ hpzs hpqs⟩
  rw [map_add,hpz]
  dsimp only [r]
  rw [add_assoc,twice,add_zero]

private theorem zBlocks_mono (Z0 Z1 : Finset P.Z) (h : Z0 ⊆ Z1) :
    zBlocks P S Z0 ⊆ zBlocks P S Z1 := by
  intro p hp
  rcases p with ⟨z,e⟩ | ⟨q,v⟩
  · exact (mem_zBlocks_z P S _ _ _).mpr (h ((mem_zBlocks_z P S _ _ _).mp hp))
  · exact False.elim (by simpa only [zBlocks,Finset.mem_filter,Finset.mem_univ,true_and] using hp)

private theorem zBlock_region (z : P.Z) (p : RZQ P S) :
    p ∈ zBlocks P S {z} ↔ p ∈ BDL26RZSupportedBoundary.correctionRegion P S z := by
  unfold zBlocks BDL26RZSupportedBoundary.correctionRegion fiberRegion
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rcases p with ⟨z',e⟩ | ⟨q,v⟩
  · change z' ∈ ({z} : Finset P.Z) ↔ Vertex.z z'=Vertex.z z
    simp only [Finset.mem_singleton,Vertex.z.injEq]
  · change False ↔ Vertex.q q=Vertex.z z
    simp only [reduceCtorEq]

private theorem qBlock_owner (q : P.Q) (p : RZQ P S) :
    p ∈ qBlocks P S {q} ↔ rzCorrectionOwner P S p=Vertex.q q := by
  rcases p with ⟨z,e⟩ | ⟨q',v⟩ <;>
    simp only [qBlocks,rzCorrectionOwner,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_singleton,Vertex.q.injEq,reduceCtorEq]

end Coordinates

private def reindex {α β : Type} (h : α=β) :
    Word BDL26FiniteTannerSquare.Field α ≃ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field β := by
  cases h
  exact LinearEquiv.refl _ _

private theorem reindex_apply {α β : Type} (h : α=β) (w : Word BDL26FiniteTannerSquare.Field α) (x : β) :
    reindex h w x=w ((Equiv.cast h).symm x) := by cases h; rfl

private theorem reindex_output {ι α β : Type} (h : α=β)
    (f : Word BDL26FiniteTannerSquare.Field ι →ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field α)
    (g : Word BDL26FiniteTannerSquare.Field ι →ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field β) (he : HEq f g) (w : Word BDL26FiniteTannerSquare.Field ι) :
    reindex h (f w)=g w := by cases h; rw [eq_of_heq he]; rfl

private theorem reindex_input {ι α β : Type} (h : α=β)
    (f : Word BDL26FiniteTannerSquare.Field α →ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field ι)
    (g : Word BDL26FiniteTannerSquare.Field β →ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field ι) (he : HEq f g) (w : Word BDL26FiniteTannerSquare.Field α) :
    f w=g (reindex h w) := by cases h; rw [eq_of_heq he]; rfl

private theorem reindex_membership {ι α β : Type} (h : α=β)
    (f : ι → Finset α) (g : ι → Finset β) (he : HEq f g) (z : ι) (x : α) :
    x ∈ f z ↔ Equiv.cast h x ∈ g z := by cases h; rw [eq_of_heq he]; rfl

private theorem reindex_delta0 (P U : TannerSquarePresentation) (h : P=U)
    (p : Word BDL26FiniteTannerSquare.Field P.X) :
    reindex (congrArg TannerSquarePresentation.Q h) (tannerCoboundary0 P p)=
      tannerCoboundary0 U (reindex (congrArg TannerSquarePresentation.X h) p) := by
  cases h
  rfl

private theorem reindex_delta1 (P U : TannerSquarePresentation) (h : P=U)
    (w : Word BDL26FiniteTannerSquare.Field P.Q) :
    reindex (congrArg TannerSquarePresentation.Z h) (tannerCoboundary1 P w)=
      tannerCoboundary1 U (reindex (congrArg TannerSquarePresentation.Q h) w) := by
  cases h
  rfl

open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)

abbrev Old := (state S i.val).presentation

include odd in
theorem actual_rz_state : state S (i.val+1)=rzState S (state S i.val) := by
  change nextState S i.val (state S i.val)=_
  exact if_neg odd

def upper_eq : (state S (i.val+1)).presentation=
    rzReplacementPresentation (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S :=
  congrArg ConstructionState.presentation (actual_rz_state S depth i odd)

def coord0 : FamilyX S depth i.succ ≃ RZX (Old S depth i) S :=
  Equiv.cast (congrArg TannerSquarePresentation.X (upper_eq S depth i odd))
def coord1 : FamilyQ S depth i.succ ≃ RZQ (Old S depth i) S :=
  Equiv.cast (congrArg TannerSquarePresentation.Q (upper_eq S depth i odd))
def coord2 : FamilyZ S depth i.succ ≃ RZZ (Old S depth i) S :=
  Equiv.cast (congrArg TannerSquarePresentation.Z (upper_eq S depth i odd))
def read0 : Potential S depth i ≃ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field (RZX (Old S depth i) S) :=
  reindex (congrArg TannerSquarePresentation.X (upper_eq S depth i odd))
def read1 : Upper S depth i ≃ₗ[BDL26FiniteTannerSquare.Field] Word BDL26FiniteTannerSquare.Field (RZQ (Old S depth i) S) :=
  reindex (congrArg TannerSquarePresentation.Q (upper_eq S depth i odd))
def read2 : (indexedFamily S depth).Cochain2 i.succ ≃ₗ[BDL26FiniteTannerSquare.Field]
    Word BDL26FiniteTannerSquare.Field (RZZ (Old S depth i) S) :=
  reindex (congrArg TannerSquarePresentation.Z (upper_eq S depth i odd))

@[simp] theorem read0_apply (p : Potential S depth i) (x : RZX (Old S depth i) S) :
    read0 S depth i odd p x=p ((coord0 S depth i odd).symm x) := reindex_apply _ _ _
@[simp] theorem read1_apply (w : Upper S depth i) (q : RZQ (Old S depth i) S) :
    read1 S depth i odd w q=w ((coord1 S depth i odd).symm q) := reindex_apply _ _ _
@[simp] theorem read2_apply (w : (indexedFamily S depth).Cochain2 i.succ)
    (z : RZZ (Old S depth i) S) :
    read2 S depth i odd w z=w ((coord2 S depth i odd).symm z) := reindex_apply _ _ _

def qBlocks (Q0 : Finset (Old S depth i).Q) : Finset (FamilyQ S depth i.succ) :=
  Finset.univ.filter fun q => coord1 S depth i odd q ∈ Coordinates.qBlocks (Old S depth i) S Q0
def zBlocks (Z0 : Finset (Old S depth i).Z) : Finset (FamilyQ S depth i.succ) :=
  Finset.univ.filter fun q => coord1 S depth i odd q ∈ Coordinates.zBlocks (Old S depth i) S Z0
def inputBlocks (Q0 : Finset (Old S depth i).Q) (Z0 : Finset (Old S depth i).Z) :
    Finset (FamilyQ S depth i.succ) := qBlocks S depth i odd Q0 ∪ zBlocks S depth i odd Z0
def star (Q0 : Finset (Old S depth i).Q) (Z0 : Finset (Old S depth i).Z) :
    Finset (FamilyQ S depth i.succ) :=
  inputBlocks S depth i odd Q0 (Coordinates.zplus (Old S depth i) Q0 Z0)
def potentialStar (Q0 : Finset (Old S depth i).Q) (Z0 : Finset (Old S depth i).Z) :
    Finset (FamilyX S depth i.succ) :=
  Finset.univ.filter fun x => coord0 S depth i odd x ∈ Coordinates.potentialStar (Old S depth i) S Q0 Z0
def syndromeBlocks (Z0 : Finset (Old S depth i).Z) : Finset (FamilyZ S depth i.succ) :=
  Finset.univ.filter fun z => coord2 S depth i odd z ∈ Coordinates.syndromeBlocks (Old S depth i) S Z0

theorem zBlock_eq_correctionRegion (z : (Old S depth i).Z) :
    zBlocks S depth i odd {z}=(rzData S depth i odd).correctionRegion z := by
  ext p
  have hc : p ∈ (rzData S depth i odd).correctionRegion z ↔
      coord1 S depth i odd p ∈ BDL26RZSupportedBoundary.correctionRegion (Old S depth i) S z :=
    reindex_membership (congrArg TannerSquarePresentation.Q (upper_eq S depth i odd))
      _ _ (rzData_coordinates S depth i odd).2.1 z p
  have hb : p ∈ zBlocks S depth i odd {z} ↔
      coord1 S depth i odd p ∈ Coordinates.zBlocks (Old S depth i) S {z} := by
    simp only [zBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
  exact hb.trans ((Coordinates.zBlock_region _ S z _).trans hc.symm)

def lowerError (a b : Upper S depth i) : Lower S depth i :=
  (rzData S depth i odd).induced.correctionProjection (a+b)

theorem lowerError_coordinates (a b : Upper S depth i) :
    lowerError S depth i odd a b=rzQParity (Old S depth i) S (read1 S depth i odd (a+b)) :=
  reindex_input _ _ _ (rzData_coordinates S depth i odd).2.2.2 _

theorem delta0_coordinates (p : Potential S depth i) :
    read1 S depth i odd ((indexedFamily S depth).coboundary0 i.succ p)=
      rzCoboundary0 (Old S depth i) (state S i.val).admissible S (read0 S depth i odd p) := by
  rw [indexedFamily_coboundary0]
  exact reindex_delta0 _ _ (upper_eq S depth i odd) p

theorem delta1_coordinates (w : Upper S depth i) :
    read2 S depth i odd ((indexedFamily S depth).coboundary1 i.succ w)=
      rzCoboundary1 (Old S depth i) (state S i.val).admissible S (read1 S depth i odd w) := by
  rw [indexedFamily_coboundary1]
  exact reindex_delta1 _ _ (upper_eq S depth i odd) w

theorem map1_coordinates (w : Lower S depth i) :
    read1 S depth i odd (((indexedDecoderData S depth).selectedMap i).map1 w)=
      map1Coord (Old S depth i) (state S i.val).admissible S w :=
  reindex_output _ _ _ (indexedDecoderData_selected_rz S depth i odd).2.1 w

private theorem read_support {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (f : Word BDL26FiniteTannerSquare.Field α → Word BDL26FiniteTannerSquare.Field β)
    (hf : ∀ w x, f w x=w (e.symm x)) (w : Word BDL26FiniteTannerSquare.Field α) (Y : Finset β) :
    hammingSupport (f w) ⊆ Y ↔
      hammingSupport w ⊆ Finset.univ.filter (fun x => e x ∈ Y) := by
  constructor
  · intro h x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,h ?_⟩
    simpa [hammingSupport,hf] using hx
  · intro h x hx
    have hh := h (show e.symm x ∈ hammingSupport w by simpa [hammingSupport,hf] using hx)
    simpa using (Finset.mem_filter.mp hh).2

private theorem read_input_support (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (w : Upper S depth i) :
    hammingSupport (read1 S depth i odd w) ⊆ Coordinates.inputBlocks (Old S depth i) S Q0 Z0 ↔
      hammingSupport w ⊆ inputBlocks S depth i odd Q0 Z0 := by
  rw [read_support _ _ (read1_apply S depth i odd)]
  have hset : (Finset.univ.filter fun p => coord1 S depth i odd p ∈
      Coordinates.inputBlocks (Old S depth i) S Q0 Z0)=inputBlocks S depth i odd Q0 Z0 := by
    ext p
    simp [inputBlocks,qBlocks,zBlocks,Coordinates.inputBlocks]
  rw [hset]

private theorem read_star_support (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (w : Upper S depth i) :
    hammingSupport (read1 S depth i odd w) ⊆ Coordinates.star (Old S depth i) S Q0 Z0 ↔
      hammingSupport w ⊆ star S depth i odd Q0 Z0 :=
  read_input_support S depth i odd Q0 _ w

private theorem run_coarse_apply (a : Upper S depth i) (z : (Old S depth i).Z) :
    (run S depth i odd a).coarse.val z=
      ∑ p ∈ (rzData S depth i odd).coarseRegion z, (errorSyndrome S depth i a).val p :=
  rzStepOutput_coarse_apply S depth i odd (errorSyndrome S depth i a) z

/-- The lower syndrome is derived from the original actual F09 calculation. -/
theorem lowerError_delta (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b)=
      (run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val := by
  have h := rzData_inducedCoboundaryCompatibility S depth i odd (a+b)
  change topParity (rzData S depth i odd)
      ((indexedFamily S depth).coboundary1 i.succ (a+b))=
    (indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b) at h
  funext z
  calc
    _ = ∑ p ∈ (rzData S depth i odd).coarseRegion z,
        ((indexedFamily S depth).coboundary1 i.succ (a+b)) p := (congrFun h z).symm
    _ = _ := by
      rw [Pi.add_apply,run_coarse_apply,run_coarse_apply]
      simp only [errorSyndrome,map_add,Pi.add_apply,Finset.sum_add_distrib]

private theorem run_components (a : Upper S depth i) :
    (run S depth i odd a).correction=∑ z,
      localCorrectionComponent (rzData S depth i odd) (rzData_localTopCohomology S depth i odd)
        z (errorSyndrome S depth i a).val := by
  exact AuditedLeafAdapters.rzOutput_correction
    (rzData S depth i odd) (rzData_localTopCohomology S depth i odd)
    (rzData_inducedCoboundaryCompatibility S depth i odd)
    (by change (i.val+1)%2=0; omega) (errorSyndrome S depth i a)

private theorem exact_residual_agreement (z : (Old S depth i).Z)
    (a b : Upper S depth i)
    (h : ∀ p ∈ (rzData S depth i odd).coarseRegion z,
      (errorSyndrome S depth i a).val p=(errorSyndrome S depth i b).val p) :
    localResidual (rzData S depth i odd) z (errorSyndrome S depth i a).val=
      localResidual (rzData S depth i odd) z (errorSyndrome S depth i b).val := by
  have ht : topParity (rzData S depth i odd) (errorSyndrome S depth i a).val z=
      topParity (rzData S depth i odd) (errorSyndrome S depth i b).val z :=
    Finset.sum_congr rfl h
  have hm : maskWord ((rzData S depth i odd).coarseRegion z) (errorSyndrome S depth i a).val=
      maskWord ((rzData S depth i odd).coarseRegion z) (errorSyndrome S depth i b).val := by
    funext p
    by_cases hp : p ∈ (rzData S depth i odd).coarseRegion z
    · simp only [maskWord,if_pos hp,h p hp]
    · simp only [maskWord,if_neg hp]
  unfold localResidual
  rw [hm,ht]

private theorem region_syndrome_coordinate (z : (Old S depth i).Z)
    (p : FamilyZ S depth i.succ) :
    p ∈ (rzData S depth i odd).coarseRegion z ↔ (coord2 S depth i odd p).1=z := by
  have hc : p ∈ (rzData S depth i odd).coarseRegion z ↔
      coord2 S depth i odd p ∈ BDL26RZConcreteParity.blockRegion (Old S depth i) S z :=
    reindex_membership (congrArg TannerSquarePresentation.Z (upper_eq S depth i odd))
      _ _ (rzData_coordinates S depth i odd).1 z p
  constructor
  · intro hp
    exact (Finset.mem_filter.mp (hc.mp hp)).2
  · intro hp
    exact hc.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)

/-- Unaffected original residuals, hence their original chosen corrections, agree. -/
theorem correction_difference_support (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd Q0 Z0) :
    hammingSupport ((run S depth i odd a).correction+(run S depth i odd b).correction) ⊆
      zBlocks S depth i odd (Coordinates.zplus (Old S depth i) Q0 Z0) := by
  have hs := Coordinates.syndrome_support (Old S depth i) S (state S i.val).admissible Q0 Z0
    (read1 S depth i odd (a+b)) ((read_input_support S depth i odd Q0 Z0 _).mpr he)
  have agree (z : (Old S depth i).Z) (hz : z ∉ Coordinates.zplus (Old S depth i) Q0 Z0) :
      localCorrectionComponent (rzData S depth i odd) (rzData_localTopCohomology S depth i odd)
        z (errorSyndrome S depth i a).val=
      localCorrectionComponent (rzData S depth i odd) (rzData_localTopCohomology S depth i odd)
        z (errorSyndrome S depth i b).val := by
    unfold localCorrectionComponent
    rw [exact_residual_agreement S depth i odd z a b (by
      intro p hp
      have hz' := (region_syndrome_coordinate S depth i odd z p).mp hp
      have hzero := zero_off _ _ hs (coord2 S depth i odd p) (by
        simpa [Coordinates.syndromeBlocks,hz'] using hz)
      rw [← delta1_coordinates] at hzero
      simp only [read2_apply,Equiv.symm_apply_apply,map_add,Pi.add_apply] at hzero
      have hh := congrArg (fun t : BDL26FiniteTannerSquare.Field => t+(indexedFamily S depth).coboundary1 i.succ b p) hzero
      change ((indexedFamily S depth).coboundary1 i.succ a) p=
        ((indexedFamily S depth).coboundary1 i.succ b) p
      simpa only [add_assoc,CharTwo.add_self_eq_zero,add_zero,zero_add] using hh)]
  rw [run_components,run_components,← Finset.sum_add_distrib]
  apply sum_supported
  intro z _
  by_cases hz : z ∈ Coordinates.zplus (Old S depth i) Q0 Z0
  · have hpart (w : Upper S depth i) :
        hammingSupport (localCorrectionComponent (rzData S depth i odd)
          (rzData_localTopCohomology S depth i odd) z (errorSyndrome S depth i w).val) ⊆
        zBlocks S depth i odd {z} := by
      apply supported
      intro p hp
      apply localCorrectionComponent_supported
      simpa only [← zBlock_eq_correctionRegion S depth i odd z] using hp
    have hmono : zBlocks S depth i odd {z} ⊆
        zBlocks S depth i odd (Coordinates.zplus (Old S depth i) Q0 Z0) := by
      intro p hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      apply Coordinates.zBlocks_mono _ S {z} _ (Finset.singleton_subset_iff.mpr hz)
      exact (Finset.mem_filter.mp hp).2
    exact add_supported _ _ _ ((hpart a).trans hmono) ((hpart b).trans hmono)
  · rw [agree z hz,twice]
    simp [hammingSupport]

private theorem correction_parity_zero (a : Upper S depth i) :
    rzQParity (Old S depth i) S (read1 S depth i odd (run S depth i odd a).correction)=0 := by
  rw [run_components,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro z _
  funext q
  apply Finset.sum_eq_zero
  intro v _
  rw [read1_apply]
  apply localCorrectionComponent_supported
  intro hp
  rw [← zBlock_eq_correctionRegion] at hp
  simp [zBlocks,Coordinates.zBlocks] at hp

theorem map2_coordinates (w : (indexedFamily S depth).Cochain2 i.castSucc) :
    read2 S depth i odd (((indexedDecoderData S depth).selectedMap i).map2 w)=
      map2Coord (Old S depth i) (state S i.val).admissible S w :=
  reindex_output _ _ _ (indexedDecoderData_selected_rz S depth i odd).2.2 w

private theorem selected_map2_support (Z0 : Finset (Old S depth i).Z)
    (w : (indexedFamily S depth).Cochain2 i.castSucc) (hw : hammingSupport w ⊆ Z0) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 w) ⊆
      syndromeBlocks S depth i odd Z0 := by
  apply (read_support (coord2 S depth i odd) (read2 S depth i odd)
    (read2_apply S depth i odd) _ _).mp
  rw [map2_coordinates]
  apply supported
  rintro ⟨z,v⟩ hz
  have hz' : z ∉ Z0 := by simpa [Coordinates.syndromeBlocks] using hz
  rw [map2Coord,wordPushforward_apply]
  apply Finset.sum_eq_zero
  intro z' _
  by_cases hh : (⟨z,v⟩ : RZZ (Old S depth i) S)=⟨z',rzMap1ZRoot (Old S depth i) (state S i.val).admissible z' S⟩
  · rw [if_pos hh]
    have hzz : z=z' := congrArg Sigma.fst hh
    exact zero_off w Z0 hw z' (fun hm => hz' (hzz.symm ▸ hm))
  · exact if_neg hh

theorem syndromeBlocks_eq_regions (Z0 : Finset (Old S depth i).Z) :
    syndromeBlocks S depth i odd Z0=Z0.biUnion ((rzData S depth i odd).coarseRegion) := by
  ext p
  simp only [syndromeBlocks,Coordinates.syndromeBlocks,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_biUnion,region_syndrome_coordinate]
  constructor
  · intro hp
    exact ⟨(coord2 S depth i odd p).1,hp,rfl⟩
  · rintro ⟨z,hz,he⟩
    simpa only [he] using hz

theorem qBlock_owner (q : (Old S depth i).Q) (p : FamilyQ S depth i.succ) :
    p ∈ qBlocks S depth i odd {q} ↔
      rzCorrectionOwner (Old S depth i) S (coord1 S depth i odd p)=Vertex.q q := by
  have hh : p ∈ qBlocks S depth i odd {q} ↔
      coord1 S depth i odd p ∈ Coordinates.qBlocks (Old S depth i) S {q} := by
    simp only [qBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
  exact hh.trans (Coordinates.qBlock_owner _ S q _)

private theorem reindex_function {α β γ : Type} (h : α=β)
    (f : α → γ) (g : β → γ) (he : HEq f g) (x : α) :
    f x=g (Equiv.cast h x) := by cases h; rw [eq_of_heq he]; rfl

/-- Physical Q blocks stay outside the ORIGINAL decoder correction owner. -/
theorem decoder_owner_q (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    (rzData S depth i odd).correctionOwner ((coord1 S depth i odd).symm (.inr ⟨q,v⟩))=none := by
  have hh := reindex_function (congrArg TannerSquarePresentation.Q (upper_eq S depth i odd))
    _ _ (rzData_coordinates S depth i odd).2.2.1
    ((coord1 S depth i odd).symm (.inr ⟨q,v⟩))
  change (rzData S depth i odd).correctionOwner ((coord1 S depth i odd).symm (.inr ⟨q,v⟩))=
    blockCorrectionOwner (Old S depth i) S
      (coord1 S depth i odd ((coord1 S depth i odd).symm (.inr ⟨q,v⟩))) at hh
  simpa only [Equiv.apply_symm_apply,blockCorrectionOwner] using hh

/-- Every conclusion concerns the original runs and a full upper potential. -/
def Pullback (Q0 : Finset (Old S depth i).Q) (Z0 : Finset (Old S depth i).Z)
    (a b : Upper S depth i) (p : Potential S depth i) : Prop :=
  ((indexedDecoderData S depth).selectedMap i).map1 (lowerError S depth i odd a b)=
    updated S depth i odd a b+(indexedFamily S depth).coboundary0 i.succ p ∧
  (indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b)=
    (run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val ∧
  ((indexedDecoderData S depth).selectedMap i).map2
    ((run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val)=
      (indexedFamily S depth).coboundary1 i.succ (updated S depth i odd a b) ∧
  (indexedFamily S depth).coboundary1 i.succ ((indexedFamily S depth).coboundary0 i.succ p)=0 ∧
  hammingSupport (lowerError S depth i odd a b) ⊆ Q0 ∧
  hammingSupport ((indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b)) ⊆
    Coordinates.neighborZ (Old S depth i) Q0 ∧
  hammingSupport (updated S depth i odd a b) ⊆ star S depth i odd Q0 Z0 ∧
  hammingSupport (((indexedDecoderData S depth).selectedMap i).map1 (lowerError S depth i odd a b)) ⊆
    star S depth i odd Q0 Z0 ∧
  hammingSupport p ⊆ potentialStar S depth i odd Q0 Z0 ∧
  hammingSupport ((indexedFamily S depth).coboundary0 i.succ p) ⊆ star S depth i odd Q0 Z0 ∧
  hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
    ((run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val)) ⊆
      syndromeBlocks S depth i odd (Coordinates.neighborZ (Old S depth i) Q0)

/-- Complete actual two-run result: no filling, residual or lower preimage is supplied. -/
theorem two_run (_above : 2 ≤ i.val) (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd Q0 Z0) :
    ∃ p : Potential S depth i, Pullback S depth i odd Q0 Z0 a b p := by
  let P := Old S depth i
  let l := lowerError S depth i odd a b
  let E := updated S depth i odd a b
  let M := (indexedDecoderData S depth).selectedMap i
  have hl : hammingSupport l ⊆ Q0 := by
    change hammingSupport (lowerError S depth i odd a b) ⊆ Q0
    rw [lowerError_coordinates]
    exact Coordinates.parity_support P S Q0 Z0 _
      ((read_input_support S depth i odd Q0 Z0 _).mpr he)
  have hls := lowerError_delta S depth i odd a b
  have hlz : hammingSupport ((indexedFamily S depth).coboundary1 i.castSucc l) ⊆
      Coordinates.neighborZ P Q0 := by
    rw [indexedFamily_coboundary1]
    exact Coordinates.lower_syndrome_support P Q0 l hl
  have hinput : hammingSupport (a+b) ⊆ star S depth i odd Q0 Z0 :=
    (read_star_support S depth i odd Q0 Z0 _).mp
      (((read_input_support S depth i odd Q0 Z0 _).mpr he).trans
        (Coordinates.input_subset_star P S Q0 Z0))
  have hf := correction_difference_support S depth i odd Q0 Z0 a b he
  have hE : hammingSupport E ⊆ star S depth i odd Q0 Z0 := by
    have heq : E=(a+b)+((run S depth i odd a).correction+(run S depth i odd b).correction) := by
      dsimp only [E,updated]
      abel
    rw [heq]
    exact add_supported _ _ _ hinput (hf.trans Finset.subset_union_right)
  have hmap : hammingSupport (M.map1 l) ⊆ star S depth i odd Q0 Z0 := by
    dsimp only [M]
    apply (read_star_support S depth i odd Q0 Z0 _).mp
    rw [map1_coordinates]
    exact Coordinates.map1_support P S (state S i.val).admissible Q0 Z0 l hl
  let r := M.map1 l+E
  have hrs : hammingSupport r ⊆ star S depth i odd Q0 Z0 := add_supported _ _ _ hmap hE
  have hrc : (indexedFamily S depth).coboundary1 i.succ r=0 := by
    have hm := LinearMap.congr_fun M.commutes_coboundary1 l
    change (indexedFamily S depth).coboundary1 i.succ (M.map1 l)=
      M.map2 ((indexedFamily S depth).coboundary1 i.castSucc l) at hm
    have hdelta : (indexedFamily S depth).coboundary1 i.succ E=
        M.map2 ((run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val) :=
      updated_delta S depth i odd a b
    have hls' : (indexedFamily S depth).coboundary1 i.castSucc l=
        (run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val := hls
    dsimp only [r]
    rw [map_add,hm,hls',hdelta,twice]
  have hpc : rzQParity P S (read1 S depth i odd r)=0 := by
    let parity : Upper S depth i →ₗ[BDL26FiniteTannerSquare.Field]
        Word BDL26FiniteTannerSquare.Field P.Q :=
      (rzQParity P S).comp (read1 S depth i odd).toLinearMap
    have ha : parity (run S depth i odd a).correction=0 :=
      correction_parity_zero S depth i odd a
    have hb : parity (run S depth i odd b).correction=0 :=
      correction_parity_zero S depth i odd b
    have hEpar : parity E=l := by
      change parity ((a+b)+(run S depth i odd a).correction+(run S depth i odd b).correction)=l
      rw [map_add,map_add,ha,hb,add_zero,add_zero]
      exact (lowerError_coordinates S depth i odd a b).symm
    have hmpar : parity (M.map1 l)=l := by
      change rzQParity P S (read1 S depth i odd
        (((indexedDecoderData S depth).selectedMap i).map1 l))=l
      rw [map1_coordinates,rzQParity_map1Coord]
    change parity (M.map1 l+E)=0
    rw [map_add,hmpar,hEpar,twice]
  have hrc' : rzCoboundary1 P (state S i.val).admissible S (read1 S depth i odd r)=0 := by
    rw [← delta1_coordinates,hrc,map_zero]
  obtain ⟨pc,hpcob,hps⟩ := Coordinates.supported_filling P S (state S i.val).admissible
    (state S i.val).regular Q0 Z0 (read1 S depth i odd r) hrc' hpc
      ((read_star_support S depth i odd Q0 Z0 r).mpr hrs)
  let p := (read0 S depth i odd).symm pc
  have hp : (indexedFamily S depth).coboundary0 i.succ p=r := by
    apply (read1 S depth i odd).injective
    rw [delta0_coordinates]
    dsimp only [p]
    rw [LinearEquiv.apply_symm_apply,hpcob]
  have hpstar : hammingSupport p ⊆ potentialStar S depth i odd Q0 Z0 := by
    apply (read_support (coord0 S depth i odd) (read0 S depth i odd)
      (read0_apply S depth i odd) _ _).mp
    dsimp only [p]
    rw [LinearEquiv.apply_symm_apply]
    exact hps
  refine ⟨p,?_,hls,(updated_delta S depth i odd a b).symm,
    potential_cocycle S depth i p,hl,hlz,hE,hmap,hpstar,?_,?_⟩
  · rw [hp]
    dsimp only [r]
    symm
    calc
      _ = (E+E)+M.map1 l := by abel
      _ = _ := by rw [twice,zero_add]
  · rw [hp]
    exact hrs
  · rw [← hls]
    exact selected_map2_support S depth i odd _ _ hlz

/-- Actual input syndrome difference, with all qz-neighbour contributions retained. -/
theorem input_syndrome_support (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd Q0 Z0) :
    hammingSupport ((errorSyndrome S depth i a).val+(errorSyndrome S depth i b).val) ⊆
      syndromeBlocks S depth i odd (Coordinates.zplus (Old S depth i) Q0 Z0) := by
  change hammingSupport ((indexedFamily S depth).coboundary1 i.succ a+
    (indexedFamily S depth).coboundary1 i.succ b) ⊆ _
  rw [← map_add]
  apply (read_support (coord2 S depth i odd) (read2 S depth i odd)
    (read2_apply S depth i odd) _ _).mp
  rw [delta1_coordinates]
  exact Coordinates.syndrome_support _ S (state S i.val).admissible Q0 Z0 _
    ((read_input_support S depth i odd Q0 Z0 _).mpr he)

def coordinateOwner (p : FamilyQ S depth i.succ) : Vertex (Old S depth i) :=
  rzCorrectionOwner (Old S depth i) S (coord1 S depth i odd p)

def footprintQ (a b : Upper S depth i) : Finset (Old S depth i).Q :=
  Finset.univ.filter fun q => ∃ p ∈ hammingSupport (a+b), coordinateOwner S depth i odd p=.q q

def footprintZ (a b : Upper S depth i) : Finset (Old S depth i).Z :=
  Finset.univ.filter fun z => ∃ p ∈ hammingSupport (a+b), coordinateOwner S depth i odd p=.z z

theorem footprint_localized (a b : Upper S depth i) :
    hammingSupport (a+b) ⊆ inputBlocks S depth i odd
      (footprintQ S depth i odd a b) (footprintZ S depth i odd a b) := by
  intro p hp
  rcases hh : coord1 S depth i odd p with ⟨z,e⟩ | ⟨q,v⟩
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hh,Coordinates.mem_zBlocks_z]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,by simp [coordinateOwner,hh,rzCorrectionOwner]⟩
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hh,Coordinates.mem_qBlocks_q]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,by simp [coordinateOwner,hh,rzCorrectionOwner]⟩

/-- No caller cover: the original physical error support supplies the finite footprint. -/
theorem footprint_two_run (above : 2 ≤ i.val) (a b : Upper S depth i) :
    ∃ p : Potential S depth i, Pullback S depth i odd
      (footprintQ S depth i odd a b) (footprintZ S depth i odd a b) a b p :=
  two_run S depth i odd above _ _ a b (footprint_localized S depth i odd a b)

theorem one_q_block (above : 2 ≤ i.val) (q : (Old S depth i).Q)
    (a b : Upper S depth i) (he : hammingSupport (a+b) ⊆ qBlocks S depth i odd {q}) :
    ∃ p : Potential S depth i, Pullback S depth i odd {q} ∅ a b p := by
  apply two_run S depth i odd above
  exact he.trans Finset.subset_union_left

private theorem word_eq_of_add_zero {α : Type} (a b : Word BDL26FiniteTannerSquare.Field α) (h : a+b=0) : a=b := by
  have hh := congrArg (fun w => w+b) h
  simpa only [add_assoc,twice,add_zero,zero_add] using hh

/-- Z-local error differences are locally exact after the ORIGINAL two corrections. -/
theorem one_z_block (above : 2 ≤ i.val) (z : (Old S depth i).Z)
    (a b : Upper S depth i) (he : hammingSupport (a+b) ⊆ zBlocks S depth i odd {z}) :
    ∃ p : Potential S depth i, Pullback S depth i odd ∅ {z} a b p ∧
      lowerError S depth i odd a b=0 ∧
      (run S depth i odd a).coarse.val=(run S depth i odd b).coarse.val ∧
      updated S depth i odd a b=(indexedFamily S depth).coboundary0 i.succ p := by
  obtain ⟨p,hp⟩ := two_run S depth i odd above ∅ {z} a b (he.trans Finset.subset_union_right)
  have hl : lowerError S depth i odd a b=0 := by
    funext q
    exact zero_off _ _ hp.2.2.2.2.1 q (by simp)
  have hs := hp.2.1
  rw [hl,map_zero] at hs
  have hc := word_eq_of_add_zero _ _ hs.symm
  have hm := hp.1
  rw [hl,map_zero] at hm
  exact ⟨p,hp,hl,hc,word_eq_of_add_zero _ _ hm.symm⟩

/-- Every physical Q vertex, including either retained copy, gives its old q basis. -/
theorem lowerError_physical_q_basis (a : Upper S depth i) (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    lowerError S depth i odd a
      (a+(read1 S depth i odd).symm (canonicalBasisWord (Sum.inr ⟨q,v⟩)))=
      canonicalBasisWord q := by
  rw [lowerError_coordinates]
  have ha (w : Upper S depth i) : a+(a+w)=w := by rw [← add_assoc,twice,zero_add]
  rw [ha,LinearEquiv.apply_symm_apply]
  funext other
  have h := congrFun (rzQParity_single (Old S depth i) S q v 1) other
  by_cases ho : other=q
  · subst other
    simpa only [canonicalBasisWord,Pi.single_apply,if_pos rfl] using h
  · simpa only [canonicalBasisWord,Pi.single_apply,if_neg ho] using h

def incidentQ (x : (Old S depth i).X) : Finset (Old S depth i).Q :=
  Finset.univ.filter fun q => (Old S depth i).xq x q=true

/-- The stated OLD X-star input union; no upper-star-to-parent identification is assumed. -/
theorem old_x_star (above : 2 ≤ i.val) (x : (Old S depth i).X) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd
      (incidentQ S depth i x) (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x))) :
    ∃ p : Potential S depth i, Pullback S depth i odd
      (incidentQ S depth i x) (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x)) a b p :=
  two_run S depth i odd above _ _ a b he

theorem old_x_star_closed (x : (Old S depth i).X) :
    star S depth i odd (incidentQ S depth i x)
      (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x))=
    inputBlocks S depth i odd (incidentQ S depth i x)
      (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x)) := by
  simp only [star,Coordinates.zplus,Finset.union_self]

theorem equal_errors_zero_potential (a : Upper S depth i) :
    Pullback S depth i odd ∅ ∅ a a 0 := by
  have hu : updated S depth i odd a a=0 := by
    unfold updated
    rw [twice,zero_add,twice]
  simp only [Pullback,lowerError,twice,map_zero,hu,zero_add,add_zero,
    zero_support,Finset.empty_subset,and_self]

theorem potential_oldX_zero (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (p : Potential S depth i)
    (hp : hammingSupport p ⊆ potentialStar S depth i odd Q0 Z0)
    (x : (Old S depth i).X) (copy : BDL26FiniteTannerSquare.Two) :
    read0 S depth i odd p (.inr (x,copy))=0 := by
  rw [read0_apply]
  apply zero_off p _ hp
  simp [potentialStar,Coordinates.potentialStar]

/-- There is no RZ above-C2 step in a physical depth at most two. -/
theorem no_above_two_step (hdepth : depth ≤ 2) : ¬ 2 ≤ i.val := by omega

section TopHistory
open BDL26OwnerIncidenceMasks BDL26CanonicalHistoryMarks

def topStep (j : Nat) : StepIndex (2*j+4) := ⟨2*j+3,by omega⟩
theorem topStep_odd (j : Nat) : ¬ (topStep j).val % 2=0 := by simp only [topStep]; omega

def topOutput (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    AssemblyStepOutput (indexedDecoderData S (2*j+4)) (topStep j) :=
  BDL26CanonicalHistoryMarks.outputAt S (2*j+2)
    (errorSyndrome S (2*j+4) (topStep j) a) (Fin.last (2*j+1))

theorem topOutput_eq (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    topOutput S j a=run S (2*j+4) (topStep j) (topStep_odd j) a := by
  exact (BDL26CanonicalHistoryMarks.outputAt_top S (2*j+1)
    (errorSyndrome S (2*j+4) (topStep j) a)).trans
    (congrFun (actualStep_rz S (2*j+4) (topStep j) (topStep_odd j)) _)

/-- Both correction words below are literal snapshots of the original stopped histories. -/
theorem top_history_two_run (j : Nat)
    (Q0 : Finset (Old S (2*j+4) (topStep j)).Q)
    (Z0 : Finset (Old S (2*j+4) (topStep j)).Z)
    (a b : Upper S (2*j+4) (topStep j))
    (he : hammingSupport (a+b) ⊆ inputBlocks S (2*j+4) (topStep j) (topStep_odd j) Q0 Z0) :
    ∃ p : Potential S (2*j+4) (topStep j),
      Pullback S (2*j+4) (topStep j) (topStep_odd j) Q0 Z0 a b p ∧
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b)=
        a+b+(topOutput S j a).correction+(topOutput S j b).correction+
          (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p ∧
      (indexedFamily S (2*j+4)).coboundary1 (topStep j).castSucc
        (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b)=
        (topOutput S j a).coarse.val+(topOutput S j b).coarse.val := by
  obtain ⟨p,hp⟩ := two_run S (2*j+4) (topStep j) (topStep_odd j) (by simp [topStep]) Q0 Z0 a b he
  refine ⟨p,hp,?_,?_⟩
  · simpa only [topOutput_eq,updated] using hp.1
  · simpa only [topOutput_eq] using hp.2.1
end TopHistory

section ConstructorWitness
/-- A vertical Q edge at the actual retained old-X endpoint 0. -/
def seedQEdge (S : OddScale) : QDoubleCylinderEdge (transposePresentation baseTannerSquarePresentation)
    (4 : BaseQubit) S := Sum.inr ⟨(0 : BaseX),by decide⟩

def seedOutsideCoordinate (S : OddScale) : RZQ baseTannerSquarePresentation S :=
  .inl ⟨(1 : BaseZ),qToZDoubleCylinderEdge baseTannerSquarePresentation
    baseTannerSquareAdmissibleV4.toTannerSquareAdmissible (4 : BaseQubit) (1 : BaseZ) (by decide) S (seedQEdge S)⟩

/-- This is a constructor-boundary witness, not a canonical two-run counterexample. -/
theorem seed_boundary_outside_narrow_star (S : OddScale) :
    rzCoboundary0 baseTannerSquarePresentation baseTannerSquareAdmissibleV4 S
      (canonicalBasisWord (rzMap1QEdgeX baseTannerSquarePresentation S (4 : BaseQubit) (seedQEdge S)))
      (seedOutsideCoordinate S)=1 ∧
    seedOutsideCoordinate S ∉ Coordinates.inputBlocks baseTannerSquarePresentation S
      (Finset.univ.filter fun q => baseTannerSquarePresentation.qz q (0 : BaseZ)=true) {(0 : BaseZ)} := by
  constructor
  · have h := congrFun (rzMap1QEdge_delta0_canonicalBasis
      baseTannerSquarePresentation baseTannerSquareAdmissibleV4 S
      (4 : BaseQubit) (seedQEdge S)) (seedOutsideCoordinate S)
    apply h.trans
    unfold rzMap1QEdgeDelta0BasisImage
    simp only [Pi.add_apply,Finset.sum_apply]
    have hqzero (v : QDoubleCylinderVertex (transposePresentation baseTannerSquarePresentation)
        (4 : BaseQubit) S) :
        canonicalBasisWord (F := BDL26FiniteTannerSquare.Field)
          (Sum.inr ⟨(4 : BaseQubit),v⟩ : RZQ baseTannerSquarePresentation S)
          (seedOutsideCoordinate S)=0 := by
      simp [canonicalBasisWord,Pi.single_apply,seedOutsideCoordinate]
    have hstart := hqzero (qDoubleCylinderEdgeStart
      (transposePresentation baseTannerSquarePresentation) (4 : BaseQubit) S (seedQEdge S))
    have hend := hqzero (qDoubleCylinderEdgeEnd
      (transposePresentation baseTannerSquarePresentation) (4 : BaseQubit) S (seedQEdge S))
    let zword (z : baseTannerSquarePresentation.Z) :
        Word BDL26FiniteTannerSquare.Field (RZQ baseTannerSquarePresentation S) :=
      if hqz : baseTannerSquarePresentation.qz (4 : BaseQubit) z=true then
        canonicalBasisWord (F := BDL26FiniteTannerSquare.Field)
          (Sum.inl ⟨z,qToZDoubleCylinderEdge baseTannerSquarePresentation
            baseTannerSquareAdmissibleV4.toTannerSquareAdmissible
              (4 : BaseQubit) z hqz S (seedQEdge S)⟩ : RZQ baseTannerSquarePresentation S)
      else 0
    let zterm (z : baseTannerSquarePresentation.Z) : BDL26FiniteTannerSquare.Field :=
      zword z (seedOutsideCoordinate S)
    let zsum : BDL26FiniteTannerSquare.Field := ∑ z : baseTannerSquarePresentation.Z, zterm z
    have hone : zterm (1 : BaseZ)=1 := by
      have hqz : baseTannerSquarePresentation.qz (4 : BaseQubit) (1 : BaseZ)=true := by decide
      have he : zword (1 : BaseZ)=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field)
          (Sum.inl ⟨(1 : BaseZ),qToZDoubleCylinderEdge baseTannerSquarePresentation
            baseTannerSquareAdmissibleV4.toTannerSquareAdmissible
              (4 : BaseQubit) (1 : BaseZ) hqz S (seedQEdge S)⟩ : RZQ baseTannerSquarePresentation S) :=
        dif_pos hqz
      exact (congrFun he (seedOutsideCoordinate S)).trans (by
        simp [canonicalBasisWord,Pi.single_apply,seedOutsideCoordinate])
    have hrest (z : baseTannerSquarePresentation.Z) (_hzmem : z ∈ (Finset.univ : Finset baseTannerSquarePresentation.Z))
        (hz : z≠(1 : BaseZ)) : zterm z=0 := by
      by_cases hqz : baseTannerSquarePresentation.qz (4 : BaseQubit) z=true
      · have he : zword z=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field)
            (Sum.inl ⟨z,qToZDoubleCylinderEdge baseTannerSquarePresentation
              baseTannerSquareAdmissibleV4.toTannerSquareAdmissible
                (4 : BaseQubit) z hqz S (seedQEdge S)⟩ : RZQ baseTannerSquarePresentation S) :=
          dif_pos hqz
        have hne : seedOutsideCoordinate S ≠
            (Sum.inl ⟨z,qToZDoubleCylinderEdge baseTannerSquarePresentation
              baseTannerSquareAdmissibleV4.toTannerSquareAdmissible
                (4 : BaseQubit) z hqz S (seedQEdge S)⟩ : RZQ baseTannerSquarePresentation S) := by
          intro heq
          have hh : (1 : BaseZ)=z := congrArg
            (fun p : RZQ baseTannerSquarePresentation S => match p with
              | .inl edge => edge.1
              | .inr _ => (1 : BaseZ)) heq
          exact hz hh.symm
        exact (congrFun he (seedOutsideCoordinate S)).trans (by
          simp only [canonicalBasisWord,Pi.single_apply,if_neg hne])
      · have he : zword z=0 := dif_neg hqz
        exact congrFun he (seedOutsideCoordinate S)
    have hsum : zsum=zterm (1 : BaseZ) :=
      Finset.sum_eq_single (s := (Finset.univ : Finset baseTannerSquarePresentation.Z))
        (f := zterm) (1 : BaseZ) hrest
        (fun hn => False.elim (hn (Finset.mem_univ _)))
    have hzsum : zsum=1 := hsum.trans hone
    exact (congrArg₂ (fun x y : BDL26FiniteTannerSquare.Field => x+y+zsum)
      hstart hend).trans (by simpa only [zero_add] using hzsum)
  · have hn : (1 : BaseZ) ∉ ({(0 : BaseZ)} : Finset BaseZ) := by decide
    intro hin
    apply hn
    exact (Coordinates.mem_input_z baseTannerSquarePresentation S _ _ (1 : BaseZ) _).mp hin
end ConstructorWitness
end QEC.Coding.BDL26RZFiniteBlockTransport
