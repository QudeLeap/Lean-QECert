import QEC.Coding.FiniteAlternatingConstruction.RXQBlockTransport

/-!
# Actual RX Q-leaf owners, assembly labels and adjacent parents

The coordinate data are the original RX adapter and raw owner fibres. The
parent is the original intrinsic-zero-cell graph parent. Native selected
syndrome images have incident Z parents; they are not assigned a Q parent.
This module constructs no lower error transport or stabilizer witness and
asserts no component-mask, history restriction or stability conclusion.
-/
noncomputable section
namespace QEC.Coding.BDL26RXQConcreteCoherence
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData (cqComponentTotal)
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26AlternatingCochain
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge
  (tannerCoboundary0 tannerCoboundary1 tannerCoboundary1_canonicalBasis_apply)
open scoped Classical BigOperators

/-! Naturality applies to the already proved complete raw/actual HEq data. -/
private theorem heq_apply_cast {A B C : Type} (h : A=B)
    (f : A → C) (g : B → C) (hf : HEq f g) (x : B) :
    f ((Equiv.cast h.symm) x)=g x := by
  cases h
  cases hf
  rfl

private theorem heq_finset_cast {A B L : Type} (h : A=B)
    (f : L → Finset A) (g : L → Finset B) (hf : HEq f g) (x : L) :
    f x=(g x).map (Equiv.cast h.symm).toEmbedding := by
  cases h
  cases hf
  ext a
  simp

private theorem cast_vertex_q (U V : TannerSquarePresentation) (hp : U=V)
    (hv : Vertex U=Vertex V) (hq : V.Q=U.Q) (q : V.Q) :
    cast hv (Vertex.q ((Equiv.cast hq) q))=Vertex.q q := by
  cases hp
  rfl

private theorem cast_vertex_z (U V : TannerSquarePresentation) (hp : U=V)
    (hv : Vertex U=Vertex V) (hz : V.Z=U.Z) (z : V.Z) :
    cast hv (Vertex.z ((Equiv.cast hz) z))=Vertex.z z := by
  cases hp
  rfl

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

private theorem successor_eq (h : i.val%2=0) :
    state S (i.val+1)=rxState S (state S i.val) := by
  change nextState S i.val (state S i.val)=_
  exact if_pos h

/-- The full old-Z physical chart uses only the defining actual successor. -/
def physicalZEquiv (h : i.val%2=0) :
    RX2 (state S i.val).presentation S ≃ FamilyZ S depth i.succ :=
  Equiv.cast (congrArg (fun C : ConstructionState => C.presentation.Z)
    (successor_eq S depth i h)).symm

/-- Exact raw/actual region equality, not a caller coherence certificate. -/
theorem correctionRegion_eq_raw (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) :
    (rxLq S depth i h).correctionRegion q =
      (fiberRegion (rxCorrectionOwner (state S i.val).presentation S) (Vertex.q q)).map
        (rxPhysicalQEquiv S depth i h).toEmbedding := by
  exact heq_finset_cast
    (congrArg (fun C : ConstructionState => C.presentation.Q) (successor_eq S depth i h))
    (rxLq S depth i h).correctionRegion
    (localQ (state S i.val).presentation S).correctionRegion
    (rxData_coordinates S depth i h).2.2.2.1 q

/-- The actual local Q syndrome region is the original raw Q-owner fibre. -/
theorem syndromeRegion_eq_raw (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) :
    (rxLq S depth i h).syndromeRegion q =
      (fiberRegion (rxSyndromeOwner (state S i.val).presentation S) (Vertex.q q)).map
        (physicalZEquiv S depth i h).toEmbedding := by
  exact heq_finset_cast
    (congrArg (fun C : ConstructionState => C.presentation.Z) (successor_eq S depth i h))
    (rxLq S depth i h).syndromeRegion
    (localQ (state S i.val).presentation S).syndromeRegion
    (rxData_coordinates S depth i h).2.2.1 q

/-- The actual owner on the physical Q chart is the original raw owner. -/
theorem correctionOwner_chart (h : i.val%2=0)
    (r : RX1 (state S i.val).presentation S) :
    vertexEquiv (state S i.val).presentation
      (correctionOwnerAt S depth i h (rxPhysicalQEquiv S depth i h r)) =
        rxCorrectionOwner (state S i.val).presentation S r := by
  have he := heq_apply_cast
    (congrArg (fun C : ConstructionState => C.presentation.Q) (successor_eq S depth i h))
    (correctionOwnerAt S depth i h)
    (fun p => (vertexEquiv (state S i.val).presentation).symm
      (rxCorrectionOwner (state S i.val).presentation S p))
    (rxData_coordinates S depth i h).2.2.2.2.2.2.2 r
  exact (congrArg (vertexEquiv (state S i.val).presentation) he).trans
    (Equiv.apply_symm_apply _ _)

/-- All raw Q-coordinate tags compute the existing adjacent graph parent. -/
theorem physicalQ_parent (h : i.val%2=0)
    (r : RX1 (state S i.val).presentation S) :
    parent S (i.val+1) (Vertex.q (rxPhysicalQEquiv S depth i h r)) =
      rxParent (state S i.val).presentation S (Vertex.q r) := by
  simp only [parent,nextParent,dif_pos h,nextRXVertex,rxPhysicalQEquiv]
  erw [cast_vertex_q _ _
    (congrArg ConstructionState.presentation (successor_eq S depth i h))] <;> rfl

/-- The corresponding statement for the original selected syndrome carrier. -/
theorem physicalZ_parent (h : i.val%2=0)
    (r : RX2 (state S i.val).presentation S) :
    parent S (i.val+1) (Vertex.z (physicalZEquiv S depth i h r)) =
      rxParent (state S i.val).presentation S (Vertex.z r) := by
  simp only [parent,nextParent,dif_pos h,nextRXVertex,physicalZEquiv]
  erw [cast_vertex_z _ _
    (congrArg ConstructionState.presentation (successor_eq S depth i h))] <;> rfl

/-- Q-leaf syndrome edges are positive-dimensional, hence unparented. -/
theorem syndromeRegion_parent_none (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ (rxLq S depth i h).syndromeRegion q) :
    parent S (i.val+1) (Vertex.z p)=none := by
  rw [syndromeRegion_eq_raw] at hp
  obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hp
  have ho := (Finset.mem_filter.mp hr).2
  have hz : rxParent (state S i.val).presentation S (Vertex.z r)=none := by
    rcases r with (⟨x,f⟩ | ⟨t,e⟩) | ⟨z,c⟩
    · cases ho
    · rfl
    · cases ho
  exact (physicalZ_parent S depth i h r).trans hz

/-- Literal raw owner membership on every physical chart coordinate. -/
theorem correctionRegion_chart_iff (h : i.val%2=0)
    (q : (state S i.val).presentation.Q)
    (r : RX1 (state S i.val).presentation S) :
    rxPhysicalQEquiv S depth i h r ∈ (rxLq S depth i h).correctionRegion q ↔
      rxCorrectionOwner (state S i.val).presentation S r=Vertex.q q := by
  rw [correctionRegion_eq_raw]
  constructor
  · intro hm
    obtain ⟨t,ht,he⟩ := Finset.mem_map.mp hm
    have hr : t=r := (rxPhysicalQEquiv S depth i h).injective he
    subst t
    exact (Finset.mem_filter.mp ht).2
  · intro hr
    exact Finset.mem_map.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,rfl⟩

/-- The concrete Q correction fibre is exactly the real Q-parent fibre. -/
theorem correctionRegion_parent_iff (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) (p : FamilyQ S depth i.succ) :
    p ∈ (rxLq S depth i h).correctionRegion q ↔
      parent S (i.val+1) (Vertex.q p)=some (Vertex.q q) := by
  obtain ⟨r,rfl⟩ := (rxPhysicalQEquiv S depth i h).surjective p
  rw [correctionRegion_chart_iff,physicalQ_parent]
  rcases r with ⟨x,e⟩ | ⟨r,v⟩
  · constructor <;> intro he <;> cases he
  · constructor
    · intro he
      have hrq : r=q := Vertex.q.inj he
      exact congrArg (fun t => some (Vertex.q t)) hrq
    · intro he
      have hrq : r=q := Vertex.q.inj (Option.some.inj he)
      exact congrArg Vertex.q hrq

/-- This consumes the original #848 incidence theorem, not a second graph. -/
theorem correctionRegion_localRegion_iff (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) (p : FamilyQ S depth i.succ) :
    p ∈ (rxLq S depth i h).correctionRegion q ↔
      Vertex.q p ∈ localRegion S (i.val+1) (Vertex.q q) :=
  (correctionRegion_parent_iff S depth i h q p).trans
    (parent_mem_iff S (i.val+1) (Vertex.q q) (Vertex.q p))

/-- Actual cylinder charts retain their raw tag, owner and genuine parent. -/
theorem q_chart_coherent (h : i.val%2=0)
    (q : (state S i.val).presentation.Q)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    (rxQVertexEquiv S depth i h q v).val =
      rxPhysicalQEquiv S depth i h (.inr ⟨q,v⟩) ∧
    vertexEquiv (state S i.val).presentation
      (correctionOwnerAt S depth i h (rxQVertexEquiv S depth i h q v).val)=Vertex.q q ∧
    parent S (i.val+1) (Vertex.q (rxQVertexEquiv S depth i h q v).val)=some (Vertex.q q) := by
  refine ⟨rxQVertexEquiv_val S depth i h q v,?_,?_⟩
  · rw [rxQVertexEquiv_val,correctionOwner_chart]
    rfl
  · exact (correctionRegion_parent_iff S depth i h q _).mp
      (rxQVertexEquiv S depth i h q v).property

/-- Raw syndrome owner equality on the complete native physical chart. -/
theorem topCenter_chart (h : i.val%2=0)
    (r : RX2 (state S i.val).presentation S) :
    vertexEquiv (state S i.val).presentation
      ((rxData S depth i h).topCenter (physicalZEquiv S depth i h r)) =
        rxSyndromeOwner (state S i.val).presentation S r := by
  have he := heq_apply_cast
    (congrArg (fun C : ConstructionState => C.presentation.Z) (successor_eq S depth i h))
    (rxData S depth i h).topCenter (topCenter (state S i.val).presentation S)
    (rxData_coordinates S depth i h).2.2.2.2.2.2.1 r
  exact (congrArg (vertexEquiv (state S i.val).presentation) he).trans
    (Equiv.apply_symm_apply _ _)

private theorem raw_z_owner_parent (P : TannerSquarePresentation) (S : OddScale)
    (r : RX2 P S) (z : P.Z) (hr : rxSyndromeOwner P S r=Vertex.z z) :
    rxParent P S (Vertex.z r)=some (Vertex.z z) := by
  rcases r with (⟨x,f⟩ | ⟨q,e⟩) | ⟨w,c⟩
  · cases hr
  · cases hr
  · have hw : w=z := Vertex.z.inj hr
    subst w
    rfl

/-- Every actual selected old-Z chart has its Z parent, for BOTH copies. -/
theorem oldZ_pair_parent (h : i.val%2=0)
    (z : (state S i.val).presentation.Z) (copy : Fin 2) :
    parent S (i.val+1)
      (Vertex.z ((rxData S depth i h).induced.zPairEquiv (z,copy)).val)=some (Vertex.z z) := by
  let p := ((rxData S depth i h).induced.zPairEquiv (z,copy)).val
  let r := (physicalZEquiv S depth i h).symm p
  have hc : vertexEquiv (state S i.val).presentation ((rxData S depth i h).topCenter p)=
      Vertex.z z := congrArg (vertexEquiv (state S i.val).presentation)
        ((rxData S depth i h).topCenter_coarse_pair z copy)
  have hr : rxSyndromeOwner (state S i.val).presentation S r=Vertex.z z := by
    have he := topCenter_chart S depth i h r
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans hc
  have hp := physicalZ_parent S depth i h r
  rw [Equiv.apply_symm_apply] at hp
  exact hp.trans (raw_z_owner_parent _ S r z hr)

/-- The canonical assembly list supplies the Q label internally. -/
def qComponentIndex (h : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) :
    Fin (rxStepOutput S depth i h sigma).localComponents.length :=
  Classical.choose ((componentOwner_bijective S depth i h sigma).2 (.inr (.inl q)))

theorem qComponentIndex_owner (h : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) :
    componentOwner S depth i h sigma (qComponentIndex S depth i h sigma q)=.inr (.inl q) :=
  Classical.choose_spec ((componentOwner_bijective S depth i h sigma).2 (.inr (.inl q)))

/-- Exact #815 local piece, owner label and unchanged stored supports. -/
theorem q_assembly_snapshot (h : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) :
    let j := qComponentIndex S depth i h sigma q
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).owner=some (Vertex.q q) ∧
    (rxStepOutput S depth i h sigma).componentAt j=
      cqComponentTotal (rxData S depth i h) sigma.val q ∧
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).correctionSupport=
      (rxStepOutput S depth i h sigma).componentSupportAt j ∧
    ((rxStepOutput_ownerLabels S depth i h sigma).label j).coboundarySupport=
      hammingSupport ((rxStepOutput S depth i h sigma).componentCoboundaryAt j) := by
  dsimp only
  have hs := rxStepOutput_owner_snapshot S depth i h sigma (qComponentIndex S depth i h sigma q)
  refine ⟨?_,rxStepOutput_component_q S depth i h sigma _ q
    (qComponentIndex_owner S depth i h sigma q),hs.2.1,hs.2.2⟩
  rw [qComponentIndex_owner] at hs
  exact hs.1

/-- Every coordinate of this real assembly piece lies in its actual Q fibre. -/
theorem q_assembly_supported (h : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) :
    (rxStepOutput S depth i h sigma).componentSupportAt
      (qComponentIndex S depth i h sigma q) ⊆ (rxLq S depth i h).correctionRegion q := by
  have hs := rxStepOutput_component_supported S depth i h sigma (qComponentIndex S depth i h sigma q)
  rw [qComponentIndex_owner] at hs
  exact hs

theorem q_assembly_parent (h : i.val%2=0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) (p : FamilyQ S depth i.succ)
    (hp : p ∈ (rxStepOutput S depth i h sigma).componentSupportAt
      (qComponentIndex S depth i h sigma q)) :
    parent S (i.val+1) (Vertex.q p)=some (Vertex.q q) :=
  (correctionRegion_parent_iff S depth i h q p).mp
    (q_assembly_supported S depth i h sigma q hp)

/-- The actual native selected syndrome of one original lower Q basis word. -/
def basisImage (q : (state S i.val).presentation.Q) : Word BDL26Field (FamilyZ S depth i.succ) :=
  ((indexedDecoderData S depth).selectedMap i).map2
    ((indexedFamily S depth).coboundary1 i.castSucc (canonicalBasisWord q))

/-- This is the COMPLETE actual upper syndrome of its actual lifted basis word. -/
theorem basisImage_native_syndrome (q : (state S i.val).presentation.Q) :
    basisImage S depth i q=(indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q)) := by
  exact (LinearMap.congr_fun
    (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1)
    (canonicalBasisWord (F:=BDL26Field) q)).symm

/-- A genuine original valid input, without a caller preimage certificate. -/
def basisInput (q : (state S i.val).presentation.Q) : (indexedFamily S depth).Syndrome i.succ :=
  ⟨basisImage S depth i q,⟨((indexedDecoderData S depth).selectedMap i).map1
    (canonicalBasisWord q),(basisImage_native_syndrome S depth i q).symm⟩⟩

private theorem selected_rx (h : i.val%2=0) :
    (indexedDecoderData S depth).selectedMap i=(indexedDecoderData S depth).rxMap i := by
  rw [selectedMap_eq]
  rfl

theorem basisImage_pair (h : i.val%2=0) (q : (state S i.val).presentation.Q)
    (z : (state S i.val).presentation.Z) (copy : Fin 2) :
    basisImage S depth i q ((rxData S depth i h).induced.zPairEquiv (z,copy)).val =
      if (state S i.val).presentation.qz q z=true then 1 else 0 := by
  rw [basisImage,selected_rx S depth i h,(rxData S depth i h).induced.map2_diagonal,
    indexedFamily_coboundary1,tannerCoboundary1_canonicalBasis_apply]
  rfl

theorem basisImage_exterior (h : i.val%2=0) (q : (state S i.val).presentation.Q)
    (p : FamilyZ S depth i.succ) (hp : p ∉ (rxData S depth i h).zSector) :
    basisImage S depth i q p=0 := by
  rw [basisImage,selected_rx S depth i h]
  exact (rxData S depth i h).induced.map2_auxiliary_zero _ p
    (by simpa only [← (rxData S depth i h).zSector_eq_induced] using hp)

/-- Exhaustive support; no upper syndrome coordinates are discarded. -/
theorem basisImage_mem_iff (h : i.val%2=0) (q : (state S i.val).presentation.Q)
    (p : FamilyZ S depth i.succ) :
    p ∈ hammingSupport (basisImage S depth i q) ↔
      ∃ (z : (state S i.val).presentation.Z) (copy : Fin 2),
        (state S i.val).presentation.qz q z=true ∧
        ((rxData S depth i h).induced.zPairEquiv (z,copy)).val=p := by
  constructor
  · intro hm
    have hn := (Finset.mem_filter.mp hm).2
    have hz : p ∈ (rxData S depth i h).zSector := by
      by_contra hp
      exact hn (basisImage_exterior S depth i h q p hp)
    let pp : LocalRegionIndex (rxData S depth i h).induced.zSector :=
      ⟨p,by simpa only [← (rxData S depth i h).zSector_eq_induced] using hz⟩
    obtain ⟨⟨z,copy⟩,he⟩ := (rxData S depth i h).induced.zPairEquiv.surjective pp
    have hv : ((rxData S depth i h).induced.zPairEquiv (z,copy)).val=p := congrArg Subtype.val he
    refine ⟨z,copy,?_,hv⟩
    by_contra hqz
    have hz0 : basisImage S depth i q
        ((rxData S depth i h).induced.zPairEquiv (z,copy)).val=0 := by
      rw [basisImage_pair,if_neg hqz]
    exact hn ((congrArg (basisImage S depth i q) hv).symm.trans hz0)
  · rintro ⟨z,copy,hqz,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [basisImage_pair,if_pos hqz]; exact one_ne_zero⟩

/-- The whole support is exactly the original two-copy incident-Z region. -/
theorem basisImage_support (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    hammingSupport (basisImage S depth i q)=
      BDL26RXQBlockTransport.twoCopyIncidentZ S depth i h q := by
  ext p
  constructor
  · intro hp
    obtain ⟨z,copy,hz,hv⟩ := (basisImage_mem_iff S depth i h q p).mp hp
    apply Finset.mem_image.mpr
    exact ⟨(z,copy),Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,Finset.mem_univ _⟩,hv⟩
  · intro hp
    obtain ⟨⟨z,copy⟩,hz,hv⟩ := Finset.mem_image.mp hp
    exact (basisImage_mem_iff S depth i h q p).mpr
      ⟨z,copy,(Finset.mem_filter.mp (Finset.mem_product.mp hz).1).2,hv⟩

/-- No positive-dimensional local-Q syndrome is a native selected image coordinate. -/
theorem basisImage_localQ_zero (h : i.val%2=0)
    (q t : (state S i.val).presentation.Q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ (rxLq S depth i h).syndromeRegion t) :
    basisImage S depth i q p=0 := by
  by_contra hn
  have hm : p ∈ hammingSupport (basisImage S depth i q) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
  obtain ⟨z,copy,_,hv⟩ := (basisImage_mem_iff S depth i h q p).mp hm
  have he := (oldZ_pair_parent S depth i h z copy).symm.trans
    ((congrArg (fun p => parent S (i.val+1) (Vertex.z p)) hv).trans
      (syndromeRegion_parent_none S depth i h t p hp))
  cases he

/-- Both selected old-Z copies are retained as distinct actual coordinates. -/
theorem oldZ_pair_distinct (h : i.val%2=0) (z : (state S i.val).presentation.Z) :
    ((rxData S depth i h).induced.zPairEquiv (z,0)).val ≠
      ((rxData S depth i h).induced.zPairEquiv (z,1)).val := by
  intro he
  have hp := (rxData S depth i h).induced.zPairEquiv.injective (Subtype.ext he)
  exact (show (0 : Fin 2)≠1 by decide) (congrArg Prod.snd hp)

/-- Exact parent image of the full selected syndrome support. -/
theorem basisImage_parent_image (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    (hammingSupport (basisImage S depth i q)).image
      (fun p => parent S (i.val+1) (Vertex.z p)) =
      (BDL26RXQBlockTransport.incidentZ S i q).image (fun z => some (Vertex.z z)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨p,hp,hpu⟩ := Finset.mem_image.mp hu
    obtain ⟨z,copy,hz,hv⟩ := (basisImage_mem_iff S depth i h q p).mp hp
    apply Finset.mem_image.mpr
    refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,?_⟩
    exact (oldZ_pair_parent S depth i h z copy).symm.trans
      ((congrArg (fun p => parent S (i.val+1) (Vertex.z p)) hv).trans hpu)
  · intro hu
    obtain ⟨z,hz,hzu⟩ := Finset.mem_image.mp hu
    let p := ((rxData S depth i h).induced.zPairEquiv (z,0)).val
    apply Finset.mem_image.mpr
    refine ⟨p,(basisImage_mem_iff S depth i h q p).mpr
      ⟨z,0,(Finset.mem_filter.mp hz).2,rfl⟩,?_⟩
    exact (oldZ_pair_parent S depth i h z 0).trans hzu

/-- A nonzero actual incidence is supplied internally by the original state. -/
theorem basisImage_incident_value (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) (copy : Fin 2) :
    basisImage S depth i q ((rxData S depth i h).induced.zPairEquiv
      (BDL26RXQBlockTransport.incidentWitness S i q,copy)).val=1 := by
  rw [basisImage_pair,if_pos (BDL26RXQBlockTransport.incidentWitness_mem S i q)]

theorem basisImage_nonzero (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    basisImage S depth i q≠0 := by
  intro he
  have hv := congrFun he ((rxData S depth i h).induced.zPairEquiv
    (BDL26RXQBlockTransport.incidentWitness S i q,0)).val
  rw [basisImage_incident_value] at hv
  exact one_ne_zero hv

/-- This is a Z-parent image, and cannot be claimed to be a single Q fibre. -/
theorem basisImage_not_q_parent (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    ∃ p ∈ hammingSupport (basisImage S depth i q),
      parent S (i.val+1) (Vertex.z p)≠some (Vertex.q q) := by
  let z := BDL26RXQBlockTransport.incidentWitness S i q
  let p := ((rxData S depth i h).induced.zPairEquiv (z,0)).val
  refine ⟨p,(basisImage_mem_iff S depth i h q p).mpr
    ⟨z,0,BDL26RXQBlockTransport.incidentWitness_mem S i q,rfl⟩,?_⟩
  rw [oldZ_pair_parent]
  intro he
  cases he

/-- An internally constructed positive-dimensional Q-cylinder edge. -/
def connectorEdge (q : (state S i.val).presentation.Q) :
    QDoubleCylinderEdge (state S i.val).presentation q S :=
  .inl (0,⟨BDL26RXQBlockTransport.incidentWitness S i q,
    BDL26RXQBlockTransport.incidentWitness_mem S i q⟩,⟨0,S.half_pos⟩)

/-- An actual original unparented syndrome connector, not supplied by a caller. -/
def connector (h : i.val%2=0) (q : (state S i.val).presentation.Q) : FamilyZ S depth i.succ :=
  physicalZEquiv S depth i h (.inl (.inr ⟨q,connectorEdge S depth i q⟩))

theorem connector_parent_none (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    parent S (i.val+1) (Vertex.z (connector S depth i h q))=none := by
  exact physicalZ_parent S depth i h (.inl (.inr ⟨q,connectorEdge S depth i q⟩))

theorem connector_exterior (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    connector S depth i h q ∉ (rxData S depth i h).zSector := by
  intro hp
  rw [(rxData S depth i h).zSector_eq_regions] at hp
  change connector S depth i h q ∈
    (Finset.univ.biUnion fun z => (rxLz S depth i h).syndromeRegion z) at hp
  obtain ⟨z,_,hz⟩ := Finset.mem_biUnion.mp hp
  have hc := ((rxData S depth i h).topCenter_z_iff z (connector S depth i h q)).mp hz
  have hr := topCenter_chart S depth i h (.inl (.inr ⟨q,connectorEdge S depth i q⟩))
  have he := congrArg (vertexEquiv (state S i.val).presentation) hc
  have bad : Vertex.q q=Vertex.z z := hr.symm.trans he
  cases bad

theorem connector_value_zero (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    basisImage S depth i q (connector S depth i h q)=0 :=
  basisImage_exterior S depth i h q _ (connector_exterior S depth i h q)

/-- Nontrivial finite data on every actual RX level and every scale. -/
theorem finite_basis_classification (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    (let p := (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val
     p ∈ (rxLq S depth i h).correctionRegion q ∧
       parent S (i.val+1) (Vertex.q p)=some (Vertex.q q)) ∧
    ((rxStepOutput_ownerLabels S depth i h (basisInput S depth i q)).label
      (qComponentIndex S depth i h (basisInput S depth i q) q)).owner=some (Vertex.q q) ∧
    basisImage S depth i q≠0 ∧
    (∀ copy : Fin 2, basisImage S depth i q ((rxData S depth i h).induced.zPairEquiv
      (BDL26RXQBlockTransport.incidentWitness S i q,copy)).val=1) ∧
    parent S (i.val+1) (Vertex.z (connector S depth i h q))=none ∧
    basisImage S depth i q (connector S depth i h q)=0 := by
  refine ⟨⟨(rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property,
    (q_chart_coherent S depth i h q _).2.2⟩,?_,basisImage_nonzero S depth i h q,
    basisImage_incident_value S depth i h q,connector_parent_none S depth i h q,
    connector_value_zero S depth i h q⟩
  exact (q_assembly_snapshot S depth i h (basisInput S depth i q) q).1

end QEC.Coding.BDL26RXQConcreteCoherence
end
