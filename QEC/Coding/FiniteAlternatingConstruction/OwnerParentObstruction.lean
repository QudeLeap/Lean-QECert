import QEC.Coding.FiniteAlternatingConstruction.XLocalRadialParity
import QEC.Coding.FiniteAlternatingConstruction.RXPresentationCochain
import QEC.Coding.FiniteAlternatingConstruction.DecodingGraph
import QEC.Coding.FiniteAlternatingConstruction.ReplacementSupport
import QEC.Coding.FiniteAlternatingConstruction.ReplacementCochainMaps

/-!
# The limit of parent-fibre support for alternating maps

A local block label records every cell of a local complex. Graph parents record
only intrinsic zero cells. Consequently the next RZ map can preserve a coordinate
whose upper block label has no graph parent. These exact constructor witnesses
rule out identifying all selected-map target regions with fibres of the graph
parent composed with the upper block label.
-/

namespace QEC.Coding.BDL26OwnerParentObstruction

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical

private theorem rzMap1_basis_at_root
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    map1Coord P A S (canonicalBasisWord q)
      (Sum.inr ⟨q, rzMap1QRoot P q S⟩) = 1 := by
  calc
    _ = map1BasisImage P A S q (Sum.inr ⟨q, rzMap1QRoot P q S⟩) :=
      congrFun (map1Coord_canonicalBasis P A S q) _
    _ = 1 :=
      (map1BasisImage_apply_q P A S q ⟨q, rzMap1QRoot P q S⟩).trans (if_pos rfl)

private theorem rzMap2_basis_at_root
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) :
    map2Coord P A S (canonicalBasisWord z) ⟨z, rzMap1ZRoot P A z S⟩ = 1 := by
  calc
    _ = rzMap2BasisImage P A S z ⟨z, rzMap1ZRoot P A z S⟩ :=
      congrFun (rzMap2BasisImage_eq P A S z) _
    _ = 1 := by simp [rzMap2BasisImage, canonicalBasisWord]

/-- An RX local X-edge survives the next RZ map at its distinguished Q root,
although its upper local label has no adjacent graph parent. -/
theorem rz_after_rx_local_edge_obstruction
    (P : TannerSquarePresentation) (S : OddScale)
    (A : TannerSquareAdmissibleV4 (rxReplacementPresentation P S))
    (x : P.X) (edge : DoubleCylinderEdge P x S) :
    let q : (rxReplacementPresentation P S).Q := Sum.inl ⟨x, edge⟩
    let target : RZQ (rxReplacementPresentation P S) S :=
      Sum.inr ⟨q, rzMap1QRoot (rxReplacementPresentation P S) q S⟩
    map1Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord q) target = 1 ∧
      rxCorrectionOwner P S q = .x x ∧
      rxParent P S (rzCorrectionOwner (rxReplacementPresentation P S) S target) = none := by
  dsimp only
  constructor
  · exact rzMap1_basis_at_root (rxReplacementPresentation P S) A S (Sum.inl ⟨x, edge⟩)
  · exact ⟨rfl, rfl⟩

/-- The same obstruction already occurs in degree two, without any connector
chain: the RZ map sends an RX local X-face to one Z root. -/
theorem rz_after_rx_local_face_obstruction
    (P : TannerSquarePresentation) (S : OddScale)
    (A : TannerSquareAdmissibleV4 (rxReplacementPresentation P S))
    (x : P.X) (face : DoubleCylinderFace P x S) :
    let z : (rxReplacementPresentation P S).Z := Sum.inl (Sum.inl ⟨x, face⟩)
    let target : RZZ (rxReplacementPresentation P S) S :=
      ⟨z, rzMap1ZRoot (rxReplacementPresentation P S) A z S⟩
    map2Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord z) target = 1 ∧
      rxSyndromeOwner P S z = .x x ∧
      rxParent P S (.z (rzSyndromeOwner (rxReplacementPresentation P S) S target)) = none := by
  dsimp only
  constructor
  · exact rzMap2_basis_at_root (rxReplacementPresentation P S) A S
      (Sum.inl (Sum.inl ⟨x, face⟩))
  · exact ⟨rfl, rfl⟩

/-- Thus the proposed universal parent-fibre condition on the degree-one
basis images is false for any actual RX local edge. -/
theorem not_rz_after_rx_degree_one_parent_fibres
    (P : TannerSquarePresentation) (S : OddScale)
    (A : TannerSquareAdmissibleV4 (rxReplacementPresentation P S))
    (x : P.X) (edge : DoubleCylinderEdge P x S) :
    ¬ (∀ (source : (rxReplacementPresentation P S).Q)
      (target : RZQ (rxReplacementPresentation P S) S),
      map1Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord source) target ≠ 0 →
      rxParent P S (rzCorrectionOwner (rxReplacementPresentation P S) S target) =
        some (rxCorrectionOwner P S source)) := by
  intro h
  have hw := rz_after_rx_local_edge_obstruction P S A x edge
  dsimp only at hw
  have hne : map1Coord (rxReplacementPresentation P S) A S
      (canonicalBasisWord (Sum.inl ⟨x, edge⟩))
      (Sum.inr ⟨Sum.inl ⟨x, edge⟩,
        rzMap1QRoot (rxReplacementPresentation P S) (Sum.inl ⟨x, edge⟩) S⟩) ≠ 0 := by
    rw [hw.1]
    exact one_ne_zero
  have hh := h _ _ hne
  rw [hw.2.2] at hh
  cases hh

/-- In particular, the degree-two target-parent-fibre condition is false.
This is a basis-level obstruction, before any decoder or history restriction. -/
theorem not_rz_after_rx_degree_two_parent_fibres
    (P : TannerSquarePresentation) (S : OddScale)
    (A : TannerSquareAdmissibleV4 (rxReplacementPresentation P S))
    (x : P.X) (face : DoubleCylinderFace P x S) :
    ¬ (∀ (source : (rxReplacementPresentation P S).Z)
      (target : RZZ (rxReplacementPresentation P S) S),
      map2Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord source) target ≠ 0 →
      rxParent P S (.z (rzSyndromeOwner (rxReplacementPresentation P S) S target)) =
        some (rxSyndromeOwner P S source)) := by
  intro h
  have hw := rz_after_rx_local_face_obstruction P S A x face
  dsimp only at hw
  have hne : map2Coord (rxReplacementPresentation P S) A S
      (canonicalBasisWord (Sum.inl (Sum.inl ⟨x, face⟩)))
      ⟨Sum.inl (Sum.inl ⟨x, face⟩), rzMap1ZRoot (rxReplacementPresentation P S)
        A (Sum.inl (Sum.inl ⟨x, face⟩)) S⟩ ≠ 0 := by
    rw [hw.1]
    exact one_ne_zero
  have hh := h _ _ hne
  rw [hw.2.2] at hh
  cases hh

/-- Copy zero of the lower-left small square in the base face numbered zero. -/
def baseLocalFace : DoubleCylinderFace baseTannerSquarePresentation
    (0 : BDL26FiniteAlternatingCore.BaseX) scaleFive :=
  Sum.inl ((0 : Fin 2), (⟨(0 : BaseFace), by decide⟩,
    ⟨0, OddScale.half_pos scaleFive⟩, ⟨0, OddScale.half_pos scaleFive⟩))

/-- Fully materialized scale-five counterexample, with the successor's proved
admissibility rather than an assumed valid replacement. -/
theorem base_scale_five_not_degree_two_parent_fibres :
    let P := baseTannerSquarePresentation
    let S := scaleFive
    let A := (rxState S baseState).admissible
    ¬ (∀ (source : (rxReplacementPresentation P S).Z)
      (target : RZZ (rxReplacementPresentation P S) S),
      map2Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord source) target ≠ 0 →
      rxParent P S (.z (rzSyndromeOwner (rxReplacementPresentation P S) S target)) =
        some (rxSyndromeOwner P S source)) :=
  not_rz_after_rx_degree_two_parent_fibres baseTannerSquarePresentation scaleFive
    (rxState scaleFive baseState).admissible
    (0 : BDL26FiniteAlternatingCore.BaseX) baseLocalFace

/-! ## Genuine syndromes at the physical third and fourth levels -/

open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators

/-- Extend one local X-block correction by zero in the actual RX carrier. -/
noncomputable def extendXCorrection (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (e : Word BDL26Field (DoubleCylinderEdge P x S)) :
    Word BDL26Field (RX1 P S) := fun target => match target with
  | .inl ⟨y, edge⟩ => if h : y = x then e (h ▸ edge) else 0
  | .inr _ => 0

@[simp] theorem extendXCorrection_at_x (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (e : Word BDL26Field (DoubleCylinderEdge P x S))
    (edge : DoubleCylinderEdge P x S) :
    extendXCorrection P S x e (.inl ⟨x,edge⟩) = e edge := by
  simp [extendXCorrection]

/-- Zero connecting cost means every actual adjacent Q restriction vanishes. -/
theorem radialGauge_restriction_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (selected : Fin 2) (alpha : Neighbor P x → BDL26Field)
    (q : P.Q) (hq : P.xq x q = true) :
    rxXQDegreeOne P A q x hq S (radialGauge P A x S selected alpha) = 0 := by
  have hz := radialGauge_connectingWeight_zero P A x S selected alpha
  have hle := Finset.single_le_sum (fun (r : Neighbor P x) _ =>
    Nat.zero_le (HammingWeight (rxXQDegreeOne P A r.val x r.property S
      (radialGauge P A x S selected alpha)))) (Finset.mem_univ (⟨q,hq⟩ : Neighbor P x))
  change HammingWeight (rxXQDegreeOne P A q x hq S
    (radialGauge P A x S selected alpha)) ≤ connectingWeight P A x S _ at hle
  rw [hz] at hle
  exact (HammingWeight_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hle)

/-- A radial gauge extended into X creates no syndrome outside that X block. -/
theorem extendedRadialGauge_supported (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (selected : Fin 2) (alpha : Neighbor P x → BDL26Field)
    (z : RX2 P S) (hz : rxSyndromeOwner P S z ≠ .x x) :
    wordLinearMapTranspose (rxBoundary2 P S)
      (extendXCorrection P S x (radialGauge P A x S selected alpha)) z = 0 := by
  classical
  let e := extendXCorrection P S x (radialGauge P A x S selected alpha)
  have hQZ : rxConnectingQZ1 P S e = 0 :=
    rxConnectingQZ1_zero_on_x P S e (fun _ => rfl)
  rw [rxDelta1_decomposition]
  change rxLocalDelta1 P S e z + rxConnectingXQ1 P S e z + rxConnectingQZ1 P S e z = 0
  rw [hQZ]
  rcases z with (⟨y,face⟩ | ⟨q,edge⟩) | ⟨z,copy⟩
  · have hy : y ≠ x := by intro h; subst y; exact hz rfl
    rw [rxLocalDelta1_apply_x]
    have he : (fun edge => e (.inl ⟨y,edge⟩)) = 0 := by
      funext edge
      simp [e,extendXCorrection,hy]
    rw [he,map_zero]
    simp [rxConnectingXQ1,wordLinearMapTranspose_toLin'_apply,rxXQBoundary2Matrix]
  · rw [rxLocalDelta1_apply_q]
    have he : (fun vertex => e (.inr ⟨q,vertex⟩)) = 0 := rfl
    rw [he,map_zero,rxConnectingXQ1_apply_q P A]
    simp only [Pi.zero_apply,zero_add,add_zero]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y = x
    · subst y
      split_ifs with hq
      · simpa only [e,extendXCorrection_at_x,Pi.zero_apply] using
          congrFun (radialGauge_restriction_zero P A S x selected alpha q hq) edge
      · rfl
    · have he : (fun edge => e (.inl ⟨y,edge⟩)) = 0 := by
        funext edge
        simp [e,extendXCorrection,hy]
      simp [he]
  · simp [rxLocalDelta1,rxConnectingXQ1,wordLinearMapTranspose_toLin'_apply,
      rxLocalBoundary2Matrix,rxXQBoundary2Matrix]

/-- The local coboundary is retained exactly on the selected X block. -/
theorem extendXCorrection_delta_at_x (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (e : Word BDL26Field (DoubleCylinderEdge P x S))
    (face : DoubleCylinderFace P x S) :
    wordLinearMapTranspose (rxBoundary2 P S) (extendXCorrection P S x e)
      (.inl (.inl ⟨x,face⟩)) = wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e face := by
  rw [rxDelta1_decomposition]
  change rxLocalDelta1 P S _ _ + rxConnectingXQ1 P S _ _ + rxConnectingQZ1 P S _ _ = _
  rw [rxLocalDelta1_apply_x]
  simp [extendXCorrection_at_x,rxConnectingXQ1,rxConnectingQZ1,
    wordLinearMapTranspose_toLin'_apply,rxXQBoundary2Matrix,rxQZBoundary2Matrix]

/-- Arbitrary-word RZ evaluation, retaining the actual root and owner. -/
theorem rzMap2_apply (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) (z : P.Z)
    (v : ZDoubleCylinderVertex P z S) :
    map2Coord P A S s ⟨z,v⟩ = if v = rzMap1ZRoot P A z S then s z else 0 := by
  classical
  rw [map2Coord,wordPushforward_apply]
  rw [Fintype.sum_eq_single z]
  · simp
  · intro other hne
    have htag : (⟨z,v⟩ : RZZ P S) ≠ ⟨other,rzMap1ZRoot P A other S⟩ := by
      intro h
      exact hne (congrArg (fun t : RZZ P S => t.1) h).symm
    simp [htag]

/-- Concrete state two, above the source decoder's base stopping level. -/
noncomputable def evidenceStateTwo : ConstructionState := rzState scaleFive (rxState scaleFive baseState)

/-- Retaining an old face through both replacements gives a real state-two face. -/
def evidenceStateTwoFace : evidenceStateTwo.presentation.Face :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr ((0 : BaseFace),(0 : Fin 2))), (0 : Fin 2)))

noncomputable def evidenceX : evidenceStateTwo.presentation.X :=
  evidenceStateTwo.presentation.faceX evidenceStateTwoFace

noncomputable def evidenceFace : XStarFace evidenceStateTwo.presentation evidenceX :=
  ⟨evidenceStateTwoFace,by simp [xStarFaceMember,evidenceX]⟩

noncomputable def evidenceAlpha : Neighbor evidenceStateTwo.presentation evidenceX → BDL26Field :=
  fun q => if q = faceNeighbor evidenceStateTwo.presentation evidenceX evidenceFace 0 then 1 else 0

noncomputable def evidenceCorrection : Word BDL26Field (RX1 evidenceStateTwo.presentation scaleFive) :=
  extendXCorrection evidenceStateTwo.presentation scaleFive evidenceX
    (radialGauge evidenceStateTwo.presentation evidenceStateTwo.admissible.toTannerSquareAdmissible
      evidenceX scaleFive 0 evidenceAlpha)

noncomputable def evidenceLowerSyndrome : Word BDL26Field (RX2 evidenceStateTwo.presentation scaleFive) :=
  tannerCoboundary1 (rxReplacementPresentation evidenceStateTwo.presentation scaleFive) evidenceCorrection

noncomputable def evidenceUpperSyndrome : Word BDL26Field
    (RZZ (rxReplacementPresentation evidenceStateTwo.presentation scaleFive) scaleFive) :=
  map2Coord (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
    (rxState scaleFive evidenceStateTwo).admissible scaleFive evidenceLowerSyndrome

/-- The input is a genuine coboundary, not an arbitrary basis cochain. -/
theorem evidenceLowerSyndrome_mem_range :
    evidenceLowerSyndrome ∈ LinearMap.range
      (tannerCoboundary1 (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)) :=
  ⟨evidenceCorrection,rfl⟩

theorem evidenceLowerSyndrome_nonzero : evidenceLowerSyndrome ≠ 0 := by
  let i : Fin scaleFive.half := ⟨0,OddScale.half_pos scaleFive⟩
  let face : DoubleCylinderFace evidenceStateTwo.presentation evidenceX scaleFive :=
    .inl (0,evidenceFace,i,i)
  have hdistinct : faceNeighbor evidenceStateTwo.presentation evidenceX evidenceFace 1 ≠
      faceNeighbor evidenceStateTwo.presentation evidenceX evidenceFace 0 := by
    intro h
    have hc := evidenceStateTwo.presentation.faceQ_injective evidenceStateTwoFace
      (congrArg Subtype.val h)
    exact (by decide : (1 : Fin 2) ≠ 0) hc
  have hv : evidenceLowerSyndrome (.inl (.inl ⟨evidenceX,face⟩)) = 1 := by
    unfold evidenceLowerSyndrome evidenceCorrection
    rw [rxPresentation_coboundary1_eq _ evidenceStateTwo.admissible evidenceStateTwo.regular]
    refine (extendXCorrection_delta_at_x evidenceStateTwo.presentation scaleFive evidenceX
      (radialGauge evidenceStateTwo.presentation evidenceStateTwo.admissible.toTannerSquareAdmissible
        evidenceX scaleFive 0 evidenceAlpha) face).trans ?_
    change wordLinearMapTranspose (doubleCylinderBoundary2 evidenceStateTwo.presentation evidenceX scaleFive)
      (radialGauge evidenceStateTwo.presentation evidenceStateTwo.admissible.toTannerSquareAdmissible
        evidenceX scaleFive 0 evidenceAlpha) (.inl (0,evidenceFace,i,i)) = 1
    rw [radialGauge_layer_coboundary]
    simp [i,evidenceAlpha,hdistinct]
  intro h
  rw [h] at hv
  exact zero_ne_one hv

/-- Every lower nonzero syndrome coordinate has the same genuine local owner. -/
theorem evidenceLowerSyndrome_owner (z : RX2 evidenceStateTwo.presentation scaleFive)
    (hz : evidenceLowerSyndrome z ≠ 0) :
    rxSyndromeOwner evidenceStateTwo.presentation scaleFive z = .x evidenceX := by
  by_contra h
  apply hz
  unfold evidenceLowerSyndrome evidenceCorrection
  rw [rxPresentation_coboundary1_eq _ evidenceStateTwo.admissible evidenceStateTwo.regular]
  exact extendedRadialGauge_supported _ _ _ _ _ _ z h

/-- The next image is a genuine upper coboundary by the proved cochain relation. -/
theorem evidenceUpperSyndrome_mem_range :
    evidenceUpperSyndrome ∈ LinearMap.range
      (rzCoboundary1 (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
        (rxState scaleFive evidenceStateTwo).admissible scaleFive) := by
  refine ⟨map1Coord _ (rxState scaleFive evidenceStateTwo).admissible scaleFive evidenceCorrection,?_⟩
  exact congrArg (fun M => M evidenceCorrection)
    (rzMap_commutes_coboundary1 _ (rxState scaleFive evidenceStateTwo).admissible scaleFive)

theorem evidenceUpperSyndrome_nonzero : evidenceUpperSyndrome ≠ 0 := by
  intro h
  apply evidenceLowerSyndrome_nonzero
  funext z
  have hz := congrFun h ⟨z,rzMap1ZRoot _ (rxState scaleFive evidenceStateTwo).admissible z scaleFive⟩
  have he := rzMap2_apply (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
    (rxState scaleFive evidenceStateTwo).admissible scaleFive evidenceLowerSyndrome z
    (rzMap1ZRoot (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
      (rxState scaleFive evidenceStateTwo).admissible z scaleFive)
  have he' : evidenceLowerSyndrome z = evidenceUpperSyndrome
      ⟨z,rzMap1ZRoot (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
        (rxState scaleFive evidenceStateTwo).admissible z scaleFive⟩ := by
    simpa only [evidenceUpperSyndrome,ite_true] using he.symm
  exact he'.trans hz

/-- All nonzero upper syndrome owners are unparented in the unchanged intrinsic graph. -/
theorem evidenceUpperSyndrome_parent_none
    (target : RZZ (rxReplacementPresentation evidenceStateTwo.presentation scaleFive) scaleFive)
    (h : evidenceUpperSyndrome target ≠ 0) :
    rxParent evidenceStateTwo.presentation scaleFive
      (.z (rzSyndromeOwner (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
        scaleFive target)) = none := by
  rcases target with ⟨z,v⟩
  have hz : evidenceLowerSyndrome z ≠ 0 := by
    intro hz
    apply h
    exact (rzMap2_apply (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
      (rxState scaleFive evidenceStateTwo).admissible scaleFive evidenceLowerSyndrome z v).trans
        (by simp only [hz,ite_self])
  have ho := evidenceLowerSyndrome_owner z hz
  rcases z with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · rfl
  · cases ho
  · cases ho

end QEC.Coding.BDL26OwnerParentObstruction
