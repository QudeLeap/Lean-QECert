import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformWeight

/-! # The actual radial input to the next RX step

The error has one coordinate. Its syndrome counts incident star faces;
these are different weight statements.
-/
namespace QEC.Coding.BDL26UniformRXTail

open BDL26DecodingGraph BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26IndexedDecoder
open BDL26UniformHistoryObstruction BDL26OwnerParentObstruction
open BDL26RXLocalReplacement BDL26XLocalRadialParity
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

noncomputable def selectedNeighbor (S : OddScale) (n : Nat) :=
  faceNeighbor (state S n).presentation (retainedX S n) (retainedStarFace S n) 0

def incidentStarFace (S : OddScale) (n : Nat)
    (face : XStarFace (state S n).presentation (retainedX S n)) : Prop :=
  faceNeighbor (state S n).presentation (retainedX S n) face 0 = selectedNeighbor S n ∨
  faceNeighbor (state S n).presentation (retainedX S n) face 1 = selectedNeighbor S n

theorem lower_input_other_owner (S : OddScale) (n : Nat)
    (z : RX2 (state S n).presentation S)
    (hz : rxSyndromeOwner (state S n).presentation S z ≠ .x (retainedX S n)) :
    lowerSyndromeRaw S n z = 0 := by
  by_contra h
  exact hz (lowerSyndromeRaw_owner S n z h)

/-- Raw zero-Z boundary is established before indexed successor transport. -/
theorem lower_input_raw_z_zero (S : OddScale) (n : Nat)
    (z : (state S n).presentation.Z) (b : Fin 2) :
    rxCoboundary1 (state S n).presentation S (lowerErrorRaw S n) (Sum.inr (z,b)) = 0 :=
  extendedRadialGauge_supported (state S n).presentation
    (state S n).admissible.toTannerSquareAdmissible S (retainedX S n) 0 (retainedAlpha S n)
    (Sum.inr (z,b)) (by intro h; cases h)

/-- Exact selected-copy and origin-cell formula, before counting support. -/
theorem lower_input_layer (S : OddScale) (n : Nat)
    (face : XStarFace (state S n).presentation (retainedX S n))
    (copy : Fin 2) (i j : Fin S.half) :
    lowerSyndromeRaw S n (.inl (.inl ⟨retainedX S n, .inl (copy, face, i, j)⟩)) =
      if copy = 0 ∧ i.val = 0 ∧ j.val = 0 ∧ incidentStarFace S n face then 1 else 0 := by
  unfold lowerSyndromeRaw lowerErrorRaw
  rw [rxPresentation_coboundary1_eq _ (state S n).admissible (state S n).regular]
  refine (extendXCorrection_delta_at_x (state S n).presentation S (retainedX S n)
    (radialGauge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
      (retainedX S n) S 0 (retainedAlpha S n)) (.inl (copy,face,i,j))).trans ?_
  change wordLinearMapTranspose (doubleCylinderBoundary2 (state S n).presentation (retainedX S n) S)
    (radialGauge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
      (retainedX S n) S 0 (retainedAlpha S n)) (.inl (copy,face,i,j)) = _
  rw [radialGauge_layer_coboundary]
  have hd : faceNeighbor (state S n).presentation (retainedX S n) face 0 ≠
      faceNeighbor (state S n).presentation (retainedX S n) face 1 := by
    intro h
    have hh := (state S n).presentation.faceQ_injective face.1 (congrArg Subtype.val h)
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  by_cases h0 : faceNeighbor (state S n).presentation (retainedX S n) face 0 = selectedNeighbor S n
  · have h1 : faceNeighbor (state S n).presentation (retainedX S n) face 1 ≠ selectedNeighbor S n :=
      fun h => hd (h0.trans h.symm)
    simp only [selectedNeighbor] at h0 h1
    simp [retainedAlpha, selectedNeighbor, incidentStarFace, h0, h1]
  · by_cases h1 : faceNeighbor (state S n).presentation (retainedX S n) face 1 = selectedNeighbor S n
    · simp only [selectedNeighbor] at h0 h1
      simp [retainedAlpha, selectedNeighbor, incidentStarFace, h0, h1]
    · simp only [selectedNeighbor] at h0 h1
      simp [retainedAlpha, selectedNeighbor, incidentStarFace, h0, h1]

/-- Boundary strips contribute no syndrome coordinate. -/
theorem lower_input_strip (S : OddScale) (n : Nat)
    (face : XStarFace (state S n).presentation (retainedX S n))
    (side : Fin 2) (i : Fin S.half) :
    lowerSyndromeRaw S n (.inl (.inl ⟨retainedX S n,
      .inr (subdivisionOriginalBoundaryEdge (state S n).presentation (retainedX S n) S
        (xStarFaceBoundaryEdge (state S n).presentation (retainedX S n) face side) i)⟩)) = 0 := by
  unfold lowerSyndromeRaw lowerErrorRaw
  rw [rxPresentation_coboundary1_eq _ (state S n).admissible (state S n).regular]
  refine (extendXCorrection_delta_at_x (state S n).presentation S (retainedX S n)
    (radialGauge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
      (retainedX S n) S 0 (retainedAlpha S n))
      (.inr (subdivisionOriginalBoundaryEdge (state S n).presentation (retainedX S n) S
        (xStarFaceBoundaryEdge (state S n).presentation (retainedX S n) face side) i))).trans ?_
  exact radialGauge_strip_coboundary _ _ _ _ _ _ _ _ _


noncomputable def incidentStarFaces (S : OddScale) (n : Nat) :
    Finset (XStarFace (state S n).presentation (retainedX S n)) :=
  Finset.univ.filter (incidentStarFace S n)

noncomputable def inputSpot (S : OddScale) (n : Nat)
    (f : XStarFace (state S n).presentation (retainedX S n)) :
    RX2 (state S n).presentation S :=
  .inl (.inl ⟨retainedX S n, .inl (0, f, ⟨0,S.half_pos⟩, ⟨0,S.half_pos⟩)⟩)

theorem lower_input_support (S : OddScale) (n : Nat) :
    hammingSupport (lowerSyndromeRaw S n) =
      (incidentStarFaces S n).image (inputSpot S n) := by
  ext p
  constructor
  · intro hp
    have hn : lowerSyndromeRaw S n p ≠ 0 := by simpa [hammingSupport] using hp
    have ho := lowerSyndromeRaw_owner S n p hn
    rcases p with (⟨x,cell⟩ | qe) | ze
    · have hx : x = retainedX S n := Vertex.x.inj ho
      subst x
      obtain ⟨⟨f, piece⟩, he⟩ := xLocalPieceCellMap_surjective
        (state S n).presentation (state S n).admissible (retainedX S n) S cell
      subst cell
      rcases piece with ⟨copy,i,j⟩ | ⟨side,i⟩
      · change lowerSyndromeRaw S n (.inl (.inl ⟨retainedX S n,.inl (copy,f,i,j)⟩)) ≠ 0 at hn
        rw [lower_input_layer] at hn
        have hc : copy = 0 ∧ i.val = 0 ∧ j.val = 0 ∧ incidentStarFace S n f := by
          by_contra h
          simp [h] at hn
        rcases hc with ⟨rfl,hi,hj,hf⟩
        have hi' : i = ⟨0,S.half_pos⟩ := Fin.ext hi
        have hj' : j = ⟨0,S.half_pos⟩ := Fin.ext hj
        subst i
        subst j
        exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,rfl⟩
      · exact (hn (lower_input_strip S n f side i)).elim
    · cases ho
    · cases ho
  · intro hp
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hp
    have hi := (Finset.mem_filter.mp hf).2
    simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    change lowerSyndromeRaw S n (.inl (.inl ⟨retainedX S n,
      .inl (0,f,⟨0,S.half_pos⟩,⟨0,S.half_pos⟩)⟩)) ≠ 0
    rw [lower_input_layer]
    simp [hi]

theorem inputSpot_injective (S : OddScale) (n : Nat) : Function.Injective (inputSpot S n) := by
  intro f g h
  simpa [inputSpot, Sigma.mk.inj_iff] using h

/-- Exact syndrome weight is a face count, separately from error weight one. -/
theorem lower_input_weight_exact (S : OddScale) (n : Nat) :
    HammingWeight (lowerSyndromeRaw S n) = (incidentStarFaces S n).card := by
  rw [HammingWeight, lower_input_support,
    Finset.card_image_of_injective _ (inputSpot_injective S n)]

open BDL26BoundedValence

noncomputable def incidentFaceEquiv (S : OddScale) (n : Nat) :
    {f : XStarFace (state S n).presentation (retainedX S n) // incidentStarFace S n f} ≃
      XQIncidentFace (state S n).presentation
        ⟨(retainedX S n,(selectedNeighbor S n).val),(selectedNeighbor S n).property⟩ where
  toFun f := ⟨f.1.1, by simpa [xStarFaceMember] using f.1.2, by
    rcases f.2 with h | h
    · exact ⟨0,congrArg Subtype.val h⟩
    · exact ⟨1,congrArg Subtype.val h⟩⟩
  invFun f := ⟨⟨f.1,by simpa [xStarFaceMember] using f.2.1⟩,by
    obtain ⟨i,hi⟩ := f.2.2
    fin_cases i
    · exact Or.inl (Subtype.ext hi)
    · exact Or.inr (Subtype.ext hi)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lower_input_weight_valence (S : OddScale) (n : Nat) :
    HammingWeight (lowerSyndromeRaw S n) =
      qZDegree (state S n).presentation (selectedNeighbor S n).val := by
  rw [lower_input_weight_exact]
  have hc := Fintype.card_congr (incidentFaceEquiv S n)
  rw [xqIncidentFace_card] at hc
  simpa [incidentStarFaces, Fintype.card_subtype] using hc

theorem lower_input_weight_le_four (S : OddScale) (n : Nat) :
    HammingWeight (lowerSyndromeRaw S n) ≤ 4 := by
  rw [lower_input_weight_valence]
  exact ((state_boundedValence S n).2.2 (selectedNeighbor S n).val).2.1


private theorem syndrome_weight_transport (P U : TannerSquarePresentation) (h : P = U)
    (e : Word BDL26Field U.Q) :
    HammingWeight (tannerCoboundary1 P (Eq.mpr
      (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h) e)) =
      HammingWeight (tannerCoboundary1 U e) := by
  cases h
  rfl

theorem lower_syndrome_weight_exact (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val = (incidentStarFaces S (2 * j + 2)).card := by
  change HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
    ⟨2 * j + 3, by omega⟩ (lowerError S j)) = (incidentStarFaces S (2 * j + 2)).card
  rw [indexedFamily_coboundary1]
  have h := syndrome_weight_transport _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega)))
    (lowerErrorRaw S (2 * j + 2))
  exact h.trans (lower_input_weight_exact S (2 * j + 2))

theorem lower_syndrome_weight_le_four (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val ≤ 4 := by
  change HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
    ⟨2 * j + 3, by omega⟩ (lowerError S j)) ≤ 4
  rw [indexedFamily_coboundary1]
  have h := syndrome_weight_transport _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega)))
    (lowerErrorRaw S (2 * j + 2))
  exact h.trans_le (lower_input_weight_le_four S (2 * j + 2))

end QEC.Coding.BDL26UniformRXTail
