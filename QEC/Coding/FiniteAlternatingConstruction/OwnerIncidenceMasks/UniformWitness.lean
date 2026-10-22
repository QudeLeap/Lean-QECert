import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.HistoryWitness
import QEC.Coding.FiniteAlternatingConstruction.BoundedValenceSuccessors

/-! # Actual retained faces at every physical depth

Every face used here is built from the seed by the concrete retained-face
summand, rather than supplied as a nonemptiness certificate.
-/
namespace QEC.Coding.BDL26UniformHistoryObstruction

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical

noncomputable def retainedFace (S : OddScale) : (n : Nat) → (state S n).presentation.Face
  | 0 => (0 : BaseFace)
  | n + 1 => by
      change (nextState S n (state S n)).presentation.Face
      unfold nextState
      split
      · exact Sum.inr (Sum.inr (retainedFace S n, (0 : Fin 2)))
      · exact Sum.inr (Sum.inr (retainedFace S n, (0 : Fin 2)))

noncomputable def retainedX (S : OddScale) (n : Nat) : (state S n).presentation.X :=
  (state S n).presentation.faceX (retainedFace S n)

noncomputable def retainedStarFace (S : OddScale) (n : Nat) :
    XStarFace (state S n).presentation (retainedX S n) :=
  ⟨retainedFace S n, by simp [xStarFaceMember, retainedX]⟩

noncomputable def retainedAlpha (S : OddScale) (n : Nat) :
    Neighbor (state S n).presentation (retainedX S n) → BDL26Field :=
  fun q => if q = faceNeighbor (state S n).presentation (retainedX S n)
    (retainedStarFace S n) 0 then 1 else 0

noncomputable def lowerErrorRaw (S : OddScale) (n : Nat) :
    Word BDL26Field (RX1 (state S n).presentation S) :=
  extendXCorrection (state S n).presentation S (retainedX S n)
    (radialGauge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
      (retainedX S n) S 0 (retainedAlpha S n))

noncomputable def lowerSyndromeRaw (S : OddScale) (n : Nat) : Word BDL26Field (RX2 (state S n).presentation S) :=
  tannerCoboundary1 (rxReplacementPresentation (state S n).presentation S) (lowerErrorRaw S n)

noncomputable def upperSyndromeRaw (S : OddScale) (n : Nat) : Word BDL26Field
    (RZZ (rxReplacementPresentation (state S n).presentation S) S) :=
  map2Coord (rxReplacementPresentation (state S n).presentation S)
    (rxState S (state S n)).admissible S (lowerSyndromeRaw S n)

/-- The input is a genuine coboundary, not an arbitrary basis cochain. -/
theorem lowerSyndromeRaw_mem_range (S : OddScale) (n : Nat) :
    (lowerSyndromeRaw S n) ∈ LinearMap.range
      (tannerCoboundary1 (rxReplacementPresentation (state S n).presentation S)) :=
  ⟨(lowerErrorRaw S n),rfl⟩

theorem lowerSyndromeRaw_nonzero (S : OddScale) (n : Nat) : (lowerSyndromeRaw S n) ≠ 0 := by
  let i : Fin S.half := ⟨0,OddScale.half_pos S⟩
  let face : DoubleCylinderFace (state S n).presentation (retainedX S n) S :=
    .inl (0,(retainedStarFace S n),i,i)
  have hdistinct : faceNeighbor (state S n).presentation (retainedX S n) (retainedStarFace S n) 1 ≠
      faceNeighbor (state S n).presentation (retainedX S n) (retainedStarFace S n) 0 := by
    intro h
    have hc := (state S n).presentation.faceQ_injective (retainedFace S n)
      (congrArg Subtype.val h)
    exact (by decide : (1 : Fin 2) ≠ 0) hc
  have hv : (lowerSyndromeRaw S n) (.inl (.inl ⟨(retainedX S n),face⟩)) = 1 := by
    unfold lowerSyndromeRaw lowerErrorRaw
    rw [rxPresentation_coboundary1_eq _ (state S n).admissible (state S n).regular]
    refine (extendXCorrection_delta_at_x (state S n).presentation S (retainedX S n)
      (radialGauge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
        (retainedX S n) S 0 (retainedAlpha S n)) face).trans ?_
    change wordLinearMapTranspose (doubleCylinderBoundary2 (state S n).presentation (retainedX S n) S)
      (radialGauge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
        (retainedX S n) S 0 (retainedAlpha S n)) (.inl (0,(retainedStarFace S n),i,i)) = 1
    rw [radialGauge_layer_coboundary]
    simp [i,retainedAlpha,hdistinct]
  intro h
  rw [h] at hv
  exact zero_ne_one hv

/-- Every lower nonzero syndrome coordinate has the same genuine local owner. -/
theorem lowerSyndromeRaw_owner (S : OddScale) (n : Nat) (z : RX2 (state S n).presentation S)
    (hz : (lowerSyndromeRaw S n) z ≠ 0) :
    rxSyndromeOwner (state S n).presentation S z = .x (retainedX S n) := by
  by_contra h
  apply hz
  unfold lowerSyndromeRaw lowerErrorRaw
  rw [rxPresentation_coboundary1_eq _ (state S n).admissible (state S n).regular]
  exact extendedRadialGauge_supported _ _ _ _ _ _ z h

/-- The next image is a genuine upper coboundary by the proved cochain relation. -/
theorem upperSyndromeRaw_mem_range (S : OddScale) (n : Nat) :
    (upperSyndromeRaw S n) ∈ LinearMap.range
      (rzCoboundary1 (rxReplacementPresentation (state S n).presentation S)
        (rxState S (state S n)).admissible S) := by
  refine ⟨map1Coord _ (rxState S (state S n)).admissible S (lowerErrorRaw S n),?_⟩
  exact congrArg (fun M => M (lowerErrorRaw S n))
    (rzMap_commutes_coboundary1 _ (rxState S (state S n)).admissible S)

theorem upperSyndromeRaw_nonzero (S : OddScale) (n : Nat) : (upperSyndromeRaw S n) ≠ 0 := by
  intro h
  apply (lowerSyndromeRaw_nonzero S n)
  funext z
  have hz := congrFun h ⟨z,rzMap1ZRoot _ (rxState S (state S n)).admissible z S⟩
  have he := rzMap2_apply (rxReplacementPresentation (state S n).presentation S)
    (rxState S (state S n)).admissible S (lowerSyndromeRaw S n) z
    (rzMap1ZRoot (rxReplacementPresentation (state S n).presentation S)
      (rxState S (state S n)).admissible z S)
  have he' : (lowerSyndromeRaw S n) z = (upperSyndromeRaw S n)
      ⟨z,rzMap1ZRoot (rxReplacementPresentation (state S n).presentation S)
        (rxState S (state S n)).admissible z S⟩ := by
    simpa only [upperSyndromeRaw,ite_true] using he.symm
  exact he'.trans hz

/-- All nonzero upper syndrome owners are unparented in the unchanged intrinsic graph. -/
theorem upperSyndromeRaw_parent_none (S : OddScale) (n : Nat)
    (target : RZZ (rxReplacementPresentation (state S n).presentation S) S)
    (h : (upperSyndromeRaw S n) target ≠ 0) :
    rxParent (state S n).presentation S
      (.z (rzSyndromeOwner (rxReplacementPresentation (state S n).presentation S)
        S target)) = none := by
  rcases target with ⟨z,v⟩
  have hz : (lowerSyndromeRaw S n) z ≠ 0 := by
    intro hz
    apply h
    exact (rzMap2_apply (rxReplacementPresentation (state S n).presentation S)
      (rxState S (state S n)).admissible S (lowerSyndromeRaw S n) z v).trans
        (by simp only [hz,ite_self])
  have ho := (lowerSyndromeRaw_owner S n) z hz
  rcases z with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · rfl
  · cases ho
  · cases ho

/-- Only the defining parity branch is used to identify the actual successor. -/
theorem state_rx (S : OddScale) (n : Nat) (h : n % 2 = 0) :
    state S (n + 1) = rxState S (state S n) := by
  change nextState S n (state S n) = _
  exact if_pos h

noncomputable def lowerError (S : OddScale) (j : Nat) :
    Word BDL26Field (state S ((2 * j + 2) + 1)).presentation.Q :=
  Eq.mpr (congrArg (fun C : ConstructionState => Word BDL26Field C.presentation.Q)
    (state_rx S (2 * j + 2) (by omega))) (lowerErrorRaw S (2 * j + 2))

private theorem transported_syndrome_nonzero
    (P U : TannerSquarePresentation) (h : P = U)
    (e : Word BDL26Field U.Q) (he : tannerCoboundary1 U e ≠ 0) :
    tannerCoboundary1 P
      (Eq.mpr (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h) e) ≠ 0 := by
  cases h
  exact he

noncomputable def lowerSyndrome (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).Syndrome ⟨2 * j + 3, by omega⟩ :=
  ⟨(indexedFamily S (2 * j + 4)).coboundary1 ⟨2 * j + 3, by omega⟩
    (lowerError S j), ⟨lowerError S j, rfl⟩⟩

theorem lowerSyndrome_nonzero (S : OddScale) (j : Nat) :
    (lowerSyndrome S j).val ≠ 0 := by
  change (indexedFamily S (2 * j + 4)).coboundary1
    ⟨2 * j + 3, by omega⟩ (lowerError S j) ≠ 0
  rw [indexedFamily_coboundary1]
  exact transported_syndrome_nonzero _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega)))
    (lowerErrorRaw S (2 * j + 2)) (lowerSyndromeRaw_nonzero S (2 * j + 2))

noncomputable def upperSyndrome (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).Syndrome (TopIndex (2 * j + 4)) :=
  BDL26RZDecoderAdapter.embeddedSyndrome S (2 * j + 4)
    ⟨2 * j + 3, by omega⟩ (lowerSyndrome S j)

noncomputable def topOutput (S : OddScale) (j : Nat) :
    AssemblyStepOutput (indexedDecoderData S (2 * j + 4)) ⟨2 * j + 3, by omega⟩ :=
  actualStep S (2 * j + 4) ⟨2 * j + 3, by omega⟩ (upperSyndrome S j)

theorem topOutput_coarse (S : OddScale) (j : Nat) :
    (topOutput S j).coarse = lowerSyndrome S j := by
  unfold topOutput
  rw [actualStep_rz S (2 * j + 4) ⟨2 * j + 3, by omega⟩ (by simp)]
  exact BDL26RZDecoderAdapter.rzStepOutput_map2_coarse S (2 * j + 4)
    ⟨2 * j + 3, by omega⟩ (by simp) (lowerSyndrome S j)

noncomputable def upperError (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).Correction (TopIndex (2 * j + 4)) :=
  ((indexedDecoderData S (2 * j + 4)).selectedMap ⟨2 * j + 3, by omega⟩).map1
    (lowerError S j)

theorem upperError_syndrome (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).coboundary1 (TopIndex (2 * j + 4))
      (upperError S j) = (upperSyndrome S j).val :=
  LinearMap.congr_fun
    (((indexedDecoderData S (2 * j + 4)).selectedMap
      ⟨2 * j + 3, by omega⟩).commutes_coboundary1) (lowerError S j)

theorem upperSyndrome_nonzero (S : OddScale) (j : Nat) :
    (upperSyndrome S j).val ≠ 0 := by
  intro hz
  have hw := BDL26RZDecoderAdapter.rzStepOutput_weight S (2 * j + 4)
    ⟨2 * j + 3, by omega⟩ (by simp) (upperSyndrome S j)
  have hc := BDL26RZDecoderAdapter.rzStepOutput_map2_coarse S (2 * j + 4)
    ⟨2 * j + 3, by omega⟩ (by simp) (lowerSyndrome S j)
  change (BDL26RZDecoderAdapter.rzStepOutput S (2 * j + 4)
    ⟨2 * j + 3, by omega⟩ (by simp) (upperSyndrome S j)).coarse =
      lowerSyndrome S j at hc
  rw [hc, hz, HammingWeight_zero] at hw
  exact lowerSyndrome_nonzero S j
    ((HammingWeight_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hw))

/-- The canonical tested output is literally the head of the actual C2-stopped
history, for every scale and even physical depth at least four. -/
theorem actualHistory_head (S : OddScale) (j : Nat) :
    ∃ tail, actualHistory S (2 * j + 2) (upperSyndrome S j) =
      CorrectionHistoryEntry.step (Fin.last (2 * j + 1))
        (LevelTwoHistory.suffixOutput (indexedDecoderData S (2 * j + 4))
          (Fin.last (2 * j + 1)) (topOutput S j)) :: tail :=
  LevelTwoHistory.stoppedHistory_head (2 * j + 1) (indexedDecoderData S (2 * j + 4))
    (actualAboveTwoSteps S (2 * j + 2)) (actualBase S (2 * j + 2)) (upperSyndrome S j)

private theorem transported_parent_none
    (P : TannerSquarePresentation) (U V : ConstructionState) (h : U = V)
    (e : Word BDL26Field V.presentation.Q)
    (par : Vertex V.presentation → Option (Vertex P))
    (hp : ∀ z, tannerCoboundary1 V.presentation e z ≠ 0 → par (.z z) = none) :
    ∀ z : U.presentation.Z, tannerCoboundary1 U.presentation
      (Eq.mpr (congrArg (fun T : ConstructionState => Word BDL26Field T.presentation.Q) h) e) z ≠ 0 →
      par (cast (congrArg (fun T : ConstructionState => Vertex T.presentation) h) (.z z)) = none := by
  cases h
  exact hp

theorem lowerSyndrome_parent_none (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 3)).presentation.Z)
    (hz : (lowerSyndrome S j).val z ≠ 0) :
    parent S (2 * j + 3) (.z z) = none := by
  have hn : tannerCoboundary1 (state S (2 * j + 3)).presentation
      (lowerError S j) z ≠ 0 := by
    change (indexedFamily S (2 * j + 4)).coboundary1
      ⟨2 * j + 3, by omega⟩ (lowerError S j) z ≠ 0 at hz
    simpa only [indexedFamily_coboundary1] using hz
  have hp := transported_parent_none (state S (2 * j + 2)).presentation _ _
    (state_rx S (2 * j + 2) (by omega))
    (lowerErrorRaw S (2 * j + 2)) (rxParent (state S (2 * j + 2)).presentation S)
    (by
      intro q hq
      have ho := lowerSyndromeRaw_owner S (2 * j + 2) q hq
      rcases q with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
      · rfl
      · cases ho
      · cases ho)
    z hn
  change nextParent S (2 * j + 2) (state S (2 * j + 2)) (.z z) = none
  simp only [nextParent, dif_pos (show (2 * j + 2) % 2 = 0 by omega), nextRXVertex]
  convert hp using 1
  all_goals rfl

noncomputable def topOwner (S : OddScale) (j : Nat)
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4))) :
    Vertex (state S (2 * j + 3)).presentation :=
  (BDL26RZDecoderAdapter.rzData S (2 * j + 4) ⟨2 * j + 3, by omega⟩ (by simp)).topCenter p

theorem topOwner_parent_none (S : OddScale) (j : Nat)
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    parent S (2 * j + 3) (topOwner S j p) = none := by
  obtain ⟨z,hz,hs⟩ := BDL26RZDecoderAdapter.rzData_map2_active_owner S (2 * j + 4)
    ⟨2 * j + 3, by omega⟩ (by simp) (lowerSyndrome S j).val p hp
  change parent S (2 * j + 3)
    ((BDL26RZDecoderAdapter.rzData S (2 * j + 4) ⟨2 * j + 3, by omega⟩ (by simp)).topCenter p) = none
  rw [hz]
  exact lowerSyndrome_parent_none S j z hs

noncomputable def topComponentOwner (S : OddScale) (j : Nat)
    (a : Fin (topOutput S j).localComponents.length) :
    Vertex (state S (2 * j + 3)).presentation :=
  Vertex.z (BDL26RZDecoderAdapter.componentOwner S (2 * j + 4)
    ⟨2 * j + 3, by omega⟩ (by simp) (upperSyndrome S j)
    ⟨a.val, by simpa only [topOutput, (actualStep_rz S (2 * j + 4)
      ⟨2 * j + 3, by omega⟩ (by simp))] using a.isLt⟩)

noncomputable def topMarks (S : OddScale) (j : Nat) :=
  outputMarks (topOutput S j) (topOwner S j) (topComponentOwner S j)

theorem topMarks_only_z (S : OddScale) (j : Nat)
    (v : Vertex (state S (2 * j + 3)).presentation) (hv : v ∈ topMarks S j) :
    ∃ z, v = Vertex.z z := by
  have hm := (Finset.mem_filter.mp hv).2
  rcases hm with ⟨p,rfl,_⟩ | ⟨a,rfl,_⟩ | ⟨a,p,rfl,_⟩
  · exact BDL26RZDecoderAdapter.rzData_topCenter_is_z S (2 * j + 4)
      ⟨2 * j + 3, by omega⟩ (by simp) p
  · exact ⟨_,rfl⟩
  · exact BDL26RZDecoderAdapter.rzData_topCenter_is_z S (2 * j + 4)
      ⟨2 * j + 3, by omega⟩ (by simp) p

theorem topMarks_active (S : OddScale) (j : Nat)
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : topOwner S j p ∈ topMarks S j := by
  apply outputMarks_contains_syndrome
  have hi := (actualStep_relation S (2 * j + 4) ⟨2 * j + 3, by omega⟩).input_eq
    (upperSyndrome S j)
  change (topOutput S j).input = upperSyndrome S j at hi
  rw [hi]
  exact hp

end QEC.Coding.BDL26UniformHistoryObstruction
