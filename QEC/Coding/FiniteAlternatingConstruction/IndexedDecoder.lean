import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDecoder

/-!
# The actual indexed alternating decoder family

Every carrier is an actual recursive Tanner presentation. The edge maps below
are the concrete replacement maps, transported only along the defining parity
branch. This family does not prescribe a history or a stopping level.
-/

namespace QEC.Coding.BDL26IndexedDecoder

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26ReplacementCochainMaps BDL26RZLocalReplacement BDL26RXLocalReplacement
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder BDL26AlternatingCochain
open scoped Classical

universe u


private theorem transported_heq {α β : Sort u} (h : α = β) (v : β) :
    HEq (Eq.mpr h v) v := by
  cases h
  rfl

abbrev FamilyX (S : OddScale) (depth : Nat) (i : LevelIndex depth) :=
  (state S i.val).presentation.X
abbrev FamilyQ (S : OddScale) (depth : Nat) (i : LevelIndex depth) :=
  (state S i.val).presentation.Q
abbrev FamilyZ (S : OddScale) (depth : Nat) (i : LevelIndex depth) :=
  (state S i.val).presentation.Z

noncomputable def indexedFamily (S : OddScale) (depth : Nat) :
    BDL26CochainFamily depth (FamilyX S depth) (FamilyQ S depth) (FamilyZ S depth) where
  complex := fun i => BDL26LevelTwoDecoder.presentationComplex (state S i.val).presentation

theorem indexedFamily_coboundary0 (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    (indexedFamily S depth).coboundary0 i =
      tannerCoboundary0 (state S i.val).presentation := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q

theorem indexedFamily_coboundary1 (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    (indexedFamily S depth).coboundary1 i =
      tannerCoboundary1 (state S i.val).presentation := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z

noncomputable def indexedEdgeMap (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    BDL26CochainMap (indexedFamily S depth) i where
  map0 := stepMap0 S i.val
  map1 := stepMap1 S i.val
  map2 := stepMap2 S i.val
  commutes_coboundary0 := by
    rw [indexedFamily_coboundary0, indexedFamily_coboundary0]
    exact nextMap_commutes0 S i.val (state S i.val)
  commutes_coboundary1 := by
    rw [indexedFamily_coboundary1, indexedFamily_coboundary1]
    exact nextMap_commutes1 S i.val (state S i.val)

/-- Both storage slots hold the same genuine adjacent map. -/
noncomputable def indexedDecoderData (S : OddScale) (depth : Nat) :
    BDL26DecoderData depth (FamilyX S depth) (FamilyQ S depth) (FamilyZ S depth) where
  family := indexedFamily S depth
  rxMap := indexedEdgeMap S depth
  rzMap := indexedEdgeMap S depth

theorem selectedMap_eq (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    (indexedDecoderData S depth).selectedMap i = indexedEdgeMap S depth i := by
  unfold BDL26DecoderData.selectedMap
  split <;> rfl

/-- The two-level specialization uses identical carriers and differentials. -/
theorem indexedFamily_levelTwo (S : OddScale) :
    indexedFamily S 2 = BDL26LevelTwoDecoder.decoderFamily S := rfl

/-- All three first-edge maps are the concrete RX maps, not zero fillers. -/
theorem indexedDecoderData_levelTwo_zero (S : OddScale) :
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map0 =
      (rxMap baseTannerSquarePresentation S).map0 ∧
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map1 =
      (rxMap baseTannerSquarePresentation S).map1 ∧
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map2 =
      (rxMap baseTannerSquarePresentation S).map2 := by
  rw [selectedMap_eq]
  exact ⟨rfl, rfl, rfl⟩

/-- All three second-edge maps agree with the physical-C₂ adapter. -/
theorem indexedDecoderData_levelTwo_one (S : OddScale) :
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map0 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map0 ∧
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map1 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map1 ∧
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map2 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map2 := by
  rw [selectedMap_eq]
  exact ⟨rfl, rfl, rfl⟩

/-- All degrees of the selected even-lower-index map are the actual RX maps.
Heterogeneous equality records only the defining successor-carrier transport. -/
theorem indexedDecoderData_selected_rx (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) :
    HEq ((indexedDecoderData S depth).selectedMap i).map0
      (rxMap (state S i.val).presentation S).map0 ∧
    HEq ((indexedDecoderData S depth).selectedMap i).map1
      (rxMap (state S i.val).presentation S).map1 ∧
    HEq ((indexedDecoderData S depth).selectedMap i).map2
      (rxMap (state S i.val).presentation S).map2 := by
  rw [selectedMap_eq]
  simp only [indexedEdgeMap, stepMap0, stepMap1, stepMap2, nextMap0,
    nextMap1, nextMap2, dif_pos h, rxMap]
  exact ⟨transported_heq _ _, transported_heq _ _, transported_heq _ _⟩


/-- All degrees of the selected odd-lower-index map are the actual RZ maps. -/
theorem indexedDecoderData_selected_rz (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) :
    HEq ((indexedDecoderData S depth).selectedMap i).map0
      (rzCochainMap (state S i.val).presentation (state S i.val).admissible S).map0 ∧
    HEq ((indexedDecoderData S depth).selectedMap i).map1
      (rzCochainMap (state S i.val).presentation (state S i.val).admissible S).map1 ∧
    HEq ((indexedDecoderData S depth).selectedMap i).map2
      (rzCochainMap (state S i.val).presentation (state S i.val).admissible S).map2 := by
  rw [selectedMap_eq]
  simp only [indexedEdgeMap, stepMap0, stepMap1, stepMap2, nextMap0,
    nextMap1, nextMap2, dif_neg h, rzCochainMap]
  exact ⟨transported_heq _ _, transported_heq _ _, transported_heq _ _⟩


/-- Every selected degree map agrees with the accepted depth-two decoder.
This compares the mathematical maps rather than opaque proof-bearing records. -/
theorem indexedDecoderData_levelTwo (S : OddScale) (i : StepIndex 2) :
    ((indexedDecoderData S 2).selectedMap i).map0 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map0 ∧
    ((indexedDecoderData S 2).selectedMap i).map1 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map1 ∧
    ((indexedDecoderData S 2).selectedMap i).map2 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map2 := by
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

end QEC.Coding.BDL26IndexedDecoder
