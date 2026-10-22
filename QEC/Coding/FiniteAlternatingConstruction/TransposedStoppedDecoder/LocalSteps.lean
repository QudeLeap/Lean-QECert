import QEC.Coding.FiniteAlternatingConstruction.TransposedStoppedDecoder.Coordinates
import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter
import QEC.Coding.FiniteAlternatingConstruction.IndexedDecoder
import QEC.Coding.FourDimensionalToricCode.Decoder.LevelTwoHistory

/-!
# Actual transposed local steps

The bottom presentation is the literal transpose of the original state. The
upper presentation is the literal transpose of its original parity-selected
successor. Only the materialized replacement coordinates are transported;
canonical local choices and the ordered component list are used once.
-/

noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26RXDecoderAdapter
open MultiscaleDecoder Coordinates
open scoped Classical BigOperators

/-- The same original presentation with check roles reversed. -/
def dualPresentation (S : OddScale) (n : Nat) : TannerSquarePresentation :=
  transposePresentation (state S n).presentation

abbrev DualX (S : OddScale) (depth : Nat) (i : LevelIndex depth) := (dualPresentation S i.val).X
abbrev DualQ (S : OddScale) (depth : Nat) (i : LevelIndex depth) := (dualPresentation S i.val).Q
abbrev DualZ (S : OddScale) (depth : Nat) (i : LevelIndex depth) := (dualPresentation S i.val).Z

def dualFamily (S : OddScale) (depth : Nat) :
    BDL26CochainFamily depth (DualX S depth) (DualQ S depth) (DualZ S depth) where
  complex := fun i => BDL26LevelTwoDecoder.presentationComplex (dualPresentation S i.val)

theorem dualFamily_coboundary0 (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    (dualFamily S depth).coboundary0 i = tannerCoboundary0 (dualPresentation S i.val) := by
  apply LinearMap.ext
  intro e
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ e q

theorem dualFamily_coboundary1 (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    (dualFamily S depth).coboundary1 i = tannerCoboundary1 (dualPresentation S i.val) := by
  apply LinearMap.ext
  intro e
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ e z

/-- An elementary coordinate lemma; both incidence maps remain explicit. -/
private theorem conjugate_commutes
    {A B C D E F : Type} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E] [Fintype F]
    (d : Word BDL26Field A →ₗ[BDL26Field] Word BDL26Field B)
    (d' : Word BDL26Field C →ₗ[BDL26Field] Word BDL26Field D)
    (dt : Word BDL26Field E →ₗ[BDL26Field] Word BDL26Field F)
    (e : E ≃ C) (f : F ≃ D)
    (h : ∀ w, d' (wordEquiv e w) = wordEquiv f (dt w))
    (m : Word BDL26Field A →ₗ[BDL26Field] Word BDL26Field C)
    (n : Word BDL26Field B →ₗ[BDL26Field] Word BDL26Field D)
    (hm : d'.comp m = n.comp d) :
    dt.comp ((wordEquiv e).symm.toLinearMap.comp m) =
      ((wordEquiv f).symm.toLinearMap.comp n).comp d := by
  apply LinearMap.ext
  intro w
  apply (wordEquiv f).injective
  change wordEquiv f (dt ((wordEquiv e).symm (m w))) =
    wordEquiv f ((wordEquiv f).symm (n (d w)))
  rw [← h,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun hm w

/-- Original RX step, actual dual RZ map in degree 0. -/
def dualRXMap0 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rxState S C).presentation).X :=
  (wordEquiv (rxDualX C.presentation S)).symm.toLinearMap.comp
    (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).map0

/-- Original RX step, actual dual RZ map in degree 1. -/
def dualRXMap1 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rxState S C).presentation).Q :=
  (wordEquiv (rxDualQ C.presentation S)).symm.toLinearMap.comp
    (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).map1

/-- Original RX step, actual dual RZ map in degree 2. -/
def dualRXMap2 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rxState S C).presentation).Z :=
  (wordEquiv (rxDualZ C.presentation S)).symm.toLinearMap.comp
    (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).map2

theorem dualRXMap_commutes0 (S : OddScale) (C : ConstructionState) :
    (tannerCoboundary0 (transposePresentation (rxState S C).presentation)).comp (dualRXMap0 S C) =
      (dualRXMap1 S C).comp (tannerCoboundary0 (transposePresentation C.presentation)) := by
  have hc := (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).commutes_coboundary0
  rw [BDL26RZDecoderAdapter.presentationFamily_coboundary0,
    BDL26RZDecoderAdapter.presentationFamily_coboundary0] at hc
  exact conjugate_commutes _ _ _ (rxDualX C.presentation S)
    (rxDualQ C.presentation S)
    (rxDual_coboundary0 C.presentation C.admissible C.regular S) _ _ hc

theorem dualRXMap_commutes1 (S : OddScale) (C : ConstructionState) :
    (tannerCoboundary1 (transposePresentation (rxState S C).presentation)).comp (dualRXMap1 S C) =
      (dualRXMap2 S C).comp (tannerCoboundary1 (transposePresentation C.presentation)) := by
  have hc := (BDL26RZDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) S).commutes_coboundary1
  rw [BDL26RZDecoderAdapter.presentationFamily_coboundary1,
    BDL26RZDecoderAdapter.presentationFamily_coboundary1] at hc
  exact conjugate_commutes _ _ _ (rxDualQ C.presentation S)
    (rxDualZ C.presentation S)
    (rxDual_coboundary1 C.presentation C.admissible C.regular S) _ _ hc

/-- Original RZ step, actual dual RX map in degree 0. -/
def dualRZMap0 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rzState S C).presentation).X :=
  (wordEquiv (rzDualX C.presentation S)).symm.toLinearMap.comp
    (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).map0

/-- Original RZ step, actual dual RX map in degree 1. -/
def dualRZMap1 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rzState S C).presentation).Q :=
  (wordEquiv (rzDualQ C.presentation S)).symm.toLinearMap.comp
    (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).map1

/-- Original RZ step, actual dual RX map in degree 2. -/
def dualRZMap2 (S : OddScale) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (rzState S C).presentation).Z :=
  (wordEquiv (rzDualZ C.presentation S)).symm.toLinearMap.comp
    (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).map2

theorem dualRZMap_commutes0 (S : OddScale) (C : ConstructionState) :
    (tannerCoboundary0 (transposePresentation (rzState S C).presentation)).comp (dualRZMap0 S C) =
      (dualRZMap1 S C).comp (tannerCoboundary0 (transposePresentation C.presentation)) := by
  have hc := (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).commutes_coboundary0
  rw [BDL26RXDecoderAdapter.presentationFamily_coboundary0,
    BDL26RXDecoderAdapter.presentationFamily_coboundary0] at hc
  exact conjugate_commutes _ _ _ (rzDualX C.presentation S)
    (rzDualQ C.presentation S)
    (rzDual_coboundary0 C.presentation C.admissible C.regular S) _ _ hc

theorem dualRZMap_commutes1 (S : OddScale) (C : ConstructionState) :
    (tannerCoboundary1 (transposePresentation (rzState S C).presentation)).comp (dualRZMap1 S C) =
      (dualRZMap2 S C).comp (tannerCoboundary1 (transposePresentation C.presentation)) := by
  have hc := (BDL26RXDecoderAdapter.presentationMap (transposePresentation C.presentation)
      (transposeTannerSquareAdmissibleV4 C.presentation C.admissible) (transposeTannerSquareCellularRegular C.presentation C.regular) S).commutes_coboundary1
  rw [BDL26RXDecoderAdapter.presentationFamily_coboundary1,
    BDL26RXDecoderAdapter.presentationFamily_coboundary1] at hc
  exact conjugate_commutes _ _ _ (rzDualQ C.presentation S)
    (rzDualZ C.presentation S)
    (rzDual_coboundary1 C.presentation C.admissible C.regular S) _ _ hc

def dualNextMap0 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (nextState S n C).presentation).X := by
  by_cases h : n % 2 = 0
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).X)
        (show nextState S n C = rxState S C from if_pos h)) (dualRXMap0 S C)
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).X)
        (show nextState S n C = rzState S C from if_neg h)) (dualRZMap0 S C)

def dualNextMap1 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (nextState S n C).presentation).Q := by
  by_cases h : n % 2 = 0
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).Q)
        (show nextState S n C = rxState S C from if_pos h)) (dualRXMap1 S C)
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).Q)
        (show nextState S n C = rzState S C from if_neg h)) (dualRZMap1 S C)

def dualNextMap2 (S : OddScale) (n : Nat) (C : ConstructionState) :
    Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation (nextState S n C).presentation).Z := by
  by_cases h : n % 2 = 0
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).Z)
        (show nextState S n C = rxState S C from if_pos h)) (dualRXMap2 S C)
  · exact Eq.mpr (congrArg (fun D : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation D.presentation).Z)
        (show nextState S n C = rzState S C from if_neg h)) (dualRZMap2 S C)

private theorem transport_commutes0 (C D E : ConstructionState) (h : D = E)
    (m : Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).X)
    (n : Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).Q)
    (hc : (tannerCoboundary0 (transposePresentation E.presentation)).comp m =
      n.comp (tannerCoboundary0 (transposePresentation C.presentation))) :
    (tannerCoboundary0 (transposePresentation D.presentation)).comp
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word BDL26Field (transposePresentation C.presentation).X →ₗ[BDL26Field]
          Word BDL26Field (transposePresentation B.presentation).X) h) m) =
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
          Word BDL26Field (transposePresentation B.presentation).Q) h) n).comp
        (tannerCoboundary0 (transposePresentation C.presentation)) := by
  cases h
  exact hc

theorem dualNextMap_commutes0 (S : OddScale) (n : Nat) (C : ConstructionState) :
    (tannerCoboundary0 (transposePresentation (nextState S n C).presentation)).comp
      (dualNextMap0 S n C) =
    (dualNextMap1 S n C).comp (tannerCoboundary0 (transposePresentation C.presentation)) := by
  by_cases h : n % 2 = 0
  · have ht := transport_commutes0 C (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h) _ _ (dualRXMap_commutes0 S C)
    simpa only [dualNextMap0,dualNextMap1,dif_pos h] using ht
  · have ht := transport_commutes0 C (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h) _ _ (dualRZMap_commutes0 S C)
    simpa only [dualNextMap0,dualNextMap1,dif_neg h] using ht

private theorem transport_commutes1 (C D E : ConstructionState) (h : D = E)
    (m : Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).Q)
    (n : Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).Z)
    (hc : (tannerCoboundary1 (transposePresentation E.presentation)).comp m =
      n.comp (tannerCoboundary1 (transposePresentation C.presentation))) :
    (tannerCoboundary1 (transposePresentation D.presentation)).comp
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word BDL26Field (transposePresentation C.presentation).Q →ₗ[BDL26Field]
          Word BDL26Field (transposePresentation B.presentation).Q) h) m) =
      (Eq.mpr (congrArg (fun B : ConstructionState =>
        Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
          Word BDL26Field (transposePresentation B.presentation).Z) h) n).comp
        (tannerCoboundary1 (transposePresentation C.presentation)) := by
  cases h
  exact hc

theorem dualNextMap_commutes1 (S : OddScale) (n : Nat) (C : ConstructionState) :
    (tannerCoboundary1 (transposePresentation (nextState S n C).presentation)).comp
      (dualNextMap1 S n C) =
    (dualNextMap2 S n C).comp (tannerCoboundary1 (transposePresentation C.presentation)) := by
  by_cases h : n % 2 = 0
  · have ht := transport_commutes1 C (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h) _ _ (dualRXMap_commutes1 S C)
    simpa only [dualNextMap1,dualNextMap2,dif_pos h] using ht
  · have ht := transport_commutes1 C (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h) _ _ (dualRZMap_commutes1 S C)
    simpa only [dualNextMap1,dualNextMap2,dif_neg h] using ht

/-- Both storage slots retain the single actual dual adjacent map. -/
def dualEdgeMap (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    BDL26CochainMap (dualFamily S depth) i where
  map0 := dualNextMap0 S i.val (state S i.val)
  map1 := dualNextMap1 S i.val (state S i.val)
  map2 := dualNextMap2 S i.val (state S i.val)
  commutes_coboundary0 := by
    rw [dualFamily_coboundary0,dualFamily_coboundary0]
    exact dualNextMap_commutes0 S i.val (state S i.val)
  commutes_coboundary1 := by
    rw [dualFamily_coboundary1,dualFamily_coboundary1]
    exact dualNextMap_commutes1 S i.val (state S i.val)

def dualDecoderData (S : OddScale) (depth : Nat) :
    BDL26DecoderData depth (DualX S depth) (DualQ S depth) (DualZ S depth) where
  family := dualFamily S depth
  rxMap := dualEdgeMap S depth
  rzMap := dualEdgeMap S depth

@[simp] theorem dualDecoderData_selectedMap (S : OddScale) (depth : Nat)
    (i : StepIndex depth) :
    (dualDecoderData S depth).selectedMap i = dualEdgeMap S depth i := by
  unfold BDL26DecoderData.selectedMap
  split <;> rfl

/-- Inverting a concrete coordinate intertwining equation. -/
private theorem inverse_intertwines {A B C D : Type}
    (e : A ≃ B) (f : C ≃ D)
    (d : Word BDL26Field A →ₗ[BDL26Field] Word BDL26Field C)
    (d' : Word BDL26Field B →ₗ[BDL26Field] Word BDL26Field D)
    (h : ∀ w, d' (wordEquiv e w) = wordEquiv f (d w))
    (w : Word BDL26Field B) :
    d ((wordEquiv e).symm w) = (wordEquiv f).symm (d' w) := by
  apply (wordEquiv f).injective
  rw [← h,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

section CoordinateOutput
variable {d e : Nat}
variable {A0 A1 A2 : LevelIndex d → Type} {B0 B1 B2 : LevelIndex e → Type}
variable [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
variable [∀ i, Fintype (B0 i)] [∀ i, Fintype (B1 i)] [∀ i, Fintype (B2 i)]

/-- Transport a computed output once. This private constructor transports the
original ordered list; its support and coboundary snapshots are recomputed
from that very list by the existing AssemblyStepOutput constructor. -/
private def coordinateOutput
    (D : BDL26DecoderData d A0 A1 A2) (E : BDL26DecoderData e B0 B1 B2)
    (i : StepIndex d) (j : StepIndex e)
    (q : A1 i.succ ≃ B1 j.succ) (z : A2 i.succ ≃ B2 j.succ)
    (bq : A1 i.castSucc ≃ B1 j.castSucc) (bz : A2 i.castSucc ≃ B2 j.castSucc)
    (ht : ∀ w, E.family.coboundary1 j.succ (wordEquiv q w) =
      wordEquiv z (D.family.coboundary1 i.succ w))
    (hb : ∀ w, E.family.coboundary1 j.castSucc (wordEquiv bq w) =
      wordEquiv bz (D.family.coboundary1 i.castSucc w))
    (hm : ∀ w, (E.selectedMap j).map2 (wordEquiv bz w) =
      wordEquiv z ((D.selectedMap i).map2 w))
    (O : AssemblyStepOutput D i) : AssemblyStepOutput E j := by
  let input : E.family.Syndrome j.succ := ⟨wordEquiv z O.input.val,by
    obtain ⟨w,hw⟩ := O.input.property
    exact ⟨wordEquiv q w,by rw [ht,hw]⟩⟩
  let coarse : E.family.Syndrome j.castSucc := ⟨wordEquiv bz O.coarse.val,by
    obtain ⟨w,hw⟩ := O.coarse.property
    exact ⟨wordEquiv bq w,by rw [hb,hw]⟩⟩
  apply AssemblyStepOutput.ofComponents input coarse (wordEquiv q O.correction)
    (O.localComponents.map (wordEquiv q))
  · change wordEquiv z O.input.val = _
    rw [ht,hm,← map_add,O.relation]
  · rw [O.correction_decomposition]
    have hsum (l : List (D.family.Correction i.succ)) :
        wordEquiv q l.sum = (l.map (wordEquiv q)).sum := by
      induction l with
      | nil => simp
      | cons a l ih => simp only [List.sum_cons,List.map_cons,map_add,ih]
    exact hsum _

end CoordinateOutput

/-- Dependent carrier transport is proved by equality elimination; no
presentation or choice-data invariance is assumed. -/
private theorem cast_tanner_coboundary1 (P R : TannerSquarePresentation) (h : P = R)
    (w : Word BDL26Field R.Q) :
    tannerCoboundary1 P (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Q h).symm) w) =
      wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z h).symm)
        (tannerCoboundary1 R w) := by
  cases h
  rfl

private theorem transport_map_apply (C D E : ConstructionState) (h : D = E)
    (m : Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
      Word BDL26Field (transposePresentation E.presentation).Z)
    (w : Word BDL26Field (transposePresentation C.presentation).Z) :
    (Eq.mpr (congrArg (fun B : ConstructionState =>
      Word BDL26Field (transposePresentation C.presentation).Z →ₗ[BDL26Field]
        Word BDL26Field (transposePresentation B.presentation).Z) h) m) w =
      wordEquiv (Equiv.cast (congrArg (fun B : ConstructionState =>
        (transposePresentation B.presentation).Z) h).symm) (m w) := by
  cases h
  rfl

/-- Transport the literal next-state branch before specializing any recursive
state. Equality elimination in transport_map_apply keeps the map/function cast
and the coordinate cast over the very same ConstructionState equality. -/
private theorem dualNextMap2_rx_apply (S : OddScale) (n : Nat)
    (C : ConstructionState) (h : n % 2 = 0)
    (w : Word BDL26Field (transposePresentation C.presentation).Z) :
    dualNextMap2 S n C w =
      wordEquiv (Equiv.cast (congrArg (fun D : ConstructionState =>
        (transposePresentation D.presentation).Z)
        (show nextState S n C = rxState S C from if_pos h)).symm) (dualRXMap2 S C w) := by
  unfold dualNextMap2
  split
  · exact transport_map_apply C (nextState S n C) (rxState S C)
      (show nextState S n C = rxState S C from if_pos h) (dualRXMap2 S C) w
  · contradiction

/-- Transport the literal next-state branch before specializing any recursive
state. Equality elimination in transport_map_apply keeps the map/function cast
and the coordinate cast over the very same ConstructionState equality. -/
private theorem dualNextMap2_rz_apply (S : OddScale) (n : Nat)
    (C : ConstructionState) (h : ¬n % 2 = 0)
    (w : Word BDL26Field (transposePresentation C.presentation).Z) :
    dualNextMap2 S n C w =
      wordEquiv (Equiv.cast (congrArg (fun D : ConstructionState =>
        (transposePresentation D.presentation).Z)
        (show nextState S n C = rzState S C from if_neg h)).symm) (dualRZMap2 S C w) := by
  unfold dualNextMap2
  split
  · contradiction
  · exact transport_map_apply C (nextState S n C) (rzState S C)
      (show nextState S n C = rzState S C from if_neg h) (dualRZMap2 S C) w

private theorem dualStateSuccRX (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) : state S (i.val + 1) = rxState S (state S i.val) := by
  change nextState S i.val (state S i.val) = _
  exact if_pos h

/-- Materialized dual RZ coordinates to the actual original successor transpose. -/
def dualRXTopQ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) :
    (BDL26RZDecoderAdapter.presentationAt (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S (1 : LevelIndex 1)).Q ≃
      (dualPresentation S i.succ.val).Q :=
  (rxDualQ (state S i.val).presentation S).symm.trans
    (Equiv.cast (congrArg (fun C : ConstructionState =>
      (transposePresentation C.presentation).Q) (dualStateSuccRX S depth i h)).symm)

/-- Materialized dual RZ coordinates to the actual original successor transpose. -/
def dualRXTopZ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) :
    (BDL26RZDecoderAdapter.presentationAt (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S (1 : LevelIndex 1)).Z ≃
      (dualPresentation S i.succ.val).Z :=
  (rxDualZ (state S i.val).presentation S).symm.trans
    (Equiv.cast (congrArg (fun C : ConstructionState =>
      (transposePresentation C.presentation).Z) (dualStateSuccRX S depth i h)).symm)

private theorem dualRXTop_coboundary1 (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0)
    (w : (BDL26RZDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).Correction (1 : LevelIndex 1)) :
    (dualFamily S depth).coboundary1 i.succ (wordEquiv (dualRXTopQ S depth i h) w) =
      wordEquiv (dualRXTopZ S depth i h)
        ((BDL26RZDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).coboundary1 (1 : LevelIndex 1) w) := by
  have hleft := LinearMap.congr_fun (dualFamily_coboundary1 S depth i.succ)
    (wordEquiv (dualRXTopQ S depth i h) w)
  have hright := congrArg (wordEquiv (dualRXTopZ S depth i h))
    (LinearMap.congr_fun (BDL26RZDecoderAdapter.presentationFamily_coboundary1 (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S
      (1 : LevelIndex 1)) w)
  refine hleft.trans ?_
  refine Eq.trans ?_ hright.symm
  have hc := inverse_intertwines (rxDualQ (state S i.val).presentation S)
    (rxDualZ (state S i.val).presentation S) _ _
    (rxDual_coboundary1 (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) w
  let ht := congrArg (fun C : ConstructionState => transposePresentation C.presentation)
    (dualStateSuccRX S depth i h)
  change tannerCoboundary1 (dualPresentation S i.succ.val)
      (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Q ht).symm)
        ((wordEquiv (rxDualQ (state S i.val).presentation S)).symm w)) =
    wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z ht).symm)
      ((wordEquiv (rxDualZ (state S i.val).presentation S)).symm
        (tannerCoboundary1 _ w))
  exact (cast_tanner_coboundary1 _ _ ht
    ((wordEquiv (rxDualQ (state S i.val).presentation S)).symm w)).trans
      (congrArg (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z ht).symm)) hc)

private theorem dualRXTop_map2 (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0)
    (w : Word BDL26Field (dualPresentation S i.val).Z) :
    ((dualDecoderData S depth).selectedMap i).map2 w =
      wordEquiv (dualRXTopZ S depth i h)
        (((BDL26RZDecoderAdapter.presentationDecoderData (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).selectedMap (0 : StepIndex 1)).map2 w) := by
  have hselected := congrArg
    (fun M : BDL26CochainMap (dualFamily S depth) i => M.map2 w)
    (dualDecoderData_selectedMap S depth i)
  refine hselected.trans ?_
  change dualNextMap2 S i.val (state S i.val) w =
    wordEquiv (dualRXTopZ S depth i h)
      ((BDL26RZDecoderAdapter.presentationMap (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).map2 w)
  exact (dualNextMap2_rx_apply S i.val (state S i.val) h w).trans (by rfl)

/-- The actual canonical dual RZ output, transported once to the original tower. -/
def dualRXMaterializedInput (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (BDL26RZDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).Syndrome (1 : LevelIndex 1) := by
  exact ⟨(wordEquiv (dualRXTopZ S depth i h)).symm sigma.val,by
      obtain ⟨w,hw⟩ := sigma.property
      refine ⟨(wordEquiv (dualRXTopQ S depth i h)).symm w,?_⟩
      apply (wordEquiv (dualRXTopZ S depth i h)).injective
      rw [← dualRXTop_coboundary1,LinearEquiv.apply_symm_apply,hw,
        LinearEquiv.apply_symm_apply]⟩

def dualRXStepOutput (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    AssemblyStepOutput (dualDecoderData S depth) i := by
  let localInput := dualRXMaterializedInput S depth i h sigma
  let O := BDL26RZDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S localInput
  exact coordinateOutput (BDL26RZDecoderAdapter.presentationDecoderData (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S)
    (dualDecoderData S depth) (0 : StepIndex 1) i
    (dualRXTopQ S depth i h) (dualRXTopZ S depth i h) (Equiv.refl _) (Equiv.refl _)
    (dualRXTop_coboundary1 S depth i h)
    (by
      intro w
      change (dualFamily S depth).coboundary1 i.castSucc w =
        (BDL26RZDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S).coboundary1
          (0 : LevelIndex 1) w
      exact (LinearMap.congr_fun (dualFamily_coboundary1 S depth i.castSucc) w).trans
        (LinearMap.congr_fun (BDL26RZDecoderAdapter.presentationFamily_coboundary1 (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S
          (0 : LevelIndex 1)) w).symm)
    (by intro w; exact dualRXTop_map2 S depth i h w) O

/-- Exact original component order, including duplicate or zero entries. -/
theorem dualRXStepOutput_components (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRXStepOutput S depth i h sigma).localComponents =
      (BDL26RZDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S (dualRXMaterializedInput S depth i h sigma)).localComponents.map
        (wordEquiv (dualRXTopQ S depth i h)) := rfl

@[simp] theorem dualRXStepOutput_input (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRXStepOutput S depth i h sigma).input = sigma := by
  apply Subtype.ext
  change wordEquiv (dualRXTopZ S depth i h)
    ((wordEquiv (dualRXTopZ S depth i h)).symm sigma.val) = sigma.val
  exact LinearEquiv.apply_symm_apply _ _

private theorem dualStateSuccRZ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) : state S (i.val + 1) = rzState S (state S i.val) := by
  change nextState S i.val (state S i.val) = _
  exact if_neg h

/-- Materialized dual RX coordinates to the actual original successor transpose. -/
def dualRZTopQ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) :
    (BDL26RXDecoderAdapter.presentationAt (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S (1 : LevelIndex 1)).Q ≃
      (dualPresentation S i.succ.val).Q :=
  (rzDualQ (state S i.val).presentation S).symm.trans
    (Equiv.cast (congrArg (fun C : ConstructionState =>
      (transposePresentation C.presentation).Q) (dualStateSuccRZ S depth i h)).symm)

/-- Materialized dual RX coordinates to the actual original successor transpose. -/
def dualRZTopZ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) :
    (BDL26RXDecoderAdapter.presentationAt (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S (1 : LevelIndex 1)).Z ≃
      (dualPresentation S i.succ.val).Z :=
  (rzDualZ (state S i.val).presentation S).symm.trans
    (Equiv.cast (congrArg (fun C : ConstructionState =>
      (transposePresentation C.presentation).Z) (dualStateSuccRZ S depth i h)).symm)

private theorem dualRZTop_coboundary1 (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0)
    (w : (BDL26RXDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).Correction (1 : LevelIndex 1)) :
    (dualFamily S depth).coboundary1 i.succ (wordEquiv (dualRZTopQ S depth i h) w) =
      wordEquiv (dualRZTopZ S depth i h)
        ((BDL26RXDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).coboundary1 (1 : LevelIndex 1) w) := by
  have hleft := LinearMap.congr_fun (dualFamily_coboundary1 S depth i.succ)
    (wordEquiv (dualRZTopQ S depth i h) w)
  have hright := congrArg (wordEquiv (dualRZTopZ S depth i h))
    (LinearMap.congr_fun (BDL26RXDecoderAdapter.presentationFamily_coboundary1 (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S
      (1 : LevelIndex 1)) w)
  refine hleft.trans ?_
  refine Eq.trans ?_ hright.symm
  have hc := inverse_intertwines (rzDualQ (state S i.val).presentation S)
    (rzDualZ (state S i.val).presentation S) _ _
    (rzDual_coboundary1 (state S i.val).presentation (state S i.val).admissible
      (state S i.val).regular S) w
  let ht := congrArg (fun C : ConstructionState => transposePresentation C.presentation)
    (dualStateSuccRZ S depth i h)
  change tannerCoboundary1 (dualPresentation S i.succ.val)
      (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Q ht).symm)
        ((wordEquiv (rzDualQ (state S i.val).presentation S)).symm w)) =
    wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z ht).symm)
      ((wordEquiv (rzDualZ (state S i.val).presentation S)).symm
        (tannerCoboundary1 _ w))
  exact (cast_tanner_coboundary1 _ _ ht
    ((wordEquiv (rzDualQ (state S i.val).presentation S)).symm w)).trans
      (congrArg (wordEquiv (Equiv.cast (congrArg TannerSquarePresentation.Z ht).symm)) hc)

private theorem dualRZTop_map2 (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0)
    (w : Word BDL26Field (dualPresentation S i.val).Z) :
    ((dualDecoderData S depth).selectedMap i).map2 w =
      wordEquiv (dualRZTopZ S depth i h)
        (((BDL26RXDecoderAdapter.presentationDecoderData (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).selectedMap (0 : StepIndex 1)).map2 w) := by
  have hselected := congrArg
    (fun M : BDL26CochainMap (dualFamily S depth) i => M.map2 w)
    (dualDecoderData_selectedMap S depth i)
  refine hselected.trans ?_
  change dualNextMap2 S i.val (state S i.val) w =
    wordEquiv (dualRZTopZ S depth i h)
      ((BDL26RXDecoderAdapter.presentationMap (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).map2 w)
  exact (dualNextMap2_rz_apply S i.val (state S i.val) h w).trans (by rfl)

/-- The actual canonical dual RX output, transported once to the original tower. -/
def dualRZMaterializedInput (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (BDL26RXDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).Syndrome (1 : LevelIndex 1) := by
  exact ⟨(wordEquiv (dualRZTopZ S depth i h)).symm sigma.val,by
      obtain ⟨w,hw⟩ := sigma.property
      refine ⟨(wordEquiv (dualRZTopQ S depth i h)).symm w,?_⟩
      apply (wordEquiv (dualRZTopZ S depth i h)).injective
      rw [← dualRZTop_coboundary1,LinearEquiv.apply_symm_apply,hw,
        LinearEquiv.apply_symm_apply]⟩

def dualRZStepOutput (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    AssemblyStepOutput (dualDecoderData S depth) i := by
  let localInput := dualRZMaterializedInput S depth i h sigma
  let O := BDL26RXDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S localInput
  exact coordinateOutput (BDL26RXDecoderAdapter.presentationDecoderData (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S)
    (dualDecoderData S depth) (0 : StepIndex 1) i
    (dualRZTopQ S depth i h) (dualRZTopZ S depth i h) (Equiv.refl _) (Equiv.refl _)
    (dualRZTop_coboundary1 S depth i h)
    (by
      intro w
      change (dualFamily S depth).coboundary1 i.castSucc w =
        (BDL26RXDecoderAdapter.presentationFamily (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S).coboundary1
          (0 : LevelIndex 1) w
      exact (LinearMap.congr_fun (dualFamily_coboundary1 S depth i.castSucc) w).trans
        (LinearMap.congr_fun (BDL26RXDecoderAdapter.presentationFamily_coboundary1 (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S
          (0 : LevelIndex 1)) w).symm)
    (by intro w; exact dualRZTop_map2 S depth i h w) O

/-- Exact original component order, including duplicate or zero entries. -/
theorem dualRZStepOutput_components (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRZStepOutput S depth i h sigma).localComponents =
      (BDL26RXDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S (dualRZMaterializedInput S depth i h sigma)).localComponents.map
        (wordEquiv (dualRZTopQ S depth i h)) := rfl

@[simp] theorem dualRZStepOutput_input (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRZStepOutput S depth i h sigma).input = sigma := by
  apply Subtype.ext
  change wordEquiv (dualRZTopZ S depth i h)
    ((wordEquiv (dualRZTopZ S depth i h)).symm sigma.val) = sigma.val
  exact LinearEquiv.apply_symm_apply _ _

/-- The original forward parity is used once to choose the opposite dual reduction. -/
def dualStepOutput (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    AssemblyStep (dualDecoderData S depth) i := fun sigma =>
  if h : i.val % 2 = 0 then dualRXStepOutput S depth i h sigma
  else dualRZStepOutput S depth i h sigma

theorem dualStepOutput_relation (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    AssemblyStepRelation (dualDecoderData S depth) i (dualStepOutput S depth i) where
  input_eq := by
    intro sigma
    change (dualStepOutput S depth i sigma).input = sigma
    unfold dualStepOutput
    split
    · exact dualRXStepOutput_input S depth i _ sigma
    · exact dualRZStepOutput_input S depth i _ sigma
  relation := fun sigma => (dualStepOutput S depth i sigma).relation

/-- All actual local reductions above physical C2; no history is supplied. -/
def dualAboveTwoSteps (S : OddScale) (n : Nat) :
    LevelTwoHistory.AboveTwoSteps (dualDecoderData S (n + 2)) where
  step := fun i _ => dualStepOutput S (n + 2) i
  relation := fun i _ => dualStepOutput_relation S (n + 2) i

theorem dualRXStepOutput_zero_coarse (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ)
    (hs : sigma.val = 0) : (dualRXStepOutput S depth i h sigma).coarse.val = 0 := by
  have hz : (dualRXMaterializedInput S depth i h sigma).val = 0 := by
    change (wordEquiv (dualRXTopZ S depth i h)).symm sigma.val = 0
    exact (congrArg (fun w => (wordEquiv (dualRXTopZ S depth i h)).symm w) hs).trans
      (map_zero _)
  change (BDL26RZDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S
    (dualRXMaterializedInput S depth i h sigma)).coarse.val = 0
  exact BDL26RZDecoderAdapter.presentationOutput_zero_coarse (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S
    (dualRXMaterializedInput S depth i h sigma) hz

theorem dualRZStepOutput_zero_coarse (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ)
    (hs : sigma.val = 0) : (dualRZStepOutput S depth i h sigma).coarse.val = 0 := by
  have hz : (dualRZMaterializedInput S depth i h sigma).val = 0 := by
    change (wordEquiv (dualRZTopZ S depth i h)).symm sigma.val = 0
    exact (congrArg (fun w => (wordEquiv (dualRZTopZ S depth i h)).symm w) hs).trans
      (map_zero _)
  change (BDL26RXDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S
    (dualRZMaterializedInput S depth i h sigma)).coarse.val = 0
  exact BDL26RXDecoderAdapter.presentationOutput_zero_coarse (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S
    (dualRZMaterializedInput S depth i h sigma) hz

theorem dualStepOutput_zero_coarse (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (dualFamily S depth).Syndrome i.succ) (hs : sigma.val = 0) :
    (dualStepOutput S depth i sigma).coarse.val = 0 := by
  unfold dualStepOutput
  split
  · exact dualRXStepOutput_zero_coarse S depth i _ sigma hs
  · exact dualRZStepOutput_zero_coarse S depth i _ sigma hs

end QEC.Coding.BDL26TransposedStoppedDecoder
end
