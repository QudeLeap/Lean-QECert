import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Flow

/-! # Actual RX local and outgoing coboundary decomposition -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

noncomputable def xSyndromeExtend (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word BDL26Field (DoubleCylinderFace P x S) →ₗ[BDL26Field] Word BDL26Field (RX2 P S) :=
  (extendWordLinear ((localX P S).syndromeRegion x)).comp
    (wordEquiv (xSyndromeEquiv P S x)).toLinearMap

noncomputable def qSyndromeExtend (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word BDL26Field (QDoubleCylinderEdge P q S) →ₗ[BDL26Field] Word BDL26Field (RX2 P S) :=
  (extendWordLinear ((localQ P S).syndromeRegion q)).comp
    (wordEquiv (qSyndromeEquiv P S q)).toLinearMap

theorem xSyndromeExtend_same (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderFace P x S)) (f : DoubleCylinderFace P x S) :
    xSyndromeExtend P S x w (Sum.inl (Sum.inl ⟨x,f⟩)) = w f :=
  extend_reindex_at _ (xSyndromeEquiv P S x) w f

theorem qSyndromeExtend_same (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderEdge P q S)) (e : QDoubleCylinderEdge P q S) :
    qSyndromeExtend P S q w (Sum.inl (Sum.inr ⟨q,e⟩)) = w e :=
  extend_reindex_at _ (qSyndromeEquiv P S q) w e

theorem xSyndromeExtend_outside (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderFace P x S)) (p : RX2 P S)
    (hp : rxSyndromeOwner P S p ≠ Vertex.x x) : xSyndromeExtend P S x w p = 0 := by
  change extendLocalSignal ((localX P S).syndromeRegion x) _ p = 0
  rw [extendLocalSignal, dif_neg]
  intro hm
  exact hp (Finset.mem_filter.mp hm).2

theorem qSyndromeExtend_outside (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderEdge P q S)) (p : RX2 P S)
    (hp : rxSyndromeOwner P S p ≠ Vertex.q q) : qSyndromeExtend P S q w p = 0 := by
  change extendLocalSignal ((localQ P S).syndromeRegion q) _ p = 0
  rw [extendLocalSignal, dif_neg]
  intro hm
  exact hp (Finset.mem_filter.mp hm).2

theorem localDelta1_at_z (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S)) (z : P.Z) (c : Fin 2) :
    rxLocalDelta1 P S w (Sum.inr (z,c)) = 0 := by
  rw [rxLocalDelta1, wordLinearMapTranspose_toLin'_apply]
  apply Finset.sum_eq_zero
  intro source _
  rcases source with xe | qv <;> simp [rxLocalBoundary2Matrix]

theorem xLocalDelta1_extension (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) :
    rxLocalDelta1 P S (xExtend P S x w) =
      xSyndromeExtend P S x (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) w) := by
  funext p
  rcases p with (⟨y,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · rw [rxLocalDelta1_apply_x]
    by_cases h : y = x
    · subst y
      have hw : (fun e => xExtend P S x w (Sum.inl ⟨x,e⟩)) = w := by
        funext e; exact xExtend_at_x P S x w e
      rw [hw, xSyndromeExtend_same]
    · have hw : (fun e => xExtend P S x w (Sum.inl ⟨y,e⟩)) = 0 := by
        funext e; exact xExtend_other P S x y h w e
      rw [hw, map_zero]
      exact (xSyndromeExtend_outside P S x _ (Sum.inl (Sum.inl ⟨y,f⟩)) (fun hh => h (Vertex.x.inj hh))).symm
  · rw [rxLocalDelta1_apply_q]
    have hw : (fun v => xExtend P S x w (Sum.inr ⟨q,v⟩)) = 0 := by
      funext v; exact xExtend_at_q P S x w q v
    rw [hw, map_zero]
    exact (xSyndromeExtend_outside P S x _ _ (by intro hh; cases hh)).symm
  · rw [localDelta1_at_z]
    exact (xSyndromeExtend_outside P S x _ _ (by intro hh; cases hh)).symm

theorem qLocalDelta1_extension (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    rxLocalDelta1 P S (qExtend P S q w) =
      qSyndromeExtend P S q (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) := by
  funext p
  rcases p with (⟨x,f⟩ | ⟨r,e⟩) | ⟨z,c⟩
  · rw [rxLocalDelta1_apply_x]
    have hw : (fun e => qExtend P S q w (Sum.inl ⟨x,e⟩)) = 0 := by
      funext e; exact qExtend_at_x P S q w x e
    rw [hw, map_zero]
    exact (qSyndromeExtend_outside P S q _ _ (by intro hh; cases hh)).symm
  · rw [rxLocalDelta1_apply_q]
    by_cases h : r = q
    · subst r
      have hw : (fun v => qExtend P S q w (Sum.inr ⟨q,v⟩)) = w := by
        funext v; exact qExtend_at_q P S q w v
      rw [hw, qSyndromeExtend_same]
    · have hw : (fun v => qExtend P S q w (Sum.inr ⟨r,v⟩)) = 0 := by
        funext v; exact qExtend_other P S q r h w v
      rw [hw, map_zero]
      exact (qSyndromeExtend_outside P S q _ (Sum.inl (Sum.inr ⟨r,e⟩)) (fun hh => h (Vertex.q.inj hh))).symm
  · rw [localDelta1_at_z]
    exact (qSyndromeExtend_outside P S q _ _ (by intro hh; cases hh)).symm

theorem xDelta1_decomposition (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) :
    rxCoboundary1 P S (xExtend P S x w) =
      xSyndromeExtend P S x (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) w) +
        xFlow P S x w := by
  rw [rxCoboundary1, rxDelta1_decomposition]
  simp only [LinearMap.add_apply, xLocalDelta1_extension]
  rw [rxConnectingQZ1_zero_on_x P S _ (fun qv => xExtend_at_q P S x w qv.1 qv.2), add_zero]
  rfl

theorem qDelta1_decomposition (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    rxCoboundary1 P S (qExtend P S q w) =
      qSyndromeExtend P S q (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) +
        qFlow P S q w := by
  rw [rxCoboundary1, rxDelta1_decomposition]
  simp only [LinearMap.add_apply, qLocalDelta1_extension]
  rw [rxConnectingXQ1_zero_on_q P S _ (fun xe => qExtend_at_x P S q w xe.1 xe.2), add_zero]
  rfl

theorem region_restrict_extend {A : Type} [Fintype A] [DecidableEq A]
    (Y : Finset A) (f : Word BDL26Field (LocalRegionIndex Y)) :
    restrictWordLinear Y (extendWordLinear Y f) = f := by
  funext p
  change extendLocalSignal Y f p.1 = f p
  simp only [extendLocalSignal, dif_pos p.2]

theorem region_restrict_extend_disjoint {A : Type} [Fintype A] [DecidableEq A]
    (Y Z : Finset A) (h : Disjoint Y Z) (f : Word BDL26Field (LocalRegionIndex Y)) :
    restrictWordLinear Z (extendWordLinear Y f) = 0 := by
  funext p
  change extendLocalSignal Y f p.1 = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  exact Finset.disjoint_left.mp h hp p.2

theorem localCx_decomposition (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (f : Word BDL26Field (LocalRegionIndex ((localX P S).correctionRegion x))) :
    rxCoboundary1 P S (extendWordLinear ((localX P S).correctionRegion x) f) =
      extendWordLinear ((localX P S).syndromeRegion x)
        (wordLinearMapTranspose (localCx P S x).boundary2 f) +
          xFlow P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f) := by
  let rawF := (wordEquiv (xCorrectionEquiv P S x)).symm f
  have he : xExtend P S x rawF = extendWordLinear ((localX P S).correctionRegion x) f := by
    change extendWordLinear _ (wordEquiv _ ((wordEquiv _).symm f)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hd : wordLinearMapTranspose (localCx P S x).boundary2 f =
      wordEquiv (xSyndromeEquiv P S x)
        (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) rawF) := by
    rw [localCx, reindex_delta1]
    rfl
  rw [← he, xDelta1_decomposition, hd]
  rfl

theorem localCq_decomposition (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (f : Word BDL26Field (LocalRegionIndex ((localQ P S).correctionRegion q))) :
    rxCoboundary1 P S (extendWordLinear ((localQ P S).correctionRegion q) f) =
      extendWordLinear ((localQ P S).syndromeRegion q)
        (wordLinearMapTranspose (localCq P S q).boundary2 f) +
          qFlow P S q ((wordEquiv (qCorrectionEquiv P S q)).symm f) := by
  let rawF := (wordEquiv (qCorrectionEquiv P S q)).symm f
  have he : qExtend P S q rawF = extendWordLinear ((localQ P S).correctionRegion q) f := by
    change extendWordLinear _ (wordEquiv _ ((wordEquiv _).symm f)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hd : wordLinearMapTranspose (localCq P S q).boundary2 f =
      wordEquiv (qSyndromeEquiv P S q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) rawF) := by
    rw [localCq, reindex_delta1]
    rfl
  rw [← he, qDelta1_decomposition, hd]
  rfl

end QEC.Coding.BDL26RXDecoderAdapter
