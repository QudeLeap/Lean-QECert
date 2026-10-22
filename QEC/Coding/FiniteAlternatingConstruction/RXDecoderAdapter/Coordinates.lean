import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.LocalComplexes

/-! # Actual RX differential restrictions in owner-fibre coordinates -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

-- The subtype restriction is exactly raw cylinder reindexing.
theorem x_restrict_correction (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (RX1 P S)) :
    (wordEquiv (xCorrectionEquiv P S x)).symm
      (restrictWordLinear ((localX P S).correctionRegion x) w) =
        fun e => w (Sum.inl ⟨x,e⟩) := by
  funext e
  rfl

theorem q_restrict_correction (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (RX1 P S)) :
    (wordEquiv (qCorrectionEquiv P S q)).symm
      (restrictWordLinear ((localQ P S).correctionRegion q) w) =
        fun v => w (Sum.inr ⟨q,v⟩) := by
  funext v
  rfl

-- Matrix zeroes give unconditional X restriction. Q uses the already repaired staged law.
theorem raw_x_restriction (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S)) (x : P.X) (f : DoubleCylinderFace P x S) :
    rxCoboundary1 P S w (Sum.inl (Sum.inl ⟨x,f⟩)) =
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (fun e => w (Sum.inl ⟨x,e⟩)) f := by
  have hxq : rxConnectingXQ1 P S w (Sum.inl (Sum.inl ⟨x,f⟩)) = 0 := by
    rw [rxConnectingXQ1, wordLinearMapTranspose_toLin'_apply]
    apply Finset.sum_eq_zero
    intro source _
    rcases source with xEdge | qVertex <;> simp [rxXQBoundary2Matrix]
  have hqz : rxConnectingQZ1 P S w (Sum.inl (Sum.inl ⟨x,f⟩)) = 0 := by
    rw [rxConnectingQZ1, wordLinearMapTranspose_toLin'_apply]
    apply Finset.sum_eq_zero
    intro source _
    rcases source with xEdge | qVertex <;> simp [rxQZBoundary2Matrix]
  rw [rxCoboundary1, rxDelta1_decomposition]
  simp only [LinearMap.add_apply, Pi.add_apply, hxq, hqz, add_zero]
  exact rxLocalDelta1_apply_x P S w x f

theorem localCx_delta1_apply (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (LocalRegionIndex ((localX P S).correctionRegion x)))
    (f : DoubleCylinderFace P x S) :
    wordLinearMapTranspose (localCx P S x).boundary2 w (xSyndromeEquiv P S x f) =
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        ((wordEquiv (xCorrectionEquiv P S x)).symm w) f := by
  simp only [localCx, reindex_delta1, LinearMap.comp_apply, LinearEquiv.coe_coe,
    wordEquiv_apply, Equiv.symm_apply_apply]
  rfl

theorem localCq_delta1_apply (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (LocalRegionIndex ((localQ P S).correctionRegion q)))
    (e : QDoubleCylinderEdge P q S) :
    wordLinearMapTranspose (localCq P S q).boundary2 w (qSyndromeEquiv P S q e) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        ((wordEquiv (qCorrectionEquiv P S q)).symm w) e := by
  simp only [localCq, reindex_delta1, LinearMap.comp_apply, LinearEquiv.coe_coe,
    wordEquiv_apply, Equiv.symm_apply_apply]
  rfl

theorem localCx_global_restriction (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S)) (x : P.X) :
    restrictWordLinear ((localX P S).syndromeRegion x) (rxCoboundary1 P S w) =
      wordLinearMapTranspose (localCx P S x).boundary2
        (restrictWordLinear ((localX P S).correctionRegion x) w) := by
  funext p
  obtain ⟨f,rfl⟩ := (xSyndromeEquiv P S x).surjective p
  rw [localCx_delta1_apply, x_restrict_correction]
  exact raw_x_restriction P S w x f

/-- This premise is zero actual X error, as required by the connecting block. -/
theorem localCq_global_restriction (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S))
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w = 0) (q : P.Q) :
    restrictWordLinear ((localQ P S).syndromeRegion q) (rxCoboundary1 P S w) =
      wordLinearMapTranspose (localCq P S q).boundary2
        (restrictWordLinear ((localQ P S).correctionRegion q) w) := by
  funext p
  obtain ⟨e,rfl⟩ := (qSyndromeEquiv P S q).surjective p
  rw [localCq_delta1_apply, q_restrict_correction]
  exact rxCoboundary1_q_of_x_restrictions_zero P S w hx q e

end QEC.Coding.BDL26RXDecoderAdapter
