import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Coordinates

/-! # Actual RX lifts identities -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

-- Actual degree-zero X injection and its global differential restriction.
noncomputable def xLift (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word BDL26Field (DoubleCylinderVertex P x S) →ₗ[BDL26Field]
      Word BDL26Field (RX0 P S) where
  toFun w p := if h : p.1 = x then w (h ▸ p.2) else 0
  map_add' _ _ := by funext p; by_cases h : p.1 = x <;> simp [h]
  map_smul' _ _ := by funext p; by_cases h : p.1 = x <;> simp [h]

@[simp] theorem xLift_same (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderVertex P x S))
    (v : DoubleCylinderVertex P x S) : xLift P S x w ⟨x,v⟩ = w v := by
  simp [xLift]

@[simp] theorem xLift_other (P : TannerSquarePresentation) (S : OddScale) (x y : P.X)
    (h : y ≠ x) (w : Word BDL26Field (DoubleCylinderVertex P x S))
    (v : DoubleCylinderVertex P y S) : xLift P S x w ⟨y,v⟩ = 0 := by
  simp [xLift, h]

theorem raw_delta0_x (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX0 P S)) (x : P.X) (e : DoubleCylinderEdge P x S) :
    rxCoboundary0 P S w (Sum.inl ⟨x,e⟩) =
      wordLinearMapTranspose (doubleCylinderBoundary1 P x S)
        (fun v => w ⟨x,v⟩) e := by
  unfold rxCoboundary0 rxBoundary1
  rw [wordLinearMapTranspose_toLin'_apply, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single x]
  · simp only [rxBoundary1Matrix, dite_true]
    rw [doubleCylinderBoundary1, wordLinearMapTranspose_toLin'_apply]
  · intro y hy
    apply Finset.sum_eq_zero
    intro v _
    simp [rxBoundary1Matrix, hy]

theorem xLift_sum_at (P : TannerSquarePresentation) (S : OddScale)
    (w : ∀ x : P.X, Word BDL26Field (DoubleCylinderVertex P x S))
    (x : P.X) (v : DoubleCylinderVertex P x S) :
    (∑ y : P.X, xLift P S y (w y)) ⟨x,v⟩ = w x v := by
  rw [Finset.sum_apply, Fintype.sum_eq_single x]
  · exact xLift_same P S x (w x) v
  · intro y hy
    exact xLift_other P S y x (Ne.symm hy) (w y) v

theorem localCx_delta0_apply (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderVertex P x S)) (e : DoubleCylinderEdge P x S) :
    wordLinearMapTranspose (localCx P S x).boundary1 w (xCorrectionEquiv P S x e) =
      wordLinearMapTranspose (doubleCylinderBoundary1 P x S) w e := by
  simp only [localCx, reindex_delta0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    wordEquiv_apply, Equiv.symm_apply_apply]
  rfl

theorem localCx_lift_restriction (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderVertex P x S)) :
    restrictWordLinear ((localX P S).correctionRegion x) (rxCoboundary0 P S (xLift P S x w)) =
      wordLinearMapTranspose (localCx P S x).boundary1 w := by
  funext p
  obtain ⟨e,rfl⟩ := (xCorrectionEquiv P S x).surjective p
  rw [localCx_delta0_apply]
  change rxCoboundary0 P S (xLift P S x w) (Sum.inl ⟨x,e⟩) = _
  rw [raw_delta0_x]
  have hw : (fun v => xLift P S x w ⟨x,v⟩) = w := by
    funext v; exact xLift_same P S x w v
  rw [hw]

theorem localCx_lift_sum_restriction (P : TannerSquarePresentation) (S : OddScale)
    (w : ∀ x : P.X, Word BDL26Field (DoubleCylinderVertex P x S)) (x : P.X) :
    restrictWordLinear ((localX P S).correctionRegion x)
      (rxCoboundary0 P S (∑ y : P.X, xLift P S y (w y))) =
        wordLinearMapTranspose (localCx P S x).boundary1 (w x) := by
  funext p
  obtain ⟨e,rfl⟩ := (xCorrectionEquiv P S x).surjective p
  rw [localCx_delta0_apply]
  change rxCoboundary0 P S (∑ y : P.X, xLift P S y (w y)) (Sum.inl ⟨x,e⟩) = _
  rw [raw_delta0_x]
  have hw : (fun v => (∑ y : P.X, xLift P S y (w y)) ⟨x,v⟩) = w x := by
    funext v; exact xLift_sum_at P S w x v
  rw [hw]

theorem localCq_delta0_zero (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    wordLinearMapTranspose (localCq P S q).boundary1 = 0 := by
  apply LinearMap.ext
  intro w
  have hw : w = 0 := by funext j; exact Fin.elim0 j
  rw [hw, map_zero]
  rfl

end QEC.Coding.BDL26RXDecoderAdapter
