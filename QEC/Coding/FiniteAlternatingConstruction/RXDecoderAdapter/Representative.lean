import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Coordinates

/-! # Actual RX representative identities -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

-- Draft after local complex differential coordinates compile.
-- The actual Q quotient coordinate must agree with raw cone-point evaluation.
theorem localCqCoordinate_mk (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (c : (localCq P S q).middleCocycleCode.carrier) :
    localCqCohomologyEquiv P A S q (Submodule.Quotient.mk c) =
      c.1 (qCorrectionEquiv P S q (0, Sum.inl (Sum.inl ()))) := by
  change rxCqH1Coordinate P q S
    (Submodule.Quotient.mk ((reindexForward (rxCq P q S) (Equiv.refl _)
      (qCorrectionEquiv P S q) (qSyndromeEquiv P S q)).mapMiddleCocycle c)) = _
  rw [rxCqH1Coordinate_mk]
  change wordLinearMapTranspose (wordEquiv (qCorrectionEquiv P S q)).toLinearMap
    c.1 (0, Sum.inl (Sum.inl ())) = _
  rw [transpose_wordEquiv]
  rfl

noncomputable def qConstant (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    BDL26Field →ₗ[BDL26Field] (localCq P S q).middleCocycleCode.carrier where
  toFun b := ⟨fun _ => b, by
    change wordLinearMapTranspose (localCq P S q).boundary2 (fun _ => b) = 0
    rw [localCq, reindex_delta1]
    change wordEquiv (qSyndromeEquiv P S q)
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun _ => b)) = 0
    have hz : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun _ => b) = 0 := by
      funext e
      rw [qDoubleCylinderBoundary1, wordLinearMapTranspose_graphBoundary_apply]
      exact ZModModule.add_self b
    rw [hz, map_zero]⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

noncomputable def qRepresentative (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) :
    (localCq P S q).middleCohomology →ₗ[BDL26Field]
      (localCq P S q).middleCocycleCode.carrier :=
  (qConstant P S q).comp (localCqCohomologyEquiv P A S q).toLinearMap

theorem qRepresentative_section (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (h : (localCq P S q).middleCohomology) :
    (localCq P S q).middleCoboundaryInCocycles.mkQ (qRepresentative P A S q h) = h := by
  apply (localCqCohomologyEquiv P A S q).injective
  change localCqCohomologyEquiv P A S q
    (Submodule.Quotient.mk (qRepresentative P A S q h)) = localCqCohomologyEquiv P A S q h
  rw [localCqCoordinate_mk]
  rfl

noncomputable def qCohomologyEquiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    (∀ q : P.Q, (localCq P S q).middleCohomology) ≃ₗ[BDL26Field] Word BDL26Field P.Q where
  toFun h q := localCqCohomologyEquiv P A S q (h q)
  invFun w q := (localCqCohomologyEquiv P A S q).symm (w q)
  left_inv h := by funext q; exact LinearEquiv.symm_apply_apply _ _
  right_inv w := by funext q; exact LinearEquiv.apply_symm_apply _ _
  map_add' a b := by funext q; exact map_add _ _ _
  map_smul' c a := by funext q; exact map_smul (localCqCohomologyEquiv P A S q) c (a q)

@[simp] theorem qRepresentative_value (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field P.Q)
    (p : LocalRegionIndex ((localQ P S).correctionRegion q)) :
    (qRepresentative P A S q ((qCohomologyEquiv P A S).symm w q)).1 p = w q := by
  change localCqCohomologyEquiv P A S q
    ((localCqCohomologyEquiv P A S q).symm (w q)) = w q
  exact LinearEquiv.apply_symm_apply _ _

theorem map1_representative_decomposition (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (w : Word BDL26Field P.Q) :
    rxMap1Coord P S w = ∑ q : P.Q, extendWordLinear ((localQ P S).correctionRegion q)
      (qRepresentative P A S q ((qCohomologyEquiv P A S).symm w q)).1 := by
  funext p
  rw [Finset.sum_apply]
  rcases p with ⟨x,e⟩ | ⟨q,v⟩
  · rw [rxMap1Coord_localEdge]
    symm
    apply Finset.sum_eq_zero
    intro q _
    change extendLocalSignal ((localQ P S).correctionRegion q) _ (Sum.inl ⟨x,e⟩) = 0
    rw [extendLocalSignal, dif_neg]
    intro hp
    have h := (Finset.mem_filter.mp hp).2
    cases h
  · rw [rxMap1Coord_qVertex, Fintype.sum_eq_single q]
    · change w q = extendLocalSignal ((localQ P S).correctionRegion q) _ (Sum.inr ⟨q,v⟩)
      have hp : (Sum.inr ⟨q,v⟩ : RX1 P S) ∈ (localQ P S).correctionRegion q :=
        (qCorrectionEquiv P S q v).2
      simp only [extendLocalSignal, dif_pos hp]
      exact (qRepresentative_value P A S q w _).symm
    · intro r hr
      change extendLocalSignal ((localQ P S).correctionRegion r) _ (Sum.inr ⟨q,v⟩) = 0
      rw [extendLocalSignal, dif_neg]
      intro hp
      exact hr (Vertex.q.inj (Finset.mem_filter.mp hp).2).symm

end QEC.Coding.BDL26RXDecoderAdapter
