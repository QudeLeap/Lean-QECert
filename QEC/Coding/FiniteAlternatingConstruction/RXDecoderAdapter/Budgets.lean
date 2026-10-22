import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Flow

/-! # Actual RX budgets identities -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

/-- F12 on the actual X fibre, with the global outgoing flow norm. -/
theorem localCx_budget (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : P.X)
    (s : Word BDL26Field (LocalRegionIndex ((localX P S).syndromeRegion x)))
    (hs : s ∈ LinearMap.range (wordLinearMapTranspose (localCx P S x).boundary2)) :
    ∃ f : Word BDL26Field (LocalRegionIndex ((localX P S).correctionRegion x)),
      wordLinearMapTranspose (localCx P S x).boundary2 f = s ∧
        HammingWeight (xFlow P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f)) ≤
          HammingWeight s := by
  let rawS := (wordEquiv (xSyndromeEquiv P S x)).symm s
  have hrange : rawS ∈ LinearMap.range (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)) := by
    obtain ⟨f,hf⟩ := hs
    refine ⟨(wordEquiv (xCorrectionEquiv P S x)).symm f, ?_⟩
    funext face
    have h := congrFun hf (xSyndromeEquiv P S x face)
    rw [localCx_delta1_apply] at h
    exact h
  obtain ⟨rawF,hf,hw⟩ := rxCx_exists_local_weight_le_all_q
    P A R x S rawS hrange
  refine ⟨wordEquiv (xCorrectionEquiv P S x) rawF, ?_, ?_⟩
  · funext p
    obtain ⟨face,rfl⟩ := (xSyndromeEquiv P S x).surjective p
    rw [localCx_delta1_apply, LinearEquiv.symm_apply_apply, hf]
    rfl
  · rw [LinearEquiv.symm_apply_apply, xFlow_weight P A.toTannerSquareAdmissibleV2.toTannerSquareAdmissible]
    have hweight : HammingWeight rawS = HammingWeight s :=
      wordEquiv_weight (xSyndromeEquiv P S x).symm s
    exact hw.trans_eq hweight

/-- F12 on the actual Q fibre, retaining all doubled-Z coordinates. -/
theorem localCq_budget (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (s : Word BDL26Field (LocalRegionIndex ((localQ P S).syndromeRegion q)))
    (hs : s ∈ LinearMap.range (wordLinearMapTranspose (localCq P S q).boundary2)) :
    ∃ f : Word BDL26Field (LocalRegionIndex ((localQ P S).correctionRegion q)),
      wordLinearMapTranspose (localCq P S q).boundary2 f = s ∧
        HammingWeight (qFlow P S q ((wordEquiv (qCorrectionEquiv P S q)).symm f)) ≤
          HammingWeight s := by
  let rawS := (wordEquiv (qSyndromeEquiv P S q)).symm s
  have hrange : rawS ∈ LinearMap.range (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)) := by
    obtain ⟨f,hf⟩ := hs
    refine ⟨(wordEquiv (qCorrectionEquiv P S q)).symm f, ?_⟩
    funext edge
    have h := congrFun hf (qSyndromeEquiv P S q edge)
    rw [localCq_delta1_apply] at h
    exact h
  obtain ⟨rawF,hf,hw⟩ := rxCq_exists_global_outgoing_weight_le P q S rawS hrange
  refine ⟨wordEquiv (qCorrectionEquiv P S q) rawF, ?_, ?_⟩
  · funext p
    obtain ⟨edge,rfl⟩ := (qSyndromeEquiv P S q).surjective p
    rw [localCq_delta1_apply, LinearEquiv.symm_apply_apply, hf]
    rfl
  · rw [LinearEquiv.symm_apply_apply, qFlow_weight]
    have hweight : HammingWeight rawS = HammingWeight s :=
      wordEquiv_weight (qSyndromeEquiv P S q).symm s
    exact hw.trans_eq hweight

end QEC.Coding.BDL26RXDecoderAdapter
