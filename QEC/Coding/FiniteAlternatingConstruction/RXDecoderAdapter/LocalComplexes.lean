import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter.Reindex

/-! # Actual local RX complexes on owner-fibre coordinates -/

namespace QEC.Coding.BDL26RXDecoderAdapter

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
open scoped Classical

noncomputable def localCx (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :=
  reindexComplex (rxCx P x S) (Equiv.refl _) (xCorrectionEquiv P S x) (xSyndromeEquiv P S x)

noncomputable def localCq (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :=
  reindexComplex (rxCq P q S) (Equiv.refl _) (qCorrectionEquiv P S q) (qSyndromeEquiv P S q)

/-- Reindexing the actual X cohomology preserves its proved zero quotient. -/
noncomputable def localCxCohomologyEquiv (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) :
    (localCx P S x).middleCohomology ≃ₗ[BDL26Field] (rxCx P x S).middleCohomology :=
  reindexCohomologyEquiv _ _ _ _

/-- The Q coordinate chart is inherited from the actual cylinder quotient. -/
noncomputable def localCqCohomologyEquiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) :
    (localCq P S q).middleCohomology ≃ₗ[BDL26Field] BDL26Field :=
  (reindexCohomologyEquiv (rxCq P q S) (Equiv.refl _)
    (qCorrectionEquiv P S q) (qSyndromeEquiv P S q)).trans
      (LinearEquiv.ofBijective (rxCqH1Coordinate P q S) (rxCqH1Coordinate_bijective P A q S))

theorem localCx_exact (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) :
    LinearMap.ker (wordLinearMapTranspose (localCx P S x).boundary2) =
      LinearMap.range (wordLinearMapTranspose (localCx P S x).boundary1) := by
  apply le_antisymm
  · intro w hw
    let c : (localCx P S x).middleCocycleCode.carrier := ⟨w,hw⟩
    have hz : (Submodule.Quotient.mk c : (localCx P S x).middleCohomology) = 0 := by
      apply (localCxCohomologyEquiv P S x).injective
      apply (rxCxH1Coordinate_bijective P A R x S).1
      simp [rxCxH1Coordinate]
    exact (Submodule.Quotient.mk_eq_zero (localCx P S x).middleCoboundaryInCocycles).1 hz
  · exact (localCx P S x).firstCoboundaryCheckCode_le_middleCocycleCode

theorem localCq_finrank (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) :
    Module.finrank BDL26Field (localCq P S q).middleCohomology = 1 := by
  rw [(localCqCohomologyEquiv P A S q).finrank_eq]
  exact Module.finrank_self BDL26Field

end QEC.Coding.BDL26RXDecoderAdapter
