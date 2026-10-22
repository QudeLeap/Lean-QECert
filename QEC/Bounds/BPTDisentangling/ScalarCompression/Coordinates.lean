import QEC.Bounds.BPTDisentangling.SecondCut.Core

/-!
# BPT selected-sector scalar-compression coordinates

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

set_option maxHeartbeats 300000 in
/--
The physical hM relation compresses to every literal probe on the selected
left isotypic subtype.  This is the source `Pi_AB'` scalar equation before
the later block transport chooses a particular `X`.
-/
theorem secondCut_compressed_scalar_for_left_subtype_probe
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (H : Submodule Complex (M.fourFactorB region))
    (J : Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) →ₗ[Complex]
      Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
    (hJ : J = tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) H)
    (Rcompressed : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hreconstruct : M.secondCutCodeLift region =
      J.comp (Rcompressed.comp (LinearMap.adjoint J)))
    (Esub : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) H)) :
    ∃ scalar : Complex,
      Rcompressed *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) Esub *
          Rcompressed =
        scalar • Rcompressed := by
    let A := M.fourFactorA region
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let B := M.fourFactorB region
    let E := overlapLeftSubtypeLift (A := A) (B := B) H Esub
    let Lprobe := overlapLiftLeft (A := A) (B := B) (C := CD) E
    let Lsub := overlapLiftLeft (A := A) (B := H) (C := CD) Esub
    have hJadjJ : (LinearMap.adjoint J).comp J =
        (1 : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD)) := by
      simpa [hJ] using
        (adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
          (A := A) (C := CD) H)
    rcases M.secondCut_all_leftLocal_scalar_compression_of_region_recoverable region hM E with
      ⟨scalar, hscalar⟩
    have hprobe : (LinearMap.adjoint J).comp (Lprobe.comp J) = Lsub := by
      simpa [hJ] using
        (adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_subtypeLift_comp
          (A := A) (C := CD) H Esub)
    have hcompressed : Rcompressed * Lsub * Rcompressed = scalar • Rcompressed :=
      compressed_scalar_of_named_isometric_reconstruction
        J (M.secondCutCodeLift region) Lprobe Rcompressed Lsub scalar hJadjJ
        hreconstruct hprobe hscalar
    exact ⟨scalar, hcompressed⟩

end BPTCommutingProjectorModel

end Bounds
end QEC
