import QEC.Bounds.BPTSeparatedUnion.Factorizations.Factorization
import QEC.Bounds.BPTSeparatedUnion.Separation

/-!
# BPT separated-union correctability

This terminal module exposes BPT `lemma:union` (`2Dgeneral_codes08.tex:698--727`).
Its cacheable support, transport, factorization, and source-factorization
lemmas remain in the `BPTSeparatedUnion/` implementation modules.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v
namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
The BPT separated-union lemma (`2Dgeneral_codes08.tex`, lines 698--727).
`ActualProjectorSeparated` refers to the supports of the concrete commuting
projectors supplied by #378, exactly as in the source.  It first removes the
overlap `left ∩ right` from `left`: actual support separation preserves the
projector-defined boundary and its external part, while erasure recoverability
is monotone under this shrinking.  The resulting two regions are disjoint, so
the proof follows the source's rank-one disentangling calculation through the
retained #388 final-assembly witness, then uses the finite-qudit
no-information/recovery equivalence from #402.
-/
theorem regionErasureRecoverable_union_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hleft : M.RegionErasureRecoverable left)
    (hright : M.RegionErasureRecoverable right)
    (hexternal : M.RegionErasureRecoverable (M.externalBoundary left)) :
    M.RegionErasureRecoverable (left ∪ right) := by
  let normalizedLeft := left \ right
  have hnormalizedSeparated : M.ActualProjectorSeparated normalizedLeft right :=
    M.actualProjectorSeparated_sdiff_right left right hseparated
  have hnormalizedDisjoint : Disjoint normalizedLeft right :=
    sdiff_right_disjoint_right left right
  have hnormalizedLeft : M.RegionErasureRecoverable normalizedLeft := by
    apply (M.regionSubsystem normalizedLeft).erasureRecoverableFromRegister_mono
      (M.regionSubsystem left) ?_ M.codeSpace hleft
    simpa only [M.regionSubsystem_selected] using Finset.sdiff_subset
  have hboundary : M.externalBoundary normalizedLeft = M.externalBoundary left :=
    M.externalBoundary_sdiff_right_eq_of_actualProjectorSeparated left right hseparated
  have hnormalizedExternal : M.RegionErasureRecoverable (M.externalBoundary normalizedLeft) := by
    simpa only [hboundary] using hexternal
  have hunion : normalizedLeft ∪ right = left ∪ right := by
    dsimp [normalizedLeft]
    ext site
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [← hunion]
  by_cases hcode : M.codeSpace.carrier = ⊥
  · exact M.regionErasureRecoverable_of_codeSpace_carrier_eq_bot
      (normalizedLeft ∪ right) hcode
  apply ((M.regionSubsystem (normalizedLeft ∪ right)).noInformationOn_iff_exists_erasureRecovery
    M.codeSpace L.localDimension_positive).mp
  apply ((M.regionSubsystem (normalizedLeft ∪ right)).noInformationOn_iff_allLocalScalarCompression
    M.codeSpace).mpr
  apply M.allLocalScalarCompression_union_of_product normalizedLeft right hnormalizedDisjoint
  intro A B
  apply M.scalarCompression_product_of_source_factorization normalizedLeft right hright
  exact M.sourceFactorization_of_actualProjectorSeparated
    normalizedLeft right hnormalizedSeparated hnormalizedDisjoint hnormalizedLeft
      hnormalizedExternal hcode

end BPTCommutingProjectorModel
end Bounds
end QEC
