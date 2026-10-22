import QEC.Bounds.BPTDisentangling.SeparatedUnionBridge
import QEC.Bounds.GeometricLocalityTradeoff.Entropy
noncomputable section

namespace QEC
namespace Bounds
open Classical

open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
`left` and `right` are separated in the exact source sense: no actual local
BPT projector has support meeting both regions.  This deliberately contains no
extra set-disjointness hypothesis.  The terminal proof normalizes `left` to
`left \\ right`; actual separation makes that normalization invisible to every
projector-defined boundary while making the two tensor regions disjoint.
-/
def ActualProjectorSeparated (M : BPTCommutingProjectorModel L kappa)
    (left right : Finset L.Site) : Prop :=
  ∀ check,
    ¬ (((M.support check) ∩ left).Nonempty ∧
      ((M.support check) ∩ right).Nonempty)

/-- Actual-projector separation is symmetric in its two regions. -/
theorem actualProjectorSeparated_comm
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site) :
    M.ActualProjectorSeparated left right ↔
      M.ActualProjectorSeparated right left := by
  constructor
  · intro hoverlap check hboth
    exact hoverlap check ⟨hboth.2, hboth.1⟩
  · intro hoverlap check hboth
    exact hoverlap check ⟨hboth.2, hboth.1⟩

/-- No actual projector touches the overlap of source-separated regions. -/
theorem support_disjoint_intersection_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) (check : kappa) :
    Disjoint (M.support check) (left ∩ right) := by
  rw [Finset.disjoint_left]
  intro site hsupport hintersection
  apply hseparated check
  refine ⟨?_, ?_⟩
  · exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, (Finset.mem_inter.mp hintersection).1⟩⟩
  · exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, (Finset.mem_inter.mp hintersection).2⟩⟩

/--
Removing the overlap from the left region changes neither side of a projector's
source coupling test: actual separation says no projector can see a removed
site.
-/
theorem supportCouples_sdiff_right_iff_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) (check : kappa) :
    M.supportCouples check (left \ right) ↔ M.supportCouples check left := by
  unfold supportCouples
  have hsupport := M.support_disjoint_intersection_of_actualProjectorSeparated
    left right hseparated check
  constructor
  · rintro ⟨hinside, houtside⟩
    constructor
    · rcases hinside with ⟨site, hsite⟩
      rcases Finset.mem_inter.mp hsite with ⟨hsupportSite, hleftMinus⟩
      exact ⟨site, Finset.mem_inter.mpr ⟨hsupportSite, (Finset.mem_sdiff.mp hleftMinus).1⟩⟩
    · rcases houtside with ⟨site, hsite⟩
      rcases Finset.mem_sdiff.mp hsite with ⟨hsupportSite, hnotLeftMinus⟩
      refine ⟨site, Finset.mem_sdiff.mpr ⟨hsupportSite, ?_⟩⟩
      intro hleft
      by_cases hright : site ∈ right
      · exact (Finset.disjoint_left.mp hsupport) hsupportSite
          (Finset.mem_inter.mpr ⟨hleft, hright⟩)
      · exact hnotLeftMinus (Finset.mem_sdiff.mpr ⟨hleft, hright⟩)
  · rintro ⟨hinside, houtside⟩
    constructor
    · rcases hinside with ⟨site, hsite⟩
      rcases Finset.mem_inter.mp hsite with ⟨hsupportSite, hleft⟩
      refine ⟨site, Finset.mem_inter.mpr ⟨hsupportSite, ?_⟩⟩
      refine Finset.mem_sdiff.mpr ⟨hleft, ?_⟩
      intro hright
      exact (Finset.disjoint_left.mp hsupport) hsupportSite
        (Finset.mem_inter.mpr ⟨hleft, hright⟩)
    · rcases houtside with ⟨site, hsite⟩
      rcases Finset.mem_sdiff.mp hsite with ⟨hsupportSite, hnotLeft⟩
      refine ⟨site, Finset.mem_sdiff.mpr ⟨hsupportSite, ?_⟩⟩
      intro hleftMinus
      exact hnotLeft (Finset.mem_sdiff.mp hleftMinus).1

/-- Actual separation preserves the literal source boundary after normalization. -/
theorem boundary_sdiff_right_eq_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    M.boundary (left \ right) = M.boundary left := by
  ext site
  constructor
  · intro hboundary
    rcases (M.mem_boundary_iff (left \ right) site).mp hboundary with
      ⟨check, hcouples, hsupport⟩
    exact (M.mem_boundary_iff left site).mpr ⟨check,
      (M.supportCouples_sdiff_right_iff_of_actualProjectorSeparated left right
        hseparated check).mp hcouples, hsupport⟩
  · intro hboundary
    rcases (M.mem_boundary_iff left site).mp hboundary with ⟨check, hcouples, hsupport⟩
    exact (M.mem_boundary_iff (left \ right) site).mpr ⟨check,
      (M.supportCouples_sdiff_right_iff_of_actualProjectorSeparated left right
        hseparated check).mpr hcouples, hsupport⟩

/-- The source boundary itself never contains a site shared by the two regions. -/
theorem boundary_disjoint_intersection_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    Disjoint (M.boundary left) (left ∩ right) := by
  rw [Finset.disjoint_left]
  intro site hboundary hintersection
  rcases (M.mem_boundary_iff left site).mp hboundary with ⟨check, _, hsupport⟩
  exact (Finset.disjoint_left.mp
    (M.support_disjoint_intersection_of_actualProjectorSeparated left right hseparated check))
      hsupport hintersection

/-- Actual separation preserves the external source boundary after normalization. -/
theorem externalBoundary_sdiff_right_eq_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    M.externalBoundary (left \ right) = M.externalBoundary left := by
  change M.boundary (left \ right) \ (left \ right) = M.boundary left \ left
  rw [M.boundary_sdiff_right_eq_of_actualProjectorSeparated left right hseparated]
  ext site
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨hboundary, hnotLeftMinus⟩
    refine ⟨hboundary, ?_⟩
    intro hleft
    by_cases hright : site ∈ right
    · exact (Finset.disjoint_left.mp
        (M.boundary_disjoint_intersection_of_actualProjectorSeparated left right hseparated))
          hboundary (Finset.mem_inter.mpr ⟨hleft, hright⟩)
    · exact hnotLeftMinus ⟨hleft, hright⟩
  · rintro ⟨hboundary, hnotLeft⟩
    refine ⟨hboundary, ?_⟩
    intro hleftMinus
    exact hnotLeft hleftMinus.1

/-- The normalized left region is literally disjoint from the right region. -/
theorem sdiff_right_disjoint_right (left right : Finset L.Site) :
    Disjoint (left \ right) right := by
  rw [Finset.disjoint_left]
  intro site hleftMinus hright
  exact (Finset.mem_sdiff.mp hleftMinus).2 hright

/-- Actual source separation is stable when the left overlap is normalized away. -/
theorem actualProjectorSeparated_sdiff_right
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    M.ActualProjectorSeparated (left \ right) right := by
  intro check hboth
  apply hseparated check
  refine ⟨?_, hboth.2⟩
  rcases hboth.1 with ⟨site, hsite⟩
  rcases Finset.mem_inter.mp hsite with ⟨hsupport, hleftMinus⟩
  exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, (Finset.mem_sdiff.mp hleftMinus).1⟩⟩

/-- The actual source boundary of the left region is disjoint from the right region. -/
theorem boundary_disjoint_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    Disjoint (M.boundary left) right := by
  rw [Finset.disjoint_left]
  intro site hboundary hright
  rcases (M.mem_boundary_iff left site).1 hboundary with
    ⟨check, hcouples, hsite⟩
  apply hseparated check
  refine ⟨?_, ?_⟩
  · exact hcouples.1
  · exact ⟨site, Finset.mem_inter.mpr ⟨hsite, hright⟩⟩

/-- The external source boundary of the left region is disjoint from the right region. -/
theorem externalBoundary_disjoint_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    Disjoint (M.externalBoundary left) right := by
  rw [Finset.disjoint_left]
  intro site hexternal hright
  exact (Finset.disjoint_left.mp
    (M.boundary_disjoint_of_actualProjectorSeparated left right hseparated))
      (Finset.mem_sdiff.mp hexternal).1 hright

/--
Actual-projector separation leaves the right region outside both the left
region and its external boundary, namely in the source exterior `D`.
-/
theorem union_externalBoundary_disjoint_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right) :
    Disjoint (left ∪ M.externalBoundary left) right := by
  rw [Finset.disjoint_union_left]
  exact ⟨hdisjoint, M.externalBoundary_disjoint_of_actualProjectorSeparated
    left right hseparated⟩

/--
The second source region is contained in `D = complement M1 \\ partialPlus M1`.
This is derived from actual projector support separation rather than a graph
distance convention.
-/
theorem subset_exterior_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right) :
    right ⊆ M.exterior left := by
  intro site hright
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · apply Finset.mem_compl.mpr
    intro hleft
    exact (Finset.disjoint_left.mp hdisjoint) hleft hright
  · intro hexternal
    exact (Finset.disjoint_left.mp
      (M.union_externalBoundary_disjoint_of_actualProjectorSeparated left right hseparated hdisjoint))
      (Finset.mem_union_right _ hexternal) hright

end BPTCommutingProjectorModel
end Bounds
end QEC
