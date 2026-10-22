import QEC.Bounds.BPTSeparatedUnion.Transport.FourFactor

/-!
# Exterior action in region coordinates
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
theorem regionFactorization_conj_exteriorLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    ∃ Z : Semantics.Operator (M.fourFactorD region),
      let S := M.regionSubsystem region
      let T := M.regionSubsystem (region ∪ M.externalBoundary region)
      let splitCD := S.complementFactorization T (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)
      S.registerFactorization.conjOperator
          ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P) =
        TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
          (splitCD.symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by
  rcases M.exteriorLocal_eq_regionComplementLift region P with ⟨Z, hP⟩
  refine ⟨Z, ?_⟩
  dsimp
  let S := M.regionSubsystem region
  let T := M.regionSubsystem (region ∪ M.externalBoundary region)
  let splitCD := S.complementFactorization T (by
    intro site hsite
    exact Finset.mem_union_left _ hsite)
  let Q := splitCD.symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)
  have hP' : (M.regionSubsystem (M.exterior region)).extendLocalToRegister P =
      extendComplementToRegister S Q := by
    simpa [S, T, splitCD, Q] using hP
  rw [hP']
  change S.registerFactorization.conjOperator (extendComplementToRegister S Q) =
    TensorProduct.map (1 : Semantics.Operator S.selectedSystem) Q
  unfold extendComplementToRegister
  rw [S.registerFactorization.conjOperator_symm_conjOperator]

end BPTCommutingProjectorModel
end Bounds
end QEC
