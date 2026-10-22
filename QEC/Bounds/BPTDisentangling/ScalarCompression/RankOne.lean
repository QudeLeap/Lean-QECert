import QEC.Bounds.BPTDisentangling.InteractionAlgebra

/-!
# Scalar compression rank-one engine

Internal linear-algebra layer for the finite-dimensional BPT argument.
-/

noncomputable section

namespace QEC
namespace Bounds

open scoped ComplexOrder

universe u

namespace BPTCommutingProjectorModel

/--
A symmetric projection whose compression of every ambient operator is scalar
has range of dimension at most one.
-/
theorem finrank_range_le_one_of_all_scalar_compression
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection)
    (hscalar : ∀ X : Semantics.Operator H, ∃ scalar : Complex,
      P * X * P = scalar • P) :
    Module.finrank Complex (LinearMap.range P) ≤ 1 := by
  let C : Semantics.QuantumCode H := ⟨LinearMap.range P⟩
  letI : (LinearMap.range P).HasOrthogonalProjection :=
    hP.hasOrthogonalProjection_range
  have hCprojector : C.projector = P := by
    change (LinearMap.range P).starProjection.toLinearMap = P
    ext vector
    refine Submodule.eq_starProjection_of_mem_orthogonal (by simp) ?_
    rw [(LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range
      hP.isIdempotentElem).mp hP.isSymmetric]
    simpa using congr($hP.isIdempotentElem.mul_one_sub_self vector)
  have hCscalar : ∀ X : Semantics.Operator H, ∃ scalar : Complex,
      C.projector * X * C.projector = scalar • C.projector := by
    intro X
    rcases hscalar X with ⟨scalar, hX⟩
    exact ⟨scalar, by simpa [hCprojector] using hX⟩
  have hrank := finrank_carrier_le_one_of_all_scalar_compression C hCscalar
  change Module.finrank Complex (LinearMap.range P) ≤ 1 at hrank
  exact hrank

end BPTCommutingProjectorModel
end Bounds
end QEC
