import QEC.Bounds.BPTSeparatedUnion.Assembly.JointCoordinates

/-!
# Four-stage intertwining composition

Associativity alone composes four adjacent intertwining equations.
-/

namespace QEC
namespace Bounds

universe u

theorem linearMap_intertwining_four_stage
    {H0 H1 H2 H3 H4 : Type u}
    [AddCommMonoid H0] [Module Complex H0]
    [AddCommMonoid H1] [Module Complex H1]
    [AddCommMonoid H2] [Module Complex H2]
    [AddCommMonoid H3] [Module Complex H3]
    [AddCommMonoid H4] [Module Complex H4]
    (J : H1 →ₗ[Complex] H0) (T : H2 →ₗ[Complex] H1)
    (C : H3 →ₗ[Complex] H2) (O : H4 →ₗ[Complex] H3)
    (V0 : H0 →ₗ[Complex] H0) (V1 : H1 →ₗ[Complex] H1)
    (V2 : H2 →ₗ[Complex] H2) (V3 : H3 →ₗ[Complex] H3)
    (V4 : H4 →ₗ[Complex] H4)
    (h0 : V0.comp J = J.comp V1)
    (h1 : V1.comp T = T.comp V2)
    (h2 : V2.comp C = C.comp V3)
    (h3 : V3.comp O = O.comp V4) :
    V0.comp (J.comp (T.comp (C.comp O))) =
      (J.comp (T.comp (C.comp O))).comp V4 := by
  calc
    V0.comp (J.comp (T.comp (C.comp O))) =
        (V0.comp J).comp (T.comp (C.comp O)) := by
          simp only [LinearMap.comp_assoc]
    _ = (J.comp V1).comp (T.comp (C.comp O)) := by rw [h0]
    _ = J.comp ((V1.comp T).comp (C.comp O)) := by
          simp only [LinearMap.comp_assoc]
    _ = J.comp ((T.comp V2).comp (C.comp O)) := by rw [h1]
    _ = J.comp (T.comp ((V2.comp C).comp O)) := by
          simp only [LinearMap.comp_assoc]
    _ = J.comp (T.comp ((C.comp V3).comp O)) := by rw [h2]
    _ = J.comp (T.comp (C.comp (V3.comp O))) := by
          simp only [LinearMap.comp_assoc]
    _ = J.comp (T.comp (C.comp (O.comp V4))) := by rw [h3]
    _ = (J.comp (T.comp (C.comp O))).comp V4 := by
          simp only [LinearMap.comp_assoc]

theorem linearMap_intertwining_of_eq
    {H K : Type u}
    [AddCommMonoid H] [Module Complex H]
    [AddCommMonoid K] [Module Complex K]
    (embedding coordinates : H →ₗ[Complex] K)
    (physical : K →ₗ[Complex] K) (logical : H →ₗ[Complex] H)
    (hembedding : embedding = coordinates)
    (hcoordinates : physical.comp coordinates = coordinates.comp logical) :
    physical.comp embedding = embedding.comp logical := by
  rw [hembedding]
  exact hcoordinates

end Bounds
end QEC
