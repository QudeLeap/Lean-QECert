import Mathlib.RingTheory.Kaehler.Basic

/-!
# Composition and image of Kähler differential maps

The universal property proves composition along genuine compatible scalar
towers. Surjectivity of the intermediate algebra map identifies the actual
differential images in the target field.
-/

namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]

/-- Universal field differential maps compose along compatible scalar towers. -/
lemma kaehler_field_map_comp (η : KaehlerDifferential R A) :
    KaehlerDifferential.map R R A K η =
      KaehlerDifferential.map R R B K (KaehlerDifferential.map R R A B η) := by
  have h : KaehlerDifferential.map R R A K =
      ((KaehlerDifferential.map R R B K).restrictScalars A).comp
        (KaehlerDifferential.map R R A B) := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change KaehlerDifferential.map R R A K (KaehlerDifferential.D R A a) =
      KaehlerDifferential.map R R B K
        (KaehlerDifferential.map R R A B (KaehlerDifferential.D R A a))
    rw [KaehlerDifferential.map_D,KaehlerDifferential.map_D,KaehlerDifferential.map_D]
    exact congrArg (KaehlerDifferential.D R K) (IsScalarTower.algebraMap_apply A B K a)
  exact congrArg (fun f => f η) h

/-- A genuine surjective intermediate ring map preserves the differential image in the field. -/
lemma kaehler_field_map_range_iff (h : Function.Surjective (algebraMap A B))
    (ω : KaehlerDifferential R K) :
    ω ∈ (KaehlerDifferential.map R R A K).range ↔
      ω ∈ (KaehlerDifferential.map R R B K).range := by
  constructor
  · rintro ⟨η,rfl⟩
    exact ⟨KaehlerDifferential.map R R A B η,(kaehler_field_map_comp R A B K η).symm⟩
  · rintro ⟨η,rfl⟩
    obtain ⟨ζ,rfl⟩ := KaehlerDifferential.map_surjective_of_surjective R R A B h η
    exact ⟨ζ,kaehler_field_map_comp R A B K ζ⟩

end
end QEC.Coding.AlgebraicGeometry
