import QEC.Coding.AlgebraicGeometry.Towers.NormalizedCompositumEdges

/-!
# Actual integral-model endpoints of a normalized refinement

The bottom and top copies in the intermediate-field lattice are degree-one
field identifications. Their unit differents allow the normalized-chain
different formula to be stated directly on the original integral closure.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Module.IsTorsionFree A E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))

local instance endpointAmbientModelTorsionFree : Module.IsTorsionFree A (integralClosure A E) :=
  IsIntegralClosure.isTorsionFree A E

/-- A complete normalized refinement computes the actual original
integral closure's different at the supplied final prime. -/
theorem NormalizedRefinement.integralClosure_weakDifferent
    (h : NormalizedRefinement A F E Q ⊥ ⊤) :
    multiplicity Q.asIdeal (differentIdeal A (integralClosure A E)) =
      2 * ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  let K : IntermediateField F E := ⊥
  let L : IntermediateField F E := ⊤
  let C₀ := IntermediateIntegralModels.Model A F E K
  let C₁ := IntermediateIntegralModels.Model A F E L
  let P₀ := IntermediateIntegralModels.prime A F E Q K
  let P₁ := IntermediateIntegralModels.prime A F E Q L
  let p := Q.under A
  letI : Fact (K ≤ L) := ⟨bot_le⟩
  letI : IsFractionRing (integralClosure A E) E :=
    integralClosure.isFractionRing_of_finite_extension F E
  letI : Module.IsTorsionFree A (integralClosure A E) := IsIntegralClosure.isTorsionFree A E
  letI : P₀.asIdeal.LiesOver p.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change Ideal.comap (algebraMap A (integralClosure A E)) Q.asIdeal =
      Ideal.comap (algebraMap A C₀) (Ideal.comap (algebraMap C₀ (integralClosure A E)) Q.asIdeal)
    rw [Ideal.comap_comap]
    rfl
  letI : Q.asIdeal.LiesOver P₁.asIdeal := ⟨rfl⟩
  letI : P₁.asIdeal.LiesOver p.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change Ideal.comap (algebraMap A (integralClosure A E)) Q.asIdeal =
      Ideal.comap (algebraMap A C₁) (Ideal.comap (algebraMap C₁ (integralClosure A E)) Q.asIdeal)
    rw [Ideal.comap_comap]
    rfl
  letI : Module.IsTorsionFree C₁ (integralClosure A E) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra C₁ E := ((algebraMap L E).comp (algebraMap C₁ L)).toAlgebra
  letI : IsScalarTower C₁ L E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C₁ (integralClosure A E) E := IsScalarTower.of_algebraMap_eq' rfl
  have h₀ := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    A C₀ F K p P₀ IntermediateField.finrank_bot).2
  have h₁ := NormalizedRefinement.weakDifferent A F E Q h
  have hthrough := weakDifferent_tower_of_fractionFields A C₀ C₁ F L p P₀ P₁ h₀ h₁
  have htop := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    C₁ (integralClosure A E) L E P₁ Q IntermediateField.finrank_top).2
  exact weakDifferent_tower_of_fractionFields A C₁ (integralClosure A E) F E p P₁ Q hthrough htop

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
