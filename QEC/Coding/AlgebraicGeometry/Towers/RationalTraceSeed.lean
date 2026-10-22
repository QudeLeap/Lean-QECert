import QEC.Coding.AlgebraicGeometry.Towers.BasicProjectionRefinement
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWPlaces

/-!
# The literal additive seed over the rational w-field

The initial extension in the source's F9 chain is `k(w) ⊆ k(x₀)`, where
`w = x₀^16 + x₀`. Its four trace steps start the whole chain before the
recursive coordinate windows and conjugate composita are considered.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

instance sourceGaloisWField_seedScalarTower :
    IsScalarTower F256 SourceGaloisWField (RatFunc F256) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual rational `w` generator is regular or has a simple pole at
every place, not only at the named infinity place. -/
theorem sourceGaloisWFieldGenerator_order_dichotomy
    (P : GlobalPlace F256 SourceGaloisWField) :
    P.order sourceGaloisWFieldGenerator = -1 ∨
      0 ≤ P.order sourceGaloisWFieldGenerator := by
  have h := rationalPlace_order_X_dichotomy
    (GlobalPlace.comapAlgEquiv sourceGaloisWFieldEquivRatFunc P)
  simpa only [GlobalPlace.comapAlgEquiv_order, sourceGaloisWFieldEquivRatFunc_X] using h

/-- The actual initial rational field has a normalized four-trace
refinement over `k(w)`, at the contraction of any final prime of its
integral model. The parameter is the literal `w`, not the recursive RHS. -/
theorem sourceGaloisWSeed_normalizedRefinement
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A SourceGaloisWField] [IsFractionRing A SourceGaloisWField]
    [Algebra A (RatFunc F256)] [IsScalarTower A SourceGaloisWField (RatFunc F256)]
    [Module.Finite A (integralClosure A (RatFunc F256))]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (RatFunc F256))) :
    NormalizedRefinement A SourceGaloisWField (RatFunc F256) Q ⊥ ⊤ := by
  have h := artinSchreier16_bottom_normalizedRefinement A SourceGaloisWField
    (RatFunc F256) Q sourceGaloisWFieldGenerator RatFunc.X rfl
    sourceGaloisWFieldGenerator_order_dichotomy
  have htop : SourceGaloisWField⟮(RatFunc.X : RatFunc F256)⟯ = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top F256 RatFunc.adjoin_X
  rwa [htop] at h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
