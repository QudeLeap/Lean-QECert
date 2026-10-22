import QEC.Coding.AlgebraicGeometry.Towers.ClosureDifferent
import QEC.Coding.AlgebraicGeometry.Towers.ClosureRegularRefinement
import QEC.Coding.AlgebraicGeometry.Towers.RegularRefinementRamification
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWPrincipalDivisor

/-!
# No different outside the zero and pole of the actual w

The regular source/conjugate chains prove index one at each such actual
prime. Combining this with the established all-prime weak-different law
gives different exponent zero. This supplies the global support input in
Stichtenoth (2006), before any canonical-divisor or genus calculation.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree

variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]

/-- Every prime at which the literal w is a unit has index one and
different exponent zero in the actual closure over k(w). -/
theorem sourceClosureW_integralModel_regular
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)))
    (hw : (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q).valuation
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    (Q.under A).asIdeal.ramificationIdx' Q.asIdeal = 1 ∧
      multiplicity Q.asIdeal (differentIdeal A (integralClosure A (SourceGaloisClosureField m))) = 0 := by
  have he := RegularRefinement.integralClosure_ramificationIdx_eq_one
    A (sourceClosureWBase m) (SourceGaloisClosureField m) Q
    (sourceClosureW_regularRefinement m (heightOnePlace Q) hw)
  refine ⟨he, ?_⟩
  rw [sourceClosureW_integralModel_weakDifferent m A Q, he]

/-- Equivalently, every actual prime outside the support of the principal
divisor of w has different exponent zero. -/
theorem sourceClosureW_integralModel_different_zero_of_order_zero
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)))
    (hw : (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q).order
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 0) :
    multiplicity Q.asIdeal (differentIdeal A (integralClosure A (SourceGaloisClosureField m))) = 0 := by
  apply (sourceClosureW_integralModel_regular m A Q ?_).2
  let R := heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q
  have hlog : WithZero.log (R.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m)) = 0 := by
    change -WithZero.log (R.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m)) = 0 at hw
    omega
  have hne := R.valuation.ne_zero_iff.mpr (sourceGaloisWClosureGenerator_ne_zero m)
  rw [← WithZero.exp_log hne, hlog]
  simp

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
